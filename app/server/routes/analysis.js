import express from 'express';
import parseProgram from '../utils/parser.js';
import convertToSSA from '../utils/ssa.js';
import generateSMT from '../utils/smt.js';
import { PythonShell } from 'python-shell';
import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs/promises';
import dotenv from 'dotenv';
dotenv.config();

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const router = express.Router();

// Helper function to save response to file
const saveResponse = async (response, filePath) => {
  try {
    await fs.writeFile(filePath, response, 'utf8');
    console.log(`Response saved to ${filePath}`);
    return true;
  } catch (error) {
    console.error('Error saving response:', error.message);
    return false;
  }
};

router.post('/analyze', async (req, res) => {
  const { mode, program1, program2, unrollDepth = 3 } = req.body;
  try {
    console.log('Received request for mode:', mode);

    const ast1 = parseProgram(program1);
    let ast2 = null;
    if (mode === 'equivalence' && program2) {
      ast2 = parseProgram(program2);
    }

    const ssa1 = convertToSSA(ast1, unrollDepth);
    let ssa2 = null;
    if (mode === 'equivalence' && ast2) {
      ssa2 = convertToSSA(ast2, unrollDepth);
    }

    const smt = generateSMT(mode, ssa1, ssa2, unrollDepth);

    // Save SMT to file
    const outputFile = path.join(__dirname, '../debug_processed_smt.txt');
    await saveResponse(smt, outputFile);

    // Run Z3 solver with SMT
    let results;
    try {
      results = await runZ3Solver(smt, mode);
    } catch (z3Error) {
      console.error('Z3 solver error:', z3Error.message);
      results = {
        sat: 'error',
        verified: false,
        interpretation: `Z3 solver error: ${z3Error.message}`,
        counterexample: null,
        model: null
      };
    }

    const status = mode === 'equivalence'
      ? results.verified ? 'equivalent' : 'not_equivalent'
      : results.verified ? 'verified' : 'not_verified';

    res.json({
      ssa: { ssa1, ssa2 },
      smt,
      results,
      status
    });
  } catch (error) {
    console.error('Error in /analyze:', error);
    res.status(500).json({
      error: error.message,
      status: 'error'
    });
  }
});

const runZ3Solver = (smt, mode) => {
  return new Promise((resolve, reject) => {
    const pythonPath = process.env.PYTHON_PATH || 'python3';
    const scriptPath = path.resolve(__dirname, '../utils/z3solver.py');

    const options = {
      mode: 'text',
      pythonOptions: ['-u'],
      args: [JSON.stringify({ smt, mode })],
      pythonPath,
      scriptPath: path.dirname(scriptPath)
    };

    PythonShell.run(path.basename(scriptPath), options)
      .then(results => {
        if (!results || results.length === 0) {
          reject(new Error('No output from Z3 solver'));
          return;
        }

        console.log('Raw Z3 solver output:', results);

        let result;
        try {
          result = JSON.parse(results[0]);
        } catch (parseError) {
          console.error('Failed to parse Z3 solver output as JSON:', parseError.message);
          console.error('Raw output:', results[0]);
          reject(new Error(`Invalid JSON output from Z3 solver: ${results[0]}`));
          return;
        }

        if (result.error) {
          console.error('Z3 solver error:', result.error);
          resolve({
            sat: result.sat || 'error',
            verified: false,
            interpretation: 'Error in Z3 solver: ' + result.error,
            counterexample: null,
            model: null
          });
          return;
        }

        // Parse model and counterexample
        let model = null;
        let counterexample = null;

        if (result.sat === 'sat' && result.model) {
          model = {};
          if (typeof result.model === 'object') {
            Object.entries(result.model).forEach(([varName, value]) => {
              model[varName] = String(value);
            });
          } else {
            model = { result: 'Satisfiable' };
          }
        } else if (result.sat === 'sat') {
          model = { result: 'Satisfiable' };
        }

        if (result.sat === 'sat' && mode === 'equivalence' && result.counterexamples) {
          counterexample = {};
          if (typeof result.counterexamples === 'object') {
            Object.entries(result.counterexamples).forEach(([varName, value]) => {
              counterexample[varName] = String(value);
            });
          } else {
            counterexample = { result: 'Programs are not equivalent' };
          }
        } else if (result.sat === 'unsat' && mode === 'equivalence') {
          model = { result: 'Programs are equivalent' };
          counterexample = null;
        } else if (result.sat === 'sat' && mode === 'verification' && result.counterexamples) {
          counterexample = {};
          if (typeof result.counterexamples === 'object') {
            Object.entries(result.counterexamples).forEach(([varName, value]) => {
              counterexample[varName] = String(value);
            });
          } else {
            counterexample = { result: 'Assertion violation found' };
          }
        }

        if (mode === 'equivalence') {
          resolve({
            sat: result.sat,
            verified: result.sat === 'unsat', // In equivalence, unsat means equivalent
            interpretation: result.sat === 'unsat' ? 'Programs are equivalent' : 'Programs are not equivalent',
            equivalent: result.sat === 'unsat',
            counterexample,
            model
          });
        } else if (mode === 'verification') {
          resolve({
            sat: result.sat,
            verified: result.verified || result.sat === 'sat',
            interpretation: result.verified || result.sat === 'sat' ? 'Program is verified' : 'Program is not verified',
            model,
            counterexample
          });
        }
      })
      .catch(err => {
        console.error('PythonShell error:', err);
        reject(err);
      });
  });
};

export default router;