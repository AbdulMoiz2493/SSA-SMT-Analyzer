/**
 * Generate SMT constraints for program verification or equivalence checking
 * @param {string} mode - 'verification' or 'equivalence'
 * @param {Object} ssa1 - SSA representation of the first program
 * @param {Object} ssa2 - SSA representation of the second program (for equivalence checking)
 * @param {number} unrollDepth - Loop unrolling depth
 * @returns {string} - SMT formula
 */

import { extractVariables } from './variable_extractor.js';
const generateSMT = (mode, ssa1, ssa2, unrollDepth) => {
    let smt = '';
    const declaredVars = new Set();

    // Helper function to sanitize variable names
    const sanitizeVarName = (name) => {
        if (name === 'assert') return '_assert';
        return name.replace(/[^a-zA-Z0-9_]/g, '_');
    };

    const variables1 = extractVariables(ssa1.optimized);
    let variables2 = {};
    if (mode === 'equivalence' && ssa2) {
        variables2 = extractVariables(ssa2.optimized);
    }

    smt += '; SMT-LIB2 formula for ' + mode + ' checking\n';
    smt += '(set-logic QF_ALIA)\n';
    smt += '(set-option :produce-models true)\n\n';

    // Array declarations
    smt += '; Array declarations\n';
    const arrays = ['arr_0', 'arr_1'];
    if (mode === 'equivalence') {
        arrays.push('p2_arr_0', 'p2_arr_1');
    }
    arrays.forEach(arr => {
        if (!declaredVars.has(arr)) {
            smt += `(declare-const ${arr} (Array Int Int))\n`;
            declaredVars.add(arr);
        }
    });

    // Ensure output variables are declared
    smt += '\n; Output variable declarations\n';
    if (!declaredVars.has('out_0')) {
        smt += '(declare-const out_0 Int)\n';
        declaredVars.add('out_0');
    }
    if (mode === 'equivalence') {
        if (!declaredVars.has('out1_0')) {
            smt += '(declare-const out1_0 Int)\n';
            declaredVars.add('out1_0');
        }
        if (!declaredVars.has('out2_0')) {
            smt += '(declare-const out2_0 Int)\n';
            declaredVars.add('out2_0');
        }
    }

    // Variable declarations for first program
    smt += '\n; Variable declarations for program 1\n';
    Object.keys(variables1).forEach(varName => {
        const safeVarName = sanitizeVarName(varName);
        if (isKeyword(safeVarName) || /^\d+$/.test(safeVarName) || declaredVars.has(safeVarName)) return;
        const varType = variables1[varName] === '(Array Int Int)' ? '(Array Int Int)' : variables1[varName] || 'Int';
        smt += `(declare-const ${safeVarName} ${varType})\n`;
        declaredVars.add(safeVarName);
    });

    // Variable declarations for second program
    if (mode === 'equivalence' && Object.keys(variables2).length > 0) {
        smt += '\n; Variable declarations for program 2\n';
        Object.keys(variables2).forEach(varName => {
            const safeVarName = sanitizeVarName(varName);
            if (isKeyword(safeVarName) || /^\d+$/.test(safeVarName)) return;
            let actualVarName = safeVarName.startsWith('out_') && !declaredVars.has(safeVarName) ? safeVarName : `p2_${safeVarName}`;
            if (declaredVars.has(actualVarName)) return;
            const varType = variables2[varName] === '(Array Int Int)' ? '(Array Int Int)' : variables2[varName] || 'Int';
            smt += `(declare-const ${actualVarName} ${varType})\n`;
            declaredVars.add(actualVarName);
        });
    }

    // Helper functions
    smt += '\n; Helper functions\n';
    smt += '(define-fun max ((a Int) (b Int)) Int (ite (>= a b) a b))\n';
    smt += '(define-fun min ((a Int) (b Int)) Int (ite (<= a b) a b))\n';

    // Generate constraints
    if (mode === 'verification') {
        smt += generateVerificationConstraints(ssa1.optimized, ssa1.assertions || []);
    } else {
        smt += generateEquivalenceConstraints(ssa1.optimized, ssa2?.optimized || [], ssa1.assertions || [], ssa2?.assertions || []);
    }

    // Log generated SMT for debugging
    console.log('Generated SMT:\n', smt);

    return smt;
};

/**
 * Generate constraints for program verification
 */
const generateVerificationConstraints = (ssaCode, assertions) => {
    let constraints = '\n; Program constraints\n';

    ssaCode.forEach(line => {
        const constraint = ssaLineToSMT(line);
        if (constraint) {
            constraints += `${constraint.replace(/\bassert\b(?!\s*\()/g, '_assert')}\n`;
        }
    });

    constraints += '\n; Verification assertions\n';
    if (assertions.length > 0) {
        constraints += '(assert (and\n';
        assertions.forEach((assertion, index) => {
            const conditionMatch = assertion.match(/\(assert\s+(.+)\)/);
            if (conditionMatch) {
                let condition = conditionMatch[1];
                condition = condition.replace(/\bassert\b(?!\s*\()/g, '_assert');
                let openParens = (condition.match(/\(/g) || []).length;
                let closeParens = (condition.match(/\)/g) || []).length;
                if (openParens !== closeParens) {
                    console.warn(`Warning: Unbalanced parentheses in assertion ${index + 1}: ${condition}`);
                    condition = 'true'; // Fallback to avoid invalid SMT
                }
                constraints += `  ${condition}\n`;
            }
        });
        constraints += '))\n';
    } else {
        constraints += '(assert (>= out_0 0))\n';
    }

    constraints += '\n; Check satisfiability\n';
    constraints += '(check-sat)\n';
    constraints += '(get-model)\n';

    return constraints;
};

/**
 * Generate constraints for program equivalence checking
 */
const generateEquivalenceConstraints = (ssaCode1, ssaCode2, assertions1, assertions2) => {
    let constraints = '\n; Program 1 constraints\n';

    ssaCode1.forEach(line => {
        const constraint = ssaLineToSMT(line);
        if (constraint) {
            constraints += `${constraint}\n`;
        }
    });

    constraints += '\n; Program 2 constraints\n';
    ssaCode2.forEach(line => {
        let modifiedLine = line;
        const varPattern = /\b([a-zA-Z_][a-zA-Z0-9_]*)\b/g;
        const matches = line.match(varPattern);

        if (matches) {
            for (const match of matches) {
                if (isKeyword(match)) continue;
                if (match.startsWith('out_') || match.startsWith('out1_') || match.startsWith('out2_')) continue;
                const safeMatch = match === 'assert' ? '_assert' : match;
                modifiedLine = modifiedLine.replace(new RegExp(`\\b${match}\\b`, 'g'), `p2_${safeMatch}`);
            }
        }

        const constraint = ssaLineToSMT(modifiedLine);
        if (constraint) {
            constraints += `${constraint}\n`;
        }
    });

    constraints += '\n; Combined assertions\n';
    if (assertions1.length > 0 || assertions2.length > 0) {
        constraints += '(assert (and\n';

        assertions1.forEach(assertion => {
            const conditionMatch = assertion.match(/\(assert\s+(.+)\)/);
            if (conditionMatch) {
                let condition = conditionMatch[1];
                let openParens = (condition.match(/\(/g) || []).length;
                let closeParens = (condition.match(/\)/g) || []).length;
                if (openParens !== closeParens) {
                    console.warn(`Warning: Unbalanced parentheses in assertion: ${condition}`);
                    condition = 'true';
                }
                constraints += `  ${condition}\n`;
            }
        });

        assertions2.forEach(assertion => {
            const conditionMatch = assertion.match(/\(assert\s+(.+)\)/);
            if (conditionMatch) {
                let condition = conditionMatch[1];
                const varPattern = /\b([a-zA-Z_][a-zA-Z0-9_]*)\b/g;
                const matches = condition.match(varPattern);

                if (matches) {
                    for (const match of matches) {
                        if (isKeyword(match)) continue;
                        if (match.startsWith('out_') || match.startsWith('out1_') || match.startsWith('out2_')) continue;
                        const safeMatch = match === 'assert' ? '_assert' : match;
                        condition = condition.replace(new RegExp(`\\b${match}\\b`, 'g'), `p2_${safeMatch}`);
                    }
                }

                let openParens = (condition.match(/\(/g) || []).length;
                let closeParens = (condition.match(/\)/g) || []).length;
                if (openParens !== closeParens) {
                    console.warn(`Warning: Unbalanced parentheses in assertion: ${condition}`);
                    condition = 'true';
                }

                constraints += `  ${condition}\n`;
            }
        });

        constraints += '))\n';
    }

    constraints += '\n; Equivalence check\n';
    constraints += '(assert (not (= out1_0 out2_0)))\n';

    constraints += '\n; Check satisfiability\n';
    constraints += '(check-sat)\n';
    constraints += '(get-model)\n';

    return constraints;
};

/**
 * Convert an SSA statement to SMT constraint
 */
const ssaLineToSMT = (line) => {
    if (!line || typeof line !== 'string') return null;

    line = line.trim();

    if (line === '' || 
        line.startsWith(';') || 
        line.startsWith('//') ||
        line.startsWith('if') || 
        line.startsWith('else') ||
        line.startsWith('while') ||
        line.startsWith('for') ||
        line === '}' ||
        line.includes(' assert ')) {
        return null;
    }

    if (line.startsWith('assert')) {
        return null;
    }

    line = line.replace(/\bassert\b(?!\s*\()/g, '_assert');

    if (line.includes('=')) {
        const parts = line.split('=');
        if (parts.length !== 2) return null;

        const lhs = parts[0].trim();
        const rhs = parts[1].trim();

        if (!lhs || !rhs || isKeyword(lhs)) return null;

        if (rhs.includes('select') || rhs.includes('store')) {
            const fixed_rhs = fixArrayOperations(rhs);
            return `(assert (= ${lhs} ${fixed_rhs}))`;
        }

        return `(assert (= ${lhs} ${convertExprToSMT(rhs)}))`;
    }

    const smtExpr = convertExprToSMT(line);
    if (smtExpr && !isKeyword(smtExpr)) {
        return `(assert ${smtExpr})`;
    }
    return null;
};

/**
 * Fix array operations to conform to SMT-LIB2 syntax
 */
const fixArrayOperations = (expr) => {
    const arrays = ['arr_0', 'arr_1', 'p2_arr_0', 'p2_arr_1'];
    for (const arr of arrays) {
        expr = expr.replace(new RegExp(`\\b${arr}\\b(?![\\s(])`, 'g'), `(as ${arr} (Array Int Int))`);
    }

    expr = expr.replace(/select\s+\(as\s+(\w+)\s+\(Array Int Int\)\)\s+(\w+)/g, '(select (as $1 (Array Int Int)) $2)');
    expr = expr.replace(/store\s+\(as\s+(\w+)\s+\(Array Int Int\)\)\s+(\w+)\s+(\w+)/g, '(store (as $1 (Array Int Int)) $2 $3)');
    expr = expr.replace(/select\s+\(as\s+(\w+)\s+\(Array Int Int\)\)\s+\(\+\s+(\w+)\s+(\w+)\)/g, '(select (as $1 (Array Int Int)) (+ $2 $3))');
    expr = expr.replace(/store\s+\(as\s+(\w+)\s+\(Array Int Int\)\)\s+\(\+\s+(\w+)\s+(\w+)\)\s+(\w+)/g, '(store (as $1 (Array Int Int)) (+ $2 $3) $4)');

    return expr;
};

/**
 * Convert an expression to SMT syntax
 */
const convertExprToSMT = (expr) => {
    if (!expr || typeof expr !== 'string') return '0';

    expr = expr.replace(/;.*$/, '').replace(/\/\/.*$/, '').trim();

    expr = expr.replace(/\bassert\b(?!\s*\()/g, '_assert');

    if (expr === 'assert') {
        return '_assert';
    }

    if (expr.startsWith('(') && expr.endsWith(')')) {
        if (expr.includes('select') || expr.includes('store')) {
            return fixArrayOperations(expr);
        }
        return expr;
    }

    if (/^-?\d+$/.test(expr)) {
        return expr;
    }

    if (expr === 'true' || expr === 'false') {
        return expr;
    }

    if (isKeyword(expr)) {
        return '0';
    }

    if (expr.includes('select') || expr.includes('store')) {
        return fixArrayOperations(expr);
    }

    if (expr.includes('==')) {
        const [left, right] = expr.split('==').map(s => s.trim());
        return `(= ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('!=')) {
        const [left, right] = expr.split('!=').map(s => s.trim());
        return `(not (= ${convertExprToSMT(left)} ${convertExprToSMT(right)}))`;
    }

    if (expr.includes('>=')) {
        const [left, right] = expr.split('>=').map(s => s.trim());
        return `(>= ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('<=')) {
        const [left, right] = expr.split('<=').map(s => s.trim());
        return `(<= ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('>')) {
        const [left, right] = expr.split('>').map(s => s.trim());
        return `(> ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('<')) {
        const [left, right] = expr.split('<').map(s => s.trim());
        return `(< ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('&&')) {
        const [left, right] = expr.split('&&').map(s => s.trim());
        return `(and ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('||')) {
        const [left, right] = expr.split('||').map(s => s.trim());
        return `(or ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.startsWith('!')) {
        return `(not ${convertExprToSMT(expr.substring(1).trim())})`;
    }

    if (expr.includes('+')) {
        const [left, right] = expr.split('+').map(s => s.trim());
        return `(+ ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('-')) {
        const parts = expr.split('-');
        if (parts[0] === '' && parts.length === 2) {
            return `(- ${convertExprToSMT(parts[1])})`;
        } else {
            const [left, right] = [parts[0], parts.slice(1).join('-')];
            return `(- ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
        }
    }

    if (expr.includes('*')) {
        const [left, right] = expr.split('*').map(s => s.trim());
        return `(* ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('/')) {
        const [left, right] = expr.split('/').map(s => s.trim());
        return `(div ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    if (expr.includes('%')) {
        const [left, right] = expr.split('%').map(s => s.trim());
        return `(mod ${convertExprToSMT(left)} ${convertExprToSMT(right)})`;
    }

    const arrayMatch = expr.match(/(\w+)\[([^\]]+)\]/);
    if (arrayMatch) {
        const [, arrayName, index] = arrayMatch;
        return `(select (as ${arrayName} (Array Int Int)) ${convertExprToSMT(index)})`;
    }

    return expr;
};

/**
 * Check if a token is an SMT-LIB keyword
 */
const isKeyword = (token) => {
    const keywords = [
        'declare-const', 'define-fun', 'assert', 'check-sat', 'get-model',
        'and', 'or', 'not', 'ite', 'true', 'false', 'iff', 'xor',
        'let', 'forall', 'exists', 'as', 'par', 'set-logic', 'set-option',
        'Int', 'Bool', 'Real', 'String', 'Array',
        '+', '-', '*', '/', 'div', 'mod', 'abs',
        '=', '!=', '<', '<=', '>', '>=',
        'select', 'store', 'if', 'then', 'else'
    ];

    return keywords.includes(token);
};

export default generateSMT;