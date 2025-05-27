/**
 * Convert AST to Static Single Assignment form with proper loop unrolling
 * @param {Array} ast - Abstract Syntax Tree of the program
 * @param {number} unrollDepth - Number of times to unroll loops
 * @returns {Object} - Original AST, transformed SSA code, optimized SSA, and assertions
 */
const convertToSSA = (ast, unrollDepth = 3) => {
    const ssa = [];
    const assertions = []; // Store assertions separately
    let varVersions = { 
      sum: 0, i: 0, j: 0, temp: 0, arr: 0, min_idx: 0, n: 0, x: 0, y: 0,
      out: 0, out1: 0, out2: 0, in: 0, result: 0, flag: 0, cond: 0
    };
  
    /**
     * Get the next version of a variable
     * @param {string} varName - Base variable name
     * @returns {string} - SSA variable name with version
     */
    const getNextVersion = (varName) => {
      if (!varVersions.hasOwnProperty(varName)) {
        varVersions[varName] = 0;
      }
      varVersions[varName] += 1;
      return `${varName}_${varVersions[varName]}`;
    };
  
    /**
     * Convert an expression to SMT-LIB format
     * @param {string} expr - Expression to convert
     * @returns {string} - SMT-LIB formatted expression
     */
    const convertToSMTExpr = (expr) => {
      if (!expr) return '';
      
      // Clean up the expression - remove comments and trailing whitespace
      expr = expr.replace(/;.*$/, '').replace(/\/\/.*$/, '').trim();
      
      // Already in SMT format
      if (expr.startsWith('(') && expr.endsWith(')')) {
        return expr;
      }
      
      // Handle array access: arr[i] becomes (select arr i)
      expr = expr.replace(/(\w+)\[([^\]]+)\]/g, '(select $1 $2)');
      
      // Convert operators to SMT-LIB format
      return expr
        .replace(/(\w+)\s*\+\s*(\w+)/g, '(+ $1 $2)')
        .replace(/(\w+)\s*\-\s*(\w+)/g, '(- $1 $2)')
        .replace(/(\w+)\s*\*\s*(\w+)/g, '(* $1 $2)')
        .replace(/(\w+)\s*\/\s*(\w+)/g, '(div $1 $2)')
        .replace(/(\w+)\s*%\s*(\w+)/g, '(mod $1 $2)')
        .replace(/(\w+)\s*==\s*(\w+)/g, '(= $1 $2)')
        .replace(/(\w+)\s*!=\s*(\w+)/g, '(not (= $1 $2))')
        .replace(/(\w+)\s*<\s*(\w+)/g, '(< $1 $2)')
        .replace(/(\w+)\s*<=\s*(\w+)/g, '(<= $1 $2)')
        .replace(/(\w+)\s*>\s*(\w+)/g, '(> $1 $2)')
        .replace(/(\w+)\s*>=\s*(\w+)/g, '(>= $1 $2)')
        .replace(/(\w+)\s*&&\s*(\w+)/g, '(and $1 $2)')
        .replace(/(\w+)\s*\|\|\s*(\w+)/g, '(or $1 $2)')
        .replace(/!\s*(\w+)/g, '(not $1)');
    };
  
    /**
     * Process an AST block and convert it to SSA
     * @param {Array} block - AST block
     * @param {string} prefix - Line prefix for proper indentation
     * @param {number} depth - Current nesting depth
     */
    const processBlock = (block, prefix = '', depth = 0) => {
      if (!block || !Array.isArray(block)) return;
  
      for (let node of block) {
        if (!node) continue;
  
        if (node.type === 'assignment' && node.value) {
          const value = node.value;
          
          // Handle for loops
          if (value.startsWith('for')) {
            const loopMatch = value.match(/for\s*\(\s*([^:=]+)\s*:?=\s*([^;]+);\s*([^;]+);\s*([^)]+)\)/);
            if (loopMatch) {
              const [, varName, initVal, condition, update] = loopMatch.map(s => s.trim());
              let currentVar = getNextVersion(varName);
              
              // Initialize loop variable
              ssa.push(`${prefix}${currentVar} = ${convertToSMTExpr(initVal)}`);
  
              // Unroll the loop
              for (let i = 0; i < unrollDepth; i++) {
                ssa.push(`${prefix}// Unrolled iteration ${i + 1}`);
                
                // Add loop condition assertion
                const condExpr = condition.replace(new RegExp(`\\b${varName}\\b`, 'g'), currentVar);
                assertions.push(`${prefix}(assert ${convertToSMTExpr(condExpr)})`);
  
                // Process loop body
                if (node.block) {
                  processBlock(node.block, `${prefix}  `, depth + 1);
                }
  
                // Update loop variable
                const nextVar = getNextVersion(varName);
                let updateExpr;
                
                if (update.includes('++') || update.includes('+=1')) {
                  updateExpr = `(+ ${currentVar} 1)`;
                } else if (update.includes('--') || update.includes('-=1')) {
                  updateExpr = `(- ${currentVar} 1)`;
                } else if (update.includes('+=')) {
                  const increment = update.split('+=')[1].trim();
                  updateExpr = `(+ ${currentVar} ${increment})`;
                } else if (update.includes('-=')) {
                  const decrement = update.split('-=')[1].trim();
                  updateExpr = `(- ${currentVar} ${decrement})`;
                } else {
                  // Generic update expression
                  updateExpr = convertToSMTExpr(update.replace(varName, currentVar));
                }
                
                ssa.push(`${prefix}${nextVar} = ${updateExpr}`);
                currentVar = nextVar;
              }
            }
          } 
          // Handle simple assignments
          else if (value.includes(':=') || value.includes('=')) {
            let parts = value.split(':=');
            if (parts.length === 1) {
              parts = value.split('=');
            }
            
            if (parts.length !== 2) continue; // Skip invalid assignments
            
            const [varName, expr] = parts.map(s => s.trim());
            
            // Handle array assignments: arr[i] = expr
            if (varName.includes('[')) {
              const arrayMatch = varName.match(/([a-zA-Z_][a-zA-Z0-9_]*)\[([^\]]+)\]/);
              if (arrayMatch) {
                const arrayName = arrayMatch[1];
                const index = arrayMatch[2];
                
                // Convert index to SSA form if needed
                const ssaIndex = isVariable(index) && varVersions[index] ? 
                  `${index}_${varVersions[index]}` : index;
                
                // Create new array version with store operation
                const newArrVar = getNextVersion(arrayName);
                const prevArrVar = `${arrayName}_${varVersions[arrayName] || 0}`;
                
                ssa.push(`${prefix}${newArrVar} = (store ${prevArrVar} ${ssaIndex} ${convertToSMTExpr(expr)})`);
              }
            } 
            // Handle regular variable assignments
            else {
              const newVar = getNextVersion(varName);
              let smtExpr = convertToSMTExpr(expr);
              
              // Handle array accesses in the expression
              if (expr.includes('[')) {
                const arrayAccesses = expr.match(/(\w+)\[([^\]]+)\]/g);
                if (arrayAccesses) {
                  let modifiedExpr = expr;
                  for (const access of arrayAccesses) {
                    const [arrayName, index] = access.replace('[', ' ').replace(']', '').split(' ');
                    const ssaIndex = isVariable(index) && varVersions[index] ? 
                      `${index}_${varVersions[index]}` : index;
                    const ssaArray = `${arrayName}_${varVersions[arrayName] || 0}`;
                    modifiedExpr = modifiedExpr.replace(
                      access, `(select ${ssaArray} ${ssaIndex})`
                    );
                  }
                  smtExpr = convertToSMTExpr(modifiedExpr);
                }
              }
              
              ssa.push(`${prefix}${newVar} = ${smtExpr}`);
            }
          }
        } 
        // Handle if statements
        else if (node.type === 'if') {
          const condition = convertToSMTExpr(node.condition || 'true');
          ssa.push(`${prefix}if ${condition}`);
          
          if (node.thenBlock) {
            processBlock(node.thenBlock, `${prefix}  `, depth + 1);
          }
          
          if (node.elseBlock && node.elseBlock.length) {
            ssa.push(`${prefix}else`);
            processBlock(node.elseBlock, `${prefix}  `, depth + 1);
          }
          
          ssa.push(`${prefix}}`);
        } 
        // Handle loops (while/for)
        else if (node.type === 'loop') {
          const condition = convertToSMTExpr(node.condition || 'true');
          ssa.push(`${prefix}while ${condition}`);
          
          // Unroll the loop
          for (let i = 0; i < unrollDepth; i++) {
            ssa.push(`${prefix}// Unrolled iteration ${i + 1}`);
            assertions.push(`${prefix}(assert ${condition})`);
            
            if (node.block) {
              processBlock(node.block, `${prefix}  `, depth + 1);
            }
          }
          
          ssa.push(`${prefix}}`);
        } 
        // Handle assertions
        else if (node.type === 'assert') {
          const condition = convertToSMTExpr(node.condition || 'true');
          assertions.push(`${prefix}(assert ${condition})`);
        }
      }
    };
  
    // Check if a string is a variable name
    const isVariable = (str) => {
      return /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(str);
    };
  
    // Initialize with default variables
    ssa.push('; Initial variable declarations');
    ssa.push('n_0 = 10 ; Default array size');
    ssa.push('out_0 = 0 ; Initial output value');
    ssa.push('out1_0 = 0 ; Initial output for program 1');
    ssa.push('out2_0 = 0 ; Initial output for program 2');
    ssa.push('arr_0 = (store (store (store (store (store (store (store (store (store (store ((as const (Array Int Int)) 0) 0 1) 1 2) 2 3) 3 4) 4 5) 5 6) 6 7) 7 8) 8 9) 9 10) ; Default array initialization');
  
    // Process the AST
    processBlock(ast);
  
    // Optimize SSA
    const optimizedSsa = optimizeSSA(ssa);
    
    return { 
      original: ast, 
      transformed: ssa, 
      optimized: optimizedSsa, 
      assertions 
    };
  };
  
  /**
   * Optimize SSA code by eliminating unnecessary assignments
   * @param {Array} ssa - SSA code
   * @returns {Array} - Optimized SSA code
   */
  const optimizeSSA = (ssa) => {
    const optimized = [];
    const lastAssignments = {};
    const controlFlow = [];
    const usedVars = new Set();
    
    // First pass: collect variable uses and control flow statements
    for (let line of ssa) {
      const trimmedLine = line.trim();
      
      if (trimmedLine.includes(' = ')) {
        const [varName, rhs] = trimmedLine.split(' = ');
        const trimmedVarName = varName.trim();
        
        // Extract variables used in right-hand side
        const varsInRhs = extractVariables(rhs);
        varsInRhs.forEach(v => usedVars.add(v));
        
        // Record the assignment
        lastAssignments[trimmedVarName] = line;
      } 
      else if (trimmedLine.startsWith('if') || 
               trimmedLine.startsWith('for') || 
               trimmedLine.startsWith('while') ||
               trimmedLine.startsWith('else') ||
               trimmedLine.startsWith('assert') ||
               trimmedLine === '}' ||
               trimmedLine.startsWith('//')) {
        
        // Extract variables from control flow statements
        const varsInLine = extractVariables(trimmedLine);
        varsInLine.forEach(v => usedVars.add(v));
        
        controlFlow.push(line);
      } 
      else {
        optimized.push(line);
      }
    }
    
    // Add control flow statements
    optimized.push(...controlFlow);
    
    // Add only used assignments or the last assignment for each variable
    const processedVars = new Set();
    Object.entries(lastAssignments).forEach(([varName, line]) => {
      // Always keep output variables
      if (varName.startsWith('out') || 
          varName.startsWith('out1') || 
          varName.startsWith('out2') || 
          usedVars.has(varName) || 
          !processedVars.has(varName)) {
        
        optimized.push(line);
        processedVars.add(varName);
      }
    });
    
    return optimized;
  };
  
  /**
   * Extract variable names from an expression
   * @param {string} expr - Expression
   * @returns {Array} - List of variable names
   */
  const extractVariables = (expr) => {
    if (!expr) return [];
    
    // Extract identifiers that look like variables
    const matches = expr.match(/[a-zA-Z_][a-zA-Z0-9_]*/g) || [];
    
    // Filter out keywords and numbers
    const keywords = [
      'if', 'else', 'while', 'for', 'assert', 'select', 'store',
      'and', 'or', 'not', 'ite', 'true', 'false'
    ];
    
    return matches.filter(word => 
      !keywords.includes(word) && !/^\d+$/.test(word)
    );
  };
  
  export default convertToSSA;