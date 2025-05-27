/**
 * Extract variables and their types from SSA code
 * @param {Array<string>} ssaCode - Array of SSA code lines
 * @returns {Object} - Map of variable names to their types
 */
export const extractVariables = (ssaCode) => {
    const variables = {};
    const arrayPattern = /\b(arr_\d+|p2_arr_\d+)\b/;
    const varPattern = /\b([a-zA-Z_][a-zA-Z0-9_]*)\b/g;
  
    ssaCode.forEach(line => {
      // Check for array declarations or usage
      if (arrayPattern.test(line)) {
        const arrays = line.match(arrayPattern);
        arrays.forEach(arr => {
          variables[arr] = '(Array Int Int)';
        });
      }
  
      // Extract other variables
      const matches = line.match(varPattern);
      if (matches) {
        matches.forEach(varName => {
          if (!variables[varName] && !isKeyword(varName) && !/^\d+$/.test(varName)) {
            if (varName.startsWith('cond_') || varName.startsWith('flag_')) {
              variables[varName] = 'Bool';
            } else {
              variables[varName] = 'Int';
            }
          }
        });
      }
    });
  
    return variables;
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