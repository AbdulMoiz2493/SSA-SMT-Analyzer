import json
import sys
import re
from z3 import *

def preprocess_smt(smt):
    lines = smt.split('\n')
    cleaned_lines = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith('//') or line.startswith('if'):
            continue
        cleaned_lines.append(line)

    var_declarations = {}
    non_duplicate_lines = []
    for line in cleaned_lines:
        if line.startswith('(declare-const '):
            match = re.match(r'\(declare-const\s+([^\s]+)\s+([^)]+)', line)
            if match:
                var_name = match.group(1)
                var_type = match.group(2).strip()
                if var_name == 'assert':
                    var_name = '_assert'
                if var_name not in var_declarations:
                    var_declarations[var_name] = var_type
                    non_duplicate_lines.append(f'(declare-const {var_name} {var_type})')
        else:
            non_duplicate_lines.append(line)

    array_vars = ['arr_0', 'arr_1', 'p2_arr_0', 'p2_arr_1']
    for arr in array_vars:
        if arr in var_declarations and var_declarations[arr] != '(Array Int Int)':
            non_duplicate_lines = [line for line in non_duplicate_lines if not line.startswith(f'(declare-const {arr} ')]
            var_declarations[arr] = '(Array Int Int)'
            non_duplicate_lines.insert(0, f'(declare-const {arr} (Array Int Int))')

    used_vars = set()
    for line in non_duplicate_lines:
        if not line.startswith(';') and not line.startswith('(declare-const'):
            vars_in_line = re.findall(r'(?<!\()\b([a-zA-Z_][a-zA-Z0-9_]*)\b(?!\s*\))', line)
            used_vars.update(vars_in_line)

    keywords = {
        'declare-const', 'define-fun', 'assert', 'check-sat', 'get-model',
        'and', 'or', 'not', 'ite', 'true', 'false', 'iff', 'xor',
        'let', 'forall', 'exists', 'as', 'par', 'set-logic', 'set-option',
        'Int', 'Bool', 'Real', 'String', 'Array',
        '+', '-', '*', '/', 'div', 'mod', 'abs',
        '=', '!=', '<', '<=', '>', '>=',
        'select', 'store'
    }
    
    if 'assert' in used_vars:
        used_vars.remove('assert')
        used_vars.add('_assert')
    
    var_names = [v for v in used_vars if v not in keywords and v not in var_declarations]
    
    declarations = []
    for var in var_names:
        var_type = 'Int'
        if var.startswith(('cond_', 'flag_')):
            var_type = 'Bool'
        elif var in array_vars:
            var_type = '(Array Int Int)'
        declarations.append(f'(declare-const {var} {var_type})')
        var_declarations[var] = var_type

    logic_idx = next((i for i, line in enumerate(non_duplicate_lines) if line.startswith('(set-logic')), -1)
    if logic_idx >= 0:
        non_duplicate_lines[logic_idx + 1:logic_idx + 1] = declarations
    else:
        non_duplicate_lines = declarations + non_duplicate_lines

    fixed_lines = []
    for line in fixed_lines:
        if 'assert' in line and not line.startswith('(assert '):
            line = re.sub(r'(?<!\()\bassert\b(?!\s*\))', '_assert', line)
        fixed_lines.append(line)

    disambiguated_lines = []
    for line in fixed_lines:
        for arr in array_vars:
            if arr in line and ('select' in line or 'store' in line):
                line = re.sub(r'\b' + re.escape(arr) + r'\b(?!\s*\()', 
                              f'(as {arr} (Array Int Int))', line)
        disambiguated_lines.append(line)

    with open("debug_processed_smt.txt", "w") as f:
        f.write('\n'.join(disambiguated_lines))

    return '\n'.join(disambiguated_lines)

def parse_model(model, var_declarations):
    result = {}
    for decl in model.decls():
        name = str(decl.name())
        if name not in var_declarations:
            continue
        try:
            value = model[decl]
            var_type = var_declarations.get(name)
            if var_type == '(Array Int Int)':
                array_vals = {}
                for i in range(10):  # Increased range to capture more array elements
                    try:
                        idx = IntVal(i)
                        val = model.eval(Select(decl(), idx), model_completion=True)
                        if val is not None:
                            array_vals[str(i)] = str(val)
                    except:
                        continue
                value = array_vals if array_vals else "array"
            else:
                value = str(value) if value is not None else "undefined"
            result[name] = value
        except Exception as e:
            print(f"Error evaluating {name}: {str(e)}", file=sys.stderr)
            continue
    return result

def run_z3(smt, mode):
    try:
        processed_smt = preprocess_smt(smt)
        
        with open("debug_smt.txt", "w") as f:
            f.write(processed_smt)
        
        solver = Solver()
        var_declarations = {}
        variables = []
        
        # Parse variable declarations and create Z3 variables
        for line in processed_smt.split('\n'):
            if line.startswith('(declare-const '):
                match = re.match(r'\(declare-const\s+([^\s]+)\s+([^)]+)', line)
                if match:
                    var_name = match.group(1)
                    var_type = match.group(2).strip()
                    var_declarations[var_name] = var_type
                    if var_type == 'Int':
                        variables.append(Int(var_name))
                    elif var_type == 'Bool':
                        variables.append(Bool(var_name))
                    elif var_type == '(Array Int Int)':
                        variables.append(Array(var_name, IntSort(), IntSort()))

        try:
            solver.from_string(processed_smt)
        except Exception as e:
            error_msg = str(e)
            missing_vars = re.findall(r'unknown constant (\w+)', error_msg)
            missing_vars = [v for v in missing_vars if v not in ['assert', 'select', 'store']]
            
            ambiguous_consts = re.findall(r'ambiguous constant reference, more than one constant with the same sort, use a qualified expression \(as <symbol> <sort>\) to disambiguate (\w+)', error_msg)
            
            suggestion = ""
            if missing_vars:
                suggestion = f"Missing variable declarations for: {', '.join(missing_vars)}. "
                suggestion += "Check your SMT generation to ensure all variables are declared before use."
            
            if ambiguous_consts:
                ambig_msg = f"Ambiguous constants detected: {', '.join(ambiguous_consts)}. "
                ambig_msg += "These need to be qualified with their sorts using (as <var> <sort>)."
                suggestion = suggestion + "\n" + ambig_msg if suggestion else ambig_msg
            
            return {
                'error': f"{error_msg}\n{suggestion}",
                'sat': 'error',
                'verified': False,
                'counterexample': None,
                'model': None,
                'smt': processed_smt
            }
        
        result = solver.check()
        
        is_verified = (str(result) == 'unsat')
        
        output = {
            'sat': str(result),
            'verified': is_verified,
            'counterexample': None,
            'model': None
        }
        
        if result == sat:
            model = solver.model()
            parsed_model = parse_model(model, var_declarations)
            # Include all variables in the output
            if mode == 'verification':
                if not is_verified:
                    output['counterexample'] = parsed_model
                else:
                    output['model'] = parsed_model
            else:
                output['counterexample'] = parsed_model
        elif result == unsat:
            if mode == 'verification':
                output['model'] = {"result": "Program successfully verified"}
            else:
                output['model'] = {"result": "Programs are equivalent"}
        
        return output
    except Exception as e:
        print(f"Exception occurred: {str(e)}", file=sys.stderr)
        return {
            'error': str(e),
            'sat': 'error',
            'verified': False,
            'counterexample': None,
            'model': None
        }

if __name__ == '__main__':
    try:
        input_data = json.loads(sys.argv[1])
        result = run_z3(input_data['smt'], input_data['mode'])
        print(json.dumps(result))
    except Exception as e:
        print(json.dumps({
            'error': str(e),
            'sat': 'error',
            'verified': False,
            'counterexample': None,
            'model': None
        }))