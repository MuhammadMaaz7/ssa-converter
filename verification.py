from z3 import *
import re

def verify_property_with_smtlib(smtlib_code):
    # Parse the SMT-LIB code
    solver = Solver()
    
    # Extract assert statements from the SMT-LIB code
    assertions = []
    declarations = []
    
    # Process the SMT-LIB code line by line
    lines = smtlib_code.strip().split('\n')
    for line in lines:
        line = line.strip()
        
        # Skip comments and empty lines
        if line.startswith(';') or not line:
            continue
            
        # Extract declarations
        if line.startswith('(declare-'):
            declarations.append(line)
            
        # Extract assertions
        elif line.startswith('(assert'):
            # Remove the outer assert wrapper
            assertion = line[7:-1].strip()
            assertions.append(assertion)
    
    # Re-construct SMT-LIB code for the declarations and assertions
    property_smtlib = '\n'.join(declarations)
    for assertion in assertions:
        property_smtlib += f'\n(assert {assertion})'
    
    # Add code to check satisfiability
    property_smtlib += '\n(check-sat)'
    
    # Create SMT-LIB for negated property
    negated_property_smtlib = '\n'.join(declarations)
    
    # If there are multiple assertions, negate their conjunction
    if len(assertions) > 1:
        negated_assertion = f'(not (and {" ".join(assertions)}))'
    else:
        negated_assertion = f'(not {assertions[0]})'
    
    negated_property_smtlib += f'\n(assert {negated_assertion})'
    negated_property_smtlib += '\n(check-sat)'
    negated_property_smtlib += '\n(get-model)'
    
    # Use Z3's parse_smt2_string to process the negated property
    try:
        # Create a temporary solver for the negated property
        negation_solver = Solver()
        negation_solver.from_string(negated_property_smtlib)
        
        # Check if the negation is satisfiable
        result = negation_solver.check()
        
        if result == unsat:
            # The negation is unsatisfiable, so the property is verified
            return True, None
        else:
            # The negation is satisfiable, so we have a counterexample
            return False, negation_solver.model()
            
    except Z3Exception as e:
        print(f"Z3 Error: {e}")
        # Fallback method: use sexpr parsing
        ctx = Context()
        try:
            negation_solver = SolverFor("QF_BV", ctx=ctx)
            for decl in declarations:
                Z3_eval_smtlib2_string(ctx.ref(), decl)
            
            Z3_eval_smtlib2_string(ctx.ref(), f'(assert {negated_assertion})')
            result = negation_solver.check()
            
            if result == unsat:
                return True, None
            else:
                return False, negation_solver.model()
        except Exception as e2:
            print(f"Error in fallback method: {e2}")
            return None, None

# Alternative implementation using subprocess to call Z3 directly
def verify_with_z3_subprocess(smtlib_code):
    import subprocess
    import tempfile
    
    # Extract assertions from SMT-LIB code
    lines = smtlib_code.strip().split('\n')
    declarations = []
    assertions = []
    
    for line in lines:
        line = line.strip()
        if not line or line.startswith(';'):
            continue
        
        if line.startswith('(declare-') or line.startswith('(define-'):
            declarations.append(line)
        elif line.startswith('(assert'):
            assertions.append(line[7:-1].strip())
    
    # Create negated property
    if len(assertions) > 1:
        negated_assertion = f'(assert (not (and {" ".join(assertions)})))'
    else:
        negated_assertion = f'(assert (not {assertions[0]}))'
    
    # Construct the full SMT-LIB code with negated property
    negated_smtlib = '\n'.join(declarations) + '\n' + negated_assertion + '\n(check-sat)\n(get-model)'
    
    # Write to temporary file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.smt2', delete=False) as f:
        f.write(negated_smtlib)
        temp_file = f.name
    
    try:
        # Call Z3 with the temporary file
        result = subprocess.run(['z3', temp_file], capture_output=True, text=True)
        output = result.stdout.strip()
        
        # Check if the negation is unsatisfiable
        if output.startswith('unsat'):
            return True, output
        else:
            return False, output
    except Exception as e:
        return None, f"Error: {e}"
    finally:
        import os
        os.unlink(temp_file)  # Remove temporary file

def get_verified_smtlib(smtlib_code: str) -> str:
    verified, model = verify_property_with_smtlib(smtlib_code)

    annotated_code = smtlib_code.strip()
    annotated_code += "\n\n; => Z3 VERIFICATION RESULT \n"
    annotated_code += f"\n; Result: {'unsat (property verified)' if verified else 'sat (counterexample found)'}"

    if not verified and model:
        annotated_code += "\n; Counterexample Model:"
        for line in str(model).splitlines():
            annotated_code += f"\n; {line}"

    return annotated_code
