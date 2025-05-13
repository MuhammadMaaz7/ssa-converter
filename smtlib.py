import re
import sys
from typing import Dict, List, Set, Tuple, Optional

class SSAtoZ3Converter:
    def __init__(self):
        self.variable_versions: Dict[str, int] = {}  # Track latest version of each variable
        self.array_variables: Set[str] = set()       # Track array variables
        self.z3_code: List[str] = []                 # Store Z3 SMT-LIB code lines
        self.array_accesses: Set[str] = set()        # Track array access patterns
        self.array_size = 4                          # Default array size
        self.phi_conditions: Dict[str, str] = {}     # Track conditions for phi nodes
        self.symbolic_n = True                       # Whether to treat n as a symbolic variable

    def parse_ssa(self, ssa_code: str) -> None:
        """Parse the SSA code and generate Z3 SMT-LIB code."""
        self.preprocess_ssa(ssa_code)
        
        # Add header
        self.z3_code.append("; SMT-LIB translation of SSA code")
        
        # Declare n (array size parameter)
        if self.symbolic_n:
            self.z3_code.append("(declare-const n Int)")
            self.z3_code.append("(assert (> n 1))")  # Ensure n is at least 2
        else:
            self.z3_code.append("(define-const n Int 4)")  # Fixed array size
        
        self.z3_code.append("")  # Empty line for readability
        
        # Add declarations for array elements
        if self.array_variables:
            for arr_name in self.array_variables:
                for i in range(self.array_size):
                    self.z3_code.append(f"(declare-const {arr_name}{i} Int)")
                
                # Initial values (can be customized)
                self.z3_code.append("; Initial array values")
                for i in range(self.array_size):
                    self.z3_code.append(f"(assert (= {arr_name}{i} {self.array_size - i}))")
                
                self.z3_code.append("")  # Add empty line for readability
        
        # Process each line of SSA code
        lines = [line.strip() for line in ssa_code.strip().split('\n') if line.strip()]
        
        current_iteration = 0
        line_idx = 0
        
        while line_idx < len(lines):
            line = lines[line_idx]
            
            # Add a comment to show current line being processed
            self.z3_code.append(f"; Processing: {line}")
            
            # Check if this starts a new iteration
            if self._is_iteration_start(line):
                if current_iteration > 0:
                    self.z3_code.append("")  # Empty line between iterations
                self.z3_code.append(f"; Iteration {current_iteration + 1}")
                current_iteration += 1
            
            # Process the line
            self._process_line(line)
            
            line_idx += 1
        
        # Add any final assertions or checks that might be needed
        self._add_final_assertions()

    def preprocess_ssa(self, ssa_code: str) -> None:
        """Preprocess SSA code to identify variables and arrays."""
        # Identify array variables
        array_pattern = re.compile(r'(\w+)\[')
        for match in array_pattern.finditer(ssa_code):
            self.array_variables.add(match.group(1))
        
        # Count distinct array access patterns to guess array size
        array_access_pattern = re.compile(r'(\w+)\[([^]]+)\]')
        for match in array_access_pattern.finditer(ssa_code):
            self.array_accesses.add(match.group(2))
        
        # Estimate array size based on accesses
        if self.array_accesses:
            # Try to find the maximum index by evaluating simple expressions
            for access in self.array_accesses:
                try:
                    if "+" in access:
                        parts = access.split('+')
                        if len(parts) == 2 and parts[1].strip().isdigit():
                            idx = int(parts[1].strip()) + 1
                            self.array_size = max(self.array_size, idx + 1)
                    elif access.strip().isdigit():
                        self.array_size = max(self.array_size, int(access.strip()) + 1)
                except:
                    pass  # Skip complex expressions

    def _is_iteration_start(self, line: str) -> bool:
        """Check if this line starts a new logical iteration."""
        # Look for patterns like "i_X = " or "j_X = 0" that often indicate iteration starts
        return bool(re.match(r'i_\d+\s*=|j_\d+\s*=\s*0', line))

    def _process_line(self, line: str) -> None:
        """Process a single line of SSA code."""
        # Handle phi nodes (φX = condition)
        phi_match = re.match(r'φ(\d+)\s*=\s*(.+)', line)
        if phi_match:
            phi_num = phi_match.group(1)
            condition = phi_match.group(2)
            z3_condition = self._translate_condition(condition)
            self.phi_conditions[f"φ{phi_num}"] = z3_condition
            self.z3_code.append(f"; Phi condition φ{phi_num}: {z3_condition}")
            return

        # Handle array assignments with phi conditions
        array_phi_match = re.match(r'(\w+)\[([^]]+)\]\s*=\s*(φ\d+)\s*\?\s*(.+)\s*:\s*(.+)', line)
        if array_phi_match:
            arr_name = array_phi_match.group(1)
            index = array_phi_match.group(2)
            phi_ref = array_phi_match.group(3)
            true_val = array_phi_match.group(4)
            false_val = array_phi_match.group(5)
            
            # Convert the array index to a numeric value if possible
            arr_idx = self._evaluate_index(index)
            
            # Get the current version number for this array element
            var_name = f"{arr_name}{arr_idx}"
            new_version = self._get_next_version(var_name)
            
            # Translate values
            z3_condition = self.phi_conditions.get(phi_ref, "true")
            z3_true_val = self._translate_expression(true_val)
            z3_false_val = self._translate_expression(false_val)
            
            # Create the Z3 assertion
            self.z3_code.append(f"(declare-const {var_name}_{new_version} Int)")
            self.z3_code.append(f"(assert (= {var_name}_{new_version} (ite {z3_condition} {z3_true_val} {z3_false_val})))")
            return

        # Handle variable assignments with phi conditions
        var_phi_match = re.match(r'(\w+)_(\d+)\s*=\s*(φ\d+)\s*\?\s*(.+)\s*:\s*(.+)', line)
        if var_phi_match:
            var_name = var_phi_match.group(1)
            var_version = var_phi_match.group(2)
            phi_ref = var_phi_match.group(3)
            true_val = var_phi_match.group(4)
            false_val = var_phi_match.group(5)
            
            # Translate values
            z3_condition = self.phi_conditions.get(phi_ref, "true")
            z3_true_val = self._translate_expression(true_val)
            z3_false_val = self._translate_expression(false_val)
            
            # Create the Z3 assertion
            self.z3_code.append(f"(declare-const {var_name}_{var_version} Int)")
            self.z3_code.append(f"(assert (= {var_name}_{var_version} (ite {z3_condition} {z3_true_val} {z3_false_val})))")
            return

        # Handle simple assignments (var = expr)
        assign_match = re.match(r'(\w+)_(\d+)\s*=\s*(.+)', line)
        if assign_match:
            var_name = assign_match.group(1)
            var_version = assign_match.group(2)
            expr = assign_match.group(3)
            
            # Translate the expression
            z3_expr = self._translate_expression(expr)
            
            # Create the Z3 assertion
            self.z3_code.append(f"(declare-const {var_name}_{var_version} Int)")
            self.z3_code.append(f"(assert (= {var_name}_{var_version} {z3_expr}))")
            return
            
        # Handle array assignment (arr[idx] = expr)
        arr_assign_match = re.match(r'(\w+)\[([^]]+)\]\s*=\s*([^?]+)$', line)
        if arr_assign_match:
            arr_name = arr_assign_match.group(1) 
            index = arr_assign_match.group(2)
            expr = arr_assign_match.group(3).strip()
            
            # Convert the array index to a numeric value if possible
            arr_idx = self._evaluate_index(index)
            
            # Get the current version number for this array element
            var_name = f"{arr_name}{arr_idx}"
            new_version = self._get_next_version(var_name)
            
            # Translate the expression
            z3_expr = self._translate_expression(expr)
            
            # Create the Z3 assertion
            self.z3_code.append(f"(declare-const {var_name}_{new_version} Int)")
            self.z3_code.append(f"(assert (= {var_name}_{new_version} {z3_expr}))")
            return

    def _translate_condition(self, condition: str) -> str:
        """Translate an SSA condition to Z3 format."""
        # Handle complex conditions with subtraction and comparison
        # For example: "i_1 < n - 1" => "(< i_1 (- n 1))"
        subtraction_cmp_match = re.match(r'(\w+(?:_\d+)?)\s*(<|>|<=|>=)\s*(\w+(?:_\d+)?)\s*-\s*(\d+)', condition)
        if subtraction_cmp_match:
            var1 = subtraction_cmp_match.group(1)
            op = subtraction_cmp_match.group(2)
            var2 = subtraction_cmp_match.group(3)
            num = subtraction_cmp_match.group(4)
            op_map = {'<': '<', '>': '>', '<=': '<=', '>=': '>='}
            z3_op = op_map.get(op, op)
            return f"({z3_op} {var1} (- {var2} {num}))"
            
        # Handle complex conditions with n - i - 1 format
        # For example: "j_1 < n - i_1 - 1" => "(< j_1 (- (- n i_1) 1))"
        double_subtraction_cmp_match = re.match(r'(\w+(?:_\d+)?)\s*(<|>|<=|>=)\s*(\w+(?:_\d+)?)\s*-\s*(\w+(?:_\d+)?)\s*-\s*(\d+)', condition)
        if double_subtraction_cmp_match:
            var1 = double_subtraction_cmp_match.group(1)
            op = double_subtraction_cmp_match.group(2)
            var2 = double_subtraction_cmp_match.group(3)
            var3 = double_subtraction_cmp_match.group(4)
            num = double_subtraction_cmp_match.group(5)
            op_map = {'<': '<', '>': '>', '<=': '<=', '>=': '>='}
            z3_op = op_map.get(op, op)
            return f"({z3_op} {var1} (- (- {var2} {var3}) {num}))"
        
        # Replace array access comparisons
        # For example: "arr[j_1] > arr[j_1 + 1]" => "(> arr1 arr2)"
        array_cmp_match = re.match(r'(\w+)\[([^]]+)\]\s*(<|>|<=|>=)\s*(\w+)\[([^]]+)\]', condition)
        if array_cmp_match:
            arr1_name = array_cmp_match.group(1)
            idx1 = self._evaluate_index(array_cmp_match.group(2))
            op = array_cmp_match.group(3)
            arr2_name = array_cmp_match.group(4)
            idx2 = self._evaluate_index(array_cmp_match.group(5))
            
            # Get latest versions of array elements
            arr1_var = self._get_array_element_ref(arr1_name, idx1)
            arr2_var = self._get_array_element_ref(arr2_name, idx2)
            
            op_map = {'<': '<', '>': '>', '<=': '<=', '>=': '>='}
            z3_op = op_map.get(op, op)
            
            return f"({z3_op} {arr1_var} {arr2_var})"
            
        # Replace && with logical and
        condition = re.sub(r'&&', ' and ', condition)
        
        # Find comparison expressions and replace them with proper SMT-LIB syntax
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<\s*(\w+(?:_\d+)?)', r'(< \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>\s*(\w+(?:_\d+)?)', r'(> \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>=\s*(\w+(?:_\d+)?)', r'(>= \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<=\s*(\w+(?:_\d+)?)', r'(<= \1 \2)', condition)
        
        # Handle array accesses
        condition = self._replace_array_accesses(condition)
        
        # Fix: Properly format logical and expressions
        if ' and ' in condition:
            parts = condition.split(' and ')
            translated_parts = [part.strip() for part in parts]
            return f"(and {' '.join(translated_parts)})"
        
        return condition

    def _get_array_element_ref(self, arr_name: str, idx: int) -> str:
        """Get reference to an array element with proper versioning."""
        var_name = f"{arr_name}{idx}"
        version = self.variable_versions.get(var_name, 0)
        
        if version > 0:
            return f"{var_name}_{version}"
        else:
            return f"{var_name}"

    def _translate_expression(self, expr: str) -> str:
        """Translate an SSA expression to Z3 format."""
        expr = expr.strip()
        
        # Check if this is a simple variable reference
        if re.match(r'^\w+_\d+$', expr):
            return expr
            
        # Handle array access
        arr_match = re.match(r'(\w+)\[([^]]+)\]', expr)
        if arr_match:
            return self._replace_array_accesses(expr)
        
        # Handle multi-term arithmetic with parentheses
        if '+' in expr and '-' in expr:
            # Handle complex expressions like "n - i_1 - 1"
            if re.match(r'(\w+(?:_\d+)?)\s*-\s*(\w+(?:_\d+)?)\s*-\s*(\d+)', expr):
                match = re.match(r'(\w+(?:_\d+)?)\s*-\s*(\w+(?:_\d+)?)\s*-\s*(\d+)', expr)
                var1 = match.group(1)
                var2 = match.group(2)
                num = match.group(3)
                return f"(- (- {var1} {var2}) {num})"
        
        # Handle basic arithmetic
        if '+' in expr and not re.search(r'\[.+\+', expr):  # Ensure + is not inside array access
            parts = expr.split('+')
            left = self._translate_expression(parts[0].strip())
            right = self._translate_expression(parts[1].strip())
            return f"(+ {left} {right})"
        
        if '-' in expr and not re.search(r'\[.+-', expr):  # Ensure - is not inside array access
            parts = expr.split('-')
            if len(parts) == 2:  # Binary subtraction
                left = self._translate_expression(parts[0].strip())
                right = self._translate_expression(parts[1].strip())
                return f"(- {left} {right})"
        
        # Handle simple value
        if expr.isdigit() or expr == "n":
            return expr
            
        return expr

    def _replace_array_accesses(self, expr: str) -> str:
        """Replace array accesses with their variable names."""
        # Look for patterns like arr[idx]
        arr_pattern = re.compile(r'(\w+)\[([^]]+)\]')
        
        def replace_match(match):
            arr_name = match.group(1)
            index_expr = match.group(2).strip()
            
            # Try to evaluate the index
            arr_idx = self._evaluate_index(index_expr)
            
            # Get the latest version of this array element
            var_name = f"{arr_name}{arr_idx}"
            version = self.variable_versions.get(var_name, 0)
            
            if version > 0:
                return f"{var_name}_{version}"
            else:
                return f"{var_name}"
                
        return arr_pattern.sub(replace_match, expr)

    def _evaluate_index(self, index_expr: str) -> int:
        """Try to evaluate a simple index expression."""
        # Handle simple numeric index
        if index_expr.strip().isdigit():
            return int(index_expr.strip())
            
        # Handle simple expressions like "j_1 + 1"
        add_match = re.match(r'(\w+)_\d+\s*\+\s*(\d+)', index_expr)
        if add_match:
            # For simplicity, just return the numeric part
            # This is an estimation - in a real system we'd need to track variable values
            return int(add_match.group(2))
            
        # Handle j_1 - 1 type expressions
        sub_match = re.match(r'(\w+)_\d+\s*-\s*(\d+)', index_expr)
        if sub_match:
            # For variable - constant, assume index 0
            return 0
            
        # Default to index 1 for complex expressions
        return 1  # Use index 1 as default as per the SSA code

    def _get_next_version(self, var_name: str) -> int:
        """Get the next version number for a variable."""
        current = self.variable_versions.get(var_name, 0)
        self.variable_versions[var_name] = current + 1
        return current + 1  # Return the new version (1-based)

    def _add_final_assertions(self) -> None:
        """Add final assertions checking the desired properties."""
        # If we're dealing with arrays, add a check that the final array is sorted
        if self.array_variables:
            self.z3_code.append("\n; Check that the final array is sorted")
            for arr_name in self.array_variables:
                sorted_check = []
                
                for i in range(self.array_size - 1):
                    # Get the latest versions of adjacent elements
                    v1 = self.variable_versions.get(f"{arr_name}{i}", 0)
                    v2 = self.variable_versions.get(f"{arr_name}{i+1}", 0)
                    
                    # Use proper versions or original array values
                    var1 = f"{arr_name}{i}_{v1}" if v1 > 0 else f"{arr_name}{i}"
                    var2 = f"{arr_name}{i+1}_{v2}" if v2 > 0 else f"{arr_name}{i+1}"
                    
                    sorted_check.append(f"(<= {var1} {var2})")
                
                if sorted_check:
                    self.z3_code.append(f"(assert (and {' '.join(sorted_check)}))")
                    
            # Add check-sat and get-model commands
            self.z3_code.append("\n(check-sat)")
            self.z3_code.append("(get-model)")

    def generate_z3_code(self) -> str:
        """Return the generated Z3 SMT-LIB code."""
        return "\n".join(self.z3_code)


