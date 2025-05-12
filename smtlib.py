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

    def parse_ssa(self, ssa_code: str) -> None:
        """Parse the SSA code and generate Z3 SMT-LIB code."""
        self.preprocess_ssa(ssa_code)
        
        # Add declarations for array elements
        if self.array_variables:
            for arr_name in self.array_variables:
                for i in range(self.array_size):
                    self.z3_code.append(f"(declare-const {arr_name}{i} Int)")
                
                # Initial values (can be customized)
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
        # Replace && with 'and'
        condition = condition.replace('&&', ' and ')
        
        # Replace < and > operators
        condition = re.sub(r'(\w+)\s*<\s*(\w+)', r'(< \1 \2)', condition)
        condition = re.sub(r'(\w+)\s*>\s*(\w+)', r'(> \1 \2)', condition)
        condition = re.sub(r'(\w+)\s*>=\s*(\w+)', r'(>= \1 \2)', condition)
        condition = re.sub(r'(\w+)\s*<=\s*(\w+)', r'(<= \1 \2)', condition)
        
        # Handle array accesses
        condition = self._replace_array_accesses(condition)
        
        # Handle complex expressions
        if ' and ' in condition:
            parts = condition.split(' and ')
            return f"(and {' '.join(parts)})"
        
        return condition

    def _translate_expression(self, expr: str) -> str:
        """Translate an SSA expression to Z3 format."""
        # Check if this is a simple variable reference
        if re.match(r'^\w+_\d+$', expr.strip()):
            return expr.strip()
            
        # Handle array access
        arr_match = re.match(r'(\w+)\[([^]]+)\]', expr.strip())
        if arr_match:
            return self._replace_array_accesses(expr.strip())
        
        # Handle basic arithmetic
        if '+' in expr:
            parts = expr.split('+')
            left = self._translate_expression(parts[0].strip())
            right = self._translate_expression(parts[1].strip())
            return f"(+ {left} {right})"
        
        if '-' in expr:
            parts = expr.split('-')
            if len(parts) == 2:  # Binary subtraction
                left = self._translate_expression(parts[0].strip())
                right = self._translate_expression(parts[1].strip())
                return f"(- {left} {right})"
        
        # Handle simple value
        if expr.strip().isdigit() or expr.strip() == "n":
            return expr.strip()
            
        return expr.strip()

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
                return f"{var_name}_{version - 1}"
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
            return int(add_match.group(2))
            
        # Handle j_1 - 1 type expressions
        sub_match = re.match(r'(\w+)_\d+\s*-\s*(\d+)', index_expr)
        if sub_match:
            # For variable - constant, assume index 0
            return 0
            
        # Default to index 0 for complex expressions
        return 0

    def _get_next_version(self, var_name: str) -> int:
        """Get the next version number for a variable."""
        current = self.variable_versions.get(var_name, 0)
        self.variable_versions[var_name] = current + 1
        return current

    def _add_final_assertions(self) -> None:
        """Add final assertions checking the desired properties."""
        # If we're dealing with arrays, add a check that the final array is sorted
        if self.array_variables:
            for arr_name in self.array_variables:
                sorted_check = []
                
                for i in range(self.array_size - 1):
                    # Get the latest versions of adjacent elements
                    v1 = self.variable_versions.get(f"{arr_name}{i}", 0)
                    v2 = self.variable_versions.get(f"{arr_name}{i+1}", 0)
                    
                    var1 = f"{arr_name}{i}_{v1-1}" if v1 > 0 else f"{arr_name}{i}"
                    var2 = f"{arr_name}{i+1}_{v2-1}" if v2 > 0 else f"{arr_name}{i+1}"
                    
                    sorted_check.append(f"(<= {var1} {var2})")
                
                if sorted_check:
                    self.z3_code.append("\n; Check that the final array is sorted")
                    self.z3_code.append(f"(assert (and {' '.join(sorted_check)}))")

    def generate_z3_code(self) -> str:
        """Return the generated Z3 SMT-LIB code."""
        return "\n".join(self.z3_code)

