import re
import sys
from typing import Dict, List, Set, Tuple, Optional
from verification import get_verified_smtlib

class SSAtoZ3Converter:
    def __init__(self):
        self.variable_versions: Dict[str, int] = {}
        self.array_variables: Set[str] = set()
        self.z3_code: List[str] = []
        self.array_accesses: Set[str] = set()
        self.array_size = 4
        self.phi_conditions: Dict[str, str] = {}
        self.symbolic_n = True
        self.symbol_table: Dict[str, int] = {}  # Track concrete values of variables

    def parse_ssa(self, ssa_code: str) -> None:
        self.preprocess_ssa(ssa_code)
        self.z3_code.append("; SMT-LIB translation of SSA code")
        
        if self.symbolic_n:
            self.z3_code.append("(declare-const n Int)")
            self.z3_code.append("(assert (> n 1))")
        else:
            self.z3_code.append("(define-const n Int 4)")

        self.z3_code.append("")
        
        if self.array_variables:
            for arr_name in self.array_variables:
                for i in range(self.array_size):
                    self.z3_code.append(f"(declare-const {arr_name}{i} Int)")
                self.z3_code.append("; Initial array values")
                for i in range(self.array_size):
                    self.z3_code.append(f"(assert (= {arr_name}{i} {self.array_size - i}))")
                self.z3_code.append("")

        lines = [line.strip() for line in ssa_code.strip().split('\n') if line.strip()]
        current_iteration = 0
        line_idx = 0

        while line_idx < len(lines):
            line = lines[line_idx]
            self.z3_code.append(f"; Processing: {line}")
            
            if self._is_iteration_start(line):
                if current_iteration > 0:
                    self.z3_code.append("")
                self.z3_code.append(f"; Iteration {current_iteration + 1}")
                current_iteration += 1
            
            self._process_line(line)
            line_idx += 1

        self._add_final_assertions()

    def preprocess_ssa(self, ssa_code: str) -> None:
        array_pattern = re.compile(r'(\w+)\[')
        for match in array_pattern.finditer(ssa_code):
            self.array_variables.add(match.group(1))

        array_access_pattern = re.compile(r'(\w+)\[([^]]+)\]')
        for match in array_access_pattern.finditer(ssa_code):
            self.array_accesses.add(match.group(2))

    def _is_iteration_start(self, line: str) -> bool:
        return bool(re.match(r'i_\d+\s*=|j_\d+\s*=\s*0', line))

    def _process_line(self, line: str) -> None:
        phi_match = re.match(r'φ(\d+)\s*=\s*(.+)', line)
        if phi_match:
            phi_num = phi_match.group(1)
            condition = phi_match.group(2)
            z3_condition = self._translate_condition(condition)
            self.phi_conditions[f"φ{phi_num}"] = z3_condition
            self.z3_code.append(f"; Phi condition φ{phi_num}: {z3_condition}")
            return

        array_phi_match = re.match(r'(\w+)\[([^]]+)\]\s*=\s*(φ\d+)\s*\?\s*(.+)\s*:\s*(.+)', line)
        if array_phi_match:
            self._handle_array_phi_assignment(array_phi_match)
            return

        var_phi_match = re.match(r'(\w+)_(\d+)\s*=\s*(φ\d+)\s*\?\s*(.+)\s*:\s*(.+)', line)
        if var_phi_match:
            self._handle_var_phi_assignment(var_phi_match)
            return

        assign_match = re.match(r'(\w+)_(\d+)\s*=\s*(.+)', line)
        if assign_match:
            self._handle_simple_assignment(assign_match)
            return
            
        arr_assign_match = re.match(r'(\w+)\[([^]]+)\]\s*=\s*([^?]+)$', line)
        if arr_assign_match:
            self._handle_array_assignment(arr_assign_match)
            return

    def _handle_array_phi_assignment(self, match: re.Match) -> None:
        arr_name = match.group(1)
        index = match.group(2)
        phi_ref = match.group(3)
        true_val = match.group(4)
        false_val = match.group(5)
        
        # For array accesses, we need to handle both concrete and symbolic indices
        # Here we'll try to evaluate if it's concrete, otherwise keep it symbolic
        try:
            arr_idx = self._evaluate_index(index)
            var_name = f"{arr_name}{arr_idx}"
        except:
            # If we can't evaluate the index concretely, use a symbolic approach
            var_name = f"{arr_name}{index}"
        
        new_version = self._get_next_version(var_name)
        
        z3_condition = self.phi_conditions.get(phi_ref, "true")
        z3_true_val = self._translate_expression(true_val)
        z3_false_val = self._translate_expression(false_val)
        
        self.z3_code.append(f"(declare-const {var_name}_{new_version} Int)")
        self.z3_code.append(f"(assert (= {var_name}_{new_version} (ite {z3_condition} {z3_true_val} {z3_false_val})))")

    def _handle_var_phi_assignment(self, match: re.Match) -> None:
        var_name = match.group(1)
        var_version = match.group(2)
        phi_ref = match.group(3)
        true_val = match.group(4)
        false_val = match.group(5)
        
        full_var = f"{var_name}_{var_version}"
        z3_condition = self.phi_conditions.get(phi_ref, "true")
        z3_true_val = self._translate_expression(true_val)
        z3_false_val = self._translate_expression(false_val)
        
        self.z3_code.append(f"(declare-const {full_var} Int)")
        self.z3_code.append(f"(assert (= {full_var} (ite {z3_condition} {z3_true_val} {z3_false_val})))")
        # We can't reliably update symbol table with ternary expressions
        # self._update_symbol_table(full_var, f"(ite {z3_condition} {z3_true_val} {z3_false_val})")

    def _handle_simple_assignment(self, match: re.Match) -> None:
        var_name = match.group(1)
        var_version = match.group(2)
        expr = match.group(3)
        full_var = f"{var_name}_{var_version}"
        
        z3_expr = self._translate_expression(expr)
        self.z3_code.append(f"(declare-const {full_var} Int)")
        self.z3_code.append(f"(assert (= {full_var} {z3_expr}))")
        self._update_symbol_table(full_var, expr)

    def _handle_array_assignment(self, match: re.Match) -> None:
        arr_name = match.group(1)
        index = match.group(2)
        expr = match.group(3).strip()
        
        try:
            arr_idx = self._evaluate_index(index)
            var_name = f"{arr_name}{arr_idx}"
        except:
            # If we can't evaluate the index concretely, use a symbolic approach
            var_name = f"{arr_name}{index}"
            
        new_version = self._get_next_version(var_name)
        
        z3_expr = self._translate_expression(expr)
        self.z3_code.append(f"(declare-const {var_name}_{new_version} Int)")
        self.z3_code.append(f"(assert (= {var_name}_{new_version} {z3_expr}))")

    def _update_symbol_table(self, var: str, expr: str) -> None:
        try:
            value = self._evaluate_expression(expr)
            self.symbol_table[var] = value
        except:
            pass

    def _evaluate_expression(self, expr: str) -> int:
        try:
            if expr in self.symbol_table:
                return self.symbol_table[expr]
            if isinstance(expr, str) and expr.isdigit():
                return int(expr)
            
            add_match = re.match(r'(\w+_\d+)\s*\+\s*(\d+)', expr)
            if add_match:
                var, const = add_match.groups()
                return self.symbol_table.get(var, 0) + int(const)
            
            sub_match = re.match(r'(\w+_\d+)\s*-\s*(\d+)', expr)
            if sub_match:
                var, const = sub_match.groups()
                return self.symbol_table.get(var, 0) - int(const)
                
            sub_match2 = re.match(r'(\w+)\s*-\s*(\d+)', expr)
            if sub_match2:
                var, const = sub_match2.groups()
                if var == 'n':  # Special case for n-1
                    return self.array_size - int(const)
                return 0 - int(const)
                
            return 0
        except:
            raise ValueError(f"Cannot evaluate: {expr}")

    def _translate_condition(self, condition: str) -> str:
        # First, handle array accesses
        condition = self._replace_array_accesses(condition)
        
        # Handle variable comparisons
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<\s*(\w+(?:_\d+)?)', r'(< \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>\s*(\w+(?:_\d+)?)', r'(> \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<=\s*(\w+(?:_\d+)?)', r'(<= \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>=\s*(\w+(?:_\d+)?)', r'(>= \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*==\s*(\w+(?:_\d+)?)', r'(= \1 \2)', condition)
        
        # Handle literals in comparisons
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<\s*(\d+)', r'(< \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>\s*(\d+)', r'(> \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<=\s*(\d+)', r'(<= \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>=\s*(\d+)', r'(>= \1 \2)', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*==\s*(\d+)', r'(= \1 \2)', condition)
        
        # Handle expressions in comparisons (like n-1)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*<\s*(\w+)\s*-\s*(\d+)', r'(< \1 (- \2 \3))', condition)
        condition = re.sub(r'(\w+(?:_\d+)?)\s*>\s*(\w+)\s*-\s*(\d+)', r'(> \1 (- \2 \3))', condition)
        
        # Handle boolean operators
        condition = re.sub(r'&&', 'and', condition)
        condition = re.sub(r'\|\|', 'or', condition)
        
        if ' and ' in condition:
            parts = [part.strip() for part in condition.split(' and ')]
            return f"(and {' '.join(parts)})"
        if ' or ' in condition:
            parts = [part.strip() for part in condition.split(' or ')]
            return f"(or {' '.join(parts)})"
            
        return condition

    def _translate_expression(self, expr: str) -> str:
        # First handle array accesses
        expr = self._replace_array_accesses(expr)
        
        # Handle simple variable references
        if re.match(r'^\w+_\d+$', expr) or re.match(r'^\w+\d+$', expr) or re.match(r'^\d+$', expr):
            return expr
            
        # Handle arithmetic expressions
        add_match = re.match(r'(\w+(?:_\d+)?)\s*\+\s*(\d+)$', expr)
        if add_match:
            var, const = add_match.groups()
            return f"(+ {var} {const})"
            
        sub_match = re.match(r'(\w+(?:_\d+)?)\s*-\s*(\d+)$', expr)
        if sub_match:
            var, const = sub_match.groups()
            return f"(- {var} {const})"
            
        return expr

    def _replace_array_accesses(self, expr: str) -> str:
        def _process_array_access(match):
            arr_name = match.group(1)
            index_expr = match.group(2)
            
            # Try to evaluate the index concretely
            try:
                arr_idx = self._evaluate_index(index_expr)
                var_name = f"{arr_name}{arr_idx}"
            except:
                # If we can't evaluate, use a symbolic representation
                # In a real implementation, we would need proper array theory support
                if index_expr in self.symbol_table:
                    idx_val = self.symbol_table[index_expr]
                    var_name = f"{arr_name}{idx_val}"
                else:
                    # For variable indices or expressions, we'll use their names
                    # This is a simplification that might not work for all cases
                    var_name = f"{arr_name}{index_expr.replace('_', '')}"
            
            version = self.variable_versions.get(var_name, 0)
            return f"{var_name}_{version}" if version > 0 else var_name
            
        return re.sub(r'(\w+)\[([^]]+)\]', _process_array_access, expr)

    def _evaluate_index(self, index_expr: str) -> int:
        if isinstance(index_expr, int):
            return index_expr
            
        if index_expr.isdigit():
            return int(index_expr)
            
        if index_expr in self.symbol_table:
            return self.symbol_table[index_expr]
            
        var_match = re.match(r'^(\w+)_(\d+)$', index_expr)
        if var_match and var_match.group(0) in self.symbol_table:
            return self.symbol_table[var_match.group(0)]
            
        raise ValueError(f"Cannot evaluate index: {index_expr}")

    def _get_next_version(self, var_name: str) -> int:
        current = self.variable_versions.get(var_name, 0)
        self.variable_versions[var_name] = current + 1
        return current + 1

    def _add_final_assertions(self) -> None:
        if self.array_variables:
            self.z3_code.append("\n; Check that the final array is sorted")
            sorted_assertions = []
            
            for arr_name in self.array_variables:
                sorted_check = []
                for i in range(self.array_size - 1):
                    v1 = self.variable_versions.get(f"{arr_name}{i}", 0)
                    v2 = self.variable_versions.get(f"{arr_name}{i+1}", 0)
                    var1 = f"{arr_name}{i}_{v1}" if v1 > 0 else f"{arr_name}{i}"
                    var2 = f"{arr_name}{i+1}_{v2}" if v2 > 0 else f"{arr_name}{i+1}"
                    sorted_check.append(f"(<= {var1} {var2})")
                
                if sorted_check:
                    sorted_assertions.append(f"(and {' '.join(sorted_check)})")
            
            if sorted_assertions:
                self.z3_code.append(f"(assert (not {sorted_assertions[0]}))")
            
            self.z3_code.append("\n(check-sat)")
            self.z3_code.append("(get-model)")

    def generate_z3_code(self) -> str:
        return "\n".join(self.z3_code)
    
    def get_verified_code(self) -> str:
        raw_code = self.generate_z3_code()
        return get_verified_smtlib(raw_code)