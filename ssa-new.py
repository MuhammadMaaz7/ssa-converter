import tkinter as tk
from tkinter import ttk, scrolledtext
import re
from copy import deepcopy

def remove_comments(code):
    code = re.sub(r"//.*", "", code)
    code = re.sub(r"/\*.*?\*/", "", code, flags=re.DOTALL)
    return code

def parse_loop_header(header):
    match = re.match(r"(.*)=(.*)", header.strip())
    if match:
        var = match.group(1).strip()
        value = match.group(2).strip()
        return var, value
    return None, None

def extract_block(code, start_idx):
    brace_count = 1
    end_idx = start_idx
    while brace_count > 0 and end_idx < len(code):
        if code[end_idx] == '{':
            brace_count += 1
        elif code[end_idx] == '}':
            brace_count -= 1
        end_idx += 1
    return code[start_idx:end_idx-1].strip(), code[end_idx:].strip()

def unroll_code(code, unroll_count, indent_level=0):
    code = remove_comments(code).strip()
    if not code:
        return ""
    lines = []
    indent = "    " * indent_level

    # Check for the earliest loop (for or while)
    for_loop_pattern = re.compile(r"for\s*\(([^;]+);([^;]+);([^)]+)\)\s*{", re.DOTALL)
    while_loop_pattern = re.compile(r"while\s*\(([^)]+)\)\s*{", re.DOTALL)
    for_match = for_loop_pattern.search(code)
    while_match = while_loop_pattern.search(code)

    matches = []
    if for_match:
        matches.append((for_match.start(), 'for', for_match))
    if while_match:
        matches.append((while_match.start(), 'while', while_match))

    if matches:
        # Process the earliest loop
        matches.sort()
        first_match = matches[0]
        loop_type = first_match[1]
        match = first_match[2]
        loop_start = match.start()
        loop_code = code[loop_start:]

        # Process any non-loop code before the loop
        before_loop = code[:loop_start].strip()
        if before_loop:
            before_lines = unroll_code(before_loop, unroll_count, indent_level)
            lines.append(before_lines)

        # Process the loop
        if loop_type == 'for':
            init, cond, inc = match.groups()
            start_idx = match.end() - loop_start  # Adjust for loop_code substring
            loop_body, remaining = extract_block(loop_code, start_idx)
            lines.append(f"{indent}{init.strip()};")
            for _ in range(unroll_count):
                lines.append(f"{indent}if ({cond.strip()}) {{")
                unrolled_body = unroll_code(loop_body, unroll_count, indent_level + 1)
                lines.append(unrolled_body)
                lines.append(f"{indent}}}")
                lines.append(f"{indent}{inc.strip()};")
            # Process remaining code after the loop
            if remaining.strip():
                lines.append(unroll_code(remaining, unroll_count, indent_level))
        elif loop_type == 'while':
            cond = match.group(1)
            start_idx = match.end() - loop_start
            loop_body, remaining = extract_block(loop_code, start_idx)
            for _ in range(unroll_count):
                lines.append(f"{indent}if ({cond.strip()}) {{")
                unrolled_body = unroll_code(loop_body, unroll_count, indent_level + 1)
                lines.append(unrolled_body)
                lines.append(f"{indent}}}")
            # Process remaining code after the loop
            if remaining.strip():
                lines.append(unroll_code(remaining, unroll_count, indent_level))
    else:
        # No loops, process line by line
        for line in code.split(';'):
            line = line.strip()
            if line:
                lines.append(f"{indent}{line};")

    return "\n".join(lines)

import re

class SSAConverter:
    def __init__(self, array_length=10):
        self.var_versions = {}  # Tracks current version of each variable
        self.array_versions = {}  # Tracks current version of each array element
        self.current_block = []  # Stores the SSA form
        self.phi_counter = 1  # Counter for phi functions
        self.context_stack = []  # Stack for tracking nested blocks
        self.array_length = array_length
        self.if_else_stack = []  # Stack for tracking if-else conditions
        
    def get_var_version(self, var):
        """Get current version number of a variable"""
        return self.var_versions.get(var, 0)
    
    def fresh_var(self, var):
        """Create a new version of a variable"""
        count = self.get_var_version(var) + 1
        self.var_versions[var] = count
        return f"{var}_{count}"
    
    def get_array_version(self, array_name, index):
        """Get current version number of an array element"""
        index_key = f"{array_name}_{index}"
        return self.array_versions.get(index_key, 0)
    
    def fresh_array(self, index, array_name="arr"):
        """Create a new version of an array element"""
        index_key = f"{array_name}_{index}"
        count = self.get_array_version(array_name, index) + 1
        self.array_versions[index_key] = count
        return f"{array_name}{index}_{count}"
    
    def process_variable_references(self, expr):
        """Process just the variable references in an expression - always use latest version"""
        if not expr:
            return expr
            
        result = expr
        # Sort variables by length in descending order to avoid partial matches
        for var in sorted(self.var_versions.keys(), key=lambda x: -len(x)):
            if re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', var):  # valid variable name pattern  # Only match whole variable names
                pattern = rf'\b{var}\b'
                version = self.get_var_version(var)
                result = re.sub(pattern, f"{var}_{version}", result)
                
        return result
    
    def process_array_access(self, array_access):
        """Process array access like arr[j] with proper versioning"""
        array_match = re.match(r'(\w+)\[(.*)\]', array_access)
        if not array_match:
            return array_access
        
        array_name, index_expr = array_match.groups()
        
        # Process the index expression first
        processed_index = self.process_variable_references(index_expr)
        
        # Try to resolve to a numeric index
        try:
            # For simple numeric indices
            if processed_index.isdigit():
                index_value = int(processed_index)
                if 0 <= index_value < self.array_length:
                    version = self.get_array_version(array_name, index_value)
                    return f"{array_name}{index_value}_{version}"
            
            # For j+1 style expressions
            plus_match = re.match(r'(\w+)_(\d+)\s*\+\s*(\d+)', processed_index)
            if plus_match:
                var_name, var_version, offset = plus_match.groups()
                # For simple cases like j_1 + 1, return arr[j+1] properly versioned
                if var_name.isalpha() and var_version.isdigit() and offset.isdigit():
                    # We can't determine the exact index at compile time in general case
                    # But for j+1 pattern in bubble sort, we know it's accessing the next element
                    return f"{array_name}[{var_name}_{var_version} + {offset}]"
        except:
            pass
        
        # If we can't resolve, use symbolic form with proper variable versioning
        return f"{array_name}[{processed_index}]"
    
    def process_expression(self, expr):
        """Process expressions, handling variable versions and array access"""
        if not expr:
            return expr
        
        # Handle array accesses first
        array_pattern = r'(\w+)\[([^\]]+)\]'
        
        # We need to find all array accesses and process them
        matches = list(re.finditer(array_pattern, expr))
        
        # Process from right to left to avoid messing up the indices
        result = expr
        for match in reversed(matches):
            array_access = match.group(0)
            processed_access = self.process_array_access(array_access)
            start, end = match.span()
            result = result[:start] + processed_access + result[end:]
        
        # Then handle variables in expressions
        return self.process_variable_references(result)
    
    def start_if_block(self, condition):
        """Start an if block, saving context"""
        processed_condition = self.process_expression(condition)
        phi_id = self.phi_counter
        self.phi_counter += 1
        self.current_block.append(f"φ{phi_id} = {processed_condition}")
        
        # Save current state
        context = {
            'vars': {var: ver for var, ver in self.var_versions.items()},
            'arrays': {idx: ver for idx, ver in self.array_versions.items()},
            'phi_id': phi_id,
            'is_else': False
        }
        self.context_stack.append(context)
        self.if_else_stack.append({
            'phi_id': phi_id, 
            'if_vars': {}, 
            'else_vars': {},
            'if_arrays': {},
            'else_arrays': {}
        })
        
        return phi_id
    
    def process_else_block(self):
        """Process an else block"""
        if not self.context_stack or not self.if_else_stack:
            return
            
        # Restore to state before if block
        if_context = self.context_stack[-1]
        if_context['is_else'] = True
        
        # Save if branch versions before switching to else branch
        if_data = self.if_else_stack[-1]
        if_data['if_vars'] = {var: ver for var, ver in self.var_versions.items()}
        if_data['if_arrays'] = {idx: ver for idx, ver in self.array_versions.items()}
        
        # Restore versions from before if block
        self.var_versions = {var: ver for var, ver in if_context['vars'].items()}
        self.array_versions = {idx: ver for idx, ver in if_context['arrays'].items()}
    
    def end_block(self):
        """End a block (if, else) with proper phi node creation"""
        if not self.context_stack:
            return
            
        context = self.context_stack.pop()
        phi_id = context.get('phi_id')
        
        if context.get('is_else'):
            # End of else block - create comprehensive phi nodes
            if_data = self.if_else_stack.pop()
            
            # Process all variables modified in either branch
            all_vars = set(if_data['if_vars'].keys()) | set(self.var_versions.keys())
            for var in all_vars:
                if_ver = if_data['if_vars'].get(var, context['vars'].get(var, 0))
                else_ver = self.var_versions.get(var, context['vars'].get(var, 0))
                
                # Only create phi node if versions differ
                if if_ver != else_ver:
                    new_var = self.fresh_var(var)
                    self.current_block.append(f"{new_var} = φ{phi_id} ? {var}_{if_ver} : {var}_{else_ver}")
            
            # Process arrays - make phi nodes for each potentially modified array element
            all_indices = set(if_data['if_arrays'].keys()) | set(self.array_versions.keys())
            for idx_key in all_indices:
                if '_' in idx_key:
                    array_name, idx = idx_key.split('_')
                    if_ver = if_data['if_arrays'].get(idx_key, context['arrays'].get(idx_key, 0))
                    else_ver = self.array_versions.get(idx_key, context['arrays'].get(idx_key, 0))
                    
                    # Only create phi node if versions differ
                    if if_ver != else_ver:
                        # Create new version for this array element
                        new_ver = max(if_ver, else_ver) + 1
                        self.array_versions[idx_key] = new_ver
                        self.current_block.append(
                            f"{array_name}{idx}_{new_ver} = φ{phi_id} ? {array_name}{idx}_{if_ver} : {array_name}{idx}_{else_ver}"
                        )
        else:
            # End of if block without else - create phi nodes comparing with state before if
            for var, before_ver in context['vars'].items():
                after_ver = self.var_versions.get(var, before_ver)
                if before_ver != after_ver:
                    new_var = self.fresh_var(var)
                    self.current_block.append(f"{new_var} = φ{phi_id} ? {var}_{after_ver} : {var}_{before_ver}")
            
            # Create phi nodes for array elements
            for idx_key, before_ver in context['arrays'].items():
                after_ver = self.array_versions.get(idx_key, before_ver)
                if before_ver != after_ver and '_' in idx_key:
                    array_name, idx = idx_key.split('_')
                    new_ver = max(after_ver, before_ver) + 1
                    self.array_versions[idx_key] = new_ver
                    self.current_block.append(
                        f"{array_name}{idx}_{new_ver} = φ{phi_id} ? {array_name}{idx}_{after_ver} : {array_name}{idx}_{before_ver}"
                    )
    
    def handle_assignment(self, lhs, rhs):
        """Handle variable or array assignment"""
        rhs = self.process_expression(rhs)
        
        # Handle array assignment: arr[i] = value
        if '[' in lhs and ']' in lhs:
            array_match = re.match(r'(\w+)\[(.*)\]', lhs)
            if array_match:
                array_name, idx_expr = array_match.groups()
                processed_idx = self.process_variable_references(idx_expr)
                
                # If index is a simple number
                if processed_idx.isdigit():
                    idx = int(processed_idx)
                    if 0 <= idx < self.array_length:
                        new_arr = self.fresh_array(idx, array_name)
                        self.current_block.append(f"{new_arr} = {rhs}")
                    else:
                        # Out of bounds or complex index
                        self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
                else:
                    # For expressions like j_1, try to resolve
                    j_match = re.match(r'(\w+)_(\d+)', processed_idx)
                    if j_match and j_match.group(1).isalpha():
                        # We can't determine the actual value at compile time
                        # So we need to represent it symbolically but preserve SSA form
                        self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
                    elif "+" in processed_idx:
                        # Handle j+1 type indices similarly
                        self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
                    else:
                        # Other symbolic indices
                        self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
        else:
            # Regular variable assignment
            var = lhs.strip()
            new_var = self.fresh_var(var)
            self.current_block.append(f"{new_var} = {rhs}")
    
    def process_line(self, line):
        """Process a single line of code"""
        line = line.strip()
        if not line or line.startswith('//'):
            return
            
        # Remove trailing semicolon
        if line.endswith(';'):
            line = line[:-1].strip()
            
        # Skip empty lines after removing semicolon
        if not line:
            return
            
        # Handle if statements
        if_match = re.match(r'if\s*\((.*)\)', line)
        if if_match:
            condition = if_match.group(1)
            self.start_if_block(condition)
            return
            
        # Handle else statements
        if line == 'else' or line.startswith('else {'):
            self.process_else_block()
            return
            
        # Handle closing braces (end of block)
        if line == '}':
            self.end_block()
            return
        
        # Handle for loops - convert to if condition
        for_match = re.match(r'for\s*\((.*?);(.*?);(.*?)\)', line)
        if for_match:
            init, cond, incr = for_match.groups()
            # Process initialization first
            if init:
                self.process_line(init)
            # Then create an if block for the condition
            if cond:
                self.start_if_block(cond)
            # We'll process the increment later
            return
            
        # Handle variable increment/decrement
        inc_match = re.match(r'(\w+)(\+\+|--)', line)
        if inc_match:
            var, op = inc_match.groups()
            value = "1" if op == "++" else "-1"
            current_var = f"{var}_{self.get_var_version(var)}"
            new_var = self.fresh_var(var)
            self.current_block.append(f"{new_var} = {current_var} + {value}")
            return
            
        # Handle variable declarations with initialization
        if line.startswith('int ') or line.startswith('float ') or line.startswith('double '):
            # Split by commas for multiple declarations
            declarations = line[line.find(' ')+1:].split(',')
            for decl in declarations:
                decl = decl.strip()
                parts = re.split(r'\s*=\s*', decl, 1)
                var = parts[0].strip()
                if len(parts) > 1:  # Has initialization
                    rhs = parts[1].strip()
                    new_var = self.fresh_var(var)
                    processed_rhs = self.process_expression(rhs)
                    self.current_block.append(f"{new_var} = {processed_rhs}")
                else:  # Just declaration with implicit 0 initialization
                    new_var = self.fresh_var(var) 
                    self.current_block.append(f"{new_var} = 0")
            return
            
        # Handle variable assignments
        if '=' in line and not line.startswith('if ') and not line.startswith('while '):
            parts = re.split(r'\s*=\s*', line, 1)
            if len(parts) == 2:
                lhs, rhs = parts
                self.handle_assignment(lhs.strip(), rhs.strip())
            return
            
        # Handle return statements
        if line.startswith('return '):
            expr = line[7:].strip()
            processed_expr = self.process_expression(expr)
            self.current_block.append(f"return {processed_expr}")
            return
    
    def initialize_array(self):
        """Initialize array elements with version 0"""
        for i in range(self.array_length):
            index_key = f"arr_{i}"
            self.array_versions[index_key] = 0
            self.current_block.append(f"arr{i}_0 = arr[{i}]  // Initial array element")
    
    def get_ssa(self):
        """Get the complete SSA form"""
        return '\n'.join(self.current_block)

def convert_to_ssa(code, array_length=10):
    """Convert code to SSA form with improved handling"""
    import re
    converter = SSAConverter(array_length)
    converter.initialize_array()
    
    # Split code into lines and process each line
    lines = []
    in_for_loop = False
    for_cond = ""
    for_incr = ""
    
    # First pass: handle for loops by extracting their components
    for line in code.split('\n'):
        line = line.strip()
        if not line:
            continue
            
        # Extract for loop components
        for_match = re.match(r'for\s*\((.*?);(.*?);(.*?)\)\s*{?', line)
        if for_match:
            init, cond, incr = for_match.groups()
            in_for_loop = True
            for_cond = cond
            for_incr = incr
            # Add initialization
            if init:
                lines.append(init + ";")
            # Add if condition
            lines.append(f"if ({cond}) {{")
            continue
            
        # Handle end of for loop block
        if in_for_loop and line == "}":
            # Insert increment before closing brace
            lines.append(for_incr + ";")
            # Create a goto-like structure with another if
            lines.append(f"if ({for_cond}) {{")
            # Loop body would go here in real implementation
            lines.append("}")
            in_for_loop = False
            lines.append("}")
            continue
            
        lines.append(line)
    
    # Second pass: process the modified code
    for line in lines:
        converter.process_line(line)
        
    return converter.get_ssa()


def generate():
    try:
        code = input_text.get("1.0", tk.END)
        unroll_count = int(unroll_var.get())
        unrolled = unroll_code(code, unroll_count)
        
        unrolled_output.delete("1.0", tk.END)
        unrolled_output.insert(tk.END, unrolled)
        
        try:
            ssa = convert_to_ssa(unrolled)
            ssa_output.delete("1.0", tk.END)
            ssa_output.insert(tk.END, ssa)
        except Exception as e:
            ssa_output.delete("1.0", tk.END)
            ssa_output.insert(tk.END, f"SSA Conversion Error: {str(e)}")
            
    except Exception as e:
        unrolled_output.delete("1.0", tk.END)
        unrolled_output.insert(tk.END, f"Error: {str(e)}")
        ssa_output.delete("1.0", tk.END)
        ssa_output.insert(tk.END, f"Error: {str(e)}")


# And update the SSAConverter's eval_expr method:
def eval_expr(self, expr):
    # Handle array indices more robustly
    expr = re.sub(r'arr\[(\d+)\]', lambda m: f'arr{m.group(1)}', expr)
    
    # Replace variables with their current versions
    for var in sorted(self.var_versions.keys(), key=lambda x: -len(x)):
        expr = re.sub(rf'\b{var}\b', f'{var}{self.var_versions[var]}', expr)
    return expr

# GUI Setup
root = tk.Tk()
root.title("C++ to SSA Converter")

frame = ttk.Frame(root, padding=10)
frame.grid(row=0, column=0, sticky="nsew")

# Code Input
ttk.Label(frame, text="Enter C++ Code:").grid(row=0, column=0, sticky="w")
input_text = scrolledtext.ScrolledText(frame, height=10, width=80)
input_text.grid(row=1, column=0, columnspan=2, pady=5)

# Unroll Dropdown
ttk.Label(frame, text="Number of Unrolls:").grid(row=2, column=0, sticky="w")
unroll_var = tk.StringVar()
unroll_dropdown = ttk.Combobox(frame, textvariable=unroll_var, values=[1, 2, 3, 4, 5], state="readonly")
unroll_dropdown.grid(row=2, column=1, sticky="w")
unroll_dropdown.set("2")

# Buttons
ttk.Button(frame, text="Generate SSA", command=generate).grid(row=3, column=0, pady=5, sticky="w")

# Unrolled Output
ttk.Label(frame, text="Unrolled Code:").grid(row=4, column=0, sticky="w")
unrolled_output = scrolledtext.ScrolledText(frame, height=10, width=80)
unrolled_output.grid(row=5, column=0, columnspan=2, pady=5)

# SSA Output
ttk.Label(frame, text="SSA Code:").grid(row=6, column=0, sticky="w")
ssa_output = scrolledtext.ScrolledText(frame, height=15, width=80)
ssa_output.grid(row=7, column=0, columnspan=2, pady=5)

root.mainloop()