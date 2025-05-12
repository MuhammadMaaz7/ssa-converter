import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
import re
from smtlib import SSAtoZ3Converter
from functools import partial

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
            if re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', var):  # valid variable name pattern
                pattern = rf'\b{var}\b'
                version = self.get_var_version(var)
                #print("Version : %s",version)
                #print(result," 1")
                print(f"Replacing '{var}' with '{var}_{version}'")
                result = re.sub(pattern, f"{var}_{version}", result)
                #print(result," 2")
                
        if(result=="min_idx"):
            print("Pakra gaya")
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
       # print(self.process_variable_references(result))
        return self.process_variable_references(result)
    
    def start_if_block(self, condition):
        """Start an if block, saving context"""
        processed_condition = self.process_expression(condition)
       # print(processed_condition)
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
    
    # def end_block(self):
    #     """End a block (if, else) with proper phi node creation"""
    #     if not self.context_stack:
    #         return
            
    #     context = self.context_stack.pop()
    #     phi_id = context.get('phi_id')
        
    #     if context.get('is_else'):
    #         # End of else block - create comprehensive phi nodes
    #         if_data = self.if_else_stack.pop()
            
    #         # Process all variables modified in either branch
    #         all_vars = set(if_data['if_vars'].keys()) | set(self.var_versions.keys())
    #         for var in all_vars:
    #             if_ver = if_data['if_vars'].get(var, context['vars'].get(var, 0))
    #             else_ver = self.var_versions.get(var, context['vars'].get(var, 0))
                
    #             # Only create phi node if versions differ
    #             if if_ver != else_ver:
    #                 new_var = self.fresh_var(var)
    #                 self.current_block.append(f"{new_var} = φ{phi_id} ? {var}_{if_ver} : {var}_{else_ver}")
            
    #         # Process arrays - make phi nodes for each potentially modified array element
    #         all_indices = set(if_data['if_arrays'].keys()) | set(self.array_versions.keys())
    #         for idx_key in all_indices:
    #             if '_' in idx_key:
    #                 array_name, idx = idx_key.split('_')
    #                 if_ver = if_data['if_arrays'].get(idx_key, context['arrays'].get(idx_key, 0))
    #                 else_ver = self.array_versions.get(idx_key, context['arrays'].get(idx_key, 0))
                    
    #                 # Only create phi node if versions differ
    #                 if if_ver != else_ver:
    #                     # Create new version for this array element
    #                     new_ver = max(if_ver, else_ver) + 1
    #                     self.array_versions[idx_key] = new_ver
    #                     self.current_block.append(
    #                         f"{array_name}{idx}_{new_ver} = φ{phi_id} ? {array_name}{idx}_{if_ver} : {array_name}{idx}_{else_ver}"
    #                     )
    #     else:
    #         # End of if block without else - create phi nodes comparing with state before if
    #         for var, before_ver in context['vars'].items():
    #             after_ver = self.var_versions.get(var, before_ver)
    #             if before_ver != after_ver:
    #                 new_var = self.fresh_var(var)
    #                 self.current_block.append(f"{new_var} = φ{phi_id} ? {var}_{after_ver} : {var}_{before_ver}")
            
    #         # Create phi nodes for array elements
    #         for idx_key, before_ver in context['arrays'].items():
    #             after_ver = self.array_versions.get(idx_key, before_ver)
    #             if before_ver != after_ver and '_' in idx_key:
    #                 array_name, idx = idx_key.split('_')
    #                 new_ver = max(after_ver, before_ver) + 1
    #                 self.array_versions[idx_key] = new_ver
    #                 self.current_block.append(
    #                     f"{array_name}{idx}_{new_ver} = φ{phi_id} ? {array_name}{idx}_{after_ver} : {array_name}{idx}_{before_ver}"
    #                 )
    
    # def handle_assignment(self, lhs, rhs):
    #     """Handle variable or array assignment"""
    #     rhs = self.process_expression(rhs)
        
    #     # Handle array assignment: arr[i] = value
    #     if '[' in lhs and ']' in lhs:
    #         array_match = re.match(r'(\w+)\[(.*)\]', lhs)
    #         if array_match:
    #             array_name, idx_expr = array_match.groups()
    #             processed_idx = self.process_variable_references(idx_expr)
                
    #             # If index is a simple number
    #             if processed_idx.isdigit():
    #                 idx = int(processed_idx)
    #                 if 0 <= idx < self.array_length:
    #                     new_arr = self.fresh_array(idx, array_name)
    #                     self.current_block.append(f"{new_arr} = {rhs}")
    #                 else:
    #                     # Out of bounds or complex index
    #                     self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
    #             else:
    #                 # For expressions like j_1, try to resolve
    #                 j_match = re.match(r'(\w+)_(\d+)', processed_idx)
    #                 if j_match and j_match.group(1).isalpha():
    #                     # We can't determine the actual value at compile time
    #                     # So we need to represent it symbolically but preserve SSA form
    #                     self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
    #                 elif "+" in processed_idx:
    #                     # Handle j+1 type indices similarly
    #                     self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
    #                 else:
    #                     # Other symbolic indices
    #                     self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
    #     else:
    #         # Regular variable assignment
    #         var = lhs.strip()
    #         new_var = self.fresh_var(var)
    #         #print(new_var)
    #         self.current_block.append(f"{new_var} = {rhs}")
    def handle_assignment(self, lhs, rhs):
        """Handle variable or array assignment with proper phi condition checking"""
        rhs = self.process_expression(rhs)
        
        # Handle array assignment: arr[i] = value
        if '[' in lhs and ']' in lhs:
            array_match = re.match(r'(\w+)\[(.*)\]', lhs)
            if array_match:
                array_name, idx_expr = array_match.groups()
                processed_idx = self.process_expression(idx_expr)
                
                # If we're inside a conditional block, we need to track the phi conditions
                if self.context_stack:
                    current_phi = self.context_stack[-1]['phi_id']
                    # Create a new version that depends on the phi condition
                    if processed_idx.isdigit():
                        idx = int(processed_idx)
                        if 0 <= idx < self.array_length:
                            new_arr = self.fresh_array(idx, array_name)
                            self.current_block.append(f"{new_arr} = φ{current_phi} ? {rhs} : {array_name}{idx}_{self.get_array_version(array_name, idx)-1}")
                            return
                    # For symbolic indices, we need to handle differently
                    self.current_block.append(f"{array_name}[{processed_idx}] = φ{current_phi} ? {rhs} : {array_name}[{processed_idx}]")
                    return
                
                # Normal array assignment when not in conditional block
                if processed_idx.isdigit():
                    idx = int(processed_idx)
                    if 0 <= idx < self.array_length:
                        new_arr = self.fresh_array(idx, array_name)
                        self.current_block.append(f"{new_arr} = {rhs}")
                    else:
                        self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
                else:
                    self.current_block.append(f"{array_name}[{processed_idx}] = {rhs}")
        else:
            # Regular variable assignment
            var = lhs.strip()
            new_var = self.fresh_var(var)
            
            # If we're inside a conditional block, make the assignment depend on the phi condition
            if self.context_stack:
                current_phi = self.context_stack[-1]['phi_id']
                prev_version = f"{var}_{self.get_var_version(var)}"
                self.current_block.append(f"{new_var} = φ{current_phi} ? {rhs} : {prev_version}")
            else:
                self.current_block.append(f"{new_var} = {rhs}")

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
                    
                    if if_ver != else_ver:
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
    
    # ... (rest of the class remains the same)
                
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
            # self.current_block.append(f"arr{i}_0 = arr[{i}]  // Initial array element")
    
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

class SSAConverterApp:
    def __init__(self, root):
        self.root = root
        self.root.title("SSA Converter Tool")
        self.root.geometry("1000x800")
        self.root.minsize(800, 600)
        
        # Set theme
        self.style = ttk.Style()
        self.style.theme_use('clam')
        
        # Configure colors
        self.bg_color = "#f5f5f5"  # Light gray
        self.accent_color = "#4a86e8"  # Blue
        self.text_color = "#333333"  # Dark gray
        self.root.configure(bg=self.bg_color)
        
        # Configure styles
        self.style.configure('TFrame', background=self.bg_color)
        self.style.configure('TLabel', background=self.bg_color, foreground=self.text_color, font=('Arial', 10))
        self.style.configure('TButton', background=self.accent_color, foreground='white', borderwidth=0, font=('Arial', 10, 'bold'))
        self.style.configure('Header.TLabel', font=('Arial', 14, 'bold'), background=self.bg_color, foreground=self.text_color)
        self.style.configure('Mode.TButton', font=('Arial', 11), padding=8)
        
        # Current mode
        self.current_mode = tk.StringVar(value="verification")
        
        self.create_widgets()
        
    def create_widgets(self):
        # Main container
        main_container = ttk.Frame(self.root)
        main_container.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        # Header with title and mode selector
        header_frame = ttk.Frame(main_container)
        header_frame.pack(fill=tk.X, pady=(0, 15))
        
        title_label = ttk.Label(header_frame, text="SSA Converter Tool", style='Header.TLabel')
        title_label.pack(side=tk.LEFT)
        
        # Mode selector
        mode_frame = ttk.Frame(header_frame)
        mode_frame.pack(side=tk.RIGHT)
        
        ttk.Label(mode_frame, text="Mode:").pack(side=tk.LEFT, padx=(0, 10))
        
        verification_btn = ttk.Radiobutton(mode_frame, text="Verification", variable=self.current_mode, 
                                           value="verification", command=self.change_mode)
        verification_btn.pack(side=tk.LEFT, padx=5)
        
        equivalence_btn = ttk.Radiobutton(mode_frame, text="Equivalence", variable=self.current_mode, 
                                          value="equivalence", command=self.change_mode)
        equivalence_btn.pack(side=tk.LEFT, padx=5)
        
        # Content area
        self.content_frame = ttk.Frame(main_container)
        self.content_frame.pack(fill=tk.BOTH, expand=True)
        
        # Initialize with verification mode
        self.setup_verification_mode()
        
    def setup_verification_mode(self):
        # Clear existing content
        for widget in self.content_frame.winfo_children():
            widget.destroy()
            
        # Input frame
        input_frame = ttk.Frame(self.content_frame)
        input_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        # Left column - Code input
        left_frame = ttk.Frame(input_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        input_header = ttk.Frame(left_frame)
        input_header.pack(fill=tk.X)
        
        ttk.Label(input_header, text="Input C++ Code").pack(side=tk.LEFT)
        
        # File operations
        btn_frame = ttk.Frame(input_header)
        btn_frame.pack(side=tk.RIGHT)
        
        ttk.Button(btn_frame, text="Load File", command=self.load_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="Save", command=self.save_file).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="Clear", command=self.clear_input).pack(side=tk.LEFT, padx=2)
        
        # Input text area
        self.input_text = scrolledtext.ScrolledText(left_frame, wrap=tk.WORD, 
                                                   font=('Consolas', 11), bg='white')
        self.input_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Right column - Settings
        right_frame = ttk.Frame(input_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=(5, 0))
        
        ttk.Label(right_frame, text="Settings").pack(anchor='w', pady=(0, 5))
        
        # Unroll settings
        unroll_frame = ttk.Frame(right_frame)
        unroll_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(unroll_frame, text="Number of Unrolls:").pack(side=tk.LEFT)
        
        self.unroll_var = tk.StringVar(value="2")
        unroll_dropdown = ttk.Combobox(unroll_frame, textvariable=self.unroll_var, 
                                      values=[1, 2, 3, 4, 5], state="readonly", width=5)
        unroll_dropdown.pack(side=tk.LEFT, padx=(5, 0))
        
        # Generate button
        generate_btn = ttk.Button(right_frame, text="Generate", command=self.generate)
        generate_btn.pack(fill=tk.X, pady=10)
        
        # Output notebook
        output_notebook = ttk.Notebook(self.content_frame)
        output_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Unrolled code tab
        unrolled_frame = ttk.Frame(output_notebook)
        output_notebook.add(unrolled_frame, text="Unrolled Code")
        
        self.unrolled_output = scrolledtext.ScrolledText(unrolled_frame, wrap=tk.WORD, 
                                                        font=('Consolas', 11), bg='white')
        self.unrolled_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # SSA code tab
        ssa_frame = ttk.Frame(output_notebook)
        output_notebook.add(ssa_frame, text="SSA Code")
        
        self.ssa_output = scrolledtext.ScrolledText(ssa_frame, wrap=tk.WORD, 
                                                  font=('Consolas', 11), bg='white')
        self.ssa_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Z3 code tab
        z3_frame = ttk.Frame(output_notebook)
        output_notebook.add(z3_frame, text="Z3 Code")
        
        self.z3_output = scrolledtext.ScrolledText(z3_frame, wrap=tk.WORD, 
                                                 font=('Consolas', 11), bg='white')
        self.z3_output.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
    
    def setup_equivalence_mode(self):
        # Clear existing content
        for widget in self.content_frame.winfo_children():
            widget.destroy()
            
        # Split view for two programs
        paned_window = ttk.PanedWindow(self.content_frame, orient=tk.HORIZONTAL)
        paned_window.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        # Left program frame
        left_program = ttk.Frame(paned_window)
        paned_window.add(left_program, weight=1)
        
        ttk.Label(left_program, text="Program 1").pack(anchor='w')
        
        self.program1_text = scrolledtext.ScrolledText(left_program, wrap=tk.WORD, 
                                                      font=('Consolas', 11), bg='white')
        self.program1_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Right program frame
        right_program = ttk.Frame(paned_window)
        paned_window.add(right_program, weight=1)
        
        ttk.Label(right_program, text="Program 2").pack(anchor='w')
        
        self.program2_text = scrolledtext.ScrolledText(right_program, wrap=tk.WORD, 
                                                      font=('Consolas', 11), bg='white')
        self.program2_text.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
        
        # Settings and actions frame
        settings_frame = ttk.Frame(self.content_frame)
        settings_frame.pack(fill=tk.X, pady=10)
        
        # Unroll settings
        ttk.Label(settings_frame, text="Number of Unrolls:").pack(side=tk.LEFT)
        
        self.equivalence_unroll_var = tk.StringVar(value="2")
        unroll_dropdown = ttk.Combobox(settings_frame, textvariable=self.equivalence_unroll_var, 
                                      values=[1, 2, 3, 4, 5], state="readonly", width=5)
        unroll_dropdown.pack(side=tk.LEFT, padx=(5, 15))
        
        # Compare button
        compare_btn = ttk.Button(settings_frame, text="Check Equivalence", 
                                command=self.check_equivalence)
        compare_btn.pack(side=tk.RIGHT)
        
        # Results area
        results_frame = ttk.Frame(self.content_frame)
        results_frame.pack(fill=tk.BOTH, expand=True)
        
        ttk.Label(results_frame, text="Equivalence Analysis Results").pack(anchor='w')
        
        self.results_output = scrolledtext.ScrolledText(results_frame, wrap=tk.WORD, 
                                                       font=('Consolas', 11), bg='white')
        self.results_output.pack(fill=tk.BOTH, expand=True, pady=(5, 0))
    
    def change_mode(self):
        mode = self.current_mode.get()
        if mode == "verification":
            self.setup_verification_mode()
        else:
            self.setup_equivalence_mode()
    
    def generate(self):
        try:
            code = self.input_text.get("1.0", tk.END)
            unroll_count = int(self.unroll_var.get())
            
            # Generate unrolled code
            unrolled = unroll_code(code, unroll_count)
            self.unrolled_output.delete("1.0", tk.END)
            self.unrolled_output.insert(tk.END, unrolled)
            
            # Generate SSA code
            try:
                ssa = convert_to_ssa(unrolled)
                self.ssa_output.delete("1.0", tk.END)
                self.ssa_output.insert(tk.END, ssa)
                
                # Generate Z3 Code
                try:
                    converter = SSAtoZ3Converter()
                    converter.parse_ssa(ssa)
                    z3_code = converter.generate_z3_code()
                    self.z3_output.delete("1.0", tk.END)
                    self.z3_output.insert(tk.END, z3_code)
                except Exception as e:
                    self.z3_output.delete("1.0", tk.END)
                    self.z3_output.insert(tk.END, f"Z3 Generation Error: {str(e)}")
            except Exception as e:
                self.ssa_output.delete("1.0", tk.END)
                self.ssa_output.insert(tk.END, f"SSA Conversion Error: {str(e)}")
                self.z3_output.delete("1.0", tk.END)
                self.z3_output.insert(tk.END, "Z3 generation unavailable due to SSA error")
        except Exception as e:
            messagebox.showerror("Error", f"An error occurred: {str(e)}")
    
    def check_equivalence(self):
        try:
            program1 = self.program1_text.get("1.0", tk.END)
            program2 = self.program2_text.get("1.0", tk.END)
            unroll_count = int(self.equivalence_unroll_var.get())
            
            # Unroll both programs
            unrolled1 = unroll_code(program1, unroll_count)
            unrolled2 = unroll_code(program2, unroll_count)
            
            # Convert to SSA
            ssa1 = convert_to_ssa(unrolled1)
            ssa2 = convert_to_ssa(unrolled2)
            
            # Generate Z3 equivalence check
            self.results_output.delete("1.0", tk.END)
            self.results_output.insert(tk.END, "Analyzing equivalence...\n\n")
            self.results_output.insert(tk.END, "Program 1 SSA:\n" + ssa1 + "\n\n")
            self.results_output.insert(tk.END, "Program 2 SSA:\n" + ssa2 + "\n\n")
            
            # This would be where we'd implement the actual equivalence checking
            self.results_output.insert(tk.END, "Z3 Equivalence Check:\n")
            self.results_output.insert(tk.END, "// Placeholder for actual Z3 equivalence verification\n")
            self.results_output.insert(tk.END, "from z3 import *\n\n")
            self.results_output.insert(tk.END, "# This would contain the Z3 code to verify equivalence\n")
            self.results_output.insert(tk.END, "# between the two provided programs\n")
            
        except Exception as e:
            self.results_output.delete("1.0", tk.END)
            self.results_output.insert(tk.END, f"Error during equivalence check: {str(e)}")
    
    def load_file(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("C/C++ files", "*.c;*.cpp"), ("All files", "*.*")]
        )
        if file_path:
            try:
                with open(file_path, 'r') as file:
                    content = file.read()
                    if self.current_mode.get() == "verification":
                        self.input_text.delete("1.0", tk.END)
                        self.input_text.insert(tk.END, content)
                    else:
                        # Ask which program to load into
                        choice = messagebox.askquestion("Load File", 
                                                       "Load into Program 1? (No will load into Program 2)")
                        if choice == 'yes':
                            self.program1_text.delete("1.0", tk.END)
                            self.program1_text.insert(tk.END, content)
                        else:
                            self.program2_text.delete("1.0", tk.END)
                            self.program2_text.insert(tk.END, content)
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load file: {str(e)}")
    
    def save_file(self):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".cpp",
            filetypes=[("C++ files", "*.cpp"), ("All files", "*.*")]
        )
        if file_path:
            try:
                with open(file_path, 'w') as file:
                    if self.current_mode.get() == "verification":
                        content = self.input_text.get("1.0", tk.END)
                    else:
                        # Ask which program to save
                        choice = messagebox.askquestion("Save File", 
                                                       "Save Program 1? (No will save Program 2)")
                        if choice == 'yes':
                            content = self.program1_text.get("1.0", tk.END)
                        else:
                            content = self.program2_text.get("1.0", tk.END)
                    file.write(content)
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save file: {str(e)}")
    
    def clear_input(self):
        if self.current_mode.get() == "verification":
            self.input_text.delete("1.0", tk.END)
        else:
            # Ask which program to clear
            choice = messagebox.askquestion("Clear Input", 
                                           "Clear Program 1? (No will clear Program 2)")
            if choice == 'yes':
                self.program1_text.delete("1.0", tk.END)
            else:
                self.program2_text.delete("1.0", tk.END)

if __name__ == "__main__":
    root = tk.Tk()
    app = SSAConverterApp(root)
    root.mainloop()