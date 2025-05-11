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
from copy import deepcopy

class SSAConverter:
    def __init__(self, array_length=5):
        self.var_versions = {}  # Tracks current version of each variable
        self.array_versions = {}  # Tracks current version of each array element
        self.current_block = []  # Stores the SSA form
        self.phi_counter = 1  # Counter for phi functions
        self.context_stack = []  # Stack for tracking nested blocks
        self.array_length = array_length
        self.if_else_stack = []  # Stack for tracking if-else conditions
        self.debug = False  # Debug flag
    
    def get_var_version(self, var):
        """Get current version number of a variable"""
        return self.var_versions.get(var, 0)
    
    def fresh_var(self, var):
        """Create a new version of a variable"""
        count = self.get_var_version(var) + 1
        self.var_versions[var] = count
        return f"{var}_{count}"
    
    def get_array_version(self, index):
        """Get current version number of an array element"""
        return self.array_versions.get(str(index), 0)
    
    def fresh_array(self, index):
        """Create a new version of an array element"""
        index_str = str(index)
        count = self.get_array_version(index_str) + 1
        self.array_versions[index_str] = count
        return f"arr{index_str}_{count}"
    
    def eval_expr(self, expr):
        """Evaluate a simple expression with variable substitution"""
        try:
            # Replace array accesses with temporary variables
            expr = re.sub(r'arr\[(\d+)\]', lambda m: f'arr{m.group(1)}', expr)
            
            # Create a context with variable values
            ctx = {}
            for var, ver in self.var_versions.items():
                if var.isalpha():
                    try:
                        ctx[var] = int(ver)
                    except:
                        pass
            
            # Add array elements to context
            for idx, ver in self.array_versions.items():
                if idx.isdigit():
                    try:
                        ctx[f'arr{idx}'] = int(ver)
                    except:
                        pass
                        
            return eval(expr, {}, ctx)
        except:
            return None
    
    def resolve_array_index(self, index_expr):
        """Resolve array index expressions to a specific array element"""
        # Replace variables with their current versions
        for var, ver in sorted(self.var_versions.items(), key=lambda x: (-len(x[0]), x[0])):
            if var.isalpha():  # Only match whole variable names
                pattern = rf'\b{var}\b'
                index_expr = re.sub(pattern, f"{var}_{ver}", index_expr)
        
        # Try to evaluate the expression if it's simple
        try:
            result = self.eval_expr(index_expr)
            if result is not None and 0 <= result < self.array_length:
                return str(result)
        except:
            pass
        
        return index_expr
    
    def process_array_access(self, array_access):
        """Process array access like arr[j] or arr[j+1]"""
        if not array_access.startswith('arr['):
            return array_access
        
        # Extract the index expression from arr[index]
        index_expr = array_access[4:-1]
        
        # Try to resolve to a specific array element
        resolved_index = self.resolve_array_index(index_expr)
        
        # If we can resolve to a numeric index, use it directly
        if resolved_index.isdigit():
            index_value = int(resolved_index)
            if 0 <= index_value < self.array_length:
                version = self.get_array_version(index_value)
                return f"arr{index_value}_{version}"
        
        # Otherwise, keep the original expression but with versioned variables
        return f"arr[{resolved_index}]"
    
    def process_expression(self, expr):
        """Process expressions, handling variable versions and array access"""
        # Handle array accesses first
        expr = re.sub(
            r'arr\[([^\]]+)\]',
            lambda m: self.process_array_access(f"arr[{m.group(1)}]"),
            expr
        )
        
        # Then handle variables in expressions
        for var in sorted(self.var_versions.keys(), key=lambda x: -len(x)):
            if var.isalpha():  # Only match whole variable names
                pattern = rf'\b{var}\b'
                expr = re.sub(pattern, f"{var}_{self.get_var_version(var)}", expr)
                
        return expr
    
    def handle_increment_decrement(self, line):
        """Handle postfix/prefix increment/decrement operations"""
        # Check for postfix increment/decrement: var++ or var--
        postfix_match = re.match(r'(\w+)(\+\+|--)', line)
        if postfix_match:
            var, op = postfix_match.groups()
            operator = '+' if op == '++' else '-'
            new_var = self.fresh_var(var)
            curr_var = f"{var}_{self.get_var_version(var) - 1}"  # Get previous version
            self.current_block.append(f"{new_var} = {curr_var} {operator} 1")
            return True
        
        # Check for prefix increment/decrement: ++var or --var
        prefix_match = re.match(r'(\+\+|--)(\w+)', line)
        if prefix_match:
            op, var = prefix_match.groups()
            operator = '+' if op == '++' else '-'
            new_var = self.fresh_var(var)
            curr_var = f"{var}_{self.get_var_version(var) - 1}"  # Get previous version
            self.current_block.append(f"{new_var} = {curr_var} {operator} 1")
            return True
            
        return False
    
    def create_phi_node(self, condition_id, var, true_ver, false_ver):
        """Create a phi node for a variable"""
        if true_ver == false_ver:
            return None
            
        phi_var = self.fresh_var(var)
        self.current_block.append(f"{phi_var} = φ{condition_id} ? {var}_{true_ver} : {var}_{false_ver}")
        return phi_var
    
    def create_array_phi_node(self, condition_id, index, true_ver, false_ver):
        """Create a phi node for an array element"""
        if true_ver == false_ver:
            return None
            
        new_ver = max(true_ver, false_ver) + 1
        self.array_versions[str(index)] = new_ver
        self.current_block.append(f"arr{index}_{new_ver} = φ{condition_id} ? arr{index}_{true_ver} : arr{index}_{false_ver}")
        return f"arr{index}_{new_ver}"
    
    def process_if_condition(self, condition):
        """Process an if condition, creating a phi node"""
        processed_condition = self.process_expression(condition)
        phi_id = self.phi_counter
        self.phi_counter += 1
        self.current_block.append(f"φ{phi_id} = {processed_condition}")
        return phi_id
    
    def start_if_block(self, condition):
        """Start an if block, saving context"""
        phi_id = self.process_if_condition(condition)
        
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
        
        # Save if branch versions
        if_data = self.if_else_stack[-1]
        if_data['if_vars'] = {var: ver for var, ver in self.var_versions.items()}
        if_data['if_arrays'] = {idx: ver for idx, ver in self.array_versions.items()}
        
        # Restore versions from before if block
        self.var_versions = {var: ver for var, ver in if_context['vars'].items()}
        self.array_versions = {idx: ver for idx, ver in if_context['arrays'].items()}
    
    def end_block(self):
        """End a block (if, else, for, while)"""
        if not self.context_stack:
            return
            
        context = self.context_stack.pop()
        phi_id = context.get('phi_id')
        
        if context.get('is_else'):
            # End of else block - create phi nodes
            if_data = self.if_else_stack.pop()
            if phi_id != if_data['phi_id']:
                if self.debug:
                    self.current_block.append(f"// WARNING: phi_id mismatch {phi_id} vs {if_data['phi_id']}")
            
            # Process all variables modified in either branch
            all_vars = set(if_data['if_vars'].keys()) | set(self.var_versions.keys())
            for var in all_vars:
                if_ver = if_data['if_vars'].get(var, context['vars'].get(var, 0))
                else_ver = self.var_versions.get(var, context['vars'].get(var, 0))
                if if_ver != else_ver:
                    self.create_phi_node(phi_id, var, if_ver, else_ver)
            
            # Process arrays
            all_indices = set(if_data.get('if_arrays', {}).keys()) | set(self.array_versions.keys())
            for idx in all_indices:
                if_ver = if_data.get('if_arrays', {}).get(idx, context['arrays'].get(idx, 0))
                else_ver = self.array_versions.get(idx, context['arrays'].get(idx, 0))
                if if_ver != else_ver:
                    self.create_array_phi_node(phi_id, idx, if_ver, else_ver)
        else:
            # End of if block without else - create phi nodes
            for var, before_ver in context['vars'].items():
                after_ver = self.var_versions.get(var, before_ver)
                if before_ver != after_ver:
                    self.create_phi_node(phi_id, var, after_ver, before_ver)
            
            # Process arrays
            for idx, before_ver in context['arrays'].items():
                after_ver = self.array_versions.get(idx, before_ver)
                if before_ver != after_ver:
                    self.create_array_phi_node(phi_id, idx, after_ver, before_ver)
    
    def process_line(self, line):
        """Process a single line of code"""
        line = line.strip()
        if not line or line.startswith('//'):
            return
            
        # Remove trailing semicolon
        if line.endswith(';'):
            line = line[:-1].rstrip()
            
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
            
        # Handle increment/decrement operations
        if self.handle_increment_decrement(line):
            return
            
        # Handle variable declarations with initialization
        if line.startswith('int ') or line.startswith('float ') or line.startswith('double '):
            parts = re.split(r'\s*=\s*', line[line.find(' ')+1:], 1)
            var = parts[0].strip()
            if len(parts) > 1:  # Has initialization
                rhs = parts[1].strip()
                new_var = self.fresh_var(var)
                processed_rhs = self.process_expression(rhs)
                self.current_block.append(f"{new_var} = {processed_rhs}")
            else:  # Just declaration
                self.fresh_var(var)  # Create first version
            return
            
        # Handle variable assignments
        if '=' in line and not line.startswith('if ') and not line.startswith('while '):
            lhs, rhs = re.split(r'\s*=\s*', line, 1)
            lhs = lhs.strip()
            rhs = rhs.strip()
            
            # Handle array assignments
            if lhs.startswith('arr['):
                # Extract index expression
                idx_expr = lhs[4:-1]
                resolved_idx = self.resolve_array_index(idx_expr)
                
                # If we have a simple numeric index
                if resolved_idx.isdigit():
                    idx = int(resolved_idx)
                    if 0 <= idx < self.array_length:
                        new_arr = self.fresh_array(idx)
                        processed_rhs = self.process_expression(rhs)
                        self.current_block.append(f"{new_arr} = {processed_rhs}")
                    else:
                        # Out of bounds array access
                        processed_idx = self.process_expression(idx_expr)
                        processed_rhs = self.process_expression(rhs)
                        self.current_block.append(f"arr[{processed_idx}] = {processed_rhs}")
                else:
                    # More complex index expression
                    processed_idx = self.process_expression(idx_expr)
                    processed_rhs = self.process_expression(rhs)
                    self.current_block.append(f"arr[{processed_idx}] = {processed_rhs}")
                return
                
            # Regular variable assignment
            var = lhs.split()[0] if ' ' in lhs else lhs
            new_var = self.fresh_var(var)
            processed_rhs = self.process_expression(rhs)
            self.current_block.append(f"{new_var} = {processed_rhs}")
            return
            
        # Handle for loops - not unrolling, just initial assignment
        for_match = re.match(r'for\s*\(\s*(.*?)\s*;\s*(.*?)\s*;\s*(.*?)\s*\)', line)
        if for_match:
            init, cond, incr = for_match.groups()
            if init:
                self.process_line(init)
            return
            
        # Handle while loops
        while_match = re.match(r'while\s*\((.*)\)', line)
        if while_match:
            condition = while_match.group(1)
            self.process_if_condition(condition)  # Just create phi node for condition
            return
            
        # Handle return statements
        if line.startswith('return '):
            ret_val = line[7:].strip()
            processed_ret = self.process_expression(ret_val)
            self.current_block.append(f"return {processed_ret}")
            return
            
        # Other statements are passed through
        self.current_block.append(f"// Unprocessed: {line}")
    
    def get_ssa(self):
        """Get the SSA form"""
        return '\n'.join(self.current_block)
    
    def initialize_array(self):
        """Initialize array elements with version 0"""
        for i in range(self.array_length):
            self.array_versions[str(i)] = 0

def convert_to_ssa(code, array_length=10):
    """Convert code to SSA form"""
    converter = SSAConverter(array_length)
    converter.initialize_array()
    
    # Split code into lines and process each line
    for line in code.split('\n'):
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