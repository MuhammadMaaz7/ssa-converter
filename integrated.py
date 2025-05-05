import tkinter as tk
from tkinter import scrolledtext
import re

def unroll_loop(code, unroll_count=2, level=0):
    lines = [line.rstrip() for line in code.strip().split('\n') if line.strip()]
    if not lines:
        raise ValueError("Empty input")
    code = '\n'.join(lines)

    first_line = lines[0].strip()
    if re.match(r'^\s*\w+\s*:=\s*\d+\s*;', first_line) or re.match(r'^\s*int\s+\w+\s*=\s*\d+\s*;', first_line):
        # Allow non-loop code by returning early
        return code

    code = code.strip()
    if code.startswith('for'):
        match = re.match(r'for\s*\((.*?);(.*?);(.*?)\)\s*\{(.*)\}', code, re.DOTALL)
        if not match:
            raise ValueError("Invalid for loop format")
        init, condition, update, body = match.groups()
    elif code.startswith('while'):
        match = re.match(r'while\s*\((.*?)\)\s*\{(.*)\}', code, re.DOTALL)
        if not match:
            raise ValueError("Invalid while loop format")
        condition = match.group(1)
        body = match.group(2)
        init, update = "", ""
    else:
        # If not a loop, just return original for SSA conversion
        return code

    init = init.strip()
    condition = condition.strip()
    update = update.strip()
    body = body.strip()

    indent = '    ' * level
    result = []

    if init:
        result.append(indent + init)

    for _ in range(unroll_count):
        result.append(indent + f"if ({condition}) {{")
        inner_indent = '    ' * (level + 1)

        body_lines = body.split('\n')
        buffer = []
        nested_result = []
        inside_loop = False
        braces_balance = 0

        for line in body_lines:
            line_stripped = line.strip()
            if (line_stripped.startswith("for") or line_stripped.startswith("while")) and not inside_loop:
                inside_loop = True
                buffer = [line]
                braces_balance = line.count('{') - line.count('}')
            elif inside_loop:
                buffer.append(line)
                braces_balance += line.count('{') - line.count('}')
                if braces_balance == 0:
                    nested_code = '\n'.join(buffer)
                    nested_unrolled = unroll_loop(nested_code, unroll_count, level + 2)
                    nested_result.append(nested_unrolled)
                    inside_loop = False
            elif not inside_loop:
                nested_result.append(inner_indent + line_stripped)

        result.extend(nested_result)

        if update:
            result.append(inner_indent + update)
        elif code.startswith('while'):
            cond_var = re.match(r'^\s*(\w+)\s*[<>=]', condition)
            if cond_var:
                var = cond_var.group(1)
                result.append(inner_indent + f"{var} = {var} + 1;")

        result.append(indent + "}")

    return '\n'.join(result)


class LoopUnrollSSAApp:
    def __init__(self, root):
        self.root = root
        root.title("Loop Unroller + SSA Converter")

        tk.Label(root, text="Enter Code:").pack()
        self.input_box = scrolledtext.ScrolledText(root, height=12, width=100)
        self.input_box.pack()

        tk.Label(root, text="Number of Unrolls (only for loops):").pack()
        self.unroll_entry = tk.Entry(root)
        self.unroll_entry.insert(0, "2")
        self.unroll_entry.pack()

        self.process_button = tk.Button(root, text="Unroll and Convert to SSA", command=self.process)
        self.process_button.pack()

        tk.Label(root, text="Unrolled Code:").pack()
        self.unrolled_output = scrolledtext.ScrolledText(root, height=10, width=100)
        self.unrolled_output.pack()

        tk.Label(root, text="SSA Converted Code:").pack()
        self.ssa_output = scrolledtext.ScrolledText(root, height=10, width=100)
        self.ssa_output.pack()

    def process(self):
        code = self.input_box.get("1.0", tk.END).strip()
        try:
            unroll_count = int(self.unroll_entry.get())
            if unroll_count < 1:
                raise ValueError("Unroll count must be at least 1")
        except ValueError:
            self.unrolled_output.delete("1.0", tk.END)
            self.unrolled_output.insert(tk.END, "Error: Invalid unroll count\n")
            return

        if not code:
            self.unrolled_output.insert(tk.END, "Error: No input provided\n")
            return

        try:
            if code.strip().startswith(('for', 'while')):
                unrolled = unroll_loop(code, unroll_count)
            else:
                unrolled = code  # Skip unrolling if not a loop

            self.unrolled_output.delete("1.0", tk.END)
            self.unrolled_output.insert(tk.END, unrolled)

            ssa_code = self.convert_to_ssa(unrolled.splitlines())
            self.ssa_output.delete("1.0", tk.END)
            self.ssa_output.insert(tk.END, "\n".join(ssa_code))

        except Exception as e:
            self.unrolled_output.delete("1.0", tk.END)
            self.unrolled_output.insert(tk.END, f"Error: {str(e)}\n")

    def convert_to_ssa(self, raw_code):
        version = {}
        phi_id = 1
        stack = []
        current_assignments = {}
        final_assignments = {}

        def get_var_version(var):
            if var in {'true', 'false'} or var.isdigit():
                return var
            if var not in version:
                version[var] = 0
                current_assignments[var] = f"{var}_{version[var]}"
            return current_assignments[var]

        def bump_version(var):
            version[var] = version.get(var, 0) + 1
            current_assignments[var] = f"{var}_{version[var]}"
            return current_assignments[var]

        ssa_lines = []
        for line in raw_code:
            line = line.strip()
            if not line or line.startswith("//"):
                continue

            if re.match(r"(if|else if|while)\s*\(.*\)", line):
                keyword = line.split("(")[0].strip()
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                for var in set(vars_in_cond):
                    condition = re.sub(rf'\b{var}\b', get_var_version(var), condition)
                ssa_lines.append(f"\u03d5{phi_id} = ({condition})  // {keyword}")
                stack.append((phi_id, {}, False))
                phi_id += 1
                continue

            elif line.startswith("else"):
                if stack:
                    prev_phi_id, prev_vars, _ = stack[-1]
                    stack[-1] = (prev_phi_id, prev_vars, True)
                continue

            elif line == "}":
                if stack:
                    phi_num, assigned_vars, has_else = stack.pop()
                    for var, if_version in assigned_vars.items():
                        prev_version_num = version[var] - 1
                        prev_version = f"{var}_{prev_version_num}"
                        phi_var = bump_version(var)
                        alt_branch = f"{if_version}" if has_else else prev_version
                        ssa_lines.append(f"{phi_var} := \u03d5{phi_num}? {if_version}:{alt_branch}")
                        final_assignments[var] = phi_var
                continue

            elif "=" in line and ";" in line:
                parts = line.replace(";", "").split("=")
                if len(parts) == 2:
                    left, right = map(str.strip, parts)
                    vars_in_rhs = re.findall(r"\b[a-zA-Z_]\w*\b", right)
                    for var in set(vars_in_rhs):
                        right = re.sub(rf'\b{var}\b', get_var_version(var), right)
                    new_left = bump_version(left)
                    ssa_lines.append(f"{new_left} := {right}")
                    if stack:
                        stack[-1][1][left] = new_left
                    final_assignments[left] = new_left
                continue

            else:
                ssa_lines.append(line)

        return ssa_lines


if __name__ == "__main__":
    root = tk.Tk()
    app = LoopUnrollSSAApp(root)
    root.mainloop()
