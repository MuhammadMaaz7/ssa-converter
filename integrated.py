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
        raise ValueError("Input should start with a loop, not variable declaration")

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
        raise ValueError("Only for and while loops are supported")

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

        tk.Label(root, text="Enter Loop Code:").pack()
        self.input_box = scrolledtext.ScrolledText(root, height=12, width=100)
        self.input_box.pack()

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
        if not code:
            self.unrolled_output.insert(tk.END, "Error: No input provided\n")
            return

        try:
            unrolled = unroll_loop(code)
            self.unrolled_output.delete("1.0", tk.END)
            self.unrolled_output.insert(tk.END, unrolled)

            ssa_code = self.convert_to_ssa(unrolled.splitlines())
            self.ssa_output.delete("1.0", tk.END)
            self.ssa_output.insert(tk.END, "\n".join(ssa_code))

        except Exception as e:
            self.unrolled_output.delete("1.0", tk.END)
            self.unrolled_output.insert(tk.END, f"Error: {str(e)}\n")

    def convert_to_ssa(self, raw_code):
        ssa_lines = []
        version = {}
        phi_id = 1
        stack = []

        def get_var_version(var):
            version.setdefault(var, 0)
            return f"{var}_{version[var]}"

        def bump_version(var):
            version.setdefault(var, 0)
            version[var] += 1
            return f"{var}_{version[var]}"

        for line in raw_code:
            line = line.strip()

            if not line or line.startswith("//"):
                continue

            # Handle if / while condition
            if re.match(r"(if|else if|while)\s*\(.*\)", line):
                keyword = line.split("(")[0].strip()
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = condition
                for var in set(vars_in_cond):
                    cond_expr = re.sub(rf'\b{var}\b', get_var_version(var), cond_expr)
                ssa_lines.append(f"φ{phi_id} = ({cond_expr})  // {keyword}")
                # Save snapshot of versions before block
                pre_versions = {var: version.get(var, 0) for var in version}
                stack.append((phi_id, pre_versions, {}))  # assigned_vars dict
                phi_id += 1
                continue

            # Handle assert
            elif line.startswith("assert"):
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = condition
                for var in set(vars_in_cond):
                    cond_expr = re.sub(rf'\b{var}\b', get_var_version(var), cond_expr)
                ssa_lines.append(f"assert({cond_expr})")
                continue

            # Handle assignment
            elif "=" in line:
                parts = line.replace(";", "").split("=")
                if len(parts) != 2:
                    ssa_lines.append(f"// Skipped unsupported line: {line}")
                    continue
                left, right = map(str.strip, parts)
                right_vars = re.findall(r"\b[a-zA-Z_]\w*\b", right)
                new_right = right
                for var in set(right_vars):
                    new_right = re.sub(rf'\b{var}\b', get_var_version(var), new_right)
                new_left = bump_version(left)
                ssa_lines.append(f"{new_left} := {new_right}")
                if stack:
                    stack[-1][2][left] = version[left]  # update assigned_vars
                continue

            # Handle end of block
            elif line == "}":
                if stack:
                    cond_phi, pre_versions, assigned_vars = stack.pop()
                    for var, new_ver in assigned_vars.items():
                        old_ver = pre_versions.get(var, 0)
                        if old_ver != new_ver:
                            phi_result = bump_version(var)
                            ssa_lines.append(f"{phi_result} := φ{cond_phi}? {var}_{old_ver} : {var}_{new_ver}")
                continue

            # Handle anything else
            else:
                ssa_lines.append(f"// Unhandled: {line}")

        return ssa_lines


if __name__ == "__main__":
    root = tk.Tk()
    app = LoopUnrollSSAApp(root)
    root.mainloop()
