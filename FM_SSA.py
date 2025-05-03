import tkinter as tk
from tkinter import scrolledtext
import re

class SSAConverter:
    def __init__(self, root):
        self.root = root
        root.title("SSA Converter")

        tk.Label(root, text="Enter Code:").pack()
        self.code_input = scrolledtext.ScrolledText(root, height=15, width=80)
        self.code_input.pack()

        self.convert_button = tk.Button(root, text="Convert to SSA", command=self.convert_to_ssa)
        self.convert_button.pack()

        tk.Label(root, text="SSA Output:").pack()
        self.output_box = scrolledtext.ScrolledText(root, height=15, width=80)
        self.output_box.pack()

    def convert_to_ssa(self):
        raw_code = self.code_input.get("1.0", tk.END).strip().splitlines()
        ssa_lines = []
        version = {}
        phi_counter = 1
        indent_stack = []

        def get_version(var):
            return f"{var}{version.get(var, 0)}"

        def bump_version(var):
            version[var] = version.get(var, 0) + 1
            return f"{var}{version[var]}"

        def parse_expr(expr):
            # Replace variables in expression with versioned ones
            tokens = re.split(r'(\W+)', expr)
            return ''.join(get_version(tok) if re.match(r'^[a-zA-Z_]\w*$', tok) and not tok.isupper() else tok for tok in tokens)

        for line in raw_code:
            line = line.strip()
            if not line or line.startswith("//"):
                continue

            if line.startswith("if"):
                condition = re.search(r'\((.*)\)', line).group(1)
                condition_ssa = parse_expr(condition)
                ssa_lines.append(f"{phi_counter}. φ{phi_counter} := ({condition_ssa})")
                indent_stack.append(f"φ{phi_counter}")
                phi_counter += 1
                continue

            elif line.startswith("while"):
                condition = re.search(r'\((.*)\)', line).group(1)
                condition_ssa = parse_expr(condition)
                ssa_lines.append(f"{phi_counter}. φ{phi_counter} := ({condition_ssa})")
                indent_stack.append(f"φ{phi_counter}")
                phi_counter += 1
                continue

            elif " = " in line or ":=" in line:
                var, expr = re.split(r'\s*=\s*|\s*:=\s*', line)
                var = var.strip()
                expr = expr.strip('; ')
                expr_ssa = parse_expr(expr)
                new_var = bump_version(var)
                ssa_lines.append(f"{phi_counter}. {new_var} := {expr_ssa}")
                phi_counter += 1
                continue

            elif line.startswith("else"):
                ssa_lines.append(f"{phi_counter}. else branch for {indent_stack[-1]}")
                phi_counter += 1
                continue

            elif line.startswith("Process("):
                arg = re.search(r'Process\((.*?)\)', line).group(1)
                arg_ssa = parse_expr(arg)
                ssa_lines.append(f"{phi_counter}. Process({arg_ssa})")
                phi_counter += 1
                continue

            elif line.startswith("assert("):
                condition = re.search(r'assert\((.*)\)', line).group(1)
                condition_ssa = parse_expr(condition)
                ssa_lines.append(f"{phi_counter}. assert({condition_ssa})")
                phi_counter += 1
                continue

            else:
                ssa_lines.append(f"// Unrecognized line: {line}")

        self.output_box.delete("1.0", tk.END)
        self.output_box.insert(tk.END, "\n".join(ssa_lines))
        raw_code = self.code_input.get("1.0", tk.END).strip().splitlines()
        ssa_lines = []
        version = {}
        phi_id = 1
        indent_stack = []

        def get_version(var):
            return f"{var}{version.get(var, 0)}"

        def bump_version(var):
            version[var] = version.get(var, 0) + 1
            return f"{var}{version[var]}"

        def add_phi(var1, var2, out_var):
            nonlocal phi_id
            out_version = bump_version(out_var)
            ssa_lines.append(f"{phi_id}. {out_version} := φ({var1}, {var2})")
            phi_id += 1
            return out_version

        indent_level = lambda line: len(line) - len(line.lstrip())

        env_stack = [{}]  # List of var->version mapping for each block level

        def current_env():
            return env_stack[-1]

        for line in raw_code:
            stripped = line.strip()

            # Track block structure
            while indent_stack and indent_stack[-1] >= indent_level(line):
                indent_stack.pop()
                env_stack.pop()

            if re.match(r"\w+\s*:=\s*.+", stripped):
                # Assignment like `x := x + 1`
                lhs, rhs = map(str.strip, stripped.split(":="))
                for var in re.findall(r'\b\w+\b', rhs):
                    if var in version:
                        rhs = re.sub(rf'\b{var}\b', get_version(var), rhs)
                new_version = bump_version(lhs)
                ssa_lines.append(f"{phi_id}. {new_version} := {rhs}")
                current_env()[lhs] = new_version
                phi_id += 1

            elif re.match(r"if\s*\(.+\)\s*{?", stripped):
                condition = re.findall(r"\((.*)\)", stripped)[0]
                for var in re.findall(r'\b\w+\b', condition):
                    if var in version:
                        condition = re.sub(rf'\b{var}\b', get_version(var), condition)
                ssa_lines.append(f"{phi_id}. φ{phi_id} := ({condition})")
                phi_id += 1
                indent_stack.append(indent_level(line))
                env_stack.append(current_env().copy())

            elif re.match(r"while\s*\(.+\)\s*{?", stripped):
                condition = re.findall(r"\((.*)\)", stripped)[0]
                for var in re.findall(r'\b\w+\b', condition):
                    if var in version:
                        condition = re.sub(rf'\b{var}\b', get_version(var), condition)
                ssa_lines.append(f"{phi_id}. φ{phi_id} := ({condition})")
                phi_id += 1
                indent_stack.append(indent_level(line))
                env_stack.append(current_env().copy())

            elif re.match(r"assert\s*\(.+\)", stripped):
                condition = re.findall(r"\((.*)\)", stripped)[0]
                for var in re.findall(r'\b\w+\b', condition):
                    if var in version:
                        condition = re.sub(rf'\b{var}\b', get_version(var), condition)
                ssa_lines.append(f"{phi_id}. assert({condition})")
                phi_id += 1

            elif "}" in stripped:
                # Closing brace — handled by indent logic
                continue

            elif stripped == "":
                ssa_lines.append("")
            else:
                ssa_lines.append(f"// Unrecognized line: {stripped}")

        self.output_box.delete("1.0", tk.END)
        self.output_box.insert(tk.END, "\n".join(ssa_lines))


if __name__ == "__main__":
    root = tk.Tk()
    app = SSAConverter(root)
    root.mainloop()
