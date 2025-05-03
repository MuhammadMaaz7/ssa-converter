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

            # Handle if, else if, or while
            if re.match(r"(if|else if|while)\s*\(.*\)", line):
                keyword = line.split("(")[0].strip()
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = condition
                for var in set(vars_in_cond):
                    cond_expr = re.sub(rf'\b{var}\b', get_var_version(var), cond_expr)
                ssa_lines.append(f"φ{phi_id} = ({cond_expr})  // {keyword}")
                stack.append((phi_id, []))
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
                # Ensure it's a simple one-line assignment
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
                    stack[-1][1].append(left)
                continue

            # Handle end of block
            elif line == "}":
                if stack:
                    cond_phi, assigned_vars = stack.pop()
                    for var in assigned_vars:
                        new_ver = get_var_version(var)
                        old_ver = f"{var}_{version[var] - 1}"
                        merged = bump_version(var)
                        ssa_lines.append(f"{merged} := φ{cond_phi} ? {new_ver} : {old_ver}")
                continue

            # Skip any other unsupported line
            else:
                ssa_lines.append(f"// Skipped unsupported line: {line}")

        self.output_box.delete("1.0", tk.END)
        self.output_box.insert(tk.END, "// initial inputs: i_0, next_0, data[], cookie_0\n\n")
        self.output_box.insert(tk.END, "\n".join(ssa_lines))


if __name__ == "__main__":
    root = tk.Tk()
    app = SSAConverter(root)
    root.mainloop()
