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
        i = 0

        def get_var_version(var):
            version.setdefault(var, 0)
            return f"{var}{version[var]}"

        def bump_version(var):
            version.setdefault(var, 0)
            version[var] += 1
            return f"{var}{version[var]}"

        for line in raw_code:
            line = line.strip()

            if not line or line.startswith("//"):
                continue

            if "if" in line and "<" in line:
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = " < ".join([get_var_version(v) for v in vars_in_cond])
                ssa_lines.append(f"{phi_id}. φ{phi_id} := ({cond_expr})")
                phi_id += 1
                continue

            if "==" in line and "if" in line:
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = " == ".join([get_var_version(v) for v in vars_in_cond])
                ssa_lines.append(f"{phi_id}. φ{phi_id} := ({cond_expr})")
                phi_id += 1
                continue

            if "Process(" in line:
                arr_index = re.search(r"\[(.*?)\]", line).group(1)
                arr_index = get_var_version(arr_index)
                ssa_lines.append(f"{phi_id}. if (!φ{phi_id - 1}) Process(data[{arr_index}])")
                phi_id += 1
                continue

            if ":=" in line or "=" in line:
                left, right = re.split(":=|=", line)
                left = left.strip()
                right = right.strip().replace(";", "")
                right_vars = re.findall(r"\b[a-zA-Z_]\w*\b", right)
                new_right = right
                for var in set(right_vars):
                    new_right = re.sub(rf'\b{var}\b', get_var_version(var), new_right)
                new_left = bump_version(left)
                ssa_lines.append(f"{phi_id}. {new_left} := {new_right}")
                phi_id += 1

        self.output_box.delete("1.0", tk.END)
        self.output_box.insert(tk.END, "// initial inputs: i0, next0, data[], cookie0\n\n")
        self.output_box.insert(tk.END, "\n".join(ssa_lines))


if __name__ == "__main__":
    root = tk.Tk()
    app = SSAConverter(root)
    root.mainloop()
