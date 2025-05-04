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
        unrolled_lines = []  # To store unrolled code before SSA conversion
        version = {}
        phi_id = 1
        stack = []  # Stack to track nested conditions (phi_id, assigned_vars, is_else_branch)
        current_assignments = {}  # Track current version of each variable

        def get_var_version(var):
            if var in {'true', 'false'} or var.isdigit():
                return var
            if var not in version:
                version[var] = 0
                current_assignments[var] = f"{var}_{version[var]}"
            return current_assignments[var]

        def bump_version(var):
            version[var] = version.get(var, 0) + 1
            new_version = f"{var}_{version[var]}"
            current_assignments[var] = new_version
            return new_version

        def process_line(line, output_list):
            nonlocal phi_id
            line = line.strip()
            if not line or line.startswith("//"):
                return

            if re.match(r"(if|else if|while)\s*\(.*\)", line):
                keyword = line.split("(")[0].strip()
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = condition
                for var in set(vars_in_cond):
                    cond_expr = re.sub(rf'\b{var}\b', get_var_version(var), cond_expr)
                output_list.append(f"φ{phi_id} = ({cond_expr})  // {keyword}")
                stack.append((phi_id, {}, False))
                phi_id += 1
                return

            elif line.startswith("else"):
                if stack:
                    prev_phi_id, prev_vars, _ = stack[-1]
                    stack[-1] = (prev_phi_id, prev_vars, True)
                return

            elif line.startswith("assert"):
                condition = re.search(r"\((.*?)\)", line).group(1)
                vars_in_cond = re.findall(r"\b[a-zA-Z_]\w*\b", condition)
                cond_expr = condition
                for var in set(vars_in_cond):
                    cond_expr = re.sub(rf'\b{var}\b', get_var_version(var), cond_expr)
                output_list.append(f"assert({cond_expr})")
                return

            elif "=" in line and ";" in line:
                parts = line.replace(";", "").split("=")
                # if len(parts) != 2:
                #     output_list.append(f"// Skipped unsupported line: {line}")
                #     return
                left, right = map(str.strip, parts)
                right_vars = re.findall(r"\b[a-zA-Z_]\w*\b", right)
                new_right = right
                for var in set(right_vars):
                    new_right = re.sub(rf'\b{var}\b', get_var_version(var), new_right)
                new_left = bump_version(left)
                output_list.append(f"{new_left} := {new_right}")
                if stack:
                    stack[-1][1][left] = new_left
                    
                #Now check
                #what variabe is being assigned to after if or else part runs
                #new SSA= latest if phi? SSA var in if cock: SSA var in else block
            #     e.g
            #     phi1= data[i] == cookie)
            #         i_2 = i_1 + 1;
            #    # else
            #         i_3 = i_1 - 1; 
            #     i_4= phi1? i_2:i_3    
            #After a block of if or else runs, It should check assign a new var value according to what bock of if runs like in tehe xample above 
            #Implement this logic 
            
            if stack:
                cond_phi, assigned_vars, is_else_branch = stack[-1]
                if not is_else_branch:
                    # Update the current assignments for the variables in the "if" block
                    for var, new_version in assigned_vars.items():
                        current_assignments[var] = new_version
                else:
                    # Handle merging of "if" and "else" branches
                    #But only check after both if and else
                    
                    # Check if the current line is the end of the "else" block
                    # if line == "}":
                        # # Merge the assignments from the "if" and "else" branches
                        # for var, new_version in assigned_vars.items():
                        #     if var in current_assignments:
                        #         # If the variable was assigned in both branches, create a phi function
                        #         prev_version_num = version[var] - 1
                        #         prev_version = f"{var}_{prev_version_num}"
                        #         phi_var = bump_version(var)
                        #         if_version = current_assignments[var]
                        #         else_version = new_version
                        #         output_list.append(f"{phi_var} := φ{cond_phi} ? {if_version} : {else_version}")
                        #     else:
                        #         # If the variable was only assigned in the "else" branch, just update it
                        #         current_assignments[var] = new_version
                                    
                    for var, if_version in assigned_vars.items():
                        prev_version_num = version[var] - 1
                        prev_version = f"{var}_{prev_version_num}"
                        phi_var = bump_version(var)
                        
                        
                        # Handle the case where the variable might not have an else version
                        # (like in loops where the else branch might not assign to the variable)
                        if var in current_assignments:
                            else_version = current_assignments[var]
                            # output_list.append(f"{phi_var} := φ{cond_phi} ? {if_version} : {else_version}")
                            # current_assignments[var] = phi_var
                            
                        else:
                            else_version = prev_version
                            
                        output_list.append(f"{phi_var} := φ{cond_phi} ? {if_version} : {else_version}")
                        current_assignments[var] = phi_var
                      
                
                
                return

            elif "(" in line and ")" in line and not line.startswith("if") and not line.startswith("while"):
                func_name = line.split("(")[0].strip()
                args = re.search(r"\((.*?)\)", line).group(1)
                args_vars = re.findall(r"\b[a-zA-Z_]\w*\b", args)
                new_args = args
                for var in set(args_vars):
                    new_args = re.sub(rf'\b{var}\b', get_var_version(var), new_args)
                output_list.append(f"{func_name}({new_args})")
                return

            elif line == "{":
                return

            elif line == "}":
                if stack:
                    cond_phi, assigned_vars, is_else_branch = stack.pop()
                    for var, new_version in assigned_vars.items():
                        if not is_else_branch:
                            current_assignments[var] = new_version
                        else:
                            prev_version_num = version[var] - 1
                            prev_version = f"{var}_{prev_version_num}"
                            phi_var = bump_version(var)
                            if_version = assigned_vars[var]
                            else_version = prev_version
                            output_list.append(f"{phi_var} := φ{cond_phi} ? {if_version} : {else_version}")
                return

            else:
                output_list.append(f"// Skipped unsupported line: {line}")

        i = 0
        while i < len(raw_code):
            line = raw_code[i].strip()

            if line.startswith("for (") and raw_code[i+1].strip() == "{":
                match = re.match(r"for\s*\(\s*(.*?);(.*?);(.*?)\)", line)
                if not match:
                    ssa_lines.append(f"// Could not parse for loop: {line}")
                    i += 1
                    continue

                init_part, cond_part, incr_part = map(str.strip, match.groups())

                # Find the body
                body_start = i + 1
                body_end = body_start
                brace_count = 1
                while body_end < len(raw_code) and brace_count > 0:
                    body_end += 1
                    if "{" in raw_code[body_end]:
                        brace_count += 1
                    if "}" in raw_code[body_end]:
                        brace_count -= 1

                loop_body = raw_code[body_start+1:body_end]

                # Unroll manually (twice)
                unrolled_lines.append("// Original for loop:")
                unrolled_lines.append(line)
                unrolled_lines.append("{")
                if init_part:
                    unrolled_lines.append(f"{init_part};")

                for _ in range(2):  # Unroll twice
                    unrolled_lines.append(f"if ({cond_part}) {{")
                    for stmt in loop_body:
                        unrolled_lines.append(stmt.strip())
                    if incr_part:
                        unrolled_lines.append(f"{incr_part};")
                    unrolled_lines.append("}")

                unrolled_lines.append("}")
                unrolled_lines.append("// End of unrolled for loop")

                for unrolled_line in unrolled_lines[-(len(loop_body)+3)*2:]:
                    process_line(unrolled_line, ssa_lines)

                i = body_end + 1
            else:
                process_line(line, ssa_lines)
                i += 1

        self.output_box.delete("1.0", tk.END)
        self.output_box.insert(tk.END, "// initial inputs: i_0, next_0, data[], cookie_0\n\n")
        self.output_box.insert(tk.END, "// Unrolled code:\n")
        self.output_box.insert(tk.END, "\n".join(unrolled_lines))
        self.output_box.insert(tk.END, "\n\n// SSA form:\n")
        self.output_box.insert(tk.END, "\n".join(ssa_lines))

# Run the GUI
if __name__ == "__main__":
    
    root = tk.Tk()
    app = SSAConverter(root)
    root.mainloop()
