import re

def unroll_loop(code, unroll_count=2, level=0):
    """Recursively unrolls for or while loops by the given count, supporting nested loops."""
    
    # Normalize and preserve indentation
    lines = [line.rstrip() for line in code.strip().split('\n') if line.strip()]
    if not lines:
        raise ValueError("Empty input")
    code = '\n'.join(lines)

    # Check for invalid input (variable declarations)
    first_line = lines[0].strip()
    if re.match(r'^\s*\w+\s*:=\s*\d+\s*;', first_line) or re.match(r'^\s*int\s+\w+\s*=\s*\d+\s*;', first_line):
        raise ValueError("Input should start with a loop, not variable declaration")

    # Parse for or while loop
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

    # Clean components
    init = init.strip()
    condition = condition.strip()
    update = update.strip()
    body = body.strip()

    # Build unrolled version
    indent = '    ' * level
    result = []

    if init:
        result.append(indent + init)

    for i in range(unroll_count):
        result.append(indent + f"if ({condition}) {{")
        inner_indent = '    ' * (level + 1)

        # Handle nested loops in body
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

        # Append inner body
        result.extend(nested_result)

        # Append update for this loop
        if update:
            result.append(inner_indent + update)
        elif code.startswith('while'):
            # For while loops, we need to manually update the condition variable
            cond_var = re.match(r'^\s*(\w+)\s*[<>=]', condition)
            if cond_var:
                var = cond_var.group(1)
                result.append(inner_indent + f"{var} = {var} + 1;")

        result.append(indent + "}")

    return '\n'.join(result)

def main():
    print("Loop Unroller (2 iterations)")
    print("Enter your loop code (press Enter twice when done):")
    # print("Example input:")
    # print("while (i < 2) {")
    # print("    print(i);")
    # print("    i := i + 1;")
    # print("}")

    # Read multi-line input until two consecutive empty lines
    lines = []
    while True:
        try:
            line = input()
            lines.append(line)
            if len(lines) >= 2 and lines[-1] == '' and lines[-2] == '':
                break
        except EOFError:
            break

    # Clean up the input
    code = '\n'.join(lines).strip()
    while '\n\n' in code:
        code = code.replace('\n\n', '\n')

    if not code:
        print("Error: No input provided")
        return

    try:
        unrolled = unroll_loop(code)
        print("\nUnrolled Code:")
        print(unrolled)
    except Exception as e:
        print(f"Error: {str(e)}")

if __name__ == "__main__":
    main()