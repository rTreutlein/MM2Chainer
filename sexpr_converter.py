import sys

def parse_sexpr(s, pos):
    # Skip whitespace
    while pos < len(s) and s[pos].isspace():
        pos += 1
    
    if pos >= len(s):
        raise ValueError("Unexpected end of input")
    
    if s[pos] == '(':
        pos += 1
        elements = []
        while True:
            # Skip whitespace
            while pos < len(s) and s[pos].isspace():
                pos += 1
            if pos >= len(s):
                raise ValueError("Unexpected end of input")
            if s[pos] == ')':
                pos += 1
                break
            elem, pos = parse_sexpr(s, pos)
            elements.append(elem)
        return ('list', elements), pos
    elif s[pos] == ')':
        raise ValueError("Unexpected closing parenthesis")
    else:
        # Parse atom
        start = pos
        while pos < len(s) and not s[pos].isspace() and s[pos] not in '()':
            pos += 1
        atom = s[start:pos]
        if not atom:
            raise ValueError("Empty atom")
        return ('atom', atom), pos

def format_sexpr(sexpr):
    if sexpr[0] == 'atom':
        return sexpr[1]
    else:
        children = []
        for e in sexpr[1]:
            child_str = format_sexpr(e)
            children.append(child_str)
        inner = ' '.join(children)
        return f'[{len(sexpr[1])}] {inner}'

def main():
    input_str = sys.stdin.read().strip()
    if not input_str:
        print("No input provided", file=sys.stderr)
        sys.exit(1)
    
    try:
        sexpr, final_pos = parse_sexpr(input_str, 0)
        # Check for trailing garbage
        while final_pos < len(input_str) and input_str[final_pos].isspace():
            final_pos += 1
        if final_pos < len(input_str):
            raise ValueError("Extra characters after S-expression")
        
        output = format_sexpr(sexpr)
        print(output)
    except ValueError as e:
        print(f"Error parsing S-expression: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()
