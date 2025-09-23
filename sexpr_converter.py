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

def convert_sexpr(sexpr_str, mode=True):
    parsed, pos = parse_sexpr(sexpr_str, 0)
    # Skip trailing whitespace
    while pos < len(sexpr_str) and sexpr_str[pos].isspace():
        pos += 1
    if pos < len(sexpr_str):
        raise ValueError("Extra characters after S-expression")
    
    var_to_index = {}
    next_index = [1]
    
    def format_with_state(node):
        if node[0] == 'atom':
            atom = node[1]
            if atom.startswith('$') and len(atom) > 1:
                varname = atom
                if varname not in var_to_index:
                    var_to_index[varname] = next_index[0]
                    next_index[0] += 1
                    if mode:
                        return '$'
                    else:
                        return f'_{var_to_index[varname]}'
                else:
                    return f'_{var_to_index[varname]}'
            else:
                return atom
        else:  # list
            children = []
            for child in node[1]:
                child_str = format_with_state(child)
                children.append(child_str)
            inner = ' '.join(children)
            return f'[{len(node[1])}] {inner}'
    
    return format_with_state(parsed)

if __name__ == '__main__':
    test_input = "(ev $a $b $a)"
    print(convert_sexpr(test_input, True))
    print(convert_sexpr(test_input, False))
    print(convert_sexpr("(: $prf F $tv)", True))
