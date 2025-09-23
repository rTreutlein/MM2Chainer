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

def convert_sexpr(sexpr):
    parsed , pos = parse_sexpr(sexpr, 0)
    return format_sexpr(parsed)

if __name__ == '__main__':
    print(convert_sexpr("(: $prf F $tv)"))
