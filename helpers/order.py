def parse_sexpr(s):
    """
    Parse an S-expression string into a nested Python list.
    Example: "((A $a) (B $b) (R $a $x $c))" -> [["A", "$a"], ["B", "$b"], ["R", "$a", "$x", "$c"]]
    """
    def tokenize(s):
        s = s.strip()
        if not s:
            raise ValueError("Empty S-expression")
        s = s.replace('(', ' ( ').replace(')', ' ) ')
        return s.split()

    def parse_tokens(tokens, index=0):
        if index >= len(tokens):
            raise ValueError("Unexpected end of input")
        
        result = []
        i = index
        while i < len(tokens):
            token = tokens[i]
            if token == '(':
                sublist, new_index = parse_tokens(tokens, i + 1)
                if sublist is not None:
                    result.append(sublist)
                i = new_index
            elif token == ')':
                return result, i  # Fixed to return i
            else:
                result.append(token)
            i += 1
        if index == 0 and result:
            return result, i
        raise ValueError("Missing closing parenthesis")

    tokens = tokenize(s)
    result, index = parse_tokens(tokens)
    if index != len(tokens):
        raise ValueError("Incomplete parse: extra tokens")
    return result

def print_sexpr(obj):
    """
    Convert a nested Python list back to an S-expression string.
    Example: [[["A", "$a"], ["B", "$b"]], [[["R", "$a", "$x", "$c"]], []]]
             -> "(((A $a) (B $b)) ((R $a $x $c)) ())"
    """
    if obj == []:
        return "()"
    if isinstance(obj, str):
        return obj
    if isinstance(obj, list) and all(isinstance(x, str) for x in obj):
        return "(" + " ".join(obj) + ")"
    return "(" + " ".join(print_sexpr(x) for x in obj) + ")"

def is_variable(s):
    return isinstance(s, str) and len(s) > 0 and s[0] == '$'

def get_vars(item):
    """
    Recursively get all variables from an item or sublist.
    """
    if isinstance(item, str):
        return [item] if is_variable(item) else []
    elif isinstance(item, list):
        return sum((get_vars(sub) for sub in item), [])
    return []

def disjoint(new_vars, covered):
    return not any(v in covered for v in new_vars)

def all_vars(items):
    return sum((get_vars(item) for item in items), [])

def build_structure(items):
    # Sort items by number of variables (ascending) to prioritize simpler items
    sorted_items = sorted(items, key=lambda x: len(get_vars(x)))
    
    def construct_levels(remaining, known):
        result = []
        while remaining:
            level = []
            covered = []
            # Use a copy to avoid modifying during iteration
            for item in remaining[:]:
                vars_ = get_vars(item)
                new_vars = [v for v in vars_ if v not in known]
                add = False
                if item[0] == 'CPU':
                    # Assume structure: ['CPU', fun, args, res] where args may be list
                    if len(item) == 4:
                        input_vars = get_vars(item[2])
                        input_new = [v for v in input_vars if v not in known]
                        if not input_new:  # All inputs known
                            output_vars = get_vars(item[3])
                            new_vars = [v for v in output_vars if v not in known]
                            if disjoint(new_vars, covered):
                                add = True
                else:  # Non-CPU items (e.g., proofs starting with ':')
                    if disjoint(new_vars, covered):
                        add = True
                if add:
                    level.append(item)
                    covered.extend(new_vars)
            # Remove added items from remaining
            remaining = [x for x in remaining if x not in level]
            if not level:
                break
            result.append(level)
            known.extend(all_vars(level))
        result.append([])
        return result
    
    return construct_levels(sorted_items, [])

def process_sexpr(sexpr):
    """
    Parse an S-expression, process it with build_structure, and return both the
    processed structure and its S-expression string representation.
    """
    try:
        parsed = parse_sexpr(sexpr)
        result = build_structure(parsed)
        return result, print_sexpr(result)
    except Exception as e:
        raise ValueError(f"Error processing S-expression: {e}")

if __name__ == '__main__':
    handler = MettalogHandler()

    out = handler._send_command("!(mcompile (: rule (Implication (And (A $a) (B $b)) (R $a $b)) (STV 1.0 1.0)))")
    outlst =  [item.strip() for item in out[1:-1].split(',') if item.strip()]

    for elem in outlst:
        print("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
        print(elem)
        pyexpr = parse_sexpr(elem)[0]
        structure = build_structure(pyexpr[0])
        pyexpr[0] = structure
        print(print_sexpr(pyexpr))
