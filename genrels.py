def generate_expressions():
    # Define the range of values: 0, 0.1, 0.2, ..., 1.0
    values = [round(i * 0.1, 1) for i in range(11)]
    functions = ['mul', 'div', 'min', 'max']
    results = []
    
    for func in functions:
        for a in values:
            for b in values:
                if func == 'mul':
                    result = round(a * b, 1)
                elif func == 'div':
                    # Avoid division by zero
                    if b == 0:
                        continue
                    result = round(a / b, 1)
                elif func == 'min':
                    result = min(a, b)
                elif func == 'max':
                    result = max(a, b)
                
                # Only include results that are in the valid range
                if result in values:
                    results.append(f"({func} ({a} {b}) {result})")
    
    # Write to file
    with open('mathrels.mm2', 'w') as f:
        for expr in results:
            f.write(expr + '\n')

if __name__ == "__main__":
    generate_expressions()
