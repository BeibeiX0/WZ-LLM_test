import re
import requests
import json
import time

def convert_lean_to_sage(expr):
    # Find all indices of .choose
    print("ori_lean4: ")
    print(expr)
    expr = expr.replace("↑", "").replace("Nat.", "").replace("^", "**").replace("(-1 : ℝ)", "(-1)").replace("Complex.I", "I")
    # Replace '!' + any amount of whitespace with '!'
    expr = re.sub(r'\s*!', '!', expr)
    expr = re.sub(r'\)\s*!', ')!', expr)
    while "⁻¹" in expr:
        i = expr.find("⁻¹")
        # Check if the character before is a right parenthesis
        if i > 0 and expr[i-1] == ')':
            # Case 1: Expression with parentheses, e.g. (1+2)^(-1)
            j = i - 1  # Start from right parenthesis and search left
            depth = 1
            k = j - 1
            while k >= 0 and depth > 0:
                if expr[k] == ')':
                    depth += 1
                elif expr[k] == '(':
                    depth -= 1
                k -= 1
            if depth != 0:
                break  # Parentheses do not match, skip
            binomial_expr = expr[k+1:i]
            expr = expr[:k+1] + f"1/({binomial_expr})" + expr[i+2:]
        else:
            # Case 2: Number or variable without parentheses, e.g. 2^(-1) or x^(-1)
            # Search left to find the first non-alphanumeric position
            j = i - 1
            while j >= 0 and (expr[j].isalnum() or expr[j] in '.'):
                j -= 1
            # Extract the base expression (from j+1 to i)
            base_expr = expr[j+1:i]
            if base_expr:  # Ensure valid content was extracted
                expr = expr[:j+1] + f"1/({base_expr})" + expr[i+2:]
            else:
                # If no valid content was extracted, skip this occurrence
                expr = expr[:i] + expr[i+2:]
    left_expr = None
    right_expr = None
    while expr.find('.choose') != -1:
        i = expr.find('.choose')
        # If the character left of '.' is ')', traverse left to find the **matching** left parenthesis
        # If the character left of '.' is not ')', traverse left until a space is found
        left_index = -1
        right_index = -1
        if expr[i-1] == ')':
            #Find the matching ')', not just any ')'
            left_index = i - 1
            left_paren_count = 0
            while left_index >= 0:
                if expr[left_index] == ')':
                    left_paren_count += 1
                elif expr[left_index] == '(':
                    left_paren_count -= 1
                if left_paren_count == 0:
                    break
                left_index -= 1
            if left_index >= 0:
                # Replace .choose with binomial
                # print(expr[left_index:i])
                left_expr =  expr[left_index:i]
        else:
            left_index = i - 1
            while left_index > 0 and expr[left_index-1] != ' ' and expr[left_index-1] != ')' and expr[left_index-1] != '(':
                left_index -= 1
            if left_index >= 0:
                # Replace .choose with binomial
                left_expr = expr[left_index:i]
                print("left_expr:", left_expr)
                # print(left_expr)
        # Same approach to find the right side
        if expr[i+8] == '(':
            right_index = i + 8
            right_paren_count = 0
            while right_index < len(expr):
                if expr[right_index] == '(':
                    right_paren_count += 1
                elif expr[right_index] == ')':
                    right_paren_count -= 1
                if right_paren_count == 0:
                    break
                right_index += 1
            # print("right_index:", right_index)
            if right_index <= len(expr):
                # Replace .choose with binomial
                right_expr = expr[i+8:right_index+1]
                # print(right_expr)
        else:
            right_index = i + 8
            while right_index < len(expr)-1 and expr[right_index+1] != ' ' and expr[right_index+1] != ')' and expr[right_index+1] != '(':
                right_index += 1
            if right_index <= len(expr):
                # Replace .choose with binomial
                right_expr = expr[i+8:right_index+1]
                # print(right_expr)
        expr = expr[:left_index] + f'binomial({left_expr.strip()},{right_expr.strip()})' + expr[right_index + 1:]
        # print("Current expression:", expr)
    while expr.find('.descFactorial') != -1:
        i = expr.find('.descFactorial')
        # If the character left of '.' is ')', traverse left to find the **matching** left parenthesis
        # If the character left of '.' is not ')', traverse left until a space is found
        left_index = -1
        right_index = -1
        if expr[i-1] == ')':
            #Find the matching ')', not just any ')'
            left_index = i - 1
            left_paren_count = 0
            while left_index >= 0:
                if expr[left_index] == ')':
                    left_paren_count += 1
                elif expr[left_index] == '(':
                    left_paren_count -= 1
                if left_paren_count == 0:
                    break
                left_index -= 1
            if left_index >= 0:
                # Replace .descFactorial with factorial ratio form
                # print(expr[left_index:i])
                left_expr =  expr[left_index:i]
        else:
            left_index = i - 1
            while left_index > 0 and expr[left_index-1] != ' ' and expr[left_index-1] != ')' and expr[left_index-1] != '(':
                left_index -= 1
            if left_index >= 0:
                # Replace .descFactorial with factorial ratio form
                left_expr = expr[left_index:i]
                # print(left_expr)
        # Same approach to find the right side
        if expr[i+15] == '(':
            right_index = i + 15
            right_paren_count = 0
            while right_index < len(expr):
                if expr[right_index] == '(':
                    right_paren_count += 1
                elif expr[right_index] == ')':
                    right_paren_count -= 1
                if right_paren_count == 0:
                    break
                right_index += 1
            # print("right_index:", right_index)
            if right_index <= len(expr):
                # Replace .descFactorial with factorial ratio form
                right_expr = expr[i+15:right_index+1]
                # print(right_expr)
        else:
            right_index = i + 15
            while right_index < len(expr) -1 and expr[right_index+1] != ' ' and expr[right_index+1] != ')' and expr[right_index+1] != '(' :
                right_index += 1
            if right_index <= len(expr):
                # Replace .descFactorial with factorial ratio form
                right_expr = expr[i+15:right_index+1]
                # print(right_expr)
        # Replace .descFactorial with factorial ratio form
        expr = expr[:left_index] + f'factorial({left_expr.strip()})/(factorial({left_expr.strip()} - {right_expr.strip()}))' + expr[right_index + 1:]
    while expr.find('fib') != -1:
        i = expr.find("fib")
        "only search right side"
        right_index = -1
        # Same approach to find the right side
        if expr[i+4] == '(':
            right_index = i + 4
            right_paren_count = 0
            while right_index < len(expr):
                if expr[right_index] == '(':
                    right_paren_count += 1
                elif expr[right_index] == ')':
                    right_paren_count -= 1
                if right_paren_count == 0:
                    break
                right_index += 1
            print("right_index:", right_index)
            if right_index <= len(expr):
                # Replace .descFactorial with factorial ratio form
                right_expr = expr[i+4:right_index+1]
                # print(right_expr)
        else:
            right_index = i + 4
            while right_index < len(expr) -1 and expr[right_index+1] != ' ' and expr[right_index+1] != ')' and expr[right_index+1] != '(':
                right_index += 1
            if right_index <= len(expr):
                # F_
                right_expr = expr[i+4:right_index+1]
                # print(right_expr)
        # Replace fib with F_
        expr = expr[:i] + f'F_{right_expr.strip()}' + expr[right_index + 1:]
    while expr.find('!') != -1:
        i = expr.find('!')
        if expr[i-1] == ')':
            # Find the matching ), not just any )
            left_index = i - 1
            left_paren_count = 0
            while left_index >= 0:
                if expr[left_index] == ')':
                    left_paren_count += 1
                elif expr[left_index] == '(':
                    left_paren_count -= 1
                if left_paren_count == 0:
                    break
                left_index -= 1
            if left_index >= 0:
                # Replace ! with factorial
                expr = expr[:left_index] + f'factorial({expr[left_index:i]})' + expr[i+1:]
        else:
            left_index = i - 1
            while left_index > 0 and expr[left_index-1] != ' ' and expr[left_index-1] != ')' and expr[left_index-1] != '(' and expr[left_index-1] != '+' and expr[left_index-1] != '-' and expr[left_index-1] != '*' and expr[left_index-1] != '/' and expr[left_index-1] != '^':
                left_index -= 1
            if left_index >= 0:
                # Replace ! with factorial
                expr = expr[:left_index] + f'factorial({expr[left_index:i]})' + expr[i+1:]
    print("converted_math: ")
    print(expr)
    return expr

def convert_sage_to_lean(expr):
    """
    Convert sage-style mathematical expressions to Lean format:
    - binomial(a, b) → (a.choose b)
    - binomial(a + b, c) → ((a + b).choose c)
    - Preserves original parentheses structure
    - Handles nested expressions and complex arguments
    """
    expr = expr.replace("**", "^")
    if expr.find("binomial") == -1:
        return expr
    expr = expr.replace("↑", "")
    expr = re.sub(fr'\bI\b', f'Complex.I', expr)
    
    # Record original outer parentheses status
    original_has_outer_parens = expr.startswith('(') and expr.endswith(')')
    
    # Pattern to match binomial expressions
    pattern = r'binomial\s*\((.*?),\s*(.*?)\)'
    
    def replacer(match):
        base = match.group(1).strip()
        top = match.group(2).strip()
        
        # Recursively convert any nested binomial expressions
        base = convert_sage_to_lean(base)
        top = convert_sage_to_lean(top)
        
        return f'(({base}).choose ({top}))'
    
    # We need to handle nested binomials by repeatedly applying the substitution
    # until no more changes occur
    old_expr = None
    converted = expr
    while converted != old_expr:
        old_expr = converted
        converted = re.sub(pattern, replacer, converted)
    
    # Restore original outer parentheses if needed
    if original_has_outer_parens:
        if not (converted.startswith('(') and converted.endswith(')')):
            converted = f'({converted})'
    
    return converted.strip()
# print("Converted Lean expression:")
# print(convert_lean_to_sage("n+1    ! + binomial(4, 1)"))