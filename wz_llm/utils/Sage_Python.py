from sage.all import *
from sage.symbolic.ring import SR as SymbolicRing
import operator
import re
from utils.lean2sage import convert_sage_to_lean, convert_lean_to_sage
from utils.Maple import reverse_outer_signs_and_remove_mulone, convert_negative_parentheses
def simplify_binomial(expr):
    """
    Simplify binomial expressions, keeping fraction form without expanding the denominator
    """
    if expr in ZZ or expr in QQ:
        return expr
    try:
        # First try simplifying without expanding
        simplified = expr.simplify_factorial().simplify()
        if "binomial" not in str(simplified):
            # Key step to keep the factored form
            from sage.misc.functional import numerator, denominator
            num = numerator(simplified)
            den = denominator(simplified)
            # Ensure the denominator stays in factored form
            num = num.factor()
            den = den.factor()
            return num/den
    except:
        pass
    
    # Recursively process binomial expressions
    if expr.operator() is binomial:
        n, k = expr.operands()
        if (n - k == 1):
            return n
        elif (k == 0) or (k == n):
            return 1
        elif (k == 1) or (k == n-1):
            return n
        else:
            return binomial(n, k).simplify_full()
    
    # Recursively process other operators
    elif expr.operator() is not None:
        simplified_ops = [simplify_binomial(op) for op in expr.operands()]
        result = expr.operator()(*simplified_ops)
        # Keep the final result in factored form
        from sage.misc.functional import numerator, denominator
        num = numerator(result).factor()
        den = denominator(result).factor()
        if str(den) == '1':
            return num
        return num / den
    
    return expr

# # Test cases
# n,k = var('n k')
# expr1 = 1/(n)**2
# expr2 = (-1)**(k+1) / (-1)**k
# expr3 = binomial(n, k+1)**2 / binomial(n, k)**2

# # Display results (keeping the ideal fraction form)
# simplify_binomial(expr1)  # Output: 1/(n + 1)**2
# simplify_binomial(expr2)  # Output: -1
# simplify_binomial(expr3)  # Output: binomial(n, k + 1
def get_all_variables(sage_exp):
    """
    Variable extraction function fully isolated from the R environment

    Args:
        sage_exp: string or Sage symbolic expression

    Returns:
        A string containing all variable names (space-separated)
    """
    # Create a clean symbolic computation environment
    sr = SymbolicRing()
    
    # Base variable set (guaranteed to contain at least these variables)
    safe_vars = {'a', 'a1'}
    
    try:
        # Handle string input
        if isinstance(sage_exp, str):
            # Method 1: Extract variables directly using regex (completely bypasses Sage parsing)
            import re
            pattern = r'\b[a-zA-Z][a-zA-Z0-9]*\b'
            found_vars = set(re.findall(pattern, sage_exp))
            
            # Filter out function names, constants, Python keywords, and Lean keywords
            import keyword as _keyword
            math_keywords = {'binomial', 'sqrt', 'exp', 'log', 'sin', 'cos', 'pi', 'I', 'factorial', '!'}
            python_keywords = set(_keyword.kwlist)
            lean_keywords = {'then', 'theorem', 'def', 'have', 'show', 'fun', 'let', 'by', 'do', 'where', 'with', 'match', 'open', 'import', 'Even', 'Odd', 'Real', 'Nat', 'Int', 'Finset', 'List'}
            variables = found_vars - math_keywords - python_keywords - lean_keywords
            variables.update(safe_vars)
            
            return " ".join(sorted(variables))
        
        # Handle existing expression objects
        elif hasattr(sage_exp, 'variables'):
            try:
                # Use an absolutely safe variable extraction method
                variables = {str(v) for v in sage_exp.variables() 
                            if not str(v).startswith('_')}
                variables.update(safe_vars)
                return " ".join(sorted(variables))
            except:
                return " ".join(safe_vars)
        
        return " ".join(safe_vars)
        
    except Exception as e:
        print(f"Safety warning (isolated): {str(e)}")
        return " ".join(safe_vars)
# def get_all_variables(sage_exp):
#     """Extract all variables from a Sage expression"""
#     print("Extracting variables from Sage expression:", sage_exp)
#     expr = sage_exp
#     try:
#         expr = symbolic_expression(expr)
#     except Exception as e:
#         print(f"Error converting to symbolic expression: {e}")
#         return []
#     variables = list(expr.variables())
#     variables = [str(var) for var in variables]
#     print("Extracted variables:", variables)
#     if 'a' not in variables:
#         variables += ['a']
#     if 'a1' not in variables:
#         variables += ['a1']
#     print("Final variables list:", variables)
#     return " ".join([str(var) for var in variables])
def mapping_before(sage_exp, variable):
    sage_exp = re.sub(rf'\ba\b', f'a1', sage_exp)
    sage_exp = re.sub(rf'\b{variable}\b', f'a', sage_exp)
    return sage_exp
def mapping_after(sage_exp, variable):
    sage_exp = re.sub(rf'\ba\b', f'{variable}', sage_exp)
    sage_exp = re.sub(rf'\ba1\b', f'a', sage_exp)
    return sage_exp
def calculate_ratio_sage(Ank, Bn, max_retries=3, origin_variablen='n', origin_variablek='k', num1_int=1, num2_int=0):
    """Calculate ratios A(n,k+1)/A(n,k), A(n+1,k)/A(n,k), B(n+1)/B(n), A(n+1,n+1)/A(n,n), A(n+1,n)/A(n,n)"""
    print(f"Calculating ratio: {Ank}, {Bn} (vars: {origin_variablen},{origin_variablek})")
    Ank = mapping_before(Ank, origin_variablen)
    Bn = mapping_before(Bn, origin_variablen)
    print("Preprocessed expressions:", Ank, Bn)
    try:
        # all_variales = get_all_variables(Ank+Bn)
        all_variables = get_all_variables(Ank + '+' + Bn)
        if origin_variablek=='a':
            variablek = 'a1'
        else:
            variablek = origin_variablek
        if origin_variablen=='a':
            variablen = 'a1'
        else:
            variablen = 'a'
        print("vk:",variablek)

        # 1. Define symbolic variables
        n = var(variablen)
        k = var(variablek)
        print("Defined variables:", n, k)
        all_var = var(all_variables)
        print("Defined variables:", all_var)
        # n, k are just temporary variables
        # 2. Parse input expressions directly
        # Other variables besides n and k must also be added to locals
        A_expr = sage_eval(Ank, locals={variablen: n, variablek: k, **{str(var): var for var in all_var if str(var)!=variablen and str(var)!=variablek}})
        print("A_expr:", A_expr)
        B_expr = sage_eval(Bn, locals={variablen: n, **{str(var): var for var in all_var if str(var)!=variablen}})
        
        # 3. Calculate ratios (directly operating on expressions)
        # A(n,k+1)/A(n,k)
        ratio1 = A_expr.subs({k: k+1}) / A_expr
        print("ratio1:")
        print(ratio1)
        print(f"A({variablen},{variablek}+1)/A({variablen},{variablek}) =")
        ratio = str(simplify_binomial(ratio1))
        
        # A(n+1,k)/A(n,k)
        ratio2 = A_expr.subs({n: n+1}) / A_expr
        print(f"A({variablen}+1,{variablek})/A({variablen},{variablek}) =")
        ratio2 = str(simplify_binomial(ratio2))

        if Bn!='0':
            # B(n+1)/B(n)
            ratio3 = B_expr.subs({n: n+1}) / B_expr
            print(f"B({variablen}+1)/B({variablen}) =")
            ratio3 = str(simplify_binomial(ratio3))
        else: ratio3='0'

        ratio4 = A_expr.subs({n: n+1, k: n+num1_int}) / A_expr.subs({k: n+num2_int})
        print(f"A({variablen}+1,{variablen}{num1_int})/A({variablen},{variablen}{num2_int}) =")
        ratio4 = str(simplify_binomial(ratio4))

        ratio5 = A_expr.subs({n: n+1, k: n+num2_int}) / A_expr.subs({k: n+num2_int})
        print(f"A({variablen}+1,{variablen}{num2_int})/A({variablen},{variablen}{num2_int}) =")
        ratio5 = str(simplify_binomial(ratio5))

        
    except Exception as e:
        print(f"Error: {str(e)}")
        if max_retries > 0:
            return calculate_ratio_sage(Ank, Bn, max_retries-1, variablen, variablek)
        raise
    return mapping_after(ratio, origin_variablen), mapping_after(ratio2, origin_variablen), mapping_after(ratio3, origin_variablen), mapping_after(ratio4, origin_variablen), mapping_after(ratio5, origin_variablen)
def calculate_cert_sage(Ank, Bn, origin_variablen='n', origin_variablek='k'):
    """Calculate the WZ certificate"""
    print("Calculating WZ certificate with Sage:", Ank, Bn)
    Ank = mapping_before(Ank, origin_variablen)
    Bn = mapping_before(Bn, origin_variablen)
    try:
        all_variables = get_all_variables(Ank + '+' + Bn)
    except Exception as e:
        print(f"Error getting variables: {str(e)}")
    print("All variables:", all_variables)
    if origin_variablek=='a':
        variablek = 'a1'
    else:
        variablek = origin_variablek
    if origin_variablen=='a':
        variablen = 'a1'
    else:
        variablen = 'a'
    n = var(variablen)
    k = var(variablek)
    all_var = var(all_variables)
    F_expr = sage_eval('(' + Ank + ') / (' + Bn + ')', locals={variablen: n, variablek: k, **{str(var): var for var in all_var if str(var)!=variablen and str(var)!=variablek}})
    print("F_expr:", F_expr)
    print(n, k)
    # Calculate the WZ certificate
    c = F_expr.WZ_certificate(n, k)
    c = mapping_after(str(c), origin_variablen)
    print("WZ certificate:", c)
    return c
def get_recursive_goals_sage(exp_sage, exp_lean, variable, origin_variablen='n', origin_variablek='k'):
    print('get_recursive_goals:', exp_sage, exp_lean, variable)
    if exp_lean.find(f'{variable}') == -1:
        return None
    if exp_lean.find('choose') == -1 and exp_lean.find('^') == -1 and exp_lean.find('fib') == -1 and exp_lean.find('catalan') == -1 and exp_lean.find('!') == -1 and exp_lean.find('descFactorial') == -1:
        return None
    print("Exp before processing:", exp_sage, exp_lean)
    # exp_lean = exp_lean.replace('⁻¹', '')
    original_exp = re.sub(rf'\b{variable}\b', f'({variable} + 1)', exp_lean)
    exp_sage = mapping_before(exp_sage, origin_variablen)
    all_variables = get_all_variables(exp_sage)
    print("All variables:", all_variables)
    if origin_variablek=='a':
        variablek = 'a1'
    else:
        variablek = origin_variablek
    if origin_variablen=='a':
        variablen = 'a1'
    else:
        variablen = 'a'
    try:
        n = var(variablen)
        k = var(variablek)
        all_var = var(all_variables)
    except Exception as e:
        print(f"Error defining variables: {str(e)}")
        return None
    try:
        F_expr = sage_eval(exp_sage, locals={variablen: n, variablek: k, **{str(var): var for var in all_var if str(var)!=variablen and str(var)!=variablek}}) 
    except Exception as e:
        print(f"Error evaluating expression: {str(e)}")
        return None
    try:
        # If variablen can be found
        if  variable!=origin_variablen:
            print("F_expr:", F_expr)
            # Calculate the recursive relation
            ratio = str(simplify_binomial((F_expr.subs({k: k+1}) / F_expr)))

        else:
            ratio = str(simplify_binomial((F_expr.subs({n: n+1}) / F_expr)))
    except Exception as e:
        print(f"Error calculating ratio: {str(e)}")
        return None
    ratio = mapping_after(ratio, origin_variablen)
    print("Ratio:", ratio)
    ratio = convert_sage_to_lean(ratio)
    ratio = convert_negative_parentheses(ratio)
    ratio = reverse_outer_signs_and_remove_mulone(ratio, True)
    if ratio.startswith('/'):
        return f"{original_exp} = ({exp_lean}) {ratio}"
    return f"{original_exp} = ({exp_lean}) * ({ratio})"
def get_recursive_goals_calc_sage(exp, exp_lean, origin_variablen='n', origin_variablek='k', num1=' + 1', num2='', num3=' + 1', num4=' + 1'):
    """Calculate recursive goals"""
    print('get_recursive_goals_calc:', exp, exp_lean, origin_variablen)
    # exp = exp.replace('⁻¹', '')
    if exp.find(origin_variablen) == -1 and exp.find(origin_variablek) == -1:
        return None
    if exp_lean.find('choose') == -1 and exp_lean.find('^') == -1 and exp_lean.find('fib') == -1 and exp_lean.find('catalan') == -1 and exp_lean.find('!') == -1 and exp.find('descFactorial') == -1:
        return None
    original_base_exp = re.sub(fr'\b{origin_variablen}\b', f'({origin_variablen}{num4})', exp_lean)
    original_base_exp = re.sub(fr'\b{origin_variablek}\b', f'({origin_variablen}{num2})', original_base_exp)
    
    original_exp = re.sub(fr'\b{origin_variablen}\b', f'({origin_variablen}{num3})', exp_lean)
    original_exp = re.sub(fr'\b{origin_variablek}\b', f'({origin_variablen}{num1})', original_exp)
    exp = mapping_before(exp, origin_variablen)
    all_variables = get_all_variables(exp)
    if origin_variablek=='a':
        variablek = 'a1'
    else:
        variablek = origin_variablek
    if origin_variablen=='a':
        variablen = 'a1'
    else:
        variablen = 'a'
    n = var(variablen)
    k = var(variablek)
    all_var = var(all_variables)
    F_expr = sage_eval(exp, locals={variablen: n, variablek: k, **{str(var): var for var in all_var if str(var)!=variablen and str(var)!=variablek}})
    print("F_expr:", F_expr)
    if num1.strip() == '':
        num1_int = 0
    else:
        num1_int = int(num1.replace('+', '').replace(' ', ''))
    if num2.strip() == '':
        num2_int = 0
    else:
        num2_int = int(num2.replace('+', '').replace(' ', ''))
    if num3.strip() == '': 
        num3_int = 0
    else:
        num3_int = int(num3.replace('+', '').replace(' ', ''))
    if num4.strip() == '':
        num4_int = 0
    else:
        num4_int = int(num4.replace('+', '').replace(' ', ''))
    print(F_expr.subs({n: n+1, k: n+num1_int}) / F_expr.subs({n: n+1, k: n+num2_int}))
    ratio = str(simplify_binomial((F_expr.subs({n: n+num3_int, k: n+num1_int}) / F_expr.subs({n: n+num4_int, k: n+num2_int}))))
    ratio = mapping_after(ratio, origin_variablen)
    print("Ratio:", ratio)
    ratio = convert_sage_to_lean(ratio)
    ratio = convert_negative_parentheses(ratio)
    ratio = reverse_outer_signs_and_remove_mulone(ratio, True)
    if ratio.startswith('/'):
        return f"{original_exp} = ({original_base_exp}) {ratio}"
    
    return f"{original_exp} = ({original_base_exp}) * ({ratio})"
def get_eq_zero_primise(exp, origin_variablen='n', origin_variablek='k', variable='n'):
    """Calculate the conditions under which the expression equals zero"""
    print('get_eq_zero_primise:', exp, origin_variablen, origin_variablek)
    try:
        all_variables = get_all_variables(exp)
        n = var(origin_variablen)
        k = var(origin_variablek)
        all_var = var(all_variables)
        F_expr = sage_eval(exp, locals={**{str(var): var for var in all_var}})
        print("F_expr:", F_expr)
    except Exception as e:
        print(f"Error evaluating expression in get_eq_zero_primise: {str(e)}")
        return ""
    try:
        # Calculate the values of n for which F_expr equals zero
        assume(n, 'integer')
        assume(k, 'integer')   
        assume(n >= 0)
        assume(k >= 0)  
        if variable == origin_variablen:
            zero_conditions = solve(F_expr == 0, n)
        else:
            zero_conditions = solve(F_expr == 0, k)
        print("Zero conditions:", zero_conditions)
        print("Type of zero_conditions:", type(zero_conditions))
        zero_conditions = str(zero_conditions)
        if zero_conditions == '[]':
            return ""
        if zero_conditions.startswith('[') and zero_conditions.endswith(']'):
            primise = '^'.join([cond.replace("==", "=") for cond in zero_conditions[1:-1].split(',')]).strip()
        else: primise = '^'.join([f"{variable} = {cond}" for cond in zero_conditions.split(",") if cond.strip()]).strip()
        print("Primise:", primise)
        return primise
    except Exception as e:
        print(f"Error determining zero conditions: {str(e)}")
        return ""

def get_choose_primises(expr, varn, vark, eq=False):
    # Given an expression, output when this expression equals zero
    choose_var_pair = []
    while expr.find('.choose') != -1:
        i = expr.find('.choose')
        # If the character to the left of '.' is ')', traverse left to find the **matching** left parenthesis
        # If the character to the left of '.' is not ')', traverse left until a space is found
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
        # Same approach for the right side
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
        choose_var_pair.append((left_expr.strip(), right_expr.strip()))
    pri_list = []
    for pair in choose_var_pair:
        print("pair:", pair)
        if eq:
            exp = f"{pair[0]} <= {pair[1]}"
        else: exp = f"{pair[0]} < {pair[1]}"
        try :
            all_variables = get_all_variables(exp)
            if vark not in all_variables:
                all_variables += ' ' + vark
            print("all_variables:", all_variables)
            n = var(varn)
            k = var(vark)
            assume(n>=0)
            assume(k>=0)
            all_var = var(all_variables)
            F_expr = sage_eval(exp, locals={**{str(var): var for var in all_var}})
            # n_dayu0 = sage_eval(f"{varn} >= 0", locals={**{str(var): var for var in all_var}})
            # n_dayuk = sage_eval(f"{varn} > {vark}", locals={**{str(var): var for var in all_var}})
            # Cannot introduce extra conditions, would produce redundant conditions
            
            pri = solve([F_expr], [n, k])
            print("pri:", pri)
            if str(pri).replace(" ", "").replace("\n", "") == '[]':
                continue
            print("pri:", pri)
            print(str(pri).replace(" ", ""))
            for ii in pri:
                for i in ii:
                    print("single",i)
                    if re.search(rf'\b{vark}\b', str(i)):
                        continue
                    else:
                        print("pri:", i)
                        pri_list.append(str(i).replace("==","="))
        except Exception as e:
            print(f"Error determining choose primise: {str(e)}")
            continue
    return pri_list
def get_gosper_g(f_expr, variablek):
    """Calculate Gosper's G(k)"""
    f_expr = convert_lean_to_sage(f_expr)
    print('get_gosper_g:', f_expr, variablek)
    all_variables = get_all_variables(f_expr)
    print("All variables:", all_variables)
    if variablek=='a':
        variablek_sage = 'a1'
    else:
        variablek_sage = variablek
    try:
        k = var(variablek_sage)
        all_var = var(all_variables)
    except Exception as e:
        print(f"Error defining variables: {str(e)}")
        return None
    try:
        F_expr = sage_eval(f_expr, locals={variablek_sage: k, **{str(var): var for var in all_var if str(var)!=variablek_sage}})
    except Exception as e:
        print(f"Error evaluating expression: {str(e)}")
        return None
    try:
        G_expr = F_expr.gosper_sum(k)
        G_expr = str(G_expr)
    except Exception as e:
        print(f"Error calculating Gosper G(k): {str(e)}")
        return None
    print("Gosper G(k):", G_expr)
    return convert_sage_to_lean(G_expr)
# get_gosper_g("binomial(d,m)", "d")
# calculate_cert_sage("binomial(g,o)", "2**g", origin_variablen='g', origin_variablek='o')
# # Test cases
# calculate_ratio_sage("binomial(a,k)**2", "2**a", origin_variablen='a', origin_variablek='k')
# calculate_ratio_sage("binomial(w,o)", "2^w", origin_variablen='w', origin_variablek='o')
# calculate_ratio_sage("factorial(m)^3/factorial(p)", "m^2", origin_variablen='m', origin_variablek='p')
# r = get_recursive_goals_sage("binomial(a,k)", "choose a k", 'a', origin_variablen='a', origin_variablek='k')
# print("Recursive goals result:", r)
# r = get_recursive_goals_calc_sage("binomial(a,k)", "choose a k", origin_variablen='a', origin_variablek='k', num1=' + 1', num2='- 2')
# print("Recursive goals calc result:", r)