import re
import requests
import json
import time
def convert_lean_to_math(expr):
    """
    Convert Lean-style mathematical expressions to conventional format:
    - (a.choose b) → binomial(a, b)
    - ((a).choose b) → binomial(a, b)
    - (a + b).choose c → binomial(a + b, c)
    - Preserves original parentheses structure
    - Removes type annotations like : ℝ
    """
    expr = expr.replace("↑", "")
    # Remove type annotations
    expr = re.sub(r'\s*:\s*\w+', '', expr)
    
    # Record original outer parentheses status
    original_has_outer_parens = expr.startswith('(') and expr.endswith(')')
    
    # Pattern to match choose expressions with proper parenthesis handling
    pattern = r'(\()?(\()?(.*?)\.choose\s+(\w+)(\))?(\))?'
    
    def replacer(match):
        left_paren1 = match.group(1) or ''
        left_paren2 = match.group(2) or ''
        base = match.group(3).strip()
        top = match.group(4).strip()
        right_paren1 = match.group(5) or ''
        right_paren2 = match.group(6) or ''
        
        # Preserve original parentheses only if they were part of the choose expression
        new_left = left_paren1 + left_paren2
        new_right = right_paren1 + right_paren2
        
        # Convert choose to binomial
        binomial_expr = f'binomial({base}, {top})'
        
        return f'{new_left}{binomial_expr}{new_right}'
    
    # Perform substitution
    converted = re.sub(pattern, replacer, expr)
    
    # Remove redundant parentheses pairs caused by conversion
    converted = re.sub(r'\(binomial', 'binomial', converted)
    converted = re.sub(r'\)', '', converted, count=converted.count(')') - converted.count('('))
    
    # Restore original outer parentheses if needed
    if original_has_outer_parens:
        if not (converted.startswith('(') and converted.endswith(')')):
            converted = f'({converted})'
    
    return converted.replace(":","").replace("ℝ", "").replace("↑", "").strip()
def convert_lean_to_math_test(expr):
    # Find all indices of .choose
    print("ori_lean4: ")
    print(expr)
    expr = expr.replace("↑", "").replace("Nat.", "")
    while "⁻¹" in expr:
        i = expr.find("⁻¹")
        # Find the corresponding left parenthesis for the right parenthesis
        j = i - 1
        while j >= 0 and expr[j] != ')':
            j -= 1
        if j < 0:
            break  # No matching right parenthesis, skip
        # Now find the matching left parenthesis
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
        expr = expr[:left_index] + f'({left_expr.strip()}!)/(({left_expr.strip()} - {right_expr.strip()})!)' + expr[right_index + 1:]
    while expr.find('fib') != -1:
        i = expr.find("fib")
        "Only search the right side"
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
    print("converted_math: ")
    print(expr)
    return expr
def convert_maple_to_lean_api(expr):
    def extract_lean4_code(response_json):
        try:
            data = json.loads(response_json)
            content = data["choices"][0]["message"]["content"]
            content = content.replace("```lean4", "").replace("```", "").strip()
            return content
        except (json.JSONDecodeError, KeyError, IndexError) as e:
            print(f"Error parsing response: {e}")
            return None
    url = "https://qianfan.baidubce.com/v2/chat/completions"
    payload = json.dumps({
        "model": "deepseek-r1-250528",
        "messages": [
            {
                "role": "user",
                "content": f"{expr}\nConvert the above expression to its corresponding lean4 form. Ensure your output strictly conforms to lean4 syntax. Do not output any extra content (only output the expression, no extra text)."
            }
        ],
        "stream": False
    }, ensure_ascii=False)
    headers = {
        'Content-Type': 'application/json',
        'appid': '',
        'Authorization': 'Bearer bce-v3/ALTAK-ePulGJ1LWcJeJX6IPGRFE/5b57c0ee92c0930ca3a2642a0089f87372ac2050'
    }
    
    response = requests.request("POST", url, headers=headers, data=payload.encode("utf-8"))
    return extract_lean4_code(response.text)
def convert_lean_to_maple_api(expr):
    def extract_maple_code(response_json):
        try:
            data = json.loads(response_json)
            content = data["choices"][0]["message"]["content"]
            content = content.replace("```maple", "").replace("```", "").strip()
            return content
        except (json.JSONDecodeError, KeyError, IndexError) as e:
            print(f"Error parsing response: {e}")
            return None
    url = "https://qianfan.baidubce.com/v2/chat/completions"
    payload = json.dumps({
        "model": "deepseek-r1-250528",
        "messages": [
            {
                "role": "user",
                "content": f"{expr}\nConvert the above lean4 expression to its corresponding maple form. Ensure your output strictly conforms to maple syntax. Do not output any extra content (only output the expression, no extra text)."
            }
        ],
        "stream": False
    }, ensure_ascii=False)
    headers = {
        'Content-Type': 'application/json',
        'appid': '',
        'Authorization': 'Bearer bce-v3/ALTAK-ePulGJ1LWcJeJX6IPGRFE/5b57c0ee92c0930ca3a2642a0089f87372ac2050'
    }
    
    response = requests.request("POST", url, headers=headers, data=payload.encode("utf-8"))
    print(response.text)
    return extract_maple_code(response.text)
def convert_maple_to_lean(expr):
    """
    Convert Maple-style mathematical expressions to Lean format:
    - binomial(a, b) → (a.choose b)
    - binomial(a + b, c) → ((a + b).choose c)
    - Preserves original parentheses structure
    - Handles nested expressions and complex arguments
    """
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
        base = convert_maple_to_lean(base)
        top = convert_maple_to_lean(top)
        
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
def lean2maple_internlm(expr):
    expr = expr.replace("↑","")
    #If expr is a number
    if expr.isdigit():
        return expr
    # If expr is a single variable
    if re.match(r'^[a-zA-Z_]\w*$', expr):
        return expr
    if expr.find('fib') == -1 and expr.find('choose') == -1 and expr.find('descFactorial') == -1:
        return expr
    url = 'https://chat.intern-ai.org.cn/api/v1/chat/completions'
    header = {
        'Content-Type':'application/json',
        "Authorization":"Bearer eyJ0eXBlIjoiSldUIiwiYWxnIjoiSFM1MTIifQ.eyJqdGkiOiIzMzEwMDY4MiIsInJvbCI6IlJPTEVfUkVHSVNURVIiLCJpc3MiOiJPcGVuWExhYiIsImlhdCI6MTc0OTcwNzM1MSwiY2xpZW50SWQiOiJlYm1ydm9kNnlvMG5semFlazF5cCIsInBob25lIjoiMTg2MjQ3MTk2MzIiLCJvcGVuSWQiOm51bGwsInV1aWQiOiI4N2Q0YzUxNy02YWYxLTRlMDEtYTZjZi0xMWJhNGVhY2RhZmQiLCJlbWFpbCI6IiIsImV4cCI6MTc2NTI1OTM1MX0.u3aj3_cytW-m3fcDzpmcujdAxiQnXlqZS_SH6EzG58xeObrCXRvnT1d3JODraHITG2kGMFJNQx44JxcY87wPEQ"
    }
    data = {
        "model": "internvl3-latest",  
        "messages": [{
            "role": "user",
            "content": f"{expr}\nConvert the above lean4 expression to its corresponding maple form. Ensure your output strictly conforms to maple syntax. Do not output any extra content (only output the expression, **absolutely no extra text**, if no conversion is needed just output as-is, do not arbitrarily change variable names)\n"\
            "Below are some rules for reference (follow the actual expression; these rules may not all be needed):\n"\
            "Constants or single variables should be output directly\n"\
            "If the expression contains fib: lean4's fib corresponds to maple's F_, e.g. fib (n) corresponds to F_n\n"\
            "If the expression contains choose: lean4's choose corresponds to maple's binomial\n\n"\
            "If the expression contains descFactorial: convert to factorial ratio form, e.g. expr1.descFactorial expr2 becomes expr1!/(expr1-expr2)!\n"\
        }],
        "n": 1,
        "temperature": 0.0,
        "top_p": 0.95
    }
    while True:
        try:
            res = requests.post(url, headers=header, data=json.dumps(data))
            print(res)
            print("ori_lean4: ")
            print(expr)
            print("maple: ")
            print(res.json()["choices"][0]['message']["content"])
            maplecode = res.json()["choices"][0]['message']["content"].replace("```maple", "").replace("```", "").replace("`", "").strip()
            break  # Successfully got response, exit loop
        except Exception as e:
            time.sleep(3)  # Wait before retrying
            print("Request failed, retrying...")
            print(e)
            continue
    return maplecode
def maple2lean_internlm(expr):
    expr = expr.replace("↑","")
    #If expr is a number
    if expr.isdigit():
        return expr
    # If it is a single variable
    if re.match(r'^[a-zA-Z_]\w*$', expr):
        return expr
    if expr.find('F_') == -1 and expr.find('binomial') == -1 and expr.find('!') == -1:
        return expr
    url = 'https://chat.intern-ai.org.cn/api/v1/chat/completions'
    header = {
        'Content-Type':'application/json',
        "Authorization":"Bearer eyJ0eXBlIjoiSldUIiwiYWxnIjoiSFM1MTIifQ.eyJqdGkiOiIzMzEwMDY4MiIsInJvbCI6IlJPTEVfUkVHSVNURVIiLCJpc3MiOiJPcGVuWExhYiIsImlhdCI6MTc0OTcwNzM1MSwiY2xpZW50SWQiOiJlYm1ydm9kNnlvMG5semFlazF5cCIsInBob25lIjoiMTg2MjQ3MTk2MzIiLCJvcGVuSWQiOm51bGwsInV1aWQiOiI4N2Q0YzUxNy02YWYxLTRlMDEtYTZjZi0xMWJhNGVhY2RhZmQiLCJlbWFpbCI6IiIsImV4cCI6MTc2NTI1OTM1MX0.u3aj3_cytW-m3fcDzpmcujdAxiQnXlqZS_SH6EzG58xeObrCXRvnT1d3JODraHITG2kGMFJNQx44JxcY87wPEQ"
    }
    data = {
        "model": "internvl3-latest",  
        "messages": [{
            "role": "user",
            "content": f"{expr}\nConvert the above maple expression to its corresponding lean4 form. Ensure your output strictly conforms to lean4 syntax. Do not output any extra content (only output the expression, no extra text, if no conversion is needed just output as-is)\n"\
            "Below are some rules for reference (follow the actual expression; these rules may not all be needed):\n"\
            "Constants or single variables should be output directly\n"\
            "If the expression contains F_: maple's F_ corresponds to lean4's fib, e.g. F_n corresponds to fib (n)\n"\
            "If the expression contains binomial: maple's binomial corresponds to lean4's choose\n"\
        }],
        "n": 1,
        "temperature": 0.0,
        "top_p": 0.95
    }

    while True:
        try:
            res = requests.post(url, headers=header, data=json.dumps(data))
            print(res)
            print("ori_maple: ")
            print(expr)
            print("lean4: ")
            print(res.json()["choices"][0]['message']["content"])
            leancode = res.json()["choices"][0]['message']["content"].replace("```lean4", "").replace("```", "").replace("`", "").strip()
            break  # Successfully got response, exit loop
        except Exception as e:
            time.sleep(3)  # Wait before retrying
            print("Request failed, retrying...")
            print(e)
            continue
    return leancode
def repair_expr(expr):
    #If expr is a number
    if expr.isdigit():
        return expr
    # If it is a single variable
    if re.match(r'^[a-zA-Z_]\w*$', expr):
        return expr
    url = 'https://chat.intern-ai.org.cn/api/v1/chat/completions'
    header = {
        'Content-Type':'application/json',
        "Authorization":"Bearer eyJ0eXBlIjoiSldUIiwiYWxnIjoiSFM1MTIifQ.eyJqdGkiOiIzMzEwMDY4MiIsInJvbCI6IlJPTEVfUkVHSVNURVIiLCJpc3MiOiJPcGVuWExhYiIsImlhdCI6MTc0OTcwNzM1MSwiY2xpZW50SWQiOiJlYm1ydm9kNnlvMG5semFlazF5cCIsInBob25lIjoiMTg2MjQ3MTk2MzIiLCJvcGVuSWQiOm51bGwsInV1aWQiOiI4N2Q0YzUxNy02YWYxLTRlMDEtYTZjZi0xMWJhNGVhY2RhZmQiLCJlbWFpbCI6IiIsImV4cCI6MTc2NTI1OTM1MX0.u3aj3_cytW-m3fcDzpmcujdAxiQnXlqZS_SH6EzG58xeObrCXRvnT1d3JODraHITG2kGMFJNQx44JxcY87wPEQ"
    }
    data = {
        "model": "internvl3-latest",  
        "messages": [{
            "role": "user",
            "content": f"{expr}\nRemove the unnecessary parentheses from the above lean4 expression. Ensure your output **strictly conforms to lean4 syntax**. Do not output any extra content (only output the expression, no extra text, if no conversion is needed just output as-is)\n"\
            "Functions do not need namespace prefixes\n"\
        }],
        "n": 1,
        "temperature": 0.1,
        "top_p": 0.95
    }

    while True:
        try:
            res = requests.post(url, headers=header, data=json.dumps(data))
            print("ori_lean4: ")
            print(expr)
            print("rep_lean4: ")
            print(res.json()["choices"][0]['message']["content"])
            leancode = res.json()["choices"][0]['message']["content"].replace("```lean4", "").replace("```", "").replace("`", "").replace("nat.", "").strip()
            break  # Successfully got response, exit loop
        except Exception as e:
            time.sleep(3)
            print("Request failed, retrying...")
            print(e)
            continue
    return leancode
# print(lean2maple_internlm("↑n"))
# # Test cases
# test_cases = [
#     ("((2 * k).choose k * catalan (n - k) : ℝ)", "(binomial(2 * k, k) * catalan (n - k))"),
#     ("(n.choose k)", "(binomial(n, k))"),
#     ("((n + m).choose k)", "(binomial(n + m, k))"),
#     ("(choose n k)", "(binomial(n, k))"),
#     ("((2*n).choose n)", "(binomial(2*n, n))"),
#     ("((a + (b * c)).choose (d + e))", "(binomial(a + (b * c), d + e))"),
# ]

# for input_expr, expected_output in test_cases:
#     result = convert_lean_to_math(input_expr)
#     print(f"Input: {input_expr}")
#     print(f"Expected: {expected_output}")
#     print(f"Actual: {result}")
#     print("Match:", result == expected_output)
#     print()
# print(convert_lean_to_math_test("((n + 1).choose k)"))
# print(convert_maple_to_lean("1/binomial(2*n+2,k)*binomial(2*n+1/2,k)"))
# print(convert_lean_to_maple_api("(m.choose k) *  (n.choose (r-k)) * (descPochhammer ℝ p).eval (k:ℝ )"))