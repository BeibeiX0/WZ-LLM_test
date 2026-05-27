import subprocess
from threading import Timer
import re
import uuid
import os
from utils.lean2maple import convert_lean_to_math, lean2maple_internlm, lean2maple_internlm, convert_maple_to_lean
import copy

import subprocess
import uuid
import os
import time
from threading import Timer

class MapleSession:
    def __init__(self, path='/opt/maple2024/bin/maple', timeout=10):
        self.path = path
        self.timeout = timeout
        self.process = None
        self._alive = False

    def __enter__(self):
        try:
            self.process = subprocess.Popen(
                [self.path, '-q'],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,  # line buffering
                universal_newlines=True
            )
            self._alive = True
            
            # Verify the process started successfully
            time.sleep(0.1)
            if self.process.poll() is not None:
                raise RuntimeError(f"Maple failed to start. Exit code: {self.process.returncode}")
                
            return self
        except Exception as e:
            self._cleanup()
            raise RuntimeError(f"Failed to start Maple: {str(e)}")

    def execute(self, command, timeout=None):
        if not self._alive or self.process.poll() is not None:
            raise RuntimeError("Maple process is not running")
            
        if not command.endswith(';'):
            command += ';'
            
        timeout = timeout or self.timeout
        timer = None
        
        try:
            # Add echo command to confirm connection is working
            self.process.stdin.write('"Connection check";\n')
            self.process.stdin.flush()
            
            # Send the actual command
            self.process.stdin.write(command + '\n')
            self.process.stdin.flush()
            
            timer = Timer(timeout, self._timeout_handler)
            timer.start()
            
            output = []
            while True:
                line = self.process.stdout.readline()
                if not line:
                    break
                if line.strip() in ('>', '"Connection check"'):
                    continue
                output.append(line.strip())
                if line.strip().endswith(';'):
                    break
                    
            return '\n'.join(output).rstrip(';').strip()
            
        except BrokenPipeError:
            self._alive = False
            raise RuntimeError("Maple process terminated unexpectedly")
        finally:
            if timer:
                timer.cancel()

    def _timeout_handler(self):
        self._alive = False
        if self.process:
            try:
                self.process.kill()
            except:
                pass

    def _cleanup(self):
        self._alive = False
        if self.process:
            try:
                self.process.stdin.write('quit;\n')
                self.process.stdin.flush()
            except:
                pass
            try:
                self.process.terminate()
            except:
                pass

    def __exit__(self, exc_type, exc_val, exc_tb):
        self._cleanup()
def reverse_sign(s):
    """
    Reverse the +/- signs in the string s
    """
    left_bracket = 0
    right_bracket = 0
    reverse_exp = ''
    for char in s:
        if char == '(':
            left_bracket += 1
            reverse_exp += char
        elif char == ')':
            right_bracket += 1
            reverse_exp += char
        elif left_bracket == right_bracket and (char == '+' or char == '-'):
            # Reverse the sign
            reverse_exp += '+' if char == '-' else '-'
        else:
            reverse_exp += char
    if reverse_exp.startswith('+'):
        reverse_exp = reverse_exp[1:]
    return reverse_exp
def reverse_outer_signs_and_remove_mulone(expression, mulone=True):
    """
    Strictly handle expressions of the form (-.....)/(-.....), reversing outer-level signs.
    1. First check if the expression matches this pattern
    2. If not, return the original expression as-is
    3. If it matches, reverse the leading sign inside the outermost parentheses of numerator and denominator
    """
    if mulone and expression.startswith('1/'):
        return expression[1:]
    # Strictly match the (-...)/(-...) form
    pattern = r'^\(-([^()]|\([^()]*\))*\)/\(-([^()]|\([^()]*\))*\)$'
    
    if not re.fullmatch(pattern, expression):
        print("not full")
        return expression
    
    # Process numerator
    numerator = expression.split('/')[0]
    print("numerator:", numerator)
    numerator = numerator.strip()[1:-1]
    
    # Process denominator
    denominator = expression.split('/')[1]
    print("denominator:", denominator)
    denominator = denominator.strip()[1:-1]
    numerator = reverse_sign(numerator)
    denominator = reverse_sign(denominator)
    if numerator.startswith('+'):
        numerator = numerator[1:]
    if denominator.startswith('+'):
        denominator = denominator[1:]
    return f'({numerator})' + '/' + f'({denominator})'
def convert_negative_parentheses(expr):
    """
    Identify (-.....)^n patterns in the expression and convert signs.
    Keep the exponent part unchanged.
    """
    # Match (-...)^n pattern, allowing simple nesting
    pattern = r'\(-\s*([^()]+|\([^()]*\))\s*\)(\^\d+)?'
    
    def replace_match(match):
        inner_content = match.group(1)  # Get the content inside the parentheses
        exponent = match.group(2) or ''  # Get the exponent part (empty if none)
        print("inner_content:", inner_content)
        print("exponent:", exponent)
        if exponent == '' or int(exponent.strip()[1:])%2 == 1:
            # Return as-is
            return f'(-{inner_content}){exponent}'
        return f'({reverse_sign("-"+inner_content.strip())}){exponent}'  # Replace - with +
    # Execute the substitution
    return re.sub(pattern, replace_match, expr)
def get_temp_filename(prefix):
    """Generate a temporary filename with a unique suffix"""
    unique_id = str(uuid.uuid4().hex)[:8]
    os.makedirs("tmp", exist_ok=True)
    return f"tmp/{prefix}_{unique_id}.txt"

def calculate_ratio(Ank, Bn, max_retries=3, variablen='n', variablek='k'):
    """Calculate ratios with retry mechanism"""
    # Ank = lean2maple_internlm(Ank)
    # Bn = lean2maple_internlm(Bn)
    
    akdiv_file = get_temp_filename("Akdiv")
    andiv_file = get_temp_filename("Andiv")
    bdiv_file = get_temp_filename("Bdiv")
    # TODO ANNDIV
    last_error = None
    
    for attempt in range(max_retries):
        try:
            # Use separate sessions to execute each group of commands
            with MapleSession() as maple:
                # First group of commands
                maple.execute(
                    f"""
                    with(combinat);
                    catalan := n -> binomial(2*n, n)/(n + 1);
                    A := {variablek} -> {Ank};
                    result := simplify(A({variablek}+1) / A({variablek}));
                    file := fopen("{akdiv_file}", WRITE);
                    fprintf(file, "%a", result);
                    fclose(file);
                    """
                )
                
            with MapleSession() as maple:
                # Second group of commands
                maple.execute(
                    f"""
                    with(combinat);
                    catalan := n -> binomial(2*n, n)/(n + 1);
                    A := ({variablen}, {variablek}) -> {Ank};
                    result := simplify(A({variablen}+1, {variablek}) / A({variablen}, {variablek}));
                    file := fopen("{andiv_file}", WRITE);
                    fprintf(file, "%a", result);
                    fclose(file);
                    """
                )
                
            with MapleSession() as maple:
                # Third group of commands
                maple.execute(
                    f"""
                    with(combinat);
                    catalan := n -> binomial(2*n, n)/(n + 1);
                    A := {variablen} -> {Bn};
                    result := simplify(A({variablen}+1) / A({variablen}));
                    file := fopen("{bdiv_file}", WRITE);
                    fprintf(file, "%a", result);
                    fclose(file);
                    """
                )
            
            # Read results
            with open(akdiv_file, "r") as f:
                print(f"Akdiv file: {akdiv_file}")
                Akdiv = convert_maple_to_lean(f.read().strip())
                Akdiv = reverse_outer_signs_and_remove_mulone(Akdiv, mulone=False)
            with open(andiv_file, "r") as f:
                print(f"Andiv file: {andiv_file}")
                Andiv = convert_maple_to_lean(f.read().strip())
                Andiv = reverse_outer_signs_and_remove_mulone(Andiv, mulone=False)
            with open(bdiv_file, "r") as f:
                print(f"Bdiv file: {bdiv_file}")
                Bdiv = convert_maple_to_lean(f.read().strip())
                Bdiv = reverse_outer_signs_and_remove_mulone(Bdiv, mulone=False)
            return Akdiv, Andiv, Bdiv
            
        except Exception as e:
            last_error = e
            time.sleep(1)  # Wait before retrying
            continue
            
        finally:
            # Clean up temporary files
            for f in [akdiv_file, andiv_file, bdiv_file]:
                try:
                    os.remove(f)
                except:
                    pass
    
    raise RuntimeError(f"Failed after {max_retries} attempts. Last error: {str(last_error)}")

def calculate_cert(Ank, Bn, variablen='n', variablek='k'):
    """Calculate the WZ certificate"""
    # Ank = lean2maple_internlm(Ank)
    # Bn = lean2maple_internlm(Bn)
    print('calculate_cert:', Ank, Bn)
    cert_file = get_temp_filename("cert")
    
    try:
        with MapleSession() as maple:
            maple.execute(
                f"""
                with(combinat);
                catalan := n -> binomial(2*n, n)/(n + 1);
                with(SumTools[Hypergeometric]);
                wzf := {Ank};
                wzr := {Bn};
                WZpair := WZMethod(wzf, wzr, {variablen}, {variablek}, 'cert');
                file := fopen("{cert_file}", WRITE);
                fprintf(file, "%a", cert);
                fclose(file);
                """
            )
        
        with open(cert_file, "r") as file:
            print('cert_file:', cert_file)
            cert = convert_maple_to_lean(file.read().strip())
            
        return cert
        
    finally:
        try:
            os.remove(cert_file)
        except:
            pass

def get_recursive_goals(exp_maple, exp, variable):
    print('get_recursive_goals:', exp_maple, exp, variable)
    if exp.find(f'{variable}') == -1:
        return None
    if exp.find('choose') == -1 and exp.find('^') == -1 and exp.find('fib') == -1 and exp.find('catalan') == -1 and exp.find('!') == -1 and exp.find('descFactorial') == -1:
        return None
    exp = exp.replace('⁻¹', '')
    original_exp = re.sub(rf'\b{variable}\b', f'({variable} + 1)', exp)
    print('exp:', exp)
    print('replace exp:', original_exp)
    base_exp = exp_maple
    
    recursive_goal_file = get_temp_filename("recursive_goal")
    
    try:
        # base_exp_math = lean2maple_internlm(base_exp)
        base_exp_math = base_exp
        with MapleSession() as maple:
            maple.execute(
                "with(combinat);\n"
                "catalan := n -> binomial(2*n, n)/(n + 1);\n"
                f"A := {variable} -> {base_exp_math};\n"
                f"result := simplify(A({variable}+1) / A({variable}));\n"
                f"writeto(\"{recursive_goal_file}\");\n"
                "lprint(result);\n"
                "writeto(terminal);\n"
                "result;"
            )
        
        with open(recursive_goal_file, "r") as file:
            print('recursive_goal_file:', recursive_goal_file)
            recursive_goal = convert_maple_to_lean(file.read().strip())
            recursive_goal = convert_negative_parentheses(recursive_goal)
        # if exp.find("descFactorial") != -1 or exp.find("factorial") != -1 or exp.find("!") != -1:
        #     return f"{original_exp} = ({exp}) * ({recursive_goal})"
        if exp.find("choose") == -1:
            return f"{original_exp} = ({exp}) * ({recursive_goal})"
        recursive_goal = reverse_outer_signs_and_remove_mulone(recursive_goal)
        if recursive_goal.startswith('/'):
            return f"{original_exp} = ({exp}) {recursive_goal}"
        return f"{original_exp} = ({exp}) * ({recursive_goal})"
        
    finally:
        try:
            os.remove(recursive_goal_file)
        except:
            pass

def  get_recursive_goals_calc(exp, exp_lean, variablen='n', variablek='k', num1=' + 1', num2='', num3=' + 1', num4=' + 1'):
    exp = exp.replace('⁻¹', '')
    if exp.find(variablen) == -1 and exp.find(variablek) == -1:
        return None
    if exp_lean.find('choose') == -1 and exp_lean.find('^') == -1 and exp_lean.find('fib') == -1 and exp_lean.find('catalan') == -1 and exp_lean.find('!') == -1 and exp.find('descFactorial') == -1:
        return None
    recursive_goal_file = get_temp_filename("recursive_goal")
    
    try:
        original_base_exp = re.sub(fr'\b{variablen}\b', f'({variablen}{num4})', exp_lean)
        original_base_exp = re.sub(fr'\b{variablek}\b', f'({variablen}{num2})', original_base_exp)
        
        original_exp = re.sub(fr'\b{variablen}\b', f'({variablen}{num3})', exp_lean)
        original_exp = re.sub(fr'\b{variablek}\b', f'({variablen}{num1})', original_exp)
        
        # exp_maple = lean2maple_internlm(exp)
        exp_maple = exp
        with MapleSession() as maple:
            maple.execute(
                "with(combinat);\n"
                "catalan := n -> binomial(2*n, n)/(n + 1);\n"
                f"exp_ := ({variablen}, {variablek}) -> {exp_maple};\n"
                f"result := simplify(exp_({variablen}{num3}, {variablen}{num1}) / exp_({variablen}{num4}, {variablen}{num2}));\n"
                f"writeto(\"{recursive_goal_file}\");\n"
                "lprint(result);\n"
                "writeto(terminal);\n"
                "result;"
            )
        
        with open(recursive_goal_file, "r") as file:
            print('recursive_goal_calc_file:', recursive_goal_file)
            recursive_goal = convert_maple_to_lean(file.read().strip())
            recursive_goal = convert_negative_parentheses(recursive_goal)
        # if original_base_exp.find("descFactorial") != -1 or original_base_exp.find("factorial") != -1 or original_base_exp.find("!") != -1:
        #     return f"{original_exp} = ({original_base_exp}) * ({recursive_goal})"
        if original_base_exp.find("choose") == -1:
            return f"{original_exp} = ({original_base_exp}) * ({recursive_goal})"
        recursive_goal = reverse_outer_signs_and_remove_mulone(recursive_goal)
        if recursive_goal.startswith('/'):
            return f"{original_exp} = ({original_base_exp}) {recursive_goal}"
        return f"{original_exp} = ({original_base_exp}) * ({recursive_goal})"
        
    finally:
        try:
            os.remove(recursive_goal_file)
        except:
            pass