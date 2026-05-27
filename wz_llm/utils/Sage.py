import pexpect
import os
import sys
import time
import re
from utils.lean2sage import convert_lean_to_sage, convert_sage_to_lean
from utils.Maple import reverse_outer_signs_and_remove_mulone, convert_negative_parentheses
class SageSession:
    def __init__(self, path=None, timeout=30):
        self.path = path or self._find_sage()
        self.timeout = timeout
        self.process = None
        self.prompt = "sage:"  # simplified prompt matching
        self._alive = False

    def _find_sage(self):
        """Automatically locate sage executable"""
        try:
            path = pexpect.which('sage')
            # Verify sage is actually executable
            if os.access(path, os.X_OK):
                return path
            raise RuntimeError("sage found but not executable")
        except:
            common_paths = [
                '/usr/bin/sage',
                '/usr/local/bin/sage',
                os.path.expanduser('~/sage/sage'),
                os.path.join(os.environ.get('CONDA_PREFIX', ''), 'bin/sage')
            ]
            for p in common_paths:
                if os.path.exists(p) and os.access(p, os.X_OK):
                    return p
            raise RuntimeError("Could not find executable sage")

    def __enter__(self):
        try:
            # Use the full conda environment
            env = os.environ.copy()
            env['TERM'] = 'dumb'
            env['PAGER'] = 'cat'
            
            # Start Sage process (show detailed errors)
            self.process = pexpect.spawn(
                self.path,
                timeout=self.timeout,
                encoding='utf-8',
                env=env
            )
            
            # Log all output for debugging
            self.process.logfile_read = sys.stdout
            
            # Wait for initialization
            index = self.process.expect([self.prompt, pexpect.EOF, pexpect.TIMEOUT], 
                                      timeout=120)
            
            if index == 1:  # EOF
                raise RuntimeError(f"Sage terminated unexpectedly. Exit code: {self.process.exitstatus}")
            elif index == 2:  # TIMEOUT
                raise RuntimeError("Sage startup timed out")
            
            # # Basic verification
            # self.process.sendline("2+2")
            # self.process.expect(r"4\r\n" + self.prompt)
            
            # # Set up environment
            # self.process.sendline("from sage.all import *")
            # self.process.expect(self.prompt)
            
            self._alive = True
            return self
            
        except Exception as e:
            if self.process:
                print("\nDebug info:")
                print(f"Before: {self.process.before}")
                print(f"After: {self.process.after}")
                print(f"Exit status: {getattr(self.process, 'exitstatus', None)}")
            self._cleanup()
            raise RuntimeError(f"Failed to start Sage: {str(e)}")

    def execute(self, command, timeout=None):
        """Execute Sage command"""
        if not self._alive:
            raise RuntimeError("Sage process is not running")

        timeout = timeout or self.timeout
        try:
            self.process.sendline(command)
            self.process.expect(self.prompt, timeout=timeout)
            
            # Clean up output
            output = self.process.before
            lines = [line.strip() for line in output.split('\n') 
                    if line.strip() and not line.strip().startswith(command.strip())]
            return '\n'.join(lines)
            
        except pexpect.TIMEOUT:
            raise RuntimeError(f"Command timed out after {timeout} seconds")
        except pexpect.EOF:
            self._alive = False
            raise RuntimeError("Sage process terminated unexpectedly")

    def _cleanup(self):
        """Clean up resources"""
        self._alive = False
        if self.process and not self.process.closed:
            try:
                self.process.sendline('quit()')
                time.sleep(1)
                self.process.terminate(force=True)
            except:
                pass
            finally:
                self.process.close()

    def __exit__(self, exc_type, exc_val, exc_tb):
        self._cleanup()
prefix =\
"""
from sage.symbolic.expression import Expression
from sage.functions.other import binomial
import operator

def simplify_binomial(expr):
    # First try to simplify the entire expression directly (preserving exponentiation)
    try:
        simplified = expr.simplify_factorial().simplify()
        if "binomial"  not in str(simplified):
            return simplified
    except:
        pass
    
    # Recursively process expression
    if expr.operator() is binomial:
        # Apply specific simplification rules for binomial coefficients
        n, k = expr.operands()
        if (n - k == 1):
            return n
        elif (k == 0) or (k == n):
            return 1
        elif (k == 1) or (k == n-1):
            return n
        else:
            return binomial(n, k).simplify_full()
    
    
    # Handle other operators
    elif expr.operator() is not None:
        return expr.operator()(*[simplify_binomial(op) for op in expr.operands()])
    
    return expr
"""
def get_all_variables(sage_exp):
    """Extract all variables from a Sage expression"""
    # expr = symbolic_expression(expr_str)
    with SageSession(timeout=180) as sage:
        sagescript = f"""
        expr = "{sage_exp}";
        expr = symbolic_expression(expr);
        variables = expr.variables();
        show(variables);
        """.replace('\n', '')
        results = sage.execute(sagescript)
        print(results)
    results = results.replace('sage:', '').strip().replace('(', '').replace(')', '').replace(',', '')
    return results
def mapping_before(sage_exp, variable):
    sage_exp = re.sub(rf'\ba\b', f'a1', sage_exp)
    sage_exp = re.sub(rf'\b{variable}\b', f'a', sage_exp)
    return sage_exp
def mapping_after(sage_exp, variable):
    sage_exp = re.sub(rf'\ba\b', f'{variable}', sage_exp)
    sage_exp = re.sub(rf'\ba1\b', f'a', sage_exp)
    return sage_exp
def calculate_ratio_sage(Ank, Bn, max_retries=3, variablen='n', variablek='k'):
    """Calculate ratios A(n,k+1)/A(n,k), A(n+1,k)/A(n,k), B(n+1)/B(n)"""
    print("Calculating ratio with Sage:", Ank, Bn)
    Ank = mapping_before(Ank, variablen)
    Bn = mapping_before(Bn, variablen)
    all_variables = get_all_variables(Ank + '+' + Bn)
    with SageSession(timeout=180) as sage:
        sagescript = f"""
        _ = var('{all_variables}');
        A(a,{variablek}) = {Ank};
        B(a) = {Bn};
        c = A(a,{variablek}+1)/A(a,{variablek});
        show(c.simplify());
        c = A(a+1,{variablek})/A(a,{variablek});
        show(c.simplify());
        c = B(a+1)/B(a);
        show(c.simplify());
        """.replace('\n', '')
        results = sage.execute(sagescript)
        results = results.replace('sage:', '').strip().split('\n')
        print("Sage results:", results)
        if len(results):
            results = [mapping_after(result, variablen) for result in results]
            print("Converted results:", results)
        return results
def calculate_cert_sage(Ank, Bn, variablen='n', variablek='k'):
    """Calculate WZ certificate"""
    print("Calculating WZ certificate with Sage:", Ank, Bn)
    Ank = mapping_before(Ank, variablen)
    Bn = mapping_before(Bn, variablen)
    all_variables = get_all_variables(Ank + '+' + Bn)
    with SageSession(timeout=180) as sage:
        sagescript = f"""
        _ = var('{all_variables}');
        F(a,{variablek}) = ({Ank}) / ({Bn});
        c = F(a,{variablek}).WZ_certificate(a,{variablek});
        show(c);
        """.replace('\n', '')
        results = sage.execute(sagescript)
        results = results.replace('sage:', '').strip().split('\n')
        # print("Sage results:", results)
        if len(results):
            results[0] = mapping_after(results[0], variablen)
            print("Converted results:", results)
            return results[0]  # return the first result as the certificate
        else:
            print("No certificate found.")
def get_recursive_goals_sage(exp_sage, exp_lean, variable, variablen='n'):
    print('get_recursive_goals:', exp_sage, exp_lean, variable)
    if exp_lean.find(f'{variable}') == -1:
        return None
    if exp_lean.find('choose') == -1 and exp_lean.find('^') == -1 and exp_lean.find('fib') == -1 and exp_lean.find('catalan') == -1 and exp_lean.find('!') == -1 and exp_lean.find('descFactorial') == -1:
        return None
    exp_lean = exp_lean.replace('⁻¹', '')
    original_exp = re.sub(rf'\b{variable}\b', f'({variable} + 1)', exp_lean)
            
    # If variablen can be found
    if re.findall(rf'\b{variablen}\b', exp_lean) and variable!=variablen:
        exp_sage = mapping_before(exp_sage, variablen)
        all_variables = get_all_variables(exp_sage)
        with SageSession(timeout=180) as sage:
            sagescript = f"""
            _ = var('{all_variables}');
            F({variable}) = {exp_sage};
            c = (F({variable}+1) / F({variable})).simplify();
            show(c);
            """.replace('\n', '')
            results = sage.execute(sagescript)
            results = results.replace('sage:', '').strip().split('\n')
            print("Sage results:", results)
            if len(results):
                results = results[0]
                results = mapping_after(results, variablen)
                results = convert_sage_to_lean(results)
                print("Converted results:", results)
            else:
                print("No results found.")
                return None
            results = convert_negative_parentheses(results)
            results = reverse_outer_signs_and_remove_mulone(results, True)
            if results.startswith('/'):
                return f"{original_exp} = ({exp_lean}) {results}"
            if original_exp.find('choose') != -1 and results[0]!='-':
                return f"{original_exp} = ({exp_lean}) * {results}"
            return f"{original_exp} = ({exp_lean}) * ({results})"
    else:
        exp_sage = mapping_before(exp_sage, variable)
        all_variables = get_all_variables(exp_sage)
        with SageSession(timeout=180) as sage:
            sagescript = f"""
            _ = var('{all_variables}');
            F(a) = {exp_sage};
            c = (F(a+1) / F(a)).simplify();
            show(c);
            """.replace('\n', '')
            results = sage.execute(sagescript)
            results = results.replace('sage:', '').strip().split('\n')
            print("Sage results:", results)
            if len(results):
                results = results[0]
                results = mapping_after(results, variable)
                results = convert_sage_to_lean(results)
                print("Converted results:", results)
            else:
                print("No results found.")
                return None
            results = convert_negative_parentheses(results)
            results = reverse_outer_signs_and_remove_mulone(results, True)
            if results.startswith('/'):
                return f"{original_exp} = ({exp_lean}) {results}"
            if original_exp.find('choose') != -1 and results[0]!='-':
                return f"{original_exp} = ({exp_lean}) * {results}"
            return f"{original_exp} = ({exp_lean}) * ({results})"
def  get_recursive_goals_calc_sage(exp, exp_lean, variablen='n', variablek='k', num1=' + 1', num2=''):
    """Calculate recursive goals"""
    print('get_recursive_goals_calc:', exp, exp_lean, variablen)
    exp = exp.replace('⁻¹', '')
    if exp.find(variablen) == -1 and exp.find(variablek) == -1:
        return None
    if exp_lean.find('choose') == -1 and exp_lean.find('^') == -1 and exp_lean.find('fib') == -1 and exp_lean.find('catalan') == -1 and exp_lean.find('!') == -1 and exp.find('descFactorial') == -1:
        return None
    original_base_exp = re.sub(fr'\b{variablen}\b', f'({variablen} + 1)', exp_lean)
    original_base_exp = re.sub(fr'\b{variablek}\b', f'({variablen}{num2})', original_base_exp)
    
    original_exp = re.sub(fr'\b{variablen}\b', f'({variablen} + 1)', exp_lean)
    original_exp = re.sub(fr'\b{variablek}\b', f'({variablen}{num1})', original_exp)
    exp = mapping_before(exp, variablen)
    all_variables = get_all_variables(exp)
    with SageSession(timeout=180) as sage:
        sagescript = f"""
        _ = var('{all_variables}');
        F(a,{variablek}) = {exp};
        c = (F(a+1, a{num1}) / F(a+1, a{num2})).simplify();
        show(c);
        """.replace('\n', '')
        results = sage.execute(sagescript)
        results = results.replace('sage:', '').strip().split('\n')
        print("Sage results:", results)
        if len(results):
            results = results[0]
            results = mapping_after(results, variablen)
            results = convert_sage_to_lean(results)
            results = convert_negative_parentheses(results)
            results = reverse_outer_signs_and_remove_mulone(results, True)
            print("Converted results:", results)
            if results.startswith('/'):
                return f"{original_exp} = ({original_base_exp}) {results}"
        else:
            print("No results found.")
            return None
        return f"{original_exp} = ({original_base_exp}) * ({results})"
# if __name__ == "__main__":
#     # get_all_variables("binomial(n,k)")
#     # calculate_ratio_sage("binomial(n,k)", "2^n", variablen='n', variablek='k')
#     calculate_cert_sage("binomial(n,k)", "2^n", variablen='n', variablek='k')
#     print("Testing SageSession (with debug output)...")
#     try:
#         # Display sage path
#         sage_path = pexpect.which('sage') 
#         print(f"Using Sage at: {sage_path}")
        
#         # with SageSession(timeout=180) as sage:
#         #     # print("\n1. Basic test:")
#         #     # sage.execute("2^10")
            
#         #     # print("\n2. Symbolic test:")
#         #     # print(sage.execute("x = var('x'); factor(x^2-1)"))

#         #     # print("\n3. wz test:")
#         #     # wz_test_script = """_ = var('k n');F(n,k) = binomial(n,k) / 2^n;c = F(n,k).WZ_certificate(n,k); c"""
#         #     # print(sage.execute(wz_test_script))

#         #     # print("\n3. Ratio:")
#         #     # wz_test_script = """_ = var('n k y');A(n,k) = binomial(n,k);c = A(n+1,k)/A(n,k); (c.simplify())"""
#         #     # print(sage.execute(wz_test_script))
#         #     print("\n4. Calculate ratio:")
#         # calculate_ratio("binomial(n,k)", "2^n", variablen='n', variablek='k')
#         # calculate_cert("binomial(n,k)", "2^n", variablen='n', variablek='k')
#         print(get_recursive_goals("binomial(n,k)", "n.choose(k)", "n"))
#         print(get_recursive_goals_calc("binomial(n,k)", "n.choose(k)", variablen='n', variablek='k', num1=' + 1', num2=''))
#     except Exception as e:
#         # print(f"\nFatal error: {str(e)}")
#         # print("\nTroubleshooting steps:")
#         # print("1. Verify sage installation:")
#         # print(f"   {sage_path} --version")
#         # print("2. Check conda environment:")
#         # print("   conda list sage")
#         # print("3. Try running manually:")
#         # print(f"   {sage_path} -c \"print(2^10)\"")
#         print(f"Error: {str(e)}")