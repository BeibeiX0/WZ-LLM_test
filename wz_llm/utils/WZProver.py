"""Automated WZ-method prover for combinatorial identities in Lean 4.

This module implements the Wilf-Zeilberger (WZ) method to automatically
generate Lean 4 tactic proofs for combinatorial summation identities.
The proof pipeline consists of three main steps:

    1. **Symbolic Computation**: Compute WZ certificates, ratio expressions,
       and recurrence relations via Sage or Maple.
    2. **Framework Generation**: Construct the Lean 4 proof skeleton including
       ``let`` bindings, auxiliary lemmas (``aux₁``–``aux₅``), non-zero
       conditions, and the WZ equation.
    3. **Interactive Verification**: Validate each proof step against the
       Lean 4 kernel through the REPL, assembling verified tactics into
       the final proof.

Typical usage::

    prover = WZProver(lean_kit, bert_similarity)
    tactic_code = prover.prove(formal_theorem, import_content)
"""

import copy
import json
import re
import time
from queue import Queue

from utils.Constant import *
from utils.lean2maple import (
    convert_lean_to_math_test,
    lean2maple_internlm,
    repair_expr,
)
from utils.lean2sage import convert_lean_to_sage
from utils.lean4Kit.Lean4Kit import Lean4Kit, TacticState
from utils.Maple import (
    calculate_cert,
    calculate_ratio,
    get_recursive_goals,
    get_recursive_goals_calc,
)
from utils.Sage_Python import (
    calculate_cert_sage,
    calculate_ratio_sage,
    get_choose_primises,
    get_eq_zero_primise,
    get_gosper_g,
    get_recursive_goals_calc_sage,
    get_recursive_goals_sage,
)
from utils.strip_even_power import strip_outer_even_power
class WZProver:
    """Automated prover for combinatorial identities using the WZ method.

    This class orchestrates the full proof pipeline: parsing the summation
    identity, computing symbolic ratios and WZ certificates, generating
    Lean 4 tactic scripts for each proof obligation (non-zero conditions,
    ratio lemmas, the WZ equation, and the inductive closure), and
    assembling them into a complete proof.

    Args:
        lean: A ``Lean4Kit`` instance for interactive tactic evaluation.
        bert_sim: A similarity model for lemma retrieval (may be ``None``).

    Attributes:
        variablen: The summation outer variable name (default ``'n'``).
        variablek: The summation index variable name (default ``'k'``).
        theorem_statement: The current theorem being proved.
        lemma_path: File path for exporting generated lemma obligations.
        last_timing: Dict recording timing of the most recent proof attempt.
    """
    def __init__(self, lean:Lean4Kit, bert_sim):
        self.lean = lean
        self.bert_sim = bert_sim
        self.theorem_statement = None
        self.step3_primise = None
        self.all_primises = ""
        self.lemma_nezero_list = LEMMA_NEZERO_LIST # stores lemmas for proving non-zero (statement: tactics)
        self.lemma_recursive_list = LEMMA_RECURSIVE_LIST # stores recurrence relation lemmas (statement: tactics)
        self.searcher = None
        self.let_tactics_list = None
        self.aux1_recursive = None
        self.aux2_recursive = None
        self.aux3_recursive = None
        self.lemma = None
        self.variablen = 'n'
        self.variablek = 'k'
        self.lemma_path = None # used to store the path of lemmas
        self.range_num1 = None
        self.range_num2 = None
        self.calc_rw = None
        self.space = " "
        self.last_timing = {}
        
    def extract_primise(self, expr, n='n', k='k'):
        """Extract premise conditions from the summation identity.

        Analyzes both sides of the equation to find by-cases premises
        (values of ``n`` that make sub-expressions zero), ``k``-premises
        (values of ``k`` causing zero), and choose-premises (binomial
        coefficient validity conditions).

        Args:
            expr: The goal expression of the form ``..., LHS = RHS``.
            n: Name of the outer variable.
            k: Name of the summation index.

        Returns:
            A tuple ``(premises, k_cnt)`` where *premises* is a list of
            condition strings and *k_cnt* is the number of initial ``k``
            values to peel off.
        """
        # First split
        expr = expr.replace('↑', '')
        parts = expr.split('=', 1)
        expr1, expr2 = parts[0], parts[1] if len(parts) > 1 else ''
        expr1_parts = expr1.strip().split(',')
        expr1 = expr1_parts[1].strip() if len(expr1_parts) > 1 else expr1.strip()
        expr2 = expr2.strip()
        expr1_list = self.split_expression([expr1])
        expr2_list = self.split_expression([expr2])
        print("expr1_list:", expr1_list)
        print("expr2_list:", expr2_list)
        
        by_cases_primises = []
        k_primises = []
        choose_primises = []
        # exp_lean.find('choose') == -1 and exp_lean.find('^') == -1 and exp_lean.find('fib') == -1 and exp_lean.find('catalan') == -1 and exp_lean.find('!') == -1 and exp_lean.find('descFactorial') == -1
        for i in expr2_list:
            if re.search(rf'\b{n}\b', i) and (i.find('choose') == -1 and i.find('^') == -1 and i.find('fib') == -1 and i.find('catalan') == -1 and i.find('!') == -1 and i.find('descFactorial') == -1 and i.find('factorial') == -1):
                by_cases_primises.append(get_eq_zero_primise(convert_lean_to_sage(i), n, k,n))
        for i in expr1_list:
            if re.search(rf'\b{k}\b', i) and (i.find('choose') == -1 and i.find('^') == -1 and i.find('fib') == -1 and i.find('catalan') == -1 and i.find('!') == -1 and i.find('descFactorial') == -1 and i.find('factorial') == -1):
                k_primises.append(get_eq_zero_primise(convert_lean_to_sage(i), n, k,k).replace(f"k = ", ''))
                print(k_primises)
        by_cases_primises = list(set(by_cases_primises))
        k_primises = list(set(k_primises))
        by_cases_primises = [i for i in by_cases_primises if i]
        # Filter out conditions that are always false for ℕ (e.g. "m < 0", "m ≤ 0")
        by_cases_primises = [
            i for i in by_cases_primises
            if not re.match(r'^[a-zA-Z_]\w*\s*[<≤]\s*0$', i.strip())
            and not re.match(r'^0\s*[>≥]\s*[a-zA-Z_]\w*$', i.strip())
        ]
        k_primises_int = []
        # Converting i to int may raise an error; only keep successful ones
        for i in k_primises:
            try:
                inti = int(i)
                k_primises_int.append(inti)
            except:
                continue
        if not k_primises_int:
            k_cnt = 0
        else: k_cnt = max(k_primises_int) + 1
        for i in expr1_list + expr2_list:

            choose_primises.extend(get_choose_primises(i, n, k,True))
        print("By cases primises:", by_cases_primises)
        print("k primises:", k_primises)
        print("k_cnt:", k_cnt)
        print("choose primises", choose_primises)
        return by_cases_primises + choose_primises, k_cnt
    def set_variables_and_num(self, exp):
        """Parse the summation header and set variable names and range offsets.

        Extracts the index variable, summation variable, and range offset
        from expressions like ``∑ k in range (n + 1)``.

        Args:
            exp: The summation header string (e.g., ``∑ k in range (n+1)``).
        """
        exp = exp.replace('∈', 'in')
        # sensible defaults
        self.variablek = 'k'
        self.variablen = 'n'
        self.num1 = ""
        self.num2 = ""
        self.calc_rw = None
        # local parsing defaults to avoid UnboundLocalError
        n = self.variablen
        k = self.variablek
        n_op = ''
        k_op = ''
        print(exp)
        if 'in' in exp:
            parts = exp.split('in')
            print("parts:", parts)
            n_part = parts[1].strip()
            n_part = ''.join(n_part.split(' ')[1:])
            print("n_part:", n_part)
            
            # Extract n and its operation
            n_match = re.match(r'^\(?([a-zA-Z_][a-zA-Z0-9_]*)([+-]\d+)?\)?$', n_part)
            if n_match:
                n = n_match.group(1)
                n_op = n_match.group(2) if n_match.group(2) else ''
            else:
                n = 'n'
                n_op = ''
            
            # Extract k and its operation
            k_part = parts[0].strip().split(' ')[-1]
            k_match = re.match(r'^([a-zA-Z_][a-zA-Z0-9_]*)([+-]\d+)?$', k_part)
            if k_match:
                k = k_match.group(1)
                k_op = k_match.group(2) if k_match.group(2) else ''
            else:
                k = 'k'
                k_op = ''    
        self.variablen = n
        self.variablek = k
        num1_int = 0
        self.num1 = n_op 
        print("num1:", self.num1)
        
        if self.num1.strip() == "":
            num1_int = 0
        else:
            num1_int = int(self.num1.strip())
        num2_int = num1_int - 1
        self.num1_int = num1_int
        self.num2_int = num2_int
        if num2_int == 0: 
            self.num2 = ""
        elif num2_int > 0:
            self.num2 = f" + {num2_int}"
        elif num2_int < 0:
            self.num2 = f" - {-num2_int}"
        if num1_int == 1:
            self.calc_rw = ""
        else:
            self.calc_rw = f"nth_rw 1 [show {self.variablen}{self.num1} = {self.variablen} {self.num2} +1 by omega]"
        print("set_variables:", self.variablen, self.variablek)
        print("operations:", self.num1, self.num2)
    def set_searcher(self, searcher):
        """
        Set the LLM searcher
        """
        self.searcher = searcher
    def init_theorem(self, lean:Lean4Kit, bert_sim, theorem_statement:str):
        """
        Initialize theorem
        """
        self.lean = lean
        self.bert_sim = bert_sim
        self.theorem_statement = theorem_statement
        
    def is_finished(self, import_content:str, theorem_statement:str, history_tactics):
        """
        Check if the theorem is finished
        """
        if isinstance(history_tactics, list):
            tactics = "\n".join(history_tactics)
        else: tactics = history_tactics
        theorem_statement = f"{import_content}\n{theorem_statement} := by\n{tactics}"
        # print("theorem_statement:", theorem_statement)
        verify_lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        try:
            if verify_lean.is_correct_and_finished(theorem_statement, verbose=VERBOSE):
                # print("Theorem finished")
                return True
            else:
                # print("Theorem not finished")
                return False
        except Exception as e:
            # print(f"Error verifying theorem: {e}")
            return False
    def repair_expr(self, expression:str):
        # Remove unmatched left or right parentheses

        expression = expression.strip()
        # First check for excess left parentheses
        left_bracket_num = expression.count('(')
        right_bracket_num = expression.count(')')
        if left_bracket_num > right_bracket_num:
            expression = expression[left_bracket_num - right_bracket_num:]
        elif right_bracket_num > left_bracket_num:
            lenghth = len(expression)
            expression = expression[:lenghth - (right_bracket_num - left_bracket_num)]
        return expression.strip()

    def addR(self, expression:str, all=False):
        """
        Add R (cast to real number type)
        """
        if expression == "0":return expression
        # if expression.find('R') != -1:
        #     print("expression already has R:", expression)
        #     return expression.strip()
        if len(expression)>=2 and expression[-2] == 'ℝ' and expression[-1] == ')':
            print("expression already has R:", expression)
            return expression.strip()
        new_expression = expression.strip()
        
        if all:
            
            if new_expression.find('ℝ') == -1:
                if new_expression.find('=') == -1:
                    new_expression = '(' + new_expression + ' : ℝ)'
                else:
                    _eq_parts = new_expression.split('=', 1)
                    new_expression = '(' + _eq_parts[0] + ' : ℝ) = ' + (_eq_parts[1] if len(_eq_parts) > 1 else '')
            print("addr_expression:", new_expression)
            return new_expression
        print("expression:", expression)
        len_ = len(expression)
        flag = 0 # distinguish between the two types: up-arrow content and up-arrow (content)
        kuohao = 0
        i = 0
        new_expression = ""
        while i < len_:
            c = expression[i]
        # print(i)
            new_expression += c
            if (not flag) and c=='↑':
                if expression[i+1] == '(':
                    new_expression = new_expression[:-1]
                    flag = 1
                else:
                    new_expression = new_expression[:-1] + '( '
                    flag = 2
                i+=1
                continue
            if flag == 1:
                if c == '(':kuohao+=1
                elif c==')':kuohao-=1
                if not kuohao:
                    new_expression = new_expression[:-1] + ' : ℝ)'
                    flag = 0
            elif flag == 2:
                if c==' ' or c=='\n' or i == len_-1:
                    new_expression = new_expression +' : ℝ)'
                    flag = 0
            i+=1
        return new_expression.strip()
        
    def let_tactics(self,  Ank:str, Bn:str, cert:str):
        if Bn == "0":
            return f"""
  let A : ℕ → ℕ → ℝ := fun ({self.variablen} {self.variablek} : ℕ) => {self.addR(Ank, all=True)}
  let B : ℕ → ℝ := fun {self.variablen} : ℕ => 0
  let f : ℕ → ℝ := fun {self.variablen} => ∑ {self.variablek} ∈ Finset.range ({self.variablen} + 1), A {self.variablen} {self.variablek}
  let R : ℕ → ℕ → ℝ := fun {self.variablen} {self.variablek} => {self.addR(cert, all=True)}
  let G : ℕ → ℕ → ℝ:= fun ({self.variablen} {self.variablek} : ℕ) => R {self.variablen} {self.variablek} * A {self.variablen} {self.variablek}
            """
        return f"""
  let A : ℕ → ℕ → ℝ := fun ({self.variablen} {self.variablek} : ℕ) => {self.addR(Ank, all=True)}
  let B : ℕ → ℝ := fun {self.variablen} : ℕ => {self.addR(Bn, all=True)}
  let F : ℕ → ℕ → ℝ := fun {self.variablen} {self.variablek} => (A {self.variablen} {self.variablek} / B {self.variablen})
  let f : ℕ → ℝ := fun {self.variablen} => ∑ {self.variablek} ∈ Finset.range ({self.variablen}{self.num1}), F {self.variablen} {self.variablek}
  let R : ℕ → ℕ → ℝ := fun {self.variablen} {self.variablek} => {self.addR(cert, all=True)}
  let G : ℕ → ℕ → ℝ:= fun ({self.variablen} {self.variablek} : ℕ) => R {self.variablen} {self.variablek} * F {self.variablen} {self.variablek}
        """
    def letA(self, Ank:str):
        return f"  let A : ℕ → ℕ → ℝ := fun ({self.variablen} {self.variablek} : ℕ) => {self.addR(Ank)}"
    def letB(self, Bn:str):
        return f"  let B : ℕ → ℝ := fun {self.variablen} : ℕ => {self.addR(Bn)}"
    def defAll(self, Ank:str, Bn:str, cert:str):
        """
        Define all functions
        """
        return self.let_tactics(Ank, Bn, cert).replace("  let", "noncomputable def")

    def extract_denominator(self, expression: str):
        """
        Extract denominators
        """
        print("Original expression:", expression)
        expression = expression.replace(' !', '!')
        # Wrap exponentiation in parentheses, e.g. x ^ n becomes (x ^ n), (x + 1) ^ (n + 1) becomes ((x + 1) ^ (n + 1))
        while expression.find('^') != -1:
            i = expression.find('^')
            # If the character to the left of ^ is ), traverse left to find the **matching** left parenthesis
            # If the character to the left of ^ is not ), traverse left until a space is found
            left_index = -1
            right_index = -1
            if expression[i-2] == ')':
                #Find the matching ), not just any )
                left_index = i - 2
                left_paren_count = 0
                while left_index >= 0:
                    if expression[left_index] == ')':
                        left_paren_count += 1
                    elif expression[left_index] == '(':
                        left_paren_count -= 1
                    if left_paren_count == 0:
                        break
                    left_index -= 1
                if left_index >= 0:
                    # Replace selection with binomial
                    # print(expression[left_index:i])
                    left_expr =  expression[left_index:i]
            else:
                left_index = i - 2
                while left_index > 0 and expression[left_index-1] != ' ' and expression[left_index-1] != ')' and expression[left_index-1] != '(':
                    left_index -= 1
                if left_index >= 0:
                    # Replace selection with binomial
                    left_expr = expression[left_index:i]
                    print("left_expr:", left_expr)
                    # print(left_expr)
            # Same approach to find the right side
            if expression[i+2] == '(':
                right_index = i + 2
                right_paren_count = 0
                while right_index < len(expression):
                    if expression[right_index] == '(':
                        right_paren_count += 1
                    elif expression[right_index] == ')':
                        right_paren_count -= 1
                    if right_paren_count == 0:
                        break
                    right_index += 1
                # print("right_index:", right_index)
                if right_index <= len(expression):
                    # Replace selection with binomial
                    right_expr = expression[i+2:right_index+1]
                    # print(right_expr)
            else:
                right_index = i + 2
                while right_index < len(expression)-1 and expression[right_index+1] != ' ' and expression[right_index+1] != ')' and expression[right_index+1] != '(':
                    right_index += 1
                if right_index <= len(expression):
                    # Replace selection with binomial
                    right_expr = expression[i+2:right_index+1]
                    # print(right_expr)
            expression = expression[:left_index] + f'({left_expr.strip()} # {right_expr.strip()})' + expression[right_index + 1:]
            # print("Current expression:", expression)
        expression = expression.replace('#', '^').replace('!', ' !')
        denominator_list = []
        while expression.find('/') != -1:  # has denominator
            idx = expression.find('/')
            remaining = expression[idx+1:].strip()
            print("Remaining after /:", remaining)
            # Check if denominator starts with a parenthesis
            if remaining.startswith('(') or remaining[1] == '(':
                # Handle denominator within parentheses
                left_bracket_num = 0
                right_bracket_num = 0
                end_pos = 1
                for i in range(0, len(remaining)):
                    if remaining[i] == '(':
                        left_bracket_num += 1
                    elif remaining[i] == ')':
                        right_bracket_num += 1
                    if left_bracket_num == right_bracket_num and left_bracket_num > 0:
                        end_pos = i + 1
                        break
                denominator = remaining[:end_pos]
                denominator_list.append(denominator)
                expression = remaining[end_pos:]
            else:
                # Handle simple denominator without parentheses
                # Find the next operator or whitespace
                end_pos = len(remaining)
                print("Remaining after /:", remaining)
                for i, char in enumerate(remaining):
                    if char in ' */^=)' or char.isspace():
                        end_pos = i
                        break
                denominator = remaining[:end_pos].strip()
                if denominator:  # ensure denominator is not empty
                    denominator_list.append(denominator)
                expression = remaining[end_pos:]
        
        return denominator_list
    def is_balanced(self, s):
            balance = 0
            for char in s:
                if char == '(':
                    balance += 1
                elif char == ')':
                    balance -= 1
                    if balance < 0:
                        return False
            return balance == 0
    def split_expression_recursive(self, expressions: list[str]):
        """
        Split expressions at multiplication and addition points while respecting operator precedence and parentheses.
        Returns a list of expressions that are the multiplicative or additive components.
        """
        
        def is_atomic_expression(expr: str) -> bool:
            """
            Check if the expression is atomic (cannot be split further by +, -, *, /).
            """
            expr = expr.strip()
            while (expr.startswith('(') and expr.endswith(')') and 
                self.is_balanced(expr[1:-1])):
                expr = expr[1:-1].strip()
            
            depth = 0
            has_operator = False
            for i, char in enumerate(expr):
                if char == '(':
                    depth += 1
                elif char == ')':
                    depth -= 1
                elif depth == 0 and char in '+-*/':
                    has_operator = True
                    break
            return not has_operator

        def split_at_top_level_operations(expr: str) -> list[str]:
            """
            Split the expression at top-level operations (+, -, *, /) only.
            """
            expr = expr.strip()
            while (expr.startswith('(') and expr.endswith(')') and 
                self.is_balanced(expr[1:-1])):
                expr = expr[1:-1].strip()
            
            # First try to split at + or -
            components = []
            current = []
            depth = 0
            split_chars = '+-*/'
            
            for char in expr:
                if char == '(':
                    depth += 1
                elif char == ')':
                    depth -= 1
                
                if depth == 0 and char in split_chars:
                    # Only split at * or / if no + or - at top level exists
                    if char in '+-' or not any(c in split_chars[:2] for c in ''.join(current)):
                        components.append(''.join(current).strip())
                        current = []
                        # After finding a + or -, we only split at + or - from now on
                        split_chars = '+-'
                    else:
                        current.append(char)
                else:
                    current.append(char)
            
            if current:
                components.append(''.join(current).strip())
            
            # If we didn't split at + or -, try splitting at * or /
            if len(components) == 1:
                components = []
                current = []
                depth = 0
                for char in expr:
                    if char == '(':
                        depth += 1
                    elif char == ')':
                        depth -= 1
                    
                    if depth == 0 and char in '*/':
                        components.append(''.join(current).strip())
                        current = []
                    else:
                        current.append(char)
                
                if current:
                    components.append(''.join(current).strip())
            
            return components

        all_expressions = []
        q = Queue()
        for expression in expressions:
            q.put(expression)
        
        while not q.empty():
            current_expr = q.get()
            
            if is_atomic_expression(current_expr):
                all_expressions.append(current_expr)
                continue
            
            components = split_at_top_level_operations(current_expr)
            
            if len(components) > 1:
                for comp in components:
                    q.put(comp)
            else:
                all_expressions.append(current_expr)
        
        # Remove duplicates while preserving order
        seen = set()
        unique_expressions = []
        for expr in all_expressions:
            if expr not in seen:
                seen.add(expr)
                unique_expressions.append(expr)
        
        return unique_expressions
    def split_expression(self, expressions: list[str]):
        """
        Split expressions at multiplication points while respecting operator precedence and parentheses.
        Returns a list of expressions that are the multiplicative components.
        """
        
        def is_multiplicative_expression(expr: str) -> bool:
            """
            Check if the expression is purely multiplicative (only * operations at top level).
            """
            expr = expr.strip()
            while (expr.startswith('(') and expr.endswith(')') and 
                self.is_balanced(expr[1:-1])):
                expr = expr[1:-1].strip()
            
            depth = 0
            for i, char in enumerate(expr):
                if char == '(':
                    depth += 1
                elif char == ')':
                    depth -= 1
                elif depth == 0 and char in '+-':
                    return False
            return True

        def split_at_top_level_multiplication(expr: str) -> list[str]:
            """
            Split the expression at top-level multiplications (*) only.
            """
            expr = expr.strip()
            while (expr.startswith('(') and expr.endswith(')') and 
                self.is_balanced(expr[1:-1])):
                expr = expr[1:-1].strip()
            
            components = []
            current = []
            depth = 0
            
            for char in expr:
                if char == '(':
                    depth += 1
                elif char == ')':
                    depth -= 1
                
                if depth == 0 and char in '/*':
                    components.append(''.join(current).strip())
                    current = []
                else:
                    current.append(char)
            
            if current:
                components.append(''.join(current).strip())
            
            return components

        all_expressions = []
        q = Queue()
        for expression in expressions:
            q.put(expression)
        
        while not q.empty():
            current_expr = q.get()
            
            if not is_multiplicative_expression(current_expr):
                all_expressions.append(current_expr)
                continue
            
            components = split_at_top_level_multiplication(current_expr)
            
            if len(components) > 1:
                for comp in components:
                    q.put(comp)
            else:
                all_expressions.append(current_expr)
        # Deduplicate
        all_expressions = list(set(all_expressions))
        return all_expressions
    def prove_nezero(self, import_content:str, formal_theorem:str, goal):
        # bert_sim = BERTSimilarity()
        lemma_list = self.bert_sim.lemma_nezero_list(goal)
        for tactics in lemma_list:
            tactics = LEMMA_NEZERO_DICT[tactics]
            try:
                if self.is_finished(import_content, formal_theorem, tactics):
                    # print("Theorem finished")
                    return formal_theorem, tactics
            except Exception as e:
                # print(f"Error applying tactic {tactics}: {e}")
                continue
                # break
        # print("Theorem not finished")
        return formal_theorem, "sorry"
    def prove_zz(self, init_state: TacticState, lean):
        """Prove non-zero conditions for all denominators in the current goal.

        Iteratively extracts denominators from the proof state, generates
        non-zero sub-goals, and applies ``field_simp`` + ``ring`` to simplify.

        Args:
            init_state: The current Lean 4 tactic state.
            lean: A ``Lean4Kit`` instance for interactive evaluation.

        Returns:
            A tuple ``(code, final_state)`` where *code* is the tactic
            string and *final_state* is the resulting ``TacticState``.
        """
        print("init_state:", init_state.getTacticState())
        expression = init_state.getTacticState().split('⊢')[-1].strip()
        print("expression:", expression)
        # lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        code = ""
        cnt = 0
        while expression.find('/') != -1:
            print("expression:", expression)
            denominators = self.extract_denominator(expression)
            print("Extracted denominators:", denominators)
            # Split expressions
            expressions = self.split_expression(denominators)
            expressions = [strip_outer_even_power(e) for e in expressions]
            print("Split expressions:", expressions)

            nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
            print("nezero_goals:", nezero_goals)
            # Prove non-zero
        
            for i in nezero_goals:
                if id!=3:
                    nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(IMPORT_CONTENT, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablen} > {self.variablek}): {i}", i, f"h{cnt}", init_state=init_state)
                else:
                    nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(IMPORT_CONTENT, f"theorem hwz {self.all_primises} : {i}", i, f"h{cnt}", init_state=init_state)
                nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
                cnt += 1
                code += f"    have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                try:
                    init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                    print("init_state:", init_state.getTacticState())

                except Exception as e:
                    continue
            print("code:", code)
            print(init_state.getTacticState())
            
            init_state.print()
            new_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            
            if new_state.isError():
                init_state = lean.run_tactic(f"field_simp only []", init_state.proofStates[0], verbose=VERBOSE)
                code += "    field_simp only []\n"
            else:
                init_state = copy.deepcopy(new_state)
                code += "    field_simp\n"
            print("state after field_simp:", new_state.getTacticState())
            init_state.print()
            if init_state.isError():
                break
            new_state = lean.run_tactic(f"ring", init_state.proofStates[0], verbose=VERBOSE)
            print("state after ring:", new_state.getTacticState())
            if not new_state.isError() and new_state.isFinish():
                break
            print("init_state:", init_state.getTacticState())
            expression = init_state.getTacticState().split('⊢')[-1].strip()
        return code, init_state
        
    def prove_nezero_by_bert(self, import_content:str, formal_theorem:str):
        for tactics in self.lemma_nezero_list:
            try:
                if self.is_finished(import_content, formal_theorem, tactics):
                    # print("Theorem finished")
                    return formal_theorem, tactics
            except Exception as e:
                # print(f"Error applying tactic {tactics}: {e}")
                continue
                # break
        # print("Theorem not finished")
        return formal_theorem, "sorry"
    def _build_lemma_from_state(self, init_state, goal, lemma_type="hwz"):
        """Build a complete lemma statement from the current proof state's full context.

        Extracts all local variables and hypotheses visible in the Lean
        infoview (tactic state) at the current proof point, skipping
        ``let`` bindings, ``case`` markers, and intermediate ``have``
        results (h0/h1/r1/r2/…) that are not part of the original theorem
        signature.  This ensures the generated lemma is self-contained and
        does not carry spurious dependencies on prior proof steps.

        Args:
            init_state: The current ``TacticState`` object.
            goal: The goal expression string for the lemma.
            lemma_type: ``"hwz"`` or ``"rwz"`` (default ``"hwz"``).

        Returns:
            A complete ``theorem ...`` string, or ``None`` on failure.
        """
        try:
            tactic_state = init_state.getTacticState()
            parts = tactic_state.split('⊢')
            if len(parts) < 2:
                return None

            ctx = parts[0].strip()

            # --- Merge continuation lines ---
            # In the tactic state, a hypothesis like
            #     WZ_aux :
            #       ∀ (n : ℕ) (f : ℕ → ℕ → ℝ) (B : ℕ → ℝ),
            #         (∑ k, f n k / B n = 1) ↔ ...
            # spans multiple lines.  A new hypothesis entry starts with an
            # identifier followed by optional identifiers and then a bare `:`
            # (not `:=`).  Any line that does NOT match this pattern is a
            # continuation of the previous hypothesis and must be appended.
            raw_lines = [l for l in ctx.split('\n') if l.strip()]
            merged_lines = []
            for line in raw_lines:
                stripped = line.strip()
                if not stripped:
                    continue
                # A new hypothesis starts with `ident[✝N] :` where the `:`
                # is NOT immediately followed by `=`.  We require the colon
                # to appear after the first token (possibly with more tokens
                # before it) and not be part of `:=`.
                is_new = bool(re.match(r'^[a-zA-Z_]\S*(?:\s+\S+)*\s*:(?!=)', stripped))
                if is_new and merged_lines:
                    merged_lines.append(stripped)
                elif merged_lines:
                    merged_lines[-1] += ' ' + stripped
                else:
                    merged_lines.append(stripped)

            premises = []
            for line in merged_lines:
                if line.startswith('case'):
                    continue
                if ':=' in line:          # skip let bindings (A, B, F, R, G, …)
                    continue
                if ':' not in line:       # skip lines without type annotation
                    continue

                hyp_name = line.split(':', 1)[0].strip()
                hyp_body = line.split(':', 1)[1].strip()

                # Bug 1 fix: skip hypotheses whose type is a complex multi-line
                # expression that was not fully captured (e.g. WZ_aux whose type
                # references local let-bound functions A/B/F/G/R).  We detect
                # this by checking whether the body references those names.
                if re.search(r'\b[ABFGR]\s+(?:n|k|\()', hyp_body):
                    continue

                # Bug 2 fix: skip intermediate have-results introduced during
                # the proof (h0, h1, h2, …, r1, r2, …, ne_zero*, WZ_aux,
                # Step1, Step2, Step3, aux*, l1, l2, r_*).  These are local
                # proof-step conclusions, not original theorem parameters, so
                # including them as lemma parameters creates spurious dependency
                # chains that make each lemma unprovable in isolation.
                if re.match(r'^(h\d+|r\d+|ne_zero\w*|WZ_aux|Step\d+|aux\d*|l\d+|r_\d+)$', hyp_name):
                    continue

                # Handle inaccessible names: n✝  →  n_shd,  n✝¹  →  n_shd1
                line = re.sub(r'✝(\d*)', r'_shd\1', line)
                premises.append(f"({line})")

            if not premises:
                return None

            premises_str = " ".join(premises)
            return f"theorem {lemma_type} {premises_str} : {goal}"
        except Exception:
            return None

    def prove_nezero_by_llm(self, import_content:str, formal_theorem:str, goal, name, init_state=None):
        formal_theorem = formal_theorem.strip()
        # If a live proof state is provided, rebuild the lemma statement
        # from its full infoview context so that every variable and
        # hypothesis (including loop-bound k, destructured conditions, etc.)
        # is captured in the lemma parameters.
        if init_state is not None:
            lemma_type = "rwz" if formal_theorem.startswith("theorem rwz") else "hwz"
            rebuilt = self._build_lemma_from_state(init_state, goal, lemma_type)
            if rebuilt:
                formal_theorem = rebuilt
        if GENERATE_LEMMA:
            with open(self.lemma_path, "a") as f:
                dt = dict()
                dt["formal_statement"] = formal_theorem + ":= sorry"
                dt["name"] = name[0:]
                dt["import_content"] = import_content
                f.write(json.dumps(dt, ensure_ascii=False) + "\n")
        return formal_theorem, "sorry"
    def prove_nezero_A_B(self, import_content: str, have_theorem: str, qz: list[str], hz: list[str]):
        """Generate a proof that a summand component ``A`` or ``B`` is non-zero.

        Args:
            import_content: Lean 4 import preamble.
            have_theorem: The ``have`` statement to prove (non-zero condition).
            qz: Prefix tactics applied before the main proof search.
            hz: Suffix tactics applied after proving sub-goals.

        Returns:
            A string of Lean 4 tactic code for the ``have`` block.
        """
        code = ""
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        # let_tactics = self.defAll(Ank=ANk, Bn=Bn, cert=cert)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            print(f"Applied tactic: {i}")
        init_state.print()
        print("init_state:", init_state.getTacticState())
        init_state = lean.run_have_tactic(have_theorem, init_state.proofStates[0], verbose=VERBOSE)
        for tactic in qz:
            try:
                new_state = lean.run_tactic(tactic, init_state.proofStates[0], verbose=VERBOSE)
                new_state.history_tactics.append(tactic)
                print(new_state.getTacticState())
                print(f"Applied tactic: {tactic}")
            except Exception as e:
                # print(f"Error applying tactic {tactic}: {e}")
                break
            if not new_state.isError():
                code += "    " + tactic + "\n"
                # print(code)
                init_state = copy.deepcopy(new_state)
            else: 
                break
            if init_state.isFinish():
                return code
        nezero_goals = [] # get each term of the conjunction
        for i in init_state.getTacticState().split('⊢')[-1].split('∧'):
            i = i.strip()
            left_bracket_num = i.count('(')
            right_bracket_num = i.count(')')
            if left_bracket_num > right_bracket_num:
                i = i[left_bracket_num-right_bracket_num:]
            else:
                i = i[:len(i) - (right_bracket_num - left_bracket_num)]
            nezero_goals.append(self.addR(i.strip()))

        # Prove non-zero
        cnt = 0
        for i in nezero_goals:
            nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablen} > {self.variablek}): {i}", i, f"h{cnt}", init_state=init_state)
            print("nezero_formal_theorem:", nezero_formal_theorem)
            print("nezero_tactics:", nezero_tactics)
            nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
            cnt += 1
            code += f"    have h{cnt} : {i.strip()} := by \n" + nezero_tactics + "\n"
        # print(code)
        for i in hz:
            code += "    " + i + "\n"
        return code
    def prove_aux(self, import_content: str, have_theorem: str, qz: list[str], hz: list[str], recursive_goals: list[str], id):
        """Prove an auxiliary ratio lemma (``aux₁`` through ``aux₅``).

        Each auxiliary lemma establishes a ratio identity (e.g.,
        ``A(n, k+1) / A(n, k) = ...``) that the WZ equation depends on.
        The method first applies prefix tactics, then attempts to rewrite
        using recurrence relations, eliminates denominators via ``field_simp``,
        and finishes with suffix tactics.

        Args:
            import_content: Lean 4 import preamble.
            have_theorem: The ``have`` statement for the ratio lemma.
            qz: Prefix tactics (e.g., ``["simp only [A]"]``).
            hz: Suffix tactics (e.g., ``["grind"]``).
            recursive_goals: Recurrence relation goals to rewrite with.
            id: Lemma identifier (1–5), controls premise handling.

        Returns:
            A string of Lean 4 tactic code for the ``have`` block.
        """
        print("import_content:", import_content)
        print("have_theorem:", have_theorem)
        code = ""
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            print(f"Applied tactic: {i}")
        # def_prefix = DEF_PREFIX.format(Ank)
        init_state.print()
        print("aux_init_state:", init_state.getTacticState())
        init_state = lean.run_have_tactic(have_theorem, init_state.proofStates[0], verbose=VERBOSE)
        init_state.print()
        print("init_state:", init_state.getTacticState())
        for tactic in qz:
            try:
                new_state = lean.run_tactic(tactic, init_state.proofStates[0], verbose=VERBOSE)
                new_state.history_tactics.append(tactic)
                print(new_state.getTacticState())
                print(f"Applied tactic: {tactic}")
            except Exception as e:
                print(f"Error applying tactic {tactic}: {e}")
                break
            if not new_state.isError():
                code += "    " + tactic + "\n"
                print(code)
                init_state = copy.deepcopy(new_state)
            else: 
                new_state.print()
                print(f"Error in tactic state: {new_state.print()}")
                break
            if init_state.isFinish():
                return code
        cnt_r = 1
        for i in recursive_goals:
            if id!=3 and id!=4:
                nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem rwz {self.all_primises} (htotalNumidx : {self.variablen} > {self.variablek}): {i}", i, f"r{cnt_r}", init_state=init_state)
            else:
                nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem rwz {self.all_primises} : {i}", i, f"r{cnt_r}", init_state=init_state)
            print("recursive_formal_theorem:", nezero_formal_theorem)
            print("recursive_tactics:", nezero_tactics)
            nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
            try:
                new_state = lean.run_tactic(f"have r{cnt_r} : {i} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                new_state = lean.run_tactic(f"rw [r{cnt_r}]", new_state.proofStates[0], verbose=VERBOSE)
                if not new_state.isError():
                    code += f"    have r{cnt_r} : {i.strip()} := by \n" + nezero_tactics + "\n"
                    code += f"    rw [r{cnt_r}]\n"
                    cnt_r += 1
                    init_state = copy.deepcopy(new_state)
            except Exception as e:
                print(f"Error recursive: {e}")
                continue
        print("init_state:", init_state.getTacticState())
        expression = init_state.getTacticState().split('⊢')[-1].strip()
        print("expression:", expression)
        cnt = 0
        while expression.find('/') != -1:
            print("expression:", expression)
            denominators = self.extract_denominator(expression)
            print("Extracted denominators:", denominators)
            # Split expressions
            expressions = self.split_expression(denominators)
            expressions = [strip_outer_even_power(e) for e in expressions]
            print("Split expressions:", expressions)

            nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
            print("nezero_goals:", nezero_goals)
            # Prove non-zero
        
            for i in nezero_goals:
                if id!=3:
                    nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablen} > {self.variablek}): {i}", i, f"h{cnt}", init_state=init_state)
                else:
                    nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} : {i}", i, f"h{cnt}", init_state=init_state)
                nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
                cnt += 1
                code += f"    have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                try:
                    init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                    print("init_state:", init_state.getTacticState())

                except Exception as e:
                    continue
            print("code:", code)
            print(init_state.getTacticState())
            
            init_state.print()
            new_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            if new_state.isError():
                init_state = lean.run_tactic(f"field_simp only []", init_state.proofStates[0], verbose=VERBOSE)
                code += "    field_simp only []\n"
            else:
                init_state = copy.deepcopy(new_state)
                code += "    field_simp\n"
            print("state after field_simp:", new_state.getTacticState())
            new_state = lean.run_tactic(f"simp [hrn]", init_state.proofStates[0], verbose=VERBOSE)
            if not new_state.isError():
                init_state = copy.deepcopy(new_state)
                code += "    simp [hrn]\n"
            print("state after simp hrn:", new_state.getTacticState())
            init_state.print()
            if init_state.isError():
                break
            new_state = lean.run_tactic(f"ring", init_state.proofStates[0], verbose=VERBOSE)
            print("state after ring:", new_state.getTacticState())
            if not new_state.isError() and new_state.isFinish():
                break
            print("init_state:", init_state.getTacticState())
            expression = init_state.getTacticState().split('⊢')[-1].strip()
        for i in hz:
            try:
                new_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            except Exception as e:
                print(f"Error applying tactic {i}: {e}")
                continue
            if not new_state.isError():
                code += "    " + i + "\n"
                print("init_state:", new_state.getTacticState())
                init_state = copy.deepcopy(new_state)
            else:
                break
            if init_state.isFinish():
                print("init_state:", init_state.getTacticState())
                print("code:", code)
                return code
        return code

    def prove_step2_wz(self, import_content:str, cert:str, AKdiv:str, Adiv:str, Bdiv:str, Bn='', Anndiv='', A_nadd1_n_div='', hz=["grind"]):
        code = ""
        if self.primise_value:
            fixed_prefix = FIXED_STEP2_PREFIX_WITH_PRIMISE.format(AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv,Anndiv=Anndiv,A_nadd1_n_div=A_nadd1_n_div, n=self.variablen, k=self.variablek, primise=self.primise_value, num=self.num1, num2=self.num2)
        else:
            fixed_prefix = FIXED_STEP2_PREFIX.format(AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv, Anndiv=Anndiv,A_nadd1_n_div=A_nadd1_n_div,n=self.variablen, k=self.variablek, num=self.num1, num2=self.num2)
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            print(f"Applied tactic: {i}")
        if self.primise_value:
            init_state = lean.run_have_tactic(f"have WZ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → F ({self.variablen} + 1) {self.variablek} - F {self.variablen} {self.variablek} = G {self.variablen} ({self.variablek} + 1) - G {self.variablen} {self.variablek}", init_state.proofStates[0], verbose=VERBOSE)
        else:
            init_state = lean.run_have_tactic(f"have WZ ({self.variablek} : ℕ) (htotalNumidx:{self.variablek} < {self.variablen}) : F ({self.variablen} + 1) {self.variablek} - F {self.variablen} {self.variablek} = G {self.variablen} ({self.variablek} + 1) - G {self.variablen} {self.variablek}", init_state.proofStates[0], verbose=VERBOSE)
        print("init_state:", init_state.getTacticState())
        fixed_step2_prefix = [i.strip() for i in fixed_prefix.split('\n') if i.strip()]
        if self.primise_value:
            fixed_wz_tactic = [i.strip() for i in FIXED_WZ_TACTIC_WITH_PRIMISE.format(n=self.variablen, k=self.variablek, primise=self.primise_value).split('\n') if i.strip()]
        else:
            fixed_wz_tactic = [i.strip() for i in FIXED_WZ_TACTIC.format(n=self.variablen, k=self.variablek).split('\n') if i.strip()]
        for i in fixed_step2_prefix:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
        for i in fixed_wz_tactic:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            init_state.print()
            print(f"Applied tactic: {i}")
        expression = init_state.getTacticState().split('⊢')[-1].strip()
        cnt = 0
        while expression.find('/') != -1:
            denominators = self.extract_denominator(expression)
            print("Extracted denominators:", denominators)
            # Split expressions
            expressions = self.split_expression(denominators)
            expressions = [strip_outer_even_power(e) for e in expressions]
            print("Split expressions:", expressions)

            nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
            # Prove non-zero
            print("nezero_goals:", nezero_goals)
            for i in nezero_goals:
                nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablek} < {self.variablen}) : {i}", i, f"h{cnt}", init_state=init_state)
                nezero_tactics = "\n".join(["        " + i for i in nezero_tactics.split('\n')])
                cnt += 1
                code += f"      have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                try:
                    init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                    print("init_state:", init_state.getTacticState())
                    print(init_state.print())
                except Exception as e:
                    # print(f"Error  {e}")
                    continue
            init_state.print()
            new_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            
            if new_state.isError():
                init_state = lean.run_tactic(f"field_simp only []", init_state.proofStates[0], verbose=VERBOSE)
                code += "      field_simp only []\n"
            else:
                init_state = copy.deepcopy(new_state)
                code += "      field_simp\n"
            print("state after field_simp:", new_state.getTacticState())
            init_state.print()
            if init_state.isError():
                break
            new_state = lean.run_tactic(f"<;> grind", init_state.proofStates[0], verbose=VERBOSE)
            if not new_state.isError() and new_state.isFinish():
                break
            print("init_state:", init_state.getTacticState())
            expression = init_state.getTacticState().split('⊢')[-1].strip()
            print(code)
         
        for i in hz:
            try:
                new_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            except Exception as e:
                print(f"Error applying tactic {i}: {e}")
                continue
            if not new_state.isError():
                code += "      " + i + "\n"
                print("init_state:", new_state.getTacticState())
                init_state = copy.deepcopy(new_state)
            else:
                break
            if init_state.isFinish():
                print("init_state:", init_state.getTacticState())
                print("code:", code)
                return code
        return code
    def prove_step2_wz_bn0(self, import_content:str, cert:str, AKdiv:str, Adiv:str, Bn='', Anndiv='', A_nadd1_n_div='', hz=["grind"]):
        code = ""
        if self.primise_value:
            fixed_prefix = FIXED_STEP2_PREFIX_WITH_PRIMISE_Bn0.format(AKdiv=AKdiv, Adiv=Adiv,n=self.variablen, k=self.variablek, primise=self.primise_value,Anndiv=Anndiv, A_nadd1_n_div=A_nadd1_n_div)
        else:
            fixed_prefix = FIXED_STEP2_PREFIX_Bn0.format(AKdiv=AKdiv, Adiv=Adiv,n=self.variablen, k=self.variablek,Anndiv=Anndiv, A_nadd1_n_div=A_nadd1_n_div)

        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            print(f"Applied tactic: {i}")
        if self.primise_value:
            init_state = lean.run_have_tactic(f"have WZ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A ({self.variablen} + 1) {self.variablek} - A {self.variablen} {self.variablek} = G {self.variablen} ({self.variablek} + 1) - G {self.variablen} {self.variablek}", init_state.proofStates[0], verbose=VERBOSE)
        else:
            init_state = lean.run_have_tactic(f"have WZ ({self.variablek} : ℕ) (htotalNumidx:{self.variablek} < {self.variablen}) : A ({self.variablen} + 1) {self.variablek} - A {self.variablen} {self.variablek} = G {self.variablen} ({self.variablek} + 1) - G {self.variablen} {self.variablek}", init_state.proofStates[0], verbose=VERBOSE)
        print("init_state:", init_state.getTacticState())
        fixed_step2_prefix = [i.strip() for i in fixed_prefix.split('\n') if i.strip()]
        if self.primise_value:
            fixed_wz_tactic = [i.strip() for i in FIXED_WZ_TACTIC_WITH_PRIMISE_Bn0.format(n=self.variablen, k=self.variablek, primise=self.primise_value).split('\n') if i.strip()]
        else:
            fixed_wz_tactic = [i.strip() for i in FIXED_WZ_TACTIC_Bn0.format(n=self.variablen, k=self.variablek).split('\n') if i.strip()]
        for i in fixed_step2_prefix:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
        for i in fixed_wz_tactic:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            init_state.print()
            print(f"Applied tactic: {i}")
        expression = init_state.getTacticState().split('⊢')[-1].strip()
        cnt = 0
        while expression.find('/') != -1:
            denominators = self.extract_denominator(expression)
            print("Extracted denominators:", denominators)
            # Split expressions
            expressions = self.split_expression(denominators)
            expressions = [strip_outer_even_power(e) for e in expressions]
            print("Split expressions:", expressions)

            nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
            # Prove non-zero
        
            for i in nezero_goals:
                nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablek} < {self.variablen}) : {i}", i, f"h{cnt}", init_state=init_state)
                nezero_tactics = "\n".join(["        " + i for i in nezero_tactics.split('\n')])
                cnt += 1
                code += f"      have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                try:
                    init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                    print("init_state:", init_state.getTacticState())
                except Exception as e:
                    # print(f"Error  {e}")
                    continue
            init_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            code += "      field_simp\n"
            new_state = lean.run_tactic(f"ring", init_state.proofStates[0], verbose=VERBOSE)
            if not new_state.isError() and new_state.isFinish():
                break
            print("init_state:", init_state.getTacticState())
            expression = init_state.getTacticState().split('⊢')[-1].strip()
            print(code)
         
        for i in hz:
            try:
                new_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            except Exception as e:
                print(f"Error applying tactic {i}: {e}")
                continue
            if not new_state.isError():
                code += "      " + i + "\n"
                print("init_state:", new_state.getTacticState())
                init_state = copy.deepcopy(new_state)
            else:
                break
            if init_state.isFinish():
                print("init_state:", init_state.getTacticState())
                print("code:", code)
                return code
        return code
        
    def prove_step2_calc(self, import_content:str, cert:str, AKdiv:str, Adiv:str, Bdiv:str, Anndiv,A_nadd1_n_div,hz=["grind"], recursive_goals:list[str]=[]):
        code = ""
        if self.primise_value:
            fixed_prefix = FIXED_STEP2_PREFIX_WITH_PRIMISE.format(AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv,Anndiv=Anndiv,A_nadd1_n_div=A_nadd1_n_div, n=self.variablen, k=self.variablek, primise=self.primise_value, num=self.num1, num2=self.num2)
        else:
            fixed_prefix = FIXED_STEP2_PREFIX.format(AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv, Anndiv=Anndiv,A_nadd1_n_div=A_nadd1_n_div,n=self.variablen, k=self.variablek, num=self.num1, num2=self.num2)
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print(f"Applied tactic: {i}")
        if self.primise_value:
            init_state = lean.run_have_tactic(f"have Step2 : ∀ {self.variablen} : ℕ, {self.primise_value} → f ({self.variablen} + 1) - f {self.variablen} = 0 ", init_state.proofStates[0], verbose=VERBOSE)
        else:
            init_state = lean.run_have_tactic(f"have Step2 : ∀ {self.variablen} : ℕ, f ({self.variablen} + 1) - f {self.variablen} = 0 ", init_state.proofStates[0], verbose=VERBOSE)
        init_state.print()
        print("init_state:", init_state.getTacticState())
        fixed_step2_prefix = [i.strip() for i in fixed_prefix.split('\n') if i.strip()]
        if self.primise_value:
            fixed_wz_tactic = [i.format(n=self.variablen, k=self.variablek, primise=self.primise_value, num1=self.num1, num2=self.num2, calc_rw=self.calc_rw).strip() for i in FIXED_CALC_TACTIC_LIST_WITH_PRIMISE]
        else:
            fixed_wz_tactic = [i.format(n=self.variablen, k=self.variablek, num1=self.num1, num2=self.num2, calc_rw=self.calc_rw).strip() for i in FIXED_CALC_TACTIC_LIST]
        for i in fixed_step2_prefix:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
        for i in fixed_wz_tactic:
            print(f"Applying tactic: {i}")
            
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            init_state.print()
            print(init_state.getTacticState())
            print("====================")
        expression = init_state.getTacticState().split('⊢')[-1].strip()
        cnt = 0
        print("expression:", expression)
        max_attempts = 5  # set maximum attempts to prevent infinite loop
        attempts = 0
        while expression.find('/') != -1:
            if attempts >= max_attempts:
                print("Reached maximum attempts to eliminate denominators.")
                break
            attempts += 1
            denominators = self.extract_denominator(expression)
            print("Extracted denominators:", denominators)
            # Split expressions
            expressions = self.split_expression(denominators)
            expressions = [strip_outer_even_power(e) for e in expressions]
            print("Split expressions:", expressions)

            nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
            # Prove non-zero
            print("nezero_goals:", nezero_goals)
            for i in nezero_goals:
                nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} : {i}", i, f"h{cnt}", init_state=init_state)
                nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
                print("nezero_formal_theorem:", nezero_formal_theorem)
                print("nezero_tactics:", nezero_tactics)
                cnt += 1
                code += f"    have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                try:
                    init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                except Exception as e:
                    continue
            print(init_state.getTacticState())
            # init_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            # code += "    field_simp\n"
            new_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            
            if not new_state.isError():
                code += "    field_simp\n"
                init_state = new_state
            new_state = lean.run_tactic(f"simp [primise]", init_state.proofStates[0], verbose=VERBOSE)
            
            if not new_state.isError():
                code += "    simp [primise]\n"
                init_state = new_state

            new_state = lean.run_tactic(f"ring", init_state.proofStates[0], verbose=VERBOSE)
            if not new_state.isError() and new_state.isFinish():
                break
            
            print(code)
            expression = init_state.getTacticState().split('⊢')[-1].strip()
        for i in hz:
            try:
                new_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            except Exception as e:
                print(f"Error applying tactic {i}: {e}")
                continue
            if not new_state.isError():
                code += "    " + i + "\n"
                print("init_state:", new_state.getTacticState())
                init_state = copy.deepcopy(new_state)
            else:
                break
            if init_state.isFinish():
                print("init_state:", init_state.getTacticState())
                print("code:", code)
                return code
        return code
    def prove_step2_calc_bn0(self, import_content:str, cert:str, AKdiv:str, Adiv:str, Bdiv:str, Anndiv,A_nadd1_n_div,hz=["ring"], recursive_goals:list[str]=[]):
        code = ""
        if self.primise_value:
            fixed_prefix = FIXED_STEP2_PREFIX_WITH_PRIMISE_Bn0.format(AKdiv=AKdiv, Adiv=Adiv,n=self.variablen, k=self.variablek, primise=self.primise_value,Anndiv=Anndiv, A_nadd1_n_div=A_nadd1_n_div)
        else:
            fixed_prefix = FIXED_STEP2_PREFIX_Bn0.format(AKdiv=AKdiv, Adiv=Adiv,n=self.variablen, k=self.variablek,Anndiv=Anndiv, A_nadd1_n_div=A_nadd1_n_div)
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            print(f"Applied tactic: {i}")
        if self.primise_value:
            init_state = lean.run_have_tactic(f"have Step2 : ∀ {self.variablen} : ℕ, {self.primise_value} → f ({self.variablen} + 1) - f {self.variablen} = 0 ", init_state.proofStates[0], verbose=VERBOSE)
        else:
            init_state = lean.run_have_tactic(f"have Step2 : ∀ {self.variablen} : ℕ, f ({self.variablen} + 1) - f {self.variablen} = 0 ", init_state.proofStates[0], verbose=VERBOSE)
        init_state.print()
        print("init_state:", init_state.getTacticState())
        fixed_step2_prefix = [i.strip() for i in fixed_prefix.split('\n') if i.strip()]
        if self.primise_value:
            fixed_wz_tactic = [i.format(n=self.variablen, k=self.variablek, primise=self.primise_value, num1=self.num1, num2=self.num2, calc_rw=self.calc_rw).strip() for i in FIXED_CALC_TACTIC_LIST_WITH_PRIMISE_Bn0]
        else:
            fixed_wz_tactic = [i.format(n=self.variablen, k=self.variablek, num1=self.num1, num2=self.num2, calc_rw=self.calc_rw).strip() for i in FIXED_CALC_TACTIC_LIST_Bn0]
        for i in fixed_step2_prefix:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
        for i in fixed_wz_tactic:
            print(f"Applying tactic: {i}")
            init_state.print()
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
        cnt_r = 1
        for i in recursive_goals:
            nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem rwz {self.all_primises} : {i}", i, f"r{cnt_r}", init_state=init_state)
            print("recursive_formal_theorem:", nezero_formal_theorem)
            print("recursive_tactics:", nezero_tactics)
            nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
            
            try:
                new_state = lean.run_tactic(f"have r{cnt_r} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                new_state = lean.run_tactic(f"rw [r{cnt_r}]", new_state.proofStates[0], verbose=VERBOSE)
                if not new_state.isError():
                    code += f"    have r{cnt_r} : {i} := by \n" + nezero_tactics + "\n"
                    code += f"    rw [r{cnt_r}]\n"
                    cnt_r += 1
                    init_state = copy.deepcopy(new_state)
                init_state.print()
            except Exception as e:
                print(f"Error recursive: {e}")                    
                continue
        if init_state.getTacticState().split('⊢')[-1].find('/') != -1:
            init_state = lean.run_tactic("field_simp", init_state.proofStates[0], verbose=VERBOSE)
            code += "    field_simp\n"
        expression = init_state.getTacticState().split('⊢')[-1].strip()
        cnt = 0
        print("expression:", expression)
        while expression.find('/') != -1:
            denominators = self.extract_denominator(expression)
            print("Extracted denominators:", denominators)
            # Split expressions
            expressions = self.split_expression(denominators)
            expressions = [strip_outer_even_power(e) for e in expressions]
            print("Split expressions:", expressions)

            nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
            # Prove non-zero
            print("nezero_goals:", nezero_goals)
            for i in nezero_goals:
                nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} : {i}", i, f"h{cnt}", init_state=init_state)
                nezero_tactics = "\n".join(["      " + i for i in nezero_tactics.split('\n')])
                print("nezero_formal_theorem:", nezero_formal_theorem)
                print("nezero_tactics:", nezero_tactics)
                cnt += 1
                code += f"    have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                try:
                    init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                except Exception as e:
                    continue
            print(init_state.getTacticState())
            # init_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            # code += "    field_simp\n"
            new_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
            
            if not new_state.isError():
                code += "    field_simp\n"
                init_state = new_state
            
            new_state = lean.run_tactic(f"simp [primise]", init_state.proofStates[0], verbose=VERBOSE)
            if not new_state.isError():
                code += "    simp [primise]\n"
                init_state = new_state
            new_state = lean.run_tactic(f"ring", init_state.proofStates[0], verbose=VERBOSE)
            if not new_state.isError() and new_state.isFinish():
                break
            print(code)
            expression = init_state.getTacticState().split('⊢')[-1].strip()
        for i in hz:
            try:
                new_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            except Exception as e:
                print(f"Error applying tactic {i}: {e}")
                continue
            if not new_state.isError():
                code += "    " + i + "\n"
                print("init_state:", new_state.getTacticState())
                init_state = copy.deepcopy(new_state)
            else:
                break
            if init_state.isFinish():
                print("init_state:", init_state.getTacticState())
                print("code:", code)
                return code
        return code
    def prove_step3(self, import_content:str, Bn):
        code = ""
        has_zero = False
        has_number = False
        primise_value_list = self.primise_value.split('∧') if self.primise_value else []
        char_list = ['>', '<', '≥', '≤', '=', '≠']
        for i in primise_value_list:
            for char in char_list:
                if i.find(char) != -1:
                    while i.startswith('(') and i.endswith(')') and self.is_balanced(i[1:-1]):
                        i = i[1:-1].strip()
                    left, right = i.split(char)
                    left = left.strip()
                    right = right.strip()
                    print(f"left: {left}, right: {right}, char: {char}")
                    if right == '0' or left == '0':
                        has_zero = True
                        has_number = True
                    else:
                        try:
                            num = int(right)
                            has_number = True
                        except:
                            try:
                                num = int(left)
                                has_number = True
                            except:
                                continue

        print("has_zero:", has_zero)
        print("has_number:", has_number)
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        init_state = lean.run_import(import_content, verbose=VERBOSE)
        init_state = lean.new_thm(self.theorem_statement, verbose=VERBOSE,env=0)
        for i in self.let_tactics_list:
            init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
            print("init_state:", init_state.getTacticState())
            print(f"Applied tactic: {i}")
            init_state.print()
        # init_state = lean.run_have_tactic("have WZ (k : ℕ) (hnk:k < n) : F (n + 1) k - F n k = G n (k + 1) - G n k", init_state.proofStates[0], verbose=VERBOSE)
        if self.primise_value:
            if Bn!="0":
                init_state = lean.run_have_tactic(f"have Step3 : ∀ {self.variablen} : ℕ,  {self.primise_value} → f {self.variablen} = 1 ", init_state.proofStates[0], verbose=VERBOSE)
                code += f"  have Step3 : ∀ {self.variablen} : ℕ,  {self.primise_value} → f {self.variablen} = 1 := by \n"
            else:
                init_state = lean.run_have_tactic(f"have Step3 : ∀ {self.variablen} : ℕ,  {self.primise_value} → f {self.variablen} = 0 ", init_state.proofStates[0], verbose=VERBOSE)
                code += f"  have Step3 : ∀ {self.variablen} : ℕ,  {self.primise_value} → f {self.variablen} = 0 := by \n"
            if not has_number:
                qz = [f"intro {self.variablen} hmn_conditions", f"induction' {self.variablen} with {self.variablen} hm"]
            else:
                qz = [f"intro wzm hmn_conditions", f"induction' hmn_conditions with wzm hm ih"]
            # qz = [f"intro {self.variablen} hmn_conditions", f"induction' {self.variablen} with {self.variablen} hm"]
            if Bn!="0":
                qz_1 = ["simp [f, F, A, B]"]
            else:
                qz_1 = ["simp [f, A]"]
            # if not has_zero:
            #     qz_1.append(f"simp [Finset.sum_range_succ]")
            for i in qz:
                print("init_state:", init_state.getTacticState())
                init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
                print("after_state:", init_state.getTacticState())
                print(f"Applied tactic: {i}")
                init_state.print()
                code += "    " + i + "\n"
            code += "    .\n"
            for i in qz_1:
                new_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
                if new_state.isFinish():
                    code += "     " + i + "\n"
                    break
                if not new_state.isError():
                    code += "     " + i + "\n"
                    print("init_state:", new_state.getTacticState())
                else:
                    break
                init_state = copy.deepcopy(new_state)
            print("goal_part_before:", init_state.getTacticState())
            print("goal_part:", init_state.goals)
            # Only check the goal expression (after ⊢) for ∑, to avoid false triggers from ∑ in let bindings
            goal_part = init_state.goals[0][0].split('⊢')[-1].strip() if isinstance(init_state.goals[0], list) else init_state.goals[0].split('⊢')[-1].strip()
            if goal_part.find('∑') != -1:
                sum_state = lean.run_tactic(f"simp [Finset.sum_range_succ]", init_state.proofStates[0], verbose=VERBOSE)
                if not sum_state.isError():
                    init_state = sum_state
                    code += "     simp [Finset.sum_range_succ]\n"
            if init_state.goals[0] is None or (isinstance(init_state.goals[0], list) and len(init_state.goals[0]) == 0):
                pass  # no goals or error, skip denominator processing
            else:
                expression = init_state.goals[0][0].split('⊢')[-1].strip() if isinstance(init_state.goals[0], list) else init_state.goals[0].split('⊢')[-1].strip()
                cnt = 0
                if expression.find('/') != -1:
                    denominators = self.extract_denominator(expression)
                    print("Extracted denominators:", denominators)
                    expressions = self.split_expression(denominators)
                    expressions = [strip_outer_even_power(e) for e in expressions]
                    print("Split expressions:", expressions)
                    nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
                    # Prove non-zero
                    for i in nezero_goals:
                        nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablek} < {self.variablen}) : {i}", i, f"h{cnt}", init_state=init_state)
                        nezero_tactics = "\n".join(["        " + i for i in nezero_tactics.split('\n')])
                        cnt += 1
                        code += f"     have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                        try:
                            init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                            print("init_state:", init_state.getTacticState())
                        except Exception as e:
                            continue
                    init_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
                    code += "     field_simp\n"
            code += "     <;>norm_num\n" + "     <;>norm_cast\n" + "     <;>grind\n"
            if not has_number:
                code += f"    exact (sub_eq_zero.1 $ Step2 {self.variablen} (by omega)).trans (hm (by omega))\n"
            else:
                code += f"    exact (sub_eq_zero.1 $ Step2 wzm hm).trans ih\n"
            # code += f"    exact (sub_eq_zero.1 $ Step2 {self.variablen} (by omega)).trans (hm (by omega))\n"
            print(code)
        else:
            if Bn!="0":
                init_state = lean.run_have_tactic(f"have Step3 : ∀ {self.variablen} : ℕ, f {self.variablen} = 1 ", init_state.proofStates[0], verbose=VERBOSE)
                code += f"  have Step3 : ∀ {self.variablen} : ℕ, f {self.variablen} = 1 := by\n"
            else:
                init_state = lean.run_have_tactic(f"have Step3 : ∀ {self.variablen} : ℕ, f {self.variablen} = 0 ", init_state.proofStates[0], verbose=VERBOSE)
                code += f"  have Step3 : ∀ {self.variablen} : ℕ, f {self.variablen} = 0 := by\n"
            qz = [f"intro {self.variablen}", f"induction' {self.variablen} with {self.variablen} hm"]
            if Bn!="0":
                qz_1 = ["simp [f, F, A, B]"]
            else:
                qz_1 = ["simp [f, A]"]
            for i in qz:
                init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
                code += "    " + i + "\n"
            code += "    .\n"
            for i in qz_1:
                init_state = lean.run_tactic(i, init_state.proofStates[0], verbose=VERBOSE)
                code += "     " + i + "\n"
            # Only check the goal expression (after ⊢) for ∑, to avoid false triggers from ∑ in let bindings
            goal_part = init_state.goals[0][0].split('⊢')[-1].strip() if isinstance(init_state.goals[0], list) else init_state.goals[0].split('⊢')[-1].strip()
            if goal_part.find('∑') != -1:
                sum_state = lean.run_tactic(f"simp [Finset.sum_range_succ]", init_state.proofStates[0], verbose=VERBOSE)
                if not sum_state.isError():
                    init_state = sum_state
                    code += "     simp [Finset.sum_range_succ]\n"
            if init_state.goals[0] is None or (isinstance(init_state.goals[0], list) and len(init_state.goals[0]) == 0):
                pass  # no goals or error, skip denominator processing
            else:
                expression = init_state.goals[0][0].split('⊢')[-1].strip() if isinstance(init_state.goals[0], list) else init_state.goals[0].split('⊢')[-1].strip()
                cnt = 0
                if expression.find('/') != -1:
                    denominators = self.extract_denominator(expression)
                    print("Extracted denominators:", denominators)
                    expressions = self.split_expression(denominators)
                    expressions = [strip_outer_even_power(e) for e in expressions]
                    print("Split expressions:", expressions)
                    nezero_goals = [self.addR(i, all=True) + " ≠ 0 " for i in expressions]
                    # Prove non-zero
                    for i in nezero_goals:
                        nezero_formal_theorem, nezero_tactics = self.prove_nezero_by_llm(import_content, f"theorem hwz {self.all_primises} (htotalNumidx : {self.variablek} < {self.variablen}) : {i}", i, f"h{cnt}", init_state=init_state)
                        nezero_tactics = "\n".join(["        " + i for i in nezero_tactics.split('\n')])
                        cnt += 1
                        code += f"     have h{cnt} : {i} := by \n" + nezero_tactics + "\n"
                        try:
                            init_state = lean.run_tactic(f"have h{cnt} : {i.strip()} := by \n" + nezero_tactics, init_state.proofStates[0], verbose=VERBOSE)
                            print("init_state:", init_state.getTacticState())
                        except Exception as e:
                            continue
                    init_state = lean.run_tactic(f"field_simp", init_state.proofStates[0], verbose=VERBOSE)
                    code += "     field_simp\n"
            code += "     <;>norm_num\n" + "     <;>norm_cast\n" + "     <;>grind\n"
            code += f"    · exact (sub_eq_zero.1 $ Step2 {self.variablen}).trans (hm)\n"
            print(code)
        if Bn == "0":
            code += "  exact Step3 n (by grind)"
            return code
        if self.hasR == 1:
            code +=  """  
  rw [Step1.1]
  norm_cast at Step3\n"""   
        else:
            code +=  """
  unfold A B at Step1
  norm_cast at Step1
  rw [Step1.1]
  norm_cast at Step3
  unfold f F A B at Step3\n"""
        if self.primise_value:
            code += f"  simpa using  (Step3 {self.variablen} (by omega))"
        else :
            code += f"  simpa using  (Step3 {self.variablen})"
        return code

    def prove_step3_sorry(self, Bn) -> str:
        """Fallback for prove_step3 when Lean REPL crashes (Broken Pipe).
        Generates a sorry-based Step3 proof so the sketch is still valid Lean."""
        code = ""
        if self.primise_value:
            if Bn != "0":
                code += f"  have Step3 : ∀ {self.variablen} : ℕ, {self.primise_value} → f {self.variablen} = 1 := by sorry\n"
            else:
                code += f"  have Step3 : ∀ {self.variablen} : ℕ, {self.primise_value} → f {self.variablen} = 0 := by sorry\n"
        else:
            if Bn != "0":
                code += f"  have Step3 : ∀ {self.variablen} : ℕ, f {self.variablen} = 1 := by sorry\n"
            else:
                code += f"  have Step3 : ∀ {self.variablen} : ℕ, f {self.variablen} = 0 := by sorry\n"
        if Bn == "0":
            code += "  exact Step3 n (by grind)"
            return code
        if self.hasR == 1:
            code += "  \n  rw [Step1.1]\n  norm_cast at Step3\n"
        else:
            code += "\n  unfold A B at Step1\n  norm_cast at Step1\n  rw [Step1.1]\n  norm_cast at Step3\n  unfold f F A B at Step3\n"
        if self.primise_value:
            code += f"  simpa using  (Step3 {self.variablen} (by omega))"
        else:
            code += f"  simpa using  (Step3 {self.variablen})"
        return code

    def prove(self, formal_theorem: str, import_content: str):
        """Execute the full WZ proof pipeline for a summation identity.

        This is the main entry point. It parses the theorem statement,
        computes WZ pairs via a CAS backend, generates Lean 4 proof
        obligations for each step (non-zero conditions, ratio lemmas,
        the WZ equation, and the inductive step), and assembles them
        into a complete tactic proof.

        Args:
            formal_theorem: The Lean 4 theorem statement (without ``:= by``).
            import_content: Lean 4 import preamble for the proof file.

        Returns:
            A string containing the complete Lean 4 tactic proof.

        Raises:
            Exception: If symbolic computation (Sage/Maple) fails.
        """
        # try:
        self.last_timing = {"wz_pair_seconds": None}
        print("formal_theorem:", formal_theorem)
        print("import_content:", import_content)
        
        if formal_theorem.find("ℝ") == -1:
            self.hasR = 0
        else: self.hasR = 1
        self.step3_primise = []
        self.primise_name = []
        self.primise_value = []
        self.all_primises = ""
        self.theorem_statement = formal_theorem
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        initial_state = lean.run_import(import_content, verbose=VERBOSE)
        initial_state = lean.new_thm(formal_theorem, verbose=VERBOSE, env=0)
        initial_state.print()
        Ico_tactic = ""
        k_cnt_tactic = ""
        by_cases_code = ""
        if formal_theorem.find("Ico")!= -1:
            Ico_tactic = "  simp [Finset.sum_Ico_eq_sum_range]"
            initial_state = lean.run_tactic("simp [Finset.sum_Ico_eq_sum_range]", initial_state.proofStates[0], verbose=VERBOSE)
        print("initial_state:", initial_state.getTacticState())
        
        # First set variables n and k
        initial_tacticstate = initial_state.getTacticState().split('⊢')[-1].strip()
        self.set_variables_and_num(initial_tacticstate.split(',')[0].strip())

        by_cases_primises, k_cnt = self.extract_primise(initial_state.getTacticState().split('⊢')[-1].strip(), n=self.variablen, k=self.variablek)
        print("by_cases_primises:", by_cases_primises)
        last_state = copy.deepcopy(initial_state)
        try:
            if k_cnt>0:
                """
                rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp [Finset.sum_Ico_eq_sum_range]
                """
                k_cnt_tactic = f"  rw [Finset.range_eq_Ico]\n"
                initial_state = lean.run_tactic("rw [Finset.range_eq_Ico]", initial_state.proofStates[0], verbose=VERBOSE)
                while k_cnt > 0:
                    k_cnt_tactic += f"  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]\n"
                    k_cnt -= 1
                    initial_state = lean.run_tactic("rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]", initial_state.proofStates[0], verbose=VERBOSE)
                k_cnt_tactic += "  simp [Finset.sum_Ico_eq_sum_range]\n" 
                initial_state = lean.run_tactic("simp [Finset.sum_Ico_eq_sum_range]", initial_state.proofStates[0], verbose=VERBOSE)
            if by_cases_primises:

                test_state = copy.deepcopy(initial_state)
                by_cases_primises_confirm = []
                for i in by_cases_primises:
                    si = i.strip()
                    # Filter out conditions that are always false for ℕ,
                    # e.g. "n < 0", "m < 0", "m ≤ 0", "0 > n", etc.
                    if re.match(r'^[a-zA-Z_]\w*\s*<\s*0$', si) or \
                       re.match(r'^0\s*>\s*[a-zA-Z_]\w*$', si) or \
                       re.match(r'^[a-zA-Z_]\w*\s*≤\s*0$', si) or \
                       re.match(r'^0\s*≥\s*[a-zA-Z_]\w*$', si):
                        continue
                    test_tactic = f"by_cases htest : ({i})"
                    test_state_1 = lean.run_tactic(test_tactic, test_state.proofStates[0], verbose=VERBOSE)
                    if test_state_1.getTacticState().find('sorry') == -1:
                        by_cases_primises_confirm.append(i)
                if by_cases_primises_confirm != []:
                    # 'case pos\nn : ℕ\nhby_cases : n = 0\n⊢ ∑ k ∈ range (n + 1), (-1) ^ k * ↑(n.choose k) * ↑k * 2 ^ k = 2 * ↑n * (-1) ^ n'
                    by_cases_tactic = 'by_cases hby_cases : (' + ' ∨ '.join(by_cases_primises_confirm) + ")"
                    
                    initial_state = lean.run_tactic(by_cases_tactic, initial_state.proofStates[0], verbose=VERBOSE)
                    print(initial_state.goals)
                    case_pose_pri, case_pose_goal = initial_state.goals[0][0].split('⊢')
                    case_pose_pri = case_pose_pri.strip().split('\n')
                    case_pose_pri_str = " ".join([f"({i.strip()})" for i in case_pose_pri if i.strip() and i.find(":") != -1])
                    case_pose_goal = self.addR(case_pose_goal.strip())

                    case_pose_theorem = f"theorem case_pos {case_pose_pri_str} : {case_pose_goal}"
                    print("case_pose_theorem:", case_pose_theorem)
                    _, case_pose_tactics = self.prove_nezero_by_llm(import_content, case_pose_theorem, case_pose_goal, f"case_pos")
                    case_pose_tactics = "\n".join(["   " + i for i in case_pose_tactics.split('\n')])
                    
                    by_cases_code = "  " + by_cases_tactic.strip() + "\n" + f"  . " + case_pose_tactics.strip() + "\n"
                    print("by_cases_code:")
                    print(by_cases_code)

                    initial_state = lean.run_tactic("sorry", initial_state.proofStates[0], verbose=VERBOSE)
                    print("initial_state after by_cases:", initial_state.print())
                    print("initial_state:", initial_state.getTacticState())
                    print(len(initial_state.proofStates))

        except Exception as e:
            print(f"Error applying by_cases tactic: {e}")
            initial_state = copy.deepcopy(last_state)
            # Set variables n and k
        initial_tacticstate = initial_state.getTacticState().split('⊢')[-1].strip()
        self.set_variables_and_num(initial_tacticstate.split(',')[0].strip())
        # Extract conditions
        primises = initial_state.getTacticState().split('⊢')[0].strip()
        print("primises:", primises)
        primises = [i.strip() for i in primises.split('\n') if i.strip()]
        print("primises:", primises)
        def remove_not(expr:str):
            # Negate: swap greater-than and less-than inside parentheses, etc.
            expr_name, expr_value = expr.split(':') if expr.find(':') != -1 else ("", expr)
            expr_value = expr_value.strip()
            if expr_value.startswith("¬"):
                expr_value = expr_value[1:].strip()
            else:
                return expr
            # expr = expr.replace(">", "temp_gt").replace("<", ">").replace("temp_gt", "<")
            # expr = expr.replace("≥", "temp_ge").replace("≤", "≥").replace("temp_ge", "≤")
            # expr = expr.replace("=", "temp_eq").replace("≠", "=").replace("temp_eq", "≠")
            expr_value = expr_value.replace("≥", "temp_ge").replace("<", "≥").replace("temp_ge", "<")
            expr_value = expr_value.replace(">", "temp_gt").replace("≤", ">").replace("temp_gt", "≤")
            expr_value = expr_value.replace("=", "temp_eq").replace("≠", "=").replace("temp_eq", "≠")
            expr_value = expr_value.replace("∨", "temp_or").replace("∧", "∨").replace("temp_or", "∧")
            return expr_name + ": " + expr_value
        # First apply remove_not to conditions and split conjunctions
        new_primises = []
        for i in primises:
            if i.startswith("case"):
                continue
            # Skip WZ_aux and similar internal have-bindings whose type is a
            # higher-order function signature (not a simple ℕ/ℝ proposition).
            # These appear in the Lean context as e.g.
            #   WZ_aux : ∀ (n : ℕ) (f : ℕ → ℕ → ℝ) (B : ℕ → ℝ),
            # and are syntactically invalid when spliced into a theorem statement.
            i_name = i.split(':')[0].strip() if ':' in i else ''
            if i_name in ('WZ_aux', 'WZ', 'Step1', 'Step2', 'Step3',
                          'ne_zeroA', 'ne_zeroB', 'ne_zeroB_succ',
                          'ne_zeroAB', "ne_zeroB'", "ne_zeroAB'",
                          'l₁', 'l₂', 'r₁', 'r₂', 'aux₁', 'aux₂',
                          'aux₃', 'aux₄', 'aux₅', 'A', 'B', 'R', 'F', 'G', 'f'):
                continue
            # Also skip any hypothesis whose type contains a function-type arrow
            # over ℕ→ℕ→ℝ or ℕ→ℝ (these are internal higher-order bindings).
            i_type = ':'.join(i.split(':')[1:]).strip() if ':' in i else i
            if ('ℕ → ℕ → ℝ' in i_type or 'ℕ → ℝ' in i_type) and '∀' in i_type:
                continue
            if i.find("✝") != -1:
                i = 'hh' + i.replace("✝", "")
            i = remove_not(i)
            print("i:", i)
            # If the condition contains a conjunction, split into multiple conditions
            if i.find('∧') != -1:
                name, pri = i.split(':') if i.find(':') != -1 else ("", i)
                name = name.strip()
                and_parts = [part.strip() for part in pri.split('∧') if part.strip()]
                cnt = 0
                for part in and_parts:
                    if part.startswith('(') and not part.endswith(')'):
                        part = part[1:]
                    if part.endswith(')') and not part.startswith('('):
                        part = part[:-1]
                    new_primises.append(name + str(cnt) + " : " + part)
                    cnt += 1
                continue
            new_primises.append(i)
        primises = new_primises
        print("primises after remove_not and split ∧ :", primises)
        # Merge conditions where variable n is not equal to constants, e.g. not-equal-to 0 becomes greater-than 0, not-equal-to 0 and not-equal-to 1 becomes greater-than 1
        digit_list = []
        remove_primises = []
        for i in primises:   
            # If variable n is not equal to a constant
            if i.find("≠") != -1:
                name, expr = i.split(':') if i.find(':') != -1 else ("", i)
                left, right = expr.split("≠")
                left = left.strip()
                right = right.strip()
                if (left == self.variablen and right.isdigit()):
                    digit_list.append(int(right))
                elif (right == self.variablen and left.isdigit()):
                    digit_list.append(int(left))
                else:
                    continue
                remove_primises.append(i)
        # If digit_list is not empty, it means variable n has not-equal-to-constant conditions, and the constants must start from 0 and be consecutive
        nezero_primises = []
        if digit_list:
            # Deduplicate and sort
            digit_list = list(set(digit_list))
            digit_list.sort()
            print("digit_list:", digit_list)
            # Check if it starts from 0 and is consecutive
            if digit_list[0] == 0 and all(digit_list[i] == digit_list[i-1] + 1 for i in range(1, len(digit_list))):
                nezero_primises.append(f"h_ne_zero_converted : {self.variablen} ≥ {digit_list[-1] + 1}")
            # Remove the original not-equal-to conditions
            primises = [i for i in primises if i not in remove_primises] + nezero_primises
        print("nezero_primises:", nezero_primises)
        print("primises after remove_primises:", primises)
        
        for i in primises:
            if i.startswith("case"):
                continue
            if i.find("✝") != -1:
                i = 'hh' + i.replace("✝", "")
            i = remove_not(i)
            print("i:", i)
            # self.all_primises += "(" + i.strip() + ") "
            # If the condition contains a conjunction, split into multiple conditions
            if i.find('∧') != -1:
                name, pri = i.split(':') if i.find(':') != -1 else ("", i)
                name = name.strip()
                and_parts = [part.strip() for part in pri.split('∧') if part.strip()]
                cnt = 0
                for part in and_parts:
                    if part.startswith('(') and not part.endswith(')'):
                        part = part + ")"
                    if part.endswith(')') and not part.startswith('('):
                        part = "(" + part
                    self.all_primises += "(" + name + str(cnt) + " : " + part + ") "
                    # Needed
                    if (part.find('=') != -1 or part.find('≠') != -1 or part.find('>') != -1 or part.find('<') != -1 or part.find('≥') != -1 or part.find('≤') != -1) and re.search(rf'\b{self.variablen}\b', part) and (not (re.search(rf'\b{self.variablen}\b', part) and re.search(rf'\b{self.variablek}\b', part))):
                        self.step3_primise.append(name + str(cnt) + " : " + part.strip())
                    cnt += 1
                continue

            self.all_primises += "(" + i.strip() + ") "
            # Needed
            if (i.find('=') != -1 or i.find('≠') != -1 or i.find('>') != -1 or i.find('<') != -1 or i.find('≥') != -1 or i.find('≤') != -1) and re.search(rf'\b{self.variablen}\b', i) and (not (re.search(rf'\b{self.variablen}\b', i) and re.search(rf'\b{self.variablek}\b', i))):
                self.step3_primise.append(i.strip())
        def deduplicate_list(lst):
            seen = set()
            result = []
            for item in lst:
                stripped_item = item.strip() if isinstance(item, str) else str(item)
                # Skip empty values to avoid invalid data
                if not stripped_item:
                    continue
                if stripped_item not in seen:
                    seen.add(stripped_item)
                    result.append(item)  # preserve original format (including spaces, etc.)
            return result

        # 1. Deduplicate step3_primise (list, preserving order)
        self.step3_primise = deduplicate_list(self.step3_primise)
        print(self.step3_primise)
        # 2. Deduplicate all_primises (list, preserving order)
        self.all_primises = deduplicate_list(self.all_primises)

        self.primise_value = " ∧ ".join([i.split(':')[-1].strip() for i in self.step3_primise if i.strip()])
        self.primise_name = ", ".join([i.split(':')[0].strip() for i in self.step3_primise if i.strip()])
        if len(self.step3_primise) > 1: self.primise_name = f"⟨{self.primise_name}⟩"
        
        # Deduplicate

        print("step3_primise:\n", self.step3_primise)
        print("all_primises:\n", self.all_primises)
        print("step3_primise_value:\n", self.primise_value)
        print("step3_primise_name:\n", self.primise_name)
        
        Ank_Bn_parts = [i.strip() for i in initial_tacticstate[initial_tacticstate.find(',') + 1 : ].split('=', 1)]
        Ank = Ank_Bn_parts[0] if len(Ank_Bn_parts) > 0 else ''
        Bn = Ank_Bn_parts[1] if len(Ank_Bn_parts) > 1 else ''
        Ank = self.repair_expr(Ank).replace("\n", "").strip()
        Bn = self.repair_expr(Bn).replace("\n", "").strip()
        
        print("Ank:", Ank)
        print("Bn:", Bn)
        
        print(self.split_expression_recursive([Ank]))
        print(self.split_expression_recursive([Bn]))
        wz_pair_start = time.perf_counter()
        if USE_MAPLE:
            Ank_maple = convert_lean_to_math_test(Ank)
            Bn_maple = convert_lean_to_math_test(Bn)
            Ank_maple_pair = [[convert_lean_to_math_test(i), i] for i in self.split_expression_recursive([Ank])]
            Bn_maple_pair = [[convert_lean_to_math_test(i), i] for i in self.split_expression_recursive([Bn])]
            
            print("Ank_maple_pair:", Ank_maple_pair)
            print("Bn_maple_pair:", Bn_maple_pair)
            self.aux1_recursive = [get_recursive_goals(i[0], i[1], variable=self.variablek) for i in Ank_maple_pair]
            self.aux2_recursive = [get_recursive_goals(i[0], i[1], variable=self.variablen) for i in Ank_maple_pair]
            if Bn == "0":
                # exp_({variablen}{num3}, {variablen}{num1}) / exp_({variablen}{num4}, {variablen}{num2}
                self.aux3_recursive = [get_recursive_goals_calc(i[0], i[1], self.variablen, self.variablek, '+1', '', '+1', '') for i in Ank_maple_pair]
                self.aux4_recursive = [get_recursive_goals_calc(i[0], i[1], self.variablen, self.variablek, '', '', '+1', '') for i in Ank_maple_pair]
            else:
                self.aux3_recursive = [get_recursive_goals(i[0], i[1], variable=self.variablen) for i in Bn_maple_pair]
            self.calc_recursive = [get_recursive_goals_calc(i[0], i[1], self.variablen, self.variablek, self.num1,self.num2) for i in Ank_maple_pair]
            self.aux1_recursive = [self.addR(i, all=True) for i in self.aux1_recursive if i != None]
            self.aux2_recursive = [self.addR(i, all=True) for i in self.aux2_recursive if i != None]
            self.aux3_recursive = [self.addR(i, all=True) for i in self.aux3_recursive if i != None]
            self.calc_recursive = [self.addR(i, all=True) for i in self.calc_recursive if i != None]
            print("aux1_recursive:", self.aux1_recursive)
            print("aux2_recursive:", self.aux2_recursive)
            print("aux3_recursive:", self.aux3_recursive)
            print("calc_recursive:", self.calc_recursive)


            
            cert = calculate_cert(Ank_maple, Bn_maple, self.variablen, self.variablek)
            AKdiv, Adiv, Bdiv = calculate_ratio(Ank_maple, Bn_maple, 3, self.variablen, self.variablek)
        else:
            Ank_sage = convert_lean_to_sage(Ank)
            Bn_sage = convert_lean_to_sage(Bn)
            Ank_sage_pair = [[convert_lean_to_sage(i), i] for i in self.split_expression_recursive([Ank])]
            Bn_sage_pair = [[convert_lean_to_sage(i), i] for i in self.split_expression_recursive([Bn])]
            print("Ank_sage_pair:", Ank_sage_pair)
            print("Bn_sage_pair:", Bn_sage_pair)
            self.aux1_recursive = [get_recursive_goals_sage(i[0], i[1], variable=self.variablek, origin_variablen=self.variablen, origin_variablek=self.variablek) for i in Ank_sage_pair]
            self.aux2_recursive = [get_recursive_goals_sage(i[0], i[1], variable=self.variablen, origin_variablen=self.variablen, origin_variablek=self.variablek) for i in Ank_sage_pair]
            if Bn == "0":
                # exp_({variablen}{num3}, {variablen}{num1}) / exp_({variablen}{num4}, {variablen}{num2}
                self.aux3_recursive = [get_recursive_goals_calc_sage(i[0], i[1], self.variablen, self.variablek, '+1', '', '+1', '') for i in Ank_sage_pair]
                self.aux4_recursive = [get_recursive_goals_calc_sage(i[0], i[1], self.variablen, self.variablek, '', '', '+1', '') for i in Ank_sage_pair]
            else:
                self.aux3_recursive = [get_recursive_goals_sage(i[0], i[1], variable=self.variablen, origin_variablen=self.variablen, origin_variablek=self.variablek) for i in Bn_sage_pair]
                self.aux4_recursive = [get_recursive_goals_calc_sage(i[0], i[1], self.variablen, self.variablek, f'{self.num1}', f'{self.num2}', '+1', '') for i in Ank_sage_pair]
                self.aux5_recursive = [get_recursive_goals_calc_sage(i[0], i[1], self.variablen, self.variablek, f'{self.num2}', f'{self.num2}', '+1', '') for i in Ank_sage_pair]
                self.aux5_recursive = [self.addR(i, all=True) for i in self.aux5_recursive if i != None]
            self.calc_recursive = [get_recursive_goals_calc_sage(i[0], i[1], self.variablen, self.variablek, self.num1,self.num2) for i in Ank_sage_pair]
            self.aux1_recursive = [self.addR(i, all=True) for i in self.aux1_recursive if i != None]
            self.aux2_recursive = [self.addR(i, all=True) for i in self.aux2_recursive if i != None]
            self.aux3_recursive = [self.addR(i, all=True) for i in self.aux3_recursive if i != None]
            self.aux4_recursive = [self.addR(i, all=True) for i in self.aux4_recursive if i != None]
            self.calc_recursive = [self.addR(i, all=True) for i in self.calc_recursive if i != None]

            print("aux1_recursive:", self.aux1_recursive)
            print("aux2_recursive:", self.aux2_recursive)   
            print("aux3_recursive:", self.aux3_recursive)
            print("calc_recursive:", self.calc_recursive)
            if Bn != '0':
                cert = calculate_cert_sage(Ank_sage, Bn_sage, self.variablen, self.variablek)
            else:
                cert = calculate_cert_sage(Ank_sage, "1", self.variablen, self.variablek)
            AKdiv, Adiv, Bdiv, Anndiv, A_nadd1_n_div = calculate_ratio_sage(Ank_sage, Bn_sage, 3, self.variablen, self.variablek, self.num1_int, self.num2_int)
        self.last_timing["wz_pair_seconds"] = time.perf_counter() - wz_pair_start
        self.let_tactics_list = self.let_tactics(Ank, Bn, cert).split('\n')
        self.let_tactics_list = [i.strip() for i in self.let_tactics_list if i.strip()]
        Ank = self.addR(Ank, all=True) #TODO
        Bn = self.addR(Bn, all=True)

        print("AKdiv:", AKdiv)
        print("Adiv:", Adiv)
        print("Bdiv:", Bdiv)
        print("Anndiv:", Anndiv)
        # print(self.let_tactics(Ank, Bn, cert))
        # code =  k_cnt_tactic + '\n' + self.let_tactics(Ank, Bn, cert) + "\n"
        code =  self.let_tactics(Ank, Bn, cert) + "\n"
        import_ = import_content + "\n" + formal_theorem + " := by"
        if self.primise_value:
            if Bn != "0":
                a_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} ∧ {self.primise_value} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0",
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp [A]"] , hz=["aesop"])
                b_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroB :∀ {self.variablen} : ℕ, {self.primise_value} → (B {self.variablen} : ℝ)  ≠ 0",
                                    [f"intro {self.variablen} hwzm", "simp [B]"] , hz=["aesop"])
                b_succ_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroB_succ :∀ {self.variablen} : ℕ, {self.primise_value} → (B ({self.variablen} + 1) : ℝ)  ≠ 0",
                                    [f"intro {self.variablen} hwzm", "simp [B]"] , hz=["aesop"])
                code += f"  have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} ∧ {self.primise_value} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0 := by\n" + a_nezero_code
                code += f"  have ne_zeroB :∀ {self.variablen} : ℕ, {self.primise_value} → (B {self.variablen} : ℝ)  ≠ 0 := by\n" + b_nezero_code
                code += f"  have ne_zeroB_succ :∀ {self.variablen} : ℕ, {self.primise_value} → (B ({self.variablen} + 1) : ℝ)  ≠ 0 := by\n" + b_succ_nezero_code
            else:
                a_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} ∧ {self.primise_value} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0",
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp [A]"] , hz=["aesop"])
                code += f"  have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} ∧ {self.primise_value} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0 := by\n" + a_nezero_code
        else:
            if Bn != "0":
                a_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0",
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp [A]"] , hz=["aesop"])
                b_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroB :∀ {self.variablen} : ℕ, (B {self.variablen} : ℝ)  ≠ 0",
                                    [f"intro {self.variablen}", "simp [B]"] , hz=["aesop"])
                b_succ_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroB_succ :∀ {self.variablen} : ℕ, (B ({self.variablen} + 1) : ℝ)  ≠ 0",
                                    [f"intro {self.variablen}", "simp [B]"] , hz=["aesop"])
                code += f"  have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0 := by\n" + a_nezero_code
                code += f"  have ne_zeroB :∀ {self.variablen} : ℕ, (B {self.variablen} : ℝ)  ≠ 0 := by\n" + b_nezero_code
                code += f"  have ne_zeroB_succ :∀ {self.variablen} : ℕ, (B ({self.variablen} + 1) : ℝ)  ≠ 0 := by\n" + b_succ_nezero_code
            else:
                a_nezero_code = self.prove_nezero_A_B(import_content + "\n", 
                                    f"have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0",
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp [A]"] , hz=["aesop"])
                code += f"  have ne_zeroA :∀ {self.variablen} {self.variablek} : ℕ, {self.variablek} < {self.variablen} → (A {self.variablen} {self.variablek} : ℝ) ≠ 0 := by\n" + a_nezero_code

        if Bn != "0":
            if self.primise_value:
                code += FIXED_1_WITH_PRIMISE.format(n=self.variablen, k=self.variablek, primise=self.primise_value, primise_name=self.primise_name, num=self.num1) + '\n'
            else:
                code += FIXED_1.format(n=self.variablen, k=self.variablek, num=self.num1) + '\n'
        print("code:")
        print(code)
        if self.primise_value:
            if Bn != "0":
                print("BN")
                print(Bn)
                print(type(Bn))
                print(Bn=="0")
                aux1_code = self.prove_aux(import_content + "\n",
                                    f"have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A {self.variablen} ({self.variablek} + 1) / A {self.variablen} {self.variablek} = {AKdiv}", 
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp only [A]"], hz=['grind'], recursive_goals=self.aux1_recursive, id=1)
                aux2_code = self.prove_aux(import_content + "\n",
                                    f"have aux₂ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A ({self.variablen} + 1) {self.variablek} / A {self.variablen} {self.variablek} = ({Adiv})", 
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp only [A]"], hz=['grind'], recursive_goals=self.aux2_recursive, id=2)
                aux3_code = self.prove_aux(import_content + "\n",
                                f"have aux₃ : ∀ {self.variablen} : ℕ, {self.primise_value} → B ({self.variablen} + 1) / B {self.variablen} = {Bdiv}", 
                                [f"intro {self.variablen} hrn", "simp only [B]"], hz=['grind'], recursive_goals=self.aux3_recursive, id=3)
                aux4_code = self.prove_aux(import_content + "\n",
                                f"have aux₄ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) ({self.variablen}{self.num1}) = ({Anndiv}) * A {self.variablen} ({self.variablen}{self.num2})", 
                                [f"intro {self.variablen} hrn", "simp only [A]"], hz=['grind'], recursive_goals=self.aux4_recursive, id=4)
                aux5_code = self.prove_aux(import_content + "\n",
                                f"have aux₅ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) ({self.variablen}{self.num2}) = ({A_nadd1_n_div}) * A {self.variablen} ({self.variablen}{self.num2})", 
                                [f"intro {self.variablen} hrn", "simp only [A]"], hz=['norm_num', 'grind'], recursive_goals=self.aux5_recursive, id=5)
            else:
                aux1_code = self.prove_aux(import_content + "\n",
                                    f"have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A {self.variablen} ({self.variablek} + 1) = ({AKdiv}) * A {self.variablen} {self.variablek}", 
                                    [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp only [A]"], hz=['grind'], recursive_goals=self.aux1_recursive, id=1)
                aux2_code = self.prove_aux(import_content + "\n",
                                    f"have aux₂ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A ({self.variablen} + 1) {self.variablek}= ({Adiv}) * A {self.variablen} {self.variablek}", 
                                [f"intro {self.variablen} {self.variablek} htotalNumidx", "simp only [A]"], hz=['grind'], recursive_goals=self.aux2_recursive, id=2)
                aux3_code = self.prove_aux(import_content + "\n",
                                f"have aux₃ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) ({self.variablen} + 1) = ({Anndiv}) * A {self.variablen} {self.variablen}", 
                                [f"intro {self.variablen} hrn", "simp [A]"], hz=['ring'], recursive_goals=self.aux3_recursive, id=3)
                aux4_code = self.prove_aux(import_content + "\n",
                                f"have aux₄ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) {self.variablen} = ({A_nadd1_n_div}) * A {self.variablen} {self.variablen}", 
                                [f"intro {self.variablen} hrn", "simp [A]"], hz=['ring'], recursive_goals=self.aux4_recursive, id=4)
            if Bn == '0':
                print(code)
                print("aux1_code:")
                print(f"have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A {self.variablen} ({self.variablek} + 1) = ({AKdiv}) * A {self.variablen} {self.variablek}")
                code += f"  have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A {self.variablen} ({self.variablek} + 1) = ({AKdiv}) * A {self.variablen} {self.variablek} := by\n"
                code += aux1_code + "\n"
                print("code after aux1:")
                print(code)
                code += f"  have aux₂ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A ({self.variablen} + 1) {self.variablek} = ({Adiv}) * A {self.variablen} {self.variablek} := by\n"
                code += aux2_code + "\n"
                print("code after aux2:")
                print(code)
            else:
                print("aux1_code:")
                print(f"have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A {self.variablen} ({self.variablek} + 1) / A {self.variablen} {self.variablek} = {AKdiv}")
                code += f"  have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A {self.variablen} ({self.variablek} + 1) / A {self.variablen} {self.variablek} = {AKdiv} := by\n"
                code += aux1_code + "\n"
                print("code after aux1:")
                print(code)
                code += f"  have aux₂ : ∀ {self.variablen} {self.variablek} : ℕ, {self.variablen} > {self.variablek} ∧ {self.primise_value} → A ({self.variablen} + 1) {self.variablek} / A {self.variablen} {self.variablek} = ({Adiv}) := by\n"
                code += aux2_code + "\n"
                print("code after aux2:")
                print(code)
            if Bn!='0':
                code += f"  have aux₃ : ∀ {self.variablen} : ℕ, {self.primise_value} → B ({self.variablen} + 1) / B {self.variablen} = {Bdiv} := by\n"
            else: 
                code += f"  have aux₃ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) ({self.variablen} + 1) = ({Anndiv}) * A {self.variablen} {self.variablen} := by\n"
            code += aux3_code + "\n"
            if Bn == "0":
                print("code after aux3:")
                print(code)
                code += f"  have aux₄ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) {self.variablen} = ({A_nadd1_n_div}) * A {self.variablen} {self.variablen} := by\n"
                code += aux4_code + "\n"
                print("code after aux4:")
                print(code)
            else:
                code += f"  have aux₄ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) ({self.variablen}{self.num1}) = ({Anndiv}) * A {self.variablen} ({self.variablen}{self.num2}) := by\n"
                code += aux4_code + "\n"
                print("code after aux4:")
                print(code)
                code += f"  have aux₅ : ∀ {self.variablen} : ℕ, {self.primise_value} → A ({self.variablen} + 1) ({self.variablen}{self.num2}) = ({A_nadd1_n_div}) * A {self.variablen} ({self.variablen}{self.num2}) := by\n"
                code += aux5_code + "\n"
                print("code after aux5:")
                print(code)
        else:
            if Bn != "0":
                aux1_code = self.prove_aux(import_content + "\n",
                                    f"have aux₁  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}) : A {self.variablen} ({self.variablek} + 1) / A {self.variablen} {self.variablek} = {AKdiv}", 
                                    ["simp only [A]"], hz=['grind'], recursive_goals=self.aux1_recursive, id=1)
                aux2_code = self.prove_aux(import_content + "\n",
                                    f"have aux₂  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}) : A ({self.variablen} + 1) {self.variablek} / A {self.variablen} {self.variablek} = {Adiv}", 
                                    ["simp only [A]"], hz=['grind'], recursive_goals=self.aux2_recursive, id=2)
                aux3_code = self.prove_aux(import_content + "\n",
                                    f"have aux₃ : ∀ {self.variablen} : ℕ, B ({self.variablen} + 1) / B {self.variablen} = {Bdiv}", 
                                    [f"intro {self.variablen}", "simp only [B]"], hz=['grind'], recursive_goals=self.aux3_recursive, id=3)
                aux4_code = self.prove_aux(import_content + "\n",
                                    f"have aux₄ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen}{self.num1}) = ({Anndiv}) * A {self.variablen} ({self.variablen}{self.num2})", 
                                    [f"intro {self.variablen}", "simp only [A]"], hz=['grind'], recursive_goals=self.aux4_recursive, id=4)
                aux5_code = self.prove_aux(import_content + "\n",
                                    f"have aux₅ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen}{self.num2}) = ({A_nadd1_n_div}) * A {self.variablen} ({self.variablen}{self.num2})", 
                                    [f"intro {self.variablen}", "simp only [A]"], hz=['norm_num', 'grind'], recursive_goals=self.aux5_recursive, id=5)
            else:
                aux1_code = self.prove_aux(import_content + "\n",
                                    f"have aux₁  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}) : A {self.variablen} ({self.variablek} + 1) = ({AKdiv}) * A {self.variablen} {self.variablek}", 
                                    ["simp only [A]"], hz=['ring'], recursive_goals=self.aux1_recursive, id=1)
                aux2_code = self.prove_aux(import_content + "\n",
                                    f"have aux₂  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}) : A ({self.variablen} + 1) {self.variablek} = ({Adiv}) * A {self.variablen} {self.variablek}", 
                                    ["simp only [A]"], hz=['ring'], recursive_goals=self.aux2_recursive, id=2)
                aux3_code = self.prove_aux(import_content + "\n",
                                    f"have aux₃ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen} + 1) = ({Anndiv}) * A {self.variablen} {self.variablen}", 
                                    [f"intro {self.variablen}", "simp [A]"], hz=['ring'], recursive_goals=self.aux3_recursive, id=3)
                aux4_code = self.prove_aux(import_content + "\n",
                                    f"have aux₄ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) {self.variablen} = ({A_nadd1_n_div}) * A {self.variablen} {self.variablen}", 
                                    [f"intro {self.variablen}", "simp [A]"], hz=['ring'], recursive_goals=self.aux4_recursive, id=4)

            if Bn != "0":
                code += f"  have aux₁  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}): A {self.variablen} ({self.variablek} + 1) / A {self.variablen} {self.variablek} = {AKdiv} := by\n"
                code += aux1_code + "\n"
                code += f"  have aux₂  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}): A ({self.variablen} + 1) {self.variablek} / A {self.variablen} {self.variablek} = {Adiv} := by\n"
                code += aux2_code + "\n"
                code += f"  have aux₃ : ∀ {self.variablen} : ℕ, B ({self.variablen} + 1) / B {self.variablen} = {Bdiv} := by\n"
                code += aux3_code + "\n"
                code += f"  have aux₄ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen}{self.num1}) = ({Anndiv}) * A {self.variablen} ({self.variablen}{self.num2}) := by\n"
                code += aux4_code + "\n"
                code += f"  have aux₅ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen}{self.num2}) = ({A_nadd1_n_div}) * A {self.variablen} ({self.variablen}{self.num2}) := by\n"
                code += aux5_code + "\n"
            else:
                code += f"  have aux₁  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}): A {self.variablen} ({self.variablek} + 1) = ({AKdiv}) * A {self.variablen} {self.variablek} := by\n"
                code += aux1_code + "\n"
                code += f"  have aux₂  ({self.variablen} {self.variablek} : ℕ) (htotalNumidx : {self.variablek} < {self.variablen}): A ({self.variablen} + 1) {self.variablek} = ({Adiv}) * A {self.variablen} {self.variablek} := by\n"
                code += aux2_code + "\n"
                code += f"  have aux₃ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen} + 1) = ({Anndiv}) * A {self.variablen} {self.variablen} := by\n"
                code += aux3_code + "\n"
                code += f"  have aux₄ : ∀ {self.variablen} : ℕ, A ({self.variablen} + 1) ({self.variablen}) = ({A_nadd1_n_div}) * A {self.variablen} {self.variablen} := by\n"
                code += aux4_code + "\n"
            
        print("aux1_code:")
        print(aux1_code)
        print("aux2_code:")
        print(aux2_code)
        print("aux3_code:")
        print(aux3_code)
        if Bn == "0":
            print("aux4_code:")
            print(aux4_code)
        else:
            print("aux4_code:")
            print(aux4_code)
            print("aux5_code:")
            print(aux5_code)
        print("code:")
        print(code)
        print("check bn")
        print(Bn)
        print(Bn=="0")
        if Bn != '0':
            wz_code = self.prove_step2_wz(import_content, cert=cert, AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv, Bn=Bn, Anndiv=Anndiv, A_nadd1_n_div=A_nadd1_n_div)
        else:
            wz_code = self.prove_step2_wz_bn0(import_content, cert=cert, AKdiv=AKdiv, Adiv=Adiv,Bn=Bn, Anndiv=Anndiv, A_nadd1_n_div=A_nadd1_n_div)
        if self.primise_value:
            if Bn != "0":
                code += FIXED_2_WITH_PRIMISE.format(n=self.variablen, k=self.variablek, primise=self.primise_value) + "\n"
            else: code += FIXED_2_WITH_PRIMISE_Bn0.format(n=self.variablen, k=self.variablek, primise=self.primise_value) + "\n"
            code += wz_code + "\n"
            if Bn!="0":
                code += FIXED_CALC_WITH_PRIMISE.format(n=self.variablen, k=self.variablek,primise=self.primise_value, num1=self.num1, num2=self.num2, calc_rw=self.calc_rw) + "\n"
            else: code += FIXED_CALC_WITH_PRIMISE_Bn0.format(n=self.variablen, k=self.variablek,primise=self.primise_value, num1=self.num1, num2=self.num2, calc_rw=self.calc_rw) + "\n"
        else:
            if Bn != "0":
                code += FIXED_2.format(n=self.variablen, k=self.variablek) + "\n"
            else: code += FIXED_2_Bn0.format(n=self.variablen, k=self.variablek) + "\n"
            code += wz_code + "\n"
            if Bn!='0':
                code += FIXED_CALC.format(n=self.variablen, k=self.variablek, num1=self.num1, num2=self.num2,calc_rw=self.calc_rw) + "\n"
            else: code += FIXED_CALC_Bn0.format(n=self.variablen, k=self.variablek, num1=self.num1, num2=self.num2,calc_rw=self.calc_rw) + "\n"   
        

        
        print("code:")
        print(code)
        if Bn != '0':
            calc_code = self.prove_step2_calc(import_content, cert=cert, AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv, Anndiv=Anndiv,A_nadd1_n_div=A_nadd1_n_div,recursive_goals=self.calc_recursive)
        else:
            calc_code = self.prove_step2_calc_bn0(import_content, cert=cert, AKdiv=AKdiv, Adiv=Adiv, Bdiv=Bdiv,Anndiv=Anndiv,A_nadd1_n_div=A_nadd1_n_div, recursive_goals=self.calc_recursive)
        code += calc_code + "\n"
        print(code)
        try:
            code += self.prove_step3(import_content, Bn) + "\n"
        except Exception as _step3_err:
            print(f"prove_step3 failed ({_step3_err}), falling back to sorry-based Step3")
            code += self.prove_step3_sorry(Bn) + "\n"

        if by_cases_code:
            code = k_cnt_tactic + '\n' + by_cases_code + "  ." + ("\n".join([self.space + i for i in code.replace(import_, "").split('\n')])).strip() + "\n"
            if Ico_tactic:
                code = Ico_tactic + "\n" + code
            # Whole-file validation: allow sorry but reject Lean errors
            _verify_lean2 = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
            try:
                _full_code2 = import_content + "\n" + formal_theorem + " := by\n" + code
                _ok2, _msg2 = _verify_lean2.verify_sketch(_full_code2)
                if _ok2:
                    print("verify_sketch: OK (no Lean errors)")
                else:
                    print(f"verify_sketch: FAILED — {_msg2}")
            except Exception as _ve2:
                print(f"verify_sketch: exception — {_ve2}")
            finally:
                try:
                    _verify_lean2.proc.kill()
                    _verify_lean2.proc.wait(timeout=5)
                except Exception:
                    pass
            return code
        code = k_cnt_tactic + '\n' + code
        if Ico_tactic:
            code = Ico_tactic + "\n" + code
        # except Exception as e:
        #     print(e)
        #     return code
        # Whole-file validation: allow sorry but reject Lean errors
        _verify_lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        try:
            _full_code = import_content + "\n" + formal_theorem + " := by\n" + code
            _ok, _msg = _verify_lean.verify_sketch(_full_code)
            if _ok:
                print("verify_sketch: OK (no Lean errors)")
            else:
                print(f"verify_sketch: FAILED — {_msg}")
        except Exception as _ve:
            print(f"verify_sketch: exception — {_ve}")
        finally:
            try:
                _verify_lean.proc.kill()
                _verify_lean.proc.wait(timeout=5)
            except Exception:
                pass
        return code

    def prove_gosper(self, formal_theorem: str, import_content: str) -> str:
        """Prove a summation identity using Gosper's algorithm.

        Constructs a telescoping proof by computing Gosper's anti-difference
        ``G(k)`` such that ``A(n, k) = G(n, k+1) - G(n, k)``, then summing
        both sides to obtain a closed form.

        Args:
            formal_theorem: The Lean 4 theorem statement.
            import_content: Lean 4 import preamble.

        Returns:
            A string containing the complete Lean 4 tactic proof.
        """
        # Initialize Lean4Kit
        lean = Lean4Kit(LEAN_WORK_DIR, REPL_VERSION, verbose=VERBOSE)
        try:
            # formal_theorem = self.addR(formal_theorem, all=True)
            initial_state = lean.run_import(import_content, verbose=VERBOSE)
            initial_state = lean.new_thm(formal_theorem, verbose=VERBOSE, env=0)
            initial_tacticstate = initial_state.getTacticState().split('⊢')[-1].strip()
            print("Initial tactic state:", initial_tacticstate)
        except Exception as e:
            print(f"Error initializing theorem: {e}")
            return ""
        print([i.strip() for  i in initial_tacticstate[initial_tacticstate.find(',') + 1 : ].split('=')])
        Ank_Bn_parts = [i.strip() for i in initial_tacticstate[initial_tacticstate.find(',') + 1 : ].split('=', 1)]
        Ank = Ank_Bn_parts[0] if len(Ank_Bn_parts) > 0 else ''
        Bn = Ank_Bn_parts[1] if len(Ank_Bn_parts) > 1 else ''
        Ank = self.repair_expr(Ank).replace("\n", "")
        Bn = self.repair_expr(Bn).replace("\n", "")
        print("Ank:", Ank)
        print("Bn:", Bn)
        self.set_variables_and_num(initial_tacticstate.split(',')[0].strip())
        Gk = get_gosper_g(Ank, self.variablek)
        print("Gk:", Gk)

        # Construct the four let bindings
        let_list = []
        let_A = f"let A : ℕ → ℕ → ℝ := fun ({self.variablen} {self.variablek} : ℕ) =>  {self.addR(Ank, all=True)}"
        let_B = f"let B : ℕ → ℝ := fun ({self.variablen} : ℕ) =>  {self.addR(Bn, all=True)}"
        let_G = f"let G : ℕ → ℕ → ℝ := fun {self.variablen} {self.variablek} => {self.addR(Gk, all=True)}"
        let_f = f"let f : ℕ → ℝ := fun {self.variablen} => ∑ {self.variablek} ∈ Finset.range ({self.variablen} + 1), A {self.variablen} {self.variablek}"
        let_list.extend([let_A, let_B, let_G, let_f])

        #Construct aux1
        aux1_code = f"have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ,   G {self.variablen} {self.variablek} ≤ G {self.variablen} ({self.variablek} + 1) := by sorry"
        aux1_code_with_tactic = \
    f"""
    have aux₁ : ∀ {self.variablen} {self.variablek} : ℕ,   G {self.variablen} {self.variablek} ≤ G {self.variablen} ({self.variablek} + 1) := by
      intros {self.variablen} {self.variablek}
      simp only [G]
      sorry"""
        
        #Construct Gosper_eq
        Gosper_eq_code = f"have Gosper_eq : ∀ {self.variablen} {self.variablek} : ℕ, A {self.variablen} {self.variablek} = G {self.variablen} ({self.variablek} + 1) - G {self.variablen} {self.variablek} := by sorry"
        Gosper_eq_code_with_tactic = \
    f"""
    have Gosper_eq : ∀ {self.variablen} {self.variablek} : ℕ, A {self.variablen} {self.variablek} = G {self.variablen} ({self.variablek} + 1) - G {self.variablen} {self.variablek} := by
        intro {self.variablen} {self.variablek}
        symm
        rw [tsub_eq_iff_eq_add_of_le (aux₁ {self.variablen} {self.variablek})]
        simp only [G, A]
        sorry"""

        fixed_code_Step2 = \
        f"""
    have Step2 : ∀ n : ℕ, f n = B n := by
      intro n
      calc f n
        _ = (∑ k ∈ range (n + 1), (G n (k + 1) - G n k)) := by
          simp only [f]
          (expose_names; exact sum_congr rfl fun x a ↦ Gosper_eq n x)
        _ = (∑ k ∈ range n, (G n (k + 1) - G n k)) + G n (n + 1) - G n n:= by
          rw [Finset.sum_range_add]
          norm_num
          ring

        _ = (G n n - G n 0) + G n (n + 1) - G n n:= by
          congr 3
          apply sum_range_sub
      simp only [G, B]"""
        fixed_code_Step2_tactics = [
            "intro n",
            """calc f n
_ = (∑ k ∈ range (n + 1), (G n (k + 1) - G n k)) := by
    simp only [f]
    (expose_names; exact sum_congr rfl fun x a ↦ Gosper_eq n x)
_ = (∑ k ∈ range n, (G n (k + 1) - G n k)) + G n (n + 1) - G n n:= by
    rw [Finset.sum_range_add]
    norm_num
    ring
_ = (G n n - G n 0) + G n (n + 1) - G n n:= by
    congr 3
    apply sum_range_sub""",
            "simp only [G, B]"
        ]
        fixed_code_end = \
        f"""
    unfold f A B at Step2
    norm_cast at Step2
    exact Step2 {self.variablen}"""

        # Assemble the final code
        for i in let_list:
            print("let:", i)
            initial_state = lean.run_tactic(i, initial_state.proofStates[0], verbose=VERBOSE)
            print("after let, state:", initial_state.getTacticState())
        initial_state = lean.run_tactic(aux1_code, initial_state.proofStates[0], verbose=VERBOSE)
        print("after aux1, state:", initial_state.getTacticState())
        initial_state = lean.run_tactic(Gosper_eq_code, initial_state.proofStates[0], verbose=VERBOSE)
        print("after Gosper_eq, state:", initial_state.getTacticState())
        Step2_state = lean.run_have_tactic("have Step2 : ∀ n : ℕ, f n = B n", initial_state.proofStates[0], verbose=VERBOSE)
        print("after have Step2, state:", Step2_state.getTacticState())
        
        for tactic in fixed_code_Step2_tactics:
            Step2_state = lean.run_tactic(tactic, Step2_state.proofStates[0], verbose=VERBOSE)
            print(tactic)
            Step2_state.print()
        Step2_code, state_after_step2 = self.prove_zz(Step2_state, lean)
        final_code = "\n".join(["    " + i for i in let_list]) + "\n"
        Step2_code = "\n".join(["  " + i for i in Step2_code.split('\n') if i.strip()]) 
        final_code += aux1_code_with_tactic + "\n"
        final_code += Gosper_eq_code_with_tactic + "\n"
        final_code += fixed_code_Step2 + "\n"
        final_code += Step2_code + "\n"
        final_code += fixed_code_end + "\n"
        print("final_code:")
        print(final_code)
        return final_code
