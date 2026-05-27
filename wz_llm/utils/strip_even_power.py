#!/usr/bin/env python3
"""
Strip the outermost even power from a mathematical expression.

Examples:
  ((2 * ↑n - (↑k + 1) + 2) ^ 2)  ->  (2 * ↑n - (↑k + 1) + 2)
  ((x + 1) ^ 3)                   ->  ((x + 1) ^ 3)  (odd power, unchanged)
  ((a ^ 2) + b)                   ->  ((a ^ 2) + b)  (inner power, unchanged)
"""


def strip_outer_even_power(expr):
    """
    If the outermost operation of the expression is ^ with an even exponent,
    strip that power and return the base; otherwise return as-is.

    Definition of "outermost":
      1. Strip all matching outer parentheses
      2. Find the last '^' at depth 0 in the remaining content
      3. Ensure the base has no +, -, *, / at depth 0 (i.e. ^ is the main operator)
      4. The exponent must be an even integer
    """
    s = expr.strip()
    if not s:
        return s

    # ---------- Handle ↑(...) prefix ----------
    if s.startswith('↑('):
        inner_result = strip_outer_even_power(s[1:])
        if inner_result != s[1:]:
            return '↑' + inner_result
        return expr

    # ---------- Strip matching outer parentheses ----------
    inner = s
    while inner.startswith('(') and inner.endswith(')'):
        depth, match = 1, -1
        for i in range(1, len(inner)):
            if inner[i] == '(':
                depth += 1
            elif inner[i] == ')':
                depth -= 1
                if depth == 0:
                    match = i
                    break
        if match == len(inner) - 1:
            inner = inner[1:-1].strip()
        else:
            break

    # ---------- Find the last '^' at depth 0 ----------
    depth = 0
    last_caret = -1
    for i, ch in enumerate(inner):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch == '^' and depth == 0:
            last_caret = i

    if last_caret == -1:
        return expr

    base = inner[:last_caret].strip()
    power_str = inner[last_caret + 1:].strip()

    # ---------- Verify ^ is the main operator ----------
    depth = 0
    for i, ch in enumerate(base):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif depth == 0 and ch in ('+', '-', '*', '/'):
            if ch == '-' and i == 0:
                continue          # allow unary minus
            return expr           # lower-precedence operator found, ^ is not the main op

    # ---------- Check even power ----------
    try:
        if int(power_str) % 2 == 0:
            return base
    except ValueError:
        pass

    return expr


# --------------- Tests ---------------
if __name__ == "__main__":
    tests = [
        ("((2 * ↑n - (↑k + 1) + 2) ^ 2)", "(2 * ↑n - (↑k + 1) + 2)"),
        ("((2 * ↑n - ↑k + 2) ^ 2)",       "(2 * ↑n - ↑k + 2)"),
        ("((2 * ↑n - ↑k + 3) ^ 2)",       "(2 * ↑n - ↑k + 3)"),
        ("((2 * ↑n - (↑k + 1) + 3) ^ 2)", "(2 * ↑n - (↑k + 1) + 3)"),
        ("((a + b) ^ 4)",   "(a + b)"),
        ("(x ^ 8)",         "x"),
        ("((a + b) ^ 3)",   "((a + b) ^ 3)"),
        ("(x ^ 1)",         "(x ^ 1)"),
        ("((a ^ 2) + b)",   "((a ^ 2) + b)"),
        ("((a ^ 3) ^ 2)",   "(a ^ 3)"),
        ("((a ^ 2) ^ 3)",   "((a ^ 2) ^ 3)"),
        ("a + b ^ 2",       "a + b ^ 2"),
        ("(((a + b) ^ 2))", "(a + b)"),
        ("((a + b) ^ 2) * c", "((a + b) ^ 2) * c"),
        ("((a + b) ^ k)",   "((a + b) ^ k)"),
        # ====== ↑ prefix + even power -> strip power, keep ↑ ======
        ("↑(((2 * r - a).choose r) ^ 2)", "↑((2 * r - a).choose r)"),
        # ====== No ↑ prefix + .choose + even power ======
        ("(((2 * r - a).choose r) ^ 2)", "((2 * r - a).choose r)"),
        # ====== ↑ prefix + odd power -> unchanged ======
        ("↑(((2 * r - a).choose r) ^ 3)", "↑(((2 * r - a).choose r) ^ 3)"),
        # ====== ↑ prefix but no power -> unchanged ======
        ("↑((2 * r - a).choose r)", "↑((2 * r - a).choose r)"),
        # ====== ↑ on variable (no parens), should not trigger ======
        ("↑n ^ 2", "↑n"),
    ]
    passed = failed = 0
    for inp, expected in tests:
        result = strip_outer_even_power(inp)
        ok = result == expected
        passed += ok
        failed += not ok
        tag = "PASS" if ok else "FAIL"
        print(f"  {tag}: {inp!r}  →  {result!r}")
        if not ok:
            print(f"        Expected: {expected!r}")
    print(f"\n{passed}/{passed + failed} passed")
