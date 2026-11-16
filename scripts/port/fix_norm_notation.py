"""Rewrite mathport's untranslated mathlib3 norm notation into Lean 4 syntax.

LTE uses the old mathlib3 notation `∥x∥` / `∥x∥₊` (renamed `‖x‖` in mathlib3 after LTE's pinned
commit), which mathport does not know; it emits the prefix-application form
`«expr∥ ∥» ARG` / `«expr∥ ∥₊» ARG`. ARG is always a single argument (parenthesised if compound),
so this rewrite to `‖ARG‖` / `‖ARG‖₊` is purely mechanical. Usage: fix_norm_notation.py FILE...
"""
import re, sys
OPEN = {'(': ')', '⟨': '⟩', '[': ']', '{': '}'}
STOP = set(' \t\n),]}⟩,:;')
def arg_end(s, i):
    if s[i] in OPEN:
        depth, j = 0, i
        stack = []
        while j < len(s):
            c = s[j]
            if c in OPEN: stack.append(OPEN[c])
            elif stack and c == stack[-1]:
                stack.pop()
                if not stack: return j + 1
            j += 1
        raise ValueError('unbalanced')
    j = i
    while j < len(s) and s[j] not in STOP and s[j] not in '([{⟨':
        j += 1
    # allow trailing projections/applications like `x.1` are already in the run; `f (x)` is not an arg
    return j
def fix(s):
    # First drop mathport's warning comments for this notation (they contain the token too).
    s = re.sub(r'/- ./././Mathport/Syntax/Translate/Expr.lean:\d+:\d+: warning: unsupported notation `«expr∥ ∥₊?» -/\n', '', s)
    out, n = [], 0
    pat = re.compile(r'«expr∥ ∥(₊?)»\s*')
    pos = 0
    while True:
        m = pat.search(s, pos)
        if not m: break
        a0 = m.end(); a1 = arg_end(s, a0)
        arg = s[a0:a1]
        if arg.startswith('(') and arg.endswith(')') and arg.count('(') == 1:
            arg = arg[1:-1]
        out.append(s[pos:m.start()]); out.append(f'‖{arg}‖{m.group(1)}'); pos = a1; n += 1
    out.append(s[pos:])
    s = ''.join(out)
    return s, n
if __name__ == '__main__':
    tot = 0
    for p in sys.argv[1:]:
        s = open(p).read(); t, n = fix(s)
        if n or t != s: open(p, 'w').write(t); tot += n
    print('rewrote', tot)
