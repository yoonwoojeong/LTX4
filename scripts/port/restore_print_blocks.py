"""mathport replaces an LTE declaration by `#print X /- <original decl> -/` when a declaration
named X already existed in (final-mathlib3) Mathbin. That judgement is by name only and is
unreliable (e.g. mathlib's `CategoryTheory.yoneda'` is an unrelated sheaf functor), so by
default every such block is restored to LTE's own declaration; a genuine duplicate then shows
up as an explicit "already declared" compile error to be reviewed. With `--missing-only`, only
blocks whose name is absent from the pinned mathlib4 are restored."""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
names = set(l.strip() for l in open(os.path.join(ROOT, '.lake/mathlib-names.txt')))
n = 0
for r, _, fs in os.walk(os.path.join(ROOT, 'LiquidTensorExperiment')):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(r, f); lines = open(p).read().split('\n'); out = []; i = 0; changed = False
        while i < len(lines):
            m = re.match(r'^#print (\S+) /-$', lines[i])
            if m and (m.group(1) not in names or '--missing-only' not in sys.argv):
                j = i + 1
                while lines[j] != '-/': j += 1
                out.extend(lines[i + 1:j]); i = j + 1; n += 1; changed = True
                print('restored', m.group(1), 'in', os.path.relpath(p, ROOT))
            else:
                out.append(lines[i]); i += 1
        if changed: open(p, 'w').write('\n'.join(out))
print('restored', n)
