"""Copy mathport synport output into the Lean 4 project, rewriting imports only.

* `import X` (mathlib4 module emitted without prefix)  -> `import Mathlib.X`
* `import Mathbin.Tactic.Default` (Lean 3 `import tactic`) -> `import Mathlib.Tactic`
* `import Mathbin.<shim>` (mathlib3 modules split/renamed after LTE's pinned
  mathlib3 commit) -> the mathlib4 successors listed in the shim
* `import Leanbin.Init.Default` etc. (Lean 3 core prelude) -> dropped
No proof or statement text is modified.
"""
import os, re, sys, shutil
SRC, SHIMS, MATHLIB, DST = sys.argv[1:5]
shim = {}
for root, _, fs in os.walk(SHIMS):
    for f in fs:
        if f.endswith('.lean'):
            mod = os.path.relpath(os.path.join(root, f[:-5]), SHIMS).replace('/', '.')
            imps = re.findall(r'^import (\S+)', open(os.path.join(root, f)).read(), re.M)
            shim[mod] = ['Mathlib.' + i[len('Mathbin.'):] for i in imps]
shim['Mathbin.CategoryTheory.Additive.Basic'] = ['LiquidTensorExperiment.Compat.AdditiveCategory']
def exists(mod):
    return os.path.exists(os.path.join(MATHLIB, *mod.split('.')) + '.lean')
unresolved = set()
def rewrite(m):
    if m.startswith('LiquidTensorExperiment.'): return [m]
    if m.startswith('Leanbin.'): return []
    if m == 'Mathbin.Tactic.Default': return ['Mathlib.Tactic']
    if m in shim: return shim[m]
    if m.startswith('Mathbin.'): m = m[len('Mathbin.'):]
    if exists('Mathlib.' + m): return ['Mathlib.' + m]
    unresolved.add(m); return ['Mathlib.' + m]
n = 0
for root, _, fs in os.walk(SRC):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(root, f); rel = os.path.relpath(p, SRC)
        out = []
        for line in open(p).read().split('\n'):
            mt = re.match(r'^import (\S+)\s*$', line)
            if mt:
                for i in rewrite(mt.group(1)):
                    if f'import {i}' not in out: out.append(f'import {i}')
            else:
                out.append(line)
        q = os.path.join(DST, rel); os.makedirs(os.path.dirname(q), exist_ok=True)
        open(q, 'w').write('\n'.join(out)); n += 1
print(n, 'files;', 'unresolved imports:', sorted(unresolved))
