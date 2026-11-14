"""Copy mathport synport output into the Lean 4 project, rewriting imports only.

* `import X` (local LTE module) -> `import LiquidTensorExperiment.X`
* `import X` (mathlib3 module, snake2pascal) -> mathlib4 module from `#align_import`
* `import Mathbin.Tactic.Default` (Lean 3 `import tactic`) -> `import Mathlib.Tactic`
* `import Mathbin.<shim>` (mathlib3 modules split/renamed after LTE's pinned
  mathlib3 commit) -> the mathlib4 successors listed in the shim
* `import Leanbin.Init.Default` etc. (Lean 3 core prelude) -> dropped
No proof or statement text is modified.
"""
import os, re, sys, shutil
SRC, SHIMS, MATHLIB, DST, IMPORT_RENAME = sys.argv[1:6]
import json
def s2p(x):
    r = ''.join(c[:1].upper() + c[1:] for c in x.split('_'))
    return ('_' if x.startswith('_') else '') + r + ('_' if x.endswith('_') and len(x) > 1 else '')
# mathport (nightly-2023-11-30) names mathlib3 modules by snake2pascal of the mathlib3 path;
# map those to the real mathlib4 module via mathlib4's `#align_import` table.
via_align = {'.'.join(s2p(c) for c in k.split('.')): v
             for k, v in json.load(open(IMPORT_RENAME)).items()}
local = set()
for root, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith('.lean'):
            local.add(os.path.relpath(os.path.join(root, f[:-5]), SRC).replace('/', '.'))
shim = {}
for root, _, fs in os.walk(SHIMS):
    for f in fs:
        if f.endswith('.lean'):
            mod = os.path.relpath(os.path.join(root, f[:-5]), SHIMS).replace('/', '.')
            imps = re.findall(r'^import (\S+)', open(os.path.join(root, f)).read(), re.M)
            shim[mod] = [via_align.get(i[len('Mathbin.'):], 'Mathlib.' + i[len('Mathbin.'):]) for i in imps]
shim['Mathbin.CategoryTheory.Additive.Basic'] = ['LiquidTensorExperiment.Compat.AdditiveCategory']
# Shims may import other shims: expand recursively.
def expand(ms, seen=()):
    out = []
    for i in ms:
        key = next((k for k, v in shim.items() if i == via_align.get(k[8:], 'Mathlib.' + k[8:])), None)
        if key and key not in seen: out += expand(shim[key], seen + (key,))
        else: out.append(i)
    return out
for k in list(shim): shim[k] = expand(shim[k], (k,))
# mathlib3 modules with no `#align_import` (tactic files; split topology file).
manual = {
    'Tactic.Linarith.Default': ['Mathlib.Tactic.Linarith'],
    'Tactic.RingExp': ['Mathlib.Tactic.Ring'],
    # mathlib4 #7628 split topology/subset_properties into these:
    'Topology.SubsetProperties': ['Mathlib.Topology.Compactness.Compact', 'Mathlib.Topology.Clopen',
        'Mathlib.Topology.Compactness.LocallyCompact', 'Mathlib.Topology.Compactness.SigmaCompact',
        'Mathlib.Topology.Compactness.Paracompact', 'Mathlib.Topology.Irreducible'],
}
def exists(mod):
    return os.path.exists(os.path.join(MATHLIB, *mod.split('.')) + '.lean')
unresolved = set()
def rewrite(m):
    if m.startswith('LiquidTensorExperiment.'): return [m]
    if m in local: return ['LiquidTensorExperiment.' + m]
    if m.startswith('Leanbin.'): return []
    if m == 'Mathbin.Tactic.Default': return ['Mathlib.Tactic']
    if m in shim: return shim[m]
    if m.startswith('Mathbin.'): m = m[len('Mathbin.'):]
    if m in manual: return manual[m]
    if m in via_align: return [via_align[m]]
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
