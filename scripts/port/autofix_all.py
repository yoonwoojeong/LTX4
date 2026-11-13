"""Run autofix.py over every module in dependency order; modules whose imports
still have errors are attempted anyway (they will fail fast on the missing .olean and be
retried in the next sweep). Repeats sweeps until no module changes."""
import os, re, subprocess, sys, json
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import autofix
mods = {}
for r, _, fs in os.walk(os.path.join(ROOT, 'LiquidTensorExperiment')):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(r, f); m = os.path.relpath(p, ROOT)[:-5].replace('/', '.')
            mods[m] = [i for i in re.findall(r'^import (\S+)', open(p).read(), re.M) if i.startswith('LiquidTensorExperiment.')]
order, seen = [], set()
def visit(m):
    if m in seen or m not in mods: return
    seen.add(m)
    for d in mods[m]: visit(d)
    order.append(m)
for m in sorted(mods): visit(m)
res = json.load(open(os.path.join(ROOT, '.lake/compile-results.json')))
done = {m for m, v in res.items() if v['errors'] == 0}
for sweep in range(int(sys.argv[1]) if len(sys.argv) > 1 else 3):
    changed = 0
    for m in order:
        if m in done: continue
        if any(d not in done for d in mods[m]): continue      # deps not clean yet
        sys.argv = ['autofix.py', m]
        rep = autofix.main()
        e0, e1, k = rep[m]
        if e1 == 0: done.add(m)
        if k: changed += 1
    print(f'SWEEP {sweep}: changed {changed}, clean {len(done)}', flush=True)
    if not changed: break
