"""Summarise .lake/compile-results.json: clean / own-error / blocked modules, ranked by impact."""
import json, re, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
r = json.load(open(os.path.join(ROOT, '.lake/compile-results.json')))
log = lambda m: open(os.path.join(ROOT, '.lake/compile-logs', m + '.log')).read()
deps = {m: [i for i in re.findall(r'^import (\S+)', open(os.path.join(ROOT, *m.split('.')) + '.lean').read(), re.M) if i in r] for m in r}
rev = {}
for m, ds in deps.items():
    for d in ds: rev.setdefault(d, set()).add(m)
def desc(m):
    s, st = set(), [m]
    while st:
        for y in rev.get(st.pop(), ()):
            if y not in s: s.add(y); st.append(y)
    return s
blocked = {m for m in r if 'does not exist' in log(m)}
clean = sorted(m for m, v in r.items() if v['errors'] == 0 and v['sorry_warnings'] == 0)
own = [m for m in r if m not in blocked and m not in clean]
print(f'clean {len(clean)}  own-errors {len(own)}  blocked {len(blocked)}  own-error total {sum(r[m]["errors"] for m in own)}')
if '-v' in sys.argv:
    for d, e, m in sorted(((len(desc(m)), r[m]['errors'], m) for m in own), reverse=True)[:int(sys.argv[-1]) if sys.argv[-1].isdigit() else 25]:
        print(f'{d:4d} blocked {e:4d} err  {m[23:]}')
