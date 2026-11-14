"""Compile every LiquidTensorExperiment module in dependency order (bounded parallelism),
recording per-module error counts. Lean 4 writes an .olean even when a file has errors,
so downstream modules are still checked (their own errors are reported separately)."""
import os, re, subprocess, sys, time, json, threading
from concurrent.futures import ThreadPoolExecutor
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, 'LiquidTensorExperiment'); OUT = os.path.join(ROOT, '.lake/build/lib')
LOG = os.path.join(ROOT, '.lake/compile-logs'); os.makedirs(LOG, exist_ok=True)
J = int(sys.argv[1]) if len(sys.argv) > 1 else 3
TIMEOUT = int(os.environ.get('LTE_TIMEOUT', '900'))  # seconds per module
only = set(sys.argv[2:])
mods = {}
for r, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(r, f); m = os.path.relpath(p, ROOT)[:-5].replace('/', '.')
            mods[m] = [i for i in re.findall(r'^import (\S+)', open(p).read(), re.M) if i.startswith('LiquidTensorExperiment.')]
env = dict(os.environ)
env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, capture_output=True, text=True).stdout.strip()
res = {}; cv = threading.Condition()
def run(m):
    t = time.time(); f = os.path.join(ROOT, *m.split('.')) + '.lean'
    o = os.path.join(OUT, *m.split('.')) + '.olean'; os.makedirs(os.path.dirname(o), exist_ok=True)
    try:
        r = subprocess.run(['lean', '-o', o, '-i', o[:-6] + '.ilean', f], cwd=ROOT, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        out, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired as e:
        out = f'{f}:1:0: error: TIMEOUT after {TIMEOUT}s (compile.py)\n'; rc = 1
    open(os.path.join(LOG, m + '.log'), 'w').write(out)
    errs = len(re.findall(r':\d+:\d+: error', out)); sorries = len(re.findall(r"declaration uses 'sorry'", out))
    with cv:
        res[m] = {'errors': errs, 'sorry_warnings': sorries, 'olean': os.path.exists(o), 'secs': round(time.time() - t)}
        cv.notify_all()
    print(f"{'OK ' if errs == 0 and rc == 0 else 'ERR'} {errs:4d} {res[m]['secs']:5d}s {m}", flush=True)
todo = set(mods) if not only else set(only); running = set()
with ThreadPoolExecutor(J) as ex, cv:
    while todo or running:
        ready = [m for m in todo if all(d in res or d not in mods or (only and d not in only) for d in mods[m])]
        for m in sorted(ready)[:max(0, J - len(running))]:
            todo.discard(m); running.add(m)
            def job(m=m):
                try: run(m)
                finally:
                    with cv: running.discard(m); cv.notify_all()
            ex.submit(job)
        cv.wait(2)
json.dump(res, open(os.path.join(ROOT, '.lake/compile-results.json'), 'w'), indent=1)
ok = [m for m, v in res.items() if v['errors'] == 0]
print('SUMMARY modules', len(res), 'clean', len(ok), 'total errors', sum(v['errors'] for v in res.values()))
