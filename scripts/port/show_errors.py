"""Print each error of a module with its source line. Usage: show_errors.py MODULE [maxlines]"""
import os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
m = sys.argv[1]; k = int(sys.argv[2]) if len(sys.argv) > 2 else 6
src = open(os.path.join(ROOT, *m.split('.')) + '.lean').read().split('\n')
out = open(os.path.join(ROOT, '.lake/compile-logs', m + '.log')).read()
for b in re.split(r'\n(?=/[^\n]*\.lean:\d+:\d+: )', out):
    h = re.match(r'/[^\n]*\.lean:(\d+):(\d+): error: ', b)
    if not h: continue
    ln = int(h[1]); body = b[h.end():].split('\n')
    print(f'--- L{ln}:{h[2]}  | {src[ln-1].strip()[:150]}')
    for l in body[:k]: print('    ' + l[:170])
