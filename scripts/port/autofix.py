"""Error-driven repair of mechanical mathport naming mistranslations.

For each module given, repeatedly: compile it, read Lean's error positions, and propose
*renames only* for these error kinds:

  * `invalid field 'F', the environment does not contain 'T.F'`
  * `'F' is not a field of structure 'S'` (incl. Lean 3 primed fields such as `map_id'`)
  * `unknown identifier 'X'` / `unknown constant 'X'`

A rename is proposed only if the replacement name exists in the environment
(mathlib4 name index + LTE's Lean 4 names), or comes from mathport's own Lean 3 -> Lean 4
translation table. All proposals of a round are applied together; the round is kept only
if the module's error count strictly decreases, otherwise the file is restored and the
loop stops. (A round that leaves the count unchanged but moves the first error later is
also kept: fixing an error often unmasks the next one.) Nothing other than identifiers/field names is ever edited.

Usage: autofix.py [--rounds N] MODULE...
"""
import os, re, subprocess, sys, json

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LAKE = os.path.join(ROOT, '.lake')
TIMEOUT = int(os.environ.get('LTE_TIMEOUT', '900'))  # seconds per compile


def load_lines(p):
    return [l.strip() for l in open(p) if l.strip()] if os.path.exists(p) else []


NAMES = set(load_lines(os.path.join(LAKE, 'mathlib-names.txt'))) | set(load_lines(os.path.join(LAKE, 'lte-names.txt')))
ALIGN = {}
for l in load_lines(os.path.join(LAKE, 'lte-align.txt')):
    a, _, b = l.partition(' ')
    ALIGN[a] = b
SUFFIX = {}
for n in NAMES:
    parts = n.split('.')
    for i in range(1, len(parts)):
        SUFFIX.setdefault('.'.join(parts[i:]), set()).add(n)
ALIGN_SUFFIX = {}
for a, b in ALIGN.items():
    parts = a.split('.')
    for i in range(1, len(parts)):
        ALIGN_SUFFIX.setdefault('.'.join(parts[i:]), set()).add(b)


def lower_camel(s):
    if '_' not in s.strip('_'):
        return s[:1].lower() + s[1:]
    head, *rest = [p for p in s.split('_') if p]
    return head[:1].lower() + head[1:] + ''.join(p[:1].upper() + p[1:] for p in rest)


def upper_camel(s):
    return ''.join(p[:1].upper() + p[1:] for p in s.split('_') if p)


def decap(s):
    return s[:1].lower() + s[1:]


def known(n):
    return n in NAMES or n in SUFFIX


def field_candidates(field, owner):
    cands = [decap(field), lower_camel(field), upper_camel(field)]
    if field.endswith("'"):
        cands.insert(0, field.rstrip("'"))   # Lean 3 `map_id'` style fields -> Lean 4 `map_id`
    if field == 'pt':
        cands.insert(0, 'X')   # mathport renames cone `X` -> `pt`, also wrongly for complexes
    out = []
    for c in cands:
        if c != field and c not in out and f'{owner}.{c}' in NAMES:
            out.append(c)
    return out


def ident_candidates(x):
    if x in ALIGN and known(ALIGN[x]):
        return [ALIGN[x]]
    if x in ALIGN_SUFFIX:
        tgts = {t for t in ALIGN_SUFFIX[x] if known(t)}
        if len(tgts) == 1:
            return [tgts.pop()]
    comps = x.split('.')
    ns = [upper_camel(c) if c[:1].islower() else c for c in comps[:-1]]
    last = comps[-1]
    out = []
    for l in (last, lower_camel(last), upper_camel(last), decap(last)):
        c = '.'.join(ns + [l])
        if c != x and known(c) and c not in out:
            out.append(c)
    return out[:1]


ERR = re.compile(r'^(?P<f>/[^:\n]+\.lean):(?P<l>\d+):(?P<c>\d+): error: (?P<m>.*)$', re.M)


def compile_module(mod, env):
    f = os.path.join(ROOT, *mod.split('.')) + '.lean'
    o = os.path.join(LAKE, 'build/lib', *mod.split('.')) + '.olean'
    os.makedirs(os.path.dirname(o), exist_ok=True)
    try:
        r = subprocess.run(['lean', '-o', o, '-i', o[:-6] + '.ilean', f], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=TIMEOUT)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        # a timed-out round is never accepted: report it as worse than any real result
        out = '\n'.join(f'{f}:1:0: error: TIMEOUT' for _ in range(10**4))
    os.makedirs(os.path.join(LAKE, 'compile-logs'), exist_ok=True)
    open(os.path.join(LAKE, 'compile-logs', mod + '.log'), 'w').write(out)
    return out


def proposals(out, lines):
    edits = []
    for m in ERR.finditer(out):
        ln, col, msg = int(m['l']) - 1, int(m['c']), m['m']
        if ln >= len(lines):
            continue
        line = lines[ln]
        mm = re.match(r"invalid field '([^']+)', the environment does not contain '(.+)\.\1'", msg)
        if mm:
            field, owner = mm.groups()
            for c in field_candidates(field, owner):
                for k in re.finditer(r'\.' + re.escape(field) + r"(?![\w'₀-₉])", line):
                    if k.start() >= col:
                        edits.append((ln, k.start() + 1, field, c))
                        break
                break
            continue
        mm = re.match(r"'([^']+)' is not a field of structure '([^']+)'", msg)
        if mm:
            field, owner = mm.groups()
            if line[col:col + len(field)] == field:
                for c in field_candidates(field, owner):
                    edits.append((ln, col, field, c))
                    break
            continue
        mm = re.match(r"unknown (?:identifier|constant) '([^']+)'", msg)
        if mm:
            x = mm.group(1)
            if line[col:col + len(x)] == x:
                for c in ident_candidates(x):
                    edits.append((ln, col, x, c))
                    break
    return edits


def apply(lines, edits):
    # apply right-to-left per line, skipping overlaps / duplicates
    by_line = {}
    for e in set(edits):
        by_line.setdefault(e[0], []).append(e)
    n = 0
    for ln, es in by_line.items():
        es.sort(key=lambda e: -e[1])
        last = None
        s = lines[ln]
        for _, col, old, new in es:
            if last is not None and col + len(old) > last:
                continue
            if s[col:col + len(old)] != old:
                continue
            s = s[:col] + new + s[col + len(old):]
            last = col
            n += 1
        lines[ln] = s
    return n


def count_errors(out):
    return len(ERR.findall(out))


def first_error(out):
    m = ERR.search(out)
    return (int(m['l']), int(m['c'])) if m else (10**9, 0)


def main():
    args = sys.argv[1:]
    rounds = 8
    if args and args[0] == '--rounds':
        rounds = int(args[1]); args = args[2:]
    env = dict(os.environ)
    env['LEAN_PATH'] = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT,
                                      capture_output=True, text=True).stdout.strip()
    report = {}
    for mod in args:
        path = os.path.join(ROOT, *mod.split('.')) + '.lean'
        out = compile_module(mod, env)
        errs0 = errs = count_errors(out)
        applied = 0
        for _ in range(rounds):
            if errs == 0:
                break
            text = open(path).read()
            lines = text.split('\n')
            edits = proposals(out, lines)
            if not edits:
                break
            k = apply(lines, edits)
            if not k:
                break
            open(path, 'w').write('\n'.join(lines))
            out2 = compile_module(mod, env)
            e2 = count_errors(out2)
            if e2 < errs or (e2 == errs and first_error(out2) > first_error(out)):
                errs, out, applied = e2, out2, applied + k
            else:
                open(path, 'w').write(text)
                compile_module(mod, env)
                break
        report[mod] = (errs0, errs, applied)
        print(f'{mod}: errors {errs0} -> {errs} ({applied} renames)', flush=True)
    return report


if __name__ == '__main__':
    main()
