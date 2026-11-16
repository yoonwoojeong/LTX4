"""Semantics-preserving edits applied to a *working copy* of the Lean 3 source before running
mathport (the preserved original in `lean3/` is untouched).

* `asyncI { tac }` -> `{ tac }`: LTE's `asyncI` (hacks_and_tricks/asyncI.lean) proves the first
  goal with `tac` as a separate asynchronously-elaborated lemma, purely for speed; `{ tac }`
  runs the same tactic on the same goal. mathport cannot translate the `asyncI` call (it
  comments the whole block out), but it does translate `{ tac }`.

Usage: lean3_premathport.py LEAN3_SRC_DIR  (then re-export the changed files with
`lean --ast --tlean FILE` and re-run mathport on those modules)."""
import os, re, sys
root = sys.argv[1]
for r, _, fs in os.walk(root):
    for f in fs:
        if not f.endswith('.lean') or 'hacks_and_tricks' in r: continue
        p = os.path.join(r, f); s = open(p).read()
        t = re.sub(r'\basyncI\s*(?=\{)', '', s)
        if t != s:
            open(p, 'w').write(t); print('rewrote', os.path.relpath(p, root), len(re.findall(r'\basyncI\s*(?=\{)', s)))


# ---------------------------------------------------------------------------------------------
# * `​e` (zero-width space; hacks_and_tricks/by_exactI_hack.lean) -> `(by exactI e)`.
#   That user notation is *defined* as `by exactI e`; mathport cannot translate user notation
#   and replaced these expressions -- including the statement of `first_target` -- by an error
#   string. The extent of `e` is: up to the matching `)` when the notation sits directly after
#   `(`, otherwise up to the next depth-0 `:=` or blank line.
ZWSP = '​'
def expand_zwsp(s):
    out, i = [], 0
    while True:
        j = s.find(ZWSP, i)
        if j < 0: out.append(s[i:]); break
        out.append(s[i:j]); k = j + 1; depth = 0
        inside_paren = s[:j].rstrip().endswith('(')
        while k < len(s):
            c = s[k]
            if c in '([{⟨': depth += 1
            elif c in ')]}⟩':
                if depth == 0: break           # closing paren of the enclosing `( … )`
                depth -= 1
            elif depth == 0 and not inside_paren and (s.startswith(':=', k) or s.startswith('\n\n', k)):
                break
            k += 1
        e = s[j + 1:k]; core = e.rstrip(); tail = e[len(core):]
        out.append('(by exactI ' + core + ')' + tail); i = k
    return ''.join(out)
if __name__ == '__main__' and len(sys.argv) > 1:
    for r, _, fs in os.walk(sys.argv[1]):
        for f in fs:
            if not f.endswith('.lean') or 'hacks_and_tricks' in r: continue
            p = os.path.join(r, f); s = open(p).read()
            if ZWSP in s:
                open(p, 'w').write(expand_zwsp(s)); print('expanded', s.count(ZWSP), 'zwsp in', os.path.relpath(p, sys.argv[1]))
