"""One-pass mechanical repair of mathport naming mistranslations, project-wide.

Unlike `autofix.py` (which is error-driven and only keeps a round when the error count
drops), this applies a fixed set of *renames* everywhere. It exists because fixing one
naming error often lets Lean elaborate further and report new, unrelated errors, so the
error count alone is a poor acceptance test. Every rule is a pure rename:

  1. Lean 3 primed structure fields that are unprimed in Lean 4 (`hom_inv_id'`,
     `map_comp'`, `naturality'`, ...) when used as a field in structure-instance notation
     (at the start of a line, followed by binders and `:=`).
  2. The `Iso` field `Hom :=` (mathport capitalises it) -> `hom :=`.
  3. Identifiers that do not exist in Lean 4 (neither in mathlib4 nor in LTE's own Lean 4
     declarations) and that are Lean 3 style: dotted with a lowercase namespace component
     (`category.assoc`) or snake_case. They are renamed only if mathport's own Lean 3 ->
     Lean 4 translation table, or the snake_case -> lowerCamel/UpperCamel convention,
     gives exactly one name that *does* exist.

Comments are not touched. Usage: mechanical.py [--dry-run] [FILE...]
(default: every file under LiquidTensorExperiment/).
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from autofix import NAMES, SUFFIX, ALIGN, ALIGN_SUFFIX, known, upper_camel, lower_camel, ROOT  # noqa: E402

# Only fields that are unprimed in mathlib4 (`AddMonoidHom.map_zero'`, `LinearMap.map_add'`,
# `map_smul'`, ... are still primed and must not be listed here).
PRIMED = ['hom_inv_id', 'inv_hom_id', 'map_id', 'map_comp', 'naturality', 'id_comp', 'comp_id',
          'assoc', 'map_injective', 'left_cancellation', 'right_cancellation']
FIELD_RE = re.compile(r"(?m)^(\s*)(" + '|'.join(PRIMED) + r")'(?=[\s:])")
HOM_RE = re.compile(r"(?m)^(\s*(?:\{ )?)Hom :=")
TOKEN = re.compile(r"(?<![\w.'`«])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+|[a-z][a-z0-9]*(?:_[a-z0-9']+)+)(?![\w'])")


# Lean 4 tactic / command names that are snake_case (never rename these)
TACTICS = set("""infer_instance apply_fun all_goals any_goals split_ifs push_neg push_cast fin_cases
rotate_left rotate_right align_import norm_num norm_cast exact_mod_cast apply_mod_cast simp_rw
simp_all field_simp apply_rules by_cases by_contra interval_cases set_option apply_instance
change_at refine_struct rcases_patt simp_intro unfold_let nth_rewrite nth_rw erw_at
use_discharger exacts_mod split_ands generalize_proofs choose_spec conv_lhs conv_rhs
delta_instance aesop_cat apply_assumption positivity_ext linear_combination congr_arg
congr_fun""".split())


def shorten(x, full):
    """Keep the qualification depth of the source token: `category.assoc` -> `Category.assoc`."""
    sc, fc = x.split('.'), full.split('.')
    if len(fc) > len(sc) and len(sc) > 1:
        tail = fc[-len(sc):]
        if all(a.replace('_', '').lower() == b.replace('_', '').lower() for a, b in zip(sc[:-1], tail[:-1])):
            return '.'.join(tail)
    return full


def candidates(x):
    if x in TACTICS:
        return set()
    if x in ALIGN and known(ALIGN[x]):
        return {ALIGN[x]}
    if x in ALIGN_SUFFIX:
        t = {c for c in ALIGN_SUFFIX[x] if known(c)}
        if t:
            return t
    if '.' not in x:
        return set()   # undotted names only via mathport's own translation table
    comps = x.split('.')
    ns = [upper_camel(c) if c[:1].islower() else c for c in comps[:-1]]
    last = comps[-1]
    out = set()
    for l in (last, lower_camel(last), upper_camel(last)):
        c = '.'.join(ns + [l])
        if c != x and known(c):
            out.add(c)
    return out


def lean3_style(x):
    comps = x.split('.')
    return '_' in x or any(c[:1].islower() for c in comps[:-1])


def split_comments(text):
    """Yield (is_code, chunk)."""
    i, n = 0, len(text)
    out = []
    buf = []
    while i < n:
        if text.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/-', j): depth += 1; j += 2
                elif text.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            out.append((True, ''.join(buf))); buf = []
            out.append((False, text[i:j])); i = j
        elif text.startswith('--', i):
            j = text.find('\n', i); j = n if j < 0 else j
            out.append((True, ''.join(buf))); buf = []
            out.append((False, text[i:j])); i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append((True, ''.join(buf))); buf = []
            out.append((False, text[i:j + 1])); i = j + 1
        else:
            buf.append(text[i]); i += 1
    out.append((True, ''.join(buf)))
    return out


BINDER_RE = [re.compile(r"[(\{\[⟨⦃]\s*((?:[\w'₀-₉]+\s+)*[\w'₀-₉]+)\s*:(?!=)"),
             re.compile(r"\b(?:fun|λ|intro|intros|rintro|obtain|let|have|set|cases|induction'|with|∀|∃|Σ|Π)\s+((?:[\w'₀-₉⟨⟩,|() ]+?))(?=\s*(?:=>|,|:|$|\n|;))", re.M),
             re.compile(r"⟨\s*([^⟩:=]*?)⟩")]


STRUCT_RE = re.compile(r"(?ms)^(?:@\[[^\n]*\]\s*)?(?:protected\s+)?(?:structure|class)\s[^\n]*?where\n(.*?)(?=^\S)")


def bound_names(text):
    out = set()
    # structure fields: inside a `structure` declaration, `iso.hom` is a projection of the field
    # `iso`, not the constant `Iso.hom`
    for m in STRUCT_RE.finditer(text):
        out.update(re.findall(r"(?m)^\s+\[?([A-Za-z_][\w']*)\s*:(?!=)", m.group(1)))
    for r in BINDER_RE:
        for m in r.finditer(text):
            out.update(re.findall(r"[A-Za-z_][\w']*", m.group(1)))
    return out


FIELD_DOT = re.compile(r"(?<=[\w')}\]₀-₉])\.([A-Za-z_][\w']*)(?![\w'])")
CAP_FIELDS = {'Hom': 'hom', 'Surjective': 'surjective', 'Injective': 'injective',
              'Bijective': 'bijective', 'Continuous': 'continuous'}
LAST = {}
for _a, _b in ALIGN.items():
    LAST.setdefault(_a.split('.')[-1], set()).add(_b.split('.')[-1])


def field_fix(code, m, log):
    f = m.group(1)
    # the segment before the dot: only rewrite field projections on terms (lowercase variable,
    # or a closing bracket), not namespaces such as `Endomorphisms.Hom`
    j = m.start()
    k = j
    while k > 0 and (code[k - 1].isalnum() or code[k - 1] in "_'₀₁₂₃₄₅₆₇₈₉"):
        k -= 1
    seg = code[k:j]
    if not (seg[:1].islower() or code[j - 1] in ')}]'):
        return None
    if f in CAP_FIELDS:
        return CAP_FIELDS[f]
    if '_' not in f or f in SUFFIX:
        return None
    c = {x for x in LAST.get(f, ()) if x in SUFFIX}
    if len(c) == 1:
        return c.pop()
    lc = lower_camel(f)
    if lc in SUFFIX:
        return lc
    return None


# Lean 3 `@[simp, reassoc]` also made the generated `_assoc` lemma a simp lemma; in Lean 4 this
# is written `@[reassoc (attr := simp)]` (same for `elementwise`). mathport kept the Lean 3 form.
ATTR_RE = re.compile(r"(@\[|attribute \[)(?:simp, (reassoc|elementwise)|(reassoc|elementwise), simp)\]")


def fix_code(code, log, bound=frozenset()):
    code, k = ATTR_RE.subn(lambda m: f"{m.group(1)}{m.group(2) or m.group(3)} (attr := simp)]", code)
    log['attr'] = log.get('attr', 0) + k
    code, k = FIELD_RE.subn(r'\1\2', code); log['primed field'] += k
    code, k = HOM_RE.subn(r'\1hom :=', code); log['Hom field'] += k

    def tok(m):
        x = m.group(1)
        if known(x) or not lean3_style(x) or x.startswith('_') or x in bound or x.split('.')[0] in bound:
            return x
        # never rename a declaration being defined, or a binder
        pre = code[max(0, m.start() - 40):m.start()]
        if re.search(r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|namespace|section|end|fun|let|have|intro|rintro|obtain|set|variable)\s+$', pre):
            return x
        c = candidates(x)
        if len(c) == 1:
            new = shorten(x, c.pop())
            log['ident'] += 1
            log.setdefault('pairs', {}).setdefault(f'{x} -> {new}', 0)
            log['pairs'][f'{x} -> {new}'] += 1
            return new
        return x
    code = TOKEN.sub(tok, code)

    def fld(m):
        new = field_fix(code, m, log)
        if new is None:
            return m.group(0)
        log['field'] = log.get('field', 0) + 1
        log['pairs'][f'.{m.group(1)} -> .{new}'] = log['pairs'].get(f'.{m.group(1)} -> .{new}', 0) + 1
        return '.' + new
    return FIELD_DOT.sub(fld, code)


def main():
    args = sys.argv[1:]
    dry = '--dry-run' in args
    files = [a for a in args if a != '--dry-run']
    if not files:
        for r, _, fs in os.walk(os.path.join(ROOT, 'LiquidTensorExperiment')):
            files += [os.path.join(r, f) for f in fs if f.endswith('.lean')]
    total = {'primed field': 0, 'Hom field': 0, 'ident': 0, 'field': 0, 'pairs': {}}
    changed = 0
    for f in sorted(files):
        text = open(f).read()
        log = {'primed field': 0, 'Hom field': 0, 'ident': 0, 'field': 0, 'pairs': {}}
        bound = bound_names(text)
        new = ''.join(fix_code(c, log, bound) if code else c for code, c in split_comments(text))
        total['attr'] = total.get('attr', 0) + log.get('attr', 0)
        for k in ('primed field', 'Hom field', 'ident', 'field'):
            total[k] += log[k]
        for p, v in log['pairs'].items():
            total['pairs'][p] = total['pairs'].get(p, 0) + v
        if new != text:
            changed += 1
            if not dry:
                open(f, 'w').write(new)
    print(f"files changed {changed}; primed fields {total['primed field']}; Hom fields {total['Hom field']}; identifiers {total['ident']}; dot-fields {total['field']}; simp attrs {total.get('attr', 0)}")
    if dry:
        for p, v in sorted(total['pairs'].items(), key=lambda t: -t[1]):
            print(f'{v:5d}  {p}')


if __name__ == '__main__':
    main()
