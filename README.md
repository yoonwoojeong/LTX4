# Liquid Tensor Experiment — Lean 4 port (work in progress)

This repository contains an in-progress port of the
[Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid) (LTE)
from Lean 3 to Lean 4, produced with **mathport** and then repaired by hand and by
small, auditable scripts.

**The port is not complete.** See [`PORTING_STATUS.md`](PORTING_STATUS.md) for the current
per-module status. No `sorry`, `admit` or new axioms have been introduced to make modules
compile, and no theorem statement has been weakened.

| Path | Contents |
|---|---|
| `lean3/` | The original Lean 3 source, verbatim (`leanprover-community/lean-liquid@ee47958`). |
| `LiquidTensorExperiment/` | The Lean 4 port (mathport output + repairs). |
| `LiquidTensorExperiment/Compat/` | Definitions that existed in LTE's pinned mathlib3 but not in mathlib4. |
| `scripts/port/` | The full, reproducible porting pipeline. |

## Versions

| | Lean 3 (original) | Lean 4 (port) |
|---|---|---|
| Lean | `leanprover-community/lean:3.48.0` | `leanprover/lean4:v4.3.0-rc2` |
| mathlib | mathlib3 `5947fb69` (2022-09-24) | mathlib4 `79254c9790` (2023-11-29) |
| mathport | — | `nightly-2023-11-30-10` (commit `a73a71e`) + `scripts/port/mathport.patch` |

### Why mathlib4 `79254c9790` and not `v3-eol`

Mathport's README recommends porting against mathlib4 `v3-eol` (July 2024), the last
revision with `#align` data. That revision has **already deleted the old homology API**
LTE is built on: `Algebra.Homology.Exact`, `Algebra.Homology.Homology`,
`CategoryTheory.Abelian.Homology` (removed in mathlib4#14569, July 2024) and the old
`CategoryTheory.Functor.LeftDerived` (mathlib4#8706, 2023-11-30). Porting onto `v3-eol`
would therefore mean rewriting LTE's homological algebra rather than porting it.
Instead the port follows mathport's documented "use the nearest nightly" route:
mathport `nightly-2023-11-30-10` is paired with mathlib4 `79254c9790`, which still
contains all of the above. (A complete first pass against `v3-eol` was also run; see the
git history.)

## Reproducing the pipeline

1. **Lean 3 build with export data.** In a checkout of `lean-liquid@ee47958` whose
   `leanpkg.path` points at mathlib3 `5947fb69` (olean cache from
   `oleanstorage.azureedge.net`), generate `all.lean` and run
   `lean --make --recursive --ast --tlean src`. All 403 modules compile with no errors and
   no `sorry` (this also re-verifies the original project).
2. **mathport.** Check out mathport `nightly-2023-11-30-10`, apply
   `scripts/port/mathport.patch`, `lake exe cache get && lake build`, download the release's
   `lean3-binport` / `mathlib3-binport` artifacts.
3. **Compatibility shims for mathlib3 drift** (`scripts/port/gen.py`): mathport's prebuilt
   Mathbin corresponds to the *final* mathlib3 (Oct 2023), a year newer than LTE's pin.
   18 mathlib3 modules LTE imports had been split or renamed in the meantime; each gets a
   placeholder `.tlean` and a tiny Lean 4 module re-exporting its successors.
   `category_theory.additive_category`, removed from mathlib3 in that year, is restored
   verbatim (`LiquidTensorExperiment/Compat/AdditiveCategory.lean`).
4. **Explicit alignment** (`scripts/port/LteAligns.lean`): LTE's Lean 3
   `condensed.evaluation_additive` and `Condensed.evaluation_additive` are different
   instances that mathport maps to the same Lean 4 name; the first becomes
   `Condensed.evaluation_additive'`.
5. **Semantics-preserving pre-mathport edits** (`scripts/port/lean3_premathport.py`, applied to
   a *working copy* of the Lean 3 source, never to `lean3/`):
   * `asyncI { tac }` → `{ tac }` (LTE's `asyncI` only elaborated `tac` asynchronously as an
     auxiliary lemma). mathport had commented out all 42 such proof blocks.
   * LTE's zero-width-space notation `​e` → `(by exactI e)`, which is its literal definition.
     mathport cannot translate user notation and had **replaced the statement of the main
     theorem `first_target`** (and 9 other statements in `liquid`, `statement`, `thm95.default`)
     by an error string. The re-exported Lean 3 `.tlean` of `statement` and `thm95.default` is
     byte-identical to the original; `liquid` differs only in Lean 3's auto-generated
     `_fresh.N.M` bound-variable names (alpha-equivalent).
   The edited files are re-exported with `lean --ast --tlean` and re-ported.
6. **Run mathport** on all modules in dependency order with bounded parallelism
   (`scripts/port/drive.py`, config `scripts/port/config-lte.json`). All 403 modules port.
7. **Post-process** (`scripts/port/postprocess.py`, imports only) and
   `scripts/port/fix_norm_notation.py` (LTE's old `∥x∥` notation → `‖x‖`).
8. **Restore declarations mathport commented out** (`scripts/port/restore_print_blocks.py`):
   mathport replaces an LTE declaration with `#print X /- … -/` when *some* declaration
   named `X` exists in Mathbin, judged by name only. This is unreliable (e.g. mathlib's
   `CategoryTheory.yoneda'` is an unrelated sheaf functor), so all 95 such blocks are
   restored to LTE's own declarations; genuine duplicates surface as compile errors.
9. **Project-wide mechanical renames** (`scripts/port/mechanical.py`, see below).
10. **Compile and repair.** `scripts/port/compile.py` compiles every module in dependency
   order (per-module timeout `LTE_TIMEOUT`, default 900 s) and records per-module results;
   `scripts/port/census.py` summarises them;
   `scripts/port/autofix.py` / `autofix_all.py` repair mechanical naming mistranslations
   at Lean's reported error positions (see below); remaining errors are fixed by hand.

### The mathport patch (`scripts/port/mathport.patch`)

Two small changes to mathport's *binport* stage (which only produces intermediate
`.olean`s used for name translation; the delivered Lean 4 text comes from synport):

* Lean 3.48's `.tlean` exporter does not emit `#USER_ATTR_DATA` for `to_additive_aux`
  (later Lean 3 releases do); mathport aborted the whole file. It now skips that alignment.
* When a declaration cannot be added even after stubbing its value and type, binport now
  skips that one declaration instead of aborting the module.

### The rename auto-fixer (`scripts/port/autofix.py`)

Mathport's most frequent residual errors are naming mistranslations: capitalised fields
(`iso.hom` → `.Hom`, `.Continuous`, `.Surjective`), Lean 3 snake_case references to
declarations that are lowerCamelCase in Lean 4 (`preadditive.comp_sub`), primed Lean 3
structure fields (`hom_inv_id'`), and `X.X` of a complex translated as cone `X.pt`.
The auto-fixer reads Lean's error positions and proposes **renames only**, and only to a
name that exists in mathlib4 / LTE's Lean 4 declarations or appears in mathport's own
Lean 3 → Lean 4 translation table. A round is kept only if the module's error count drops
(or stays equal while the first error moves later); otherwise the file is restored.

### The project-wide renamer (`scripts/port/mechanical.py`)

`autofix.py` keeps a round only if the error count drops, but fixing one naming error often
lets Lean elaborate further and report new errors, so many correct renames were rejected.
`mechanical.py` therefore applies a fixed set of pure renames once, everywhere outside
comments and strings:

* Lean 3 primed structure fields that mathlib4 unprimed (`hom_inv_id'`, `map_comp'`,
  `naturality'`, `id_comp'`, ...; *not* `map_zero'`/`map_add'`/`map_smul'`, which are still
  primed in mathlib4), and the `Iso` field `Hom :=` -> `hom :=`.
* Lean 3 identifiers that do not exist in Lean 4 (`category.assoc`, `eq_to_hom_refl`,
  `iso.refl`, `X.X_next_iso`, `e.Hom`, ...). A name is replaced only if mathport's own
  Lean 3 -> Lean 4 translation table (or, for dotted names, the snake_case -> camelCase
  convention) gives **exactly one** name that exists in mathlib4 or in LTE's Lean 4
  declarations. Tactic names and any name a file binds locally are never touched, and the
  qualification depth is kept (`category.assoc` -> `Category.assoc`).

`--dry-run` lists every distinct rename with its count. After it was applied, a full
recompile was compared module by module with the previous one: no module that compiled
before stopped compiling because of it.

## Manual changes

All Lean 4-specific workarounds in the source are marked `-- Porting note:`. The kinds of
manual change made so far:

* **Imports**: mathlib4 files import less transitively than mathlib3's did
  (e.g. `pow_pos`, `Fintype.induction_empty_option`, `Preadditive`).
* **Lean 4 elaboration differences**: numeral types (`(zero_lt_two (α := ℕ))`), Lean 3's
  `have h := f _ _` creating goals (→ `?_`), implicit `Functor.map` arguments,
  structure-field renames (`map_id'` → `map_id`, `Iso.hom`).
* **Instances Lean 4 rejects**: `fact_le_subst_*` in `Facts/Nnreal.lean` (the middle term
  occurs only in hypotheses, so Lean 4 finds no synthesis order) are plain theorems; they
  are not used by name anywhere.
* **`A ^ n` for types** (`HacksAndTricks/TypePow.lean`): Lean 3 unfolded the local
  `typePow` instance during instance search; Lean 4 does not, so the pi
  `AddCommGroup` instance and `rfl` `_apply` simp lemmas are registered explicitly
  (LTE already did this for `TopologicalSpace`).
* **Restored LTE definitions** that mathport had commented out (see step 8), e.g.
  `QuotientMap.homeomorph`, `CategoryTheory.yoneda'`.
* Tactic substitutions where the Lean 3 tactic does not exist: `tidy` → `aesop_cat`.
* **Lean 3 metaprograms**: mathport cannot translate `meta def` tactics and stubs them as
  `unsafe def … := sorry`. These are being rewritten as Lean 4 macros/elaborators that run
  the same tactic script (`hom_tac`, `map_tac`, `aux_simp`, `aux_tac`, `fact_arith`); the
  rest are listed in `PORTING_STATUS.md`. In particular `ChallengeNotations.lean` (part of
  the challenge statement) had its `by fact_arith` replaced by a no-op `trace` by mathport;
  this is restored.
* **Lean 4 elaboration of definitions**: Lean 4 does not include a section variable that is only
  used inside a tactic block of a statement, so where that changed a declaration's
  arguments relative to Lean 3 the binders are stated explicitly (e.g.
  `kernel_lift_comp_kernelDFromIso_hom` in `ForMathlib/HomologyIso.lean`). Lean 3's `ext`
  applied extensionality lemmas recursively (e.g. through `X ⟶ Y` of a custom category into
  kernels or coproducts); in Lean 4 an `@[ext]` lemma for `X ⟶ Y` is added where LTE defines
  a category (`Endomorphisms.hom_ext`), and the inner lemma is applied explicitly.
* **Upstreamed declarations**: where an LTE declaration was later added to mathlib with the
  same name and the same definition (e.g. `NatIso.mapHomologicalComplex`), the Lean 4 file
  uses mathlib's and says so, instead of redeclaring it.
* Naming: mathport lowercases definitions, so LTE's `Ext'`/`liquid_tensor_experiment.Ext`
  are `ext'`/`LiquidTensorExperiment.ext` (consistently across the project).

Every such change was checked against the Lean 3 statement; where coercion placement was
in doubt it was checked with Lean 3 itself (e.g. `nnreal.fact_two_pow_inv_le_two_pow_inv`).

## License

Apache 2.0, as the original project (see `LICENSE`).
