import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels

#align_import normed_group.normedWithAut

/-!

# Seminormed groups with an extra automorphism

This file contains definition 8.13 of `analytic.pdf`, a category-theoretic
definition of a seminormed group eqipped with an automorphism which scales
norms by a fixed factor `r`.

-/


open scoped NNReal

/-- A `normed_with_aut r V` structure on a seminormed group `V`
consists of an automorphism `T` satisfying `∥T v∥ = r * ∥v∥`.

In other words, it is a normed `ℤ[T^{±1}]`-module satisfying `∥T v∥ = r * ∥v∥`.

Definition 8.13 of [Analytic] -/
class NormedWithAut (r : outParam ℝ≥0) (V : SemiNormedGroupCat) where
  t : V ≅ V
  -- Porting note: Lean 3 field `T`; the Lean 4 field is `t` (see `lean3name` align table).
  norm_t : ∀ v : V, ‖((t.hom : V → V) v)‖ = r * ‖v‖

variable {r : ℝ≥0} (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

namespace NormedWithAut

theorem norm_t_inv (v : V) : ‖t.inv v‖ = r⁻¹ * ‖v‖ :=
  by
  calc
    ‖((t.inv : V → V) v)‖ = r⁻¹ * ‖(t.hom (t.inv v))‖ := ?_
    _ = r⁻¹ * ‖v‖ := ?_
  · rw [NormedWithAut.norm_t, NNReal.coe_inv, inv_mul_cancel_left₀]
    apply ne_of_gt
    rw [NNReal.coe_pos]
    exact ‹Fact (0 < r)›.out
  · -- Porting note: Lean 4 `rw [← comp_apply]` does not fire here; use `congrArg` instead.
    have hv : ((NormedWithAut.t (V := V)).hom : V → V) ((NormedWithAut.t (V := V)).inv v) = v :=
      congrArg (fun f : V ⟶ V => (f : V → V) v) (NormedWithAut.t (V := V)).inv_hom_id
    rw [hv]

end NormedWithAut

-- Porting note: Lean 3 `#lint- only unused_arguments def_lemma doc_blame` removed; the
-- Lean 4 `#lint` run reports the undocumented field `t` as an error.

