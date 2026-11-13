import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels

#align_import normed_group.normed_with_aut

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
  norm_t : ∀ v : V, ‖((T.hom : V → V) v)‖ = r * ‖v‖

variable {r : ℝ≥0} (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

namespace NormedWithAut

theorem norm_t_inv (v : V) : ‖t.inv v‖ = r⁻¹ * ‖v‖ :=
  by
  calc
    ‖((T.inv : V → V) v)‖ = r⁻¹ * ‖(T.hom (T.inv v))‖ := _
    _ = r⁻¹ * ‖v‖ := _
  · rw [NormedWithAut.norm_t, inv_mul_cancel_left₀]
    apply ne_of_gt
    rw [NNReal.coe_pos]
    exact ‹Fact (0 < r)›.out
  · rw [← CategoryTheory.comp_apply, T.inv_hom_id]; rfl

end NormedWithAut

#lint

