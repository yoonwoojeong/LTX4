import Mathlib.Analysis.Normed.Group.HomCompletion

#align_import normed_group.controlled_exactness

/-!

# A controlled exactness lemma for seminormed groups

This file contains a proof of Proposition 8.17 of `analytic.pdf`,
a technical lemma which controls, in some cases, the norm of the map
induced on completions by a normed group hom.

-/


noncomputable section

open Filter Set Function NormedAddCommGroup UniformSpace NormedAddGroupHom Finset

open scoped TopologicalSpace BigOperators

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem controlled_exactness {M M₁ M₂ : Type _} [SeminormedAddCommGroup M]
    [SeminormedAddCommGroup M₁] [SeminormedAddCommGroup M₂] {f : NormedAddGroupHom M₁ M} {C : ℝ}
    (hC : 0 < C) {D : ℝ} {g : NormedAddGroupHom M M₂} (h : f.SurjectiveOnWith g.ker C)
    (h' : g.SurjectiveOnWith g.range D) :
    ∀ ε > 0, f.Completion.SurjectiveOnWith g.Completion.ker (C + ε) :=
  by
  intro ε ε_pos hatm hatm_in
  by_cases H : hatm = 0
  · use 0
    simp only [H, le_refl, norm_zero, eq_self_iff_true, and_self_iff, MulZeroClass.mul_zero,
      map_zero]
  set hatf := f.completion
  set i := incl g.ker
  have norm_j_comp_i : ∀ x, «expr∥ ∥» (to_compl.comp i x) = «expr∥ ∥» x :=
    by
    intro x
    erw [norm_to_compl, norm_incl]
  have hatm_in : hatm ∈ closure ((to_compl.comp i).range : Set <| completion M) := by
    rwa [← NormedAddGroupHom.ker_completion h']
  have :
    ∀ k : g.ker,
      ∃ m' : completion M₁, hatf m' = (to_compl.comp i) k ∧ «expr∥ ∥» m' ≤ C * «expr∥ ∥» k :=
    by
    rintro ⟨k, k_in⟩
    rcases h k k_in with ⟨m₁, hm₁, hm₁'⟩
    use m₁
    erw [f.completion_coe, hm₁, norm_to_compl]
    exact ⟨rfl, hm₁'⟩
  exact controlled_closure_range_of_complete norm_j_comp_i hC ε_pos this _ hatm_in

