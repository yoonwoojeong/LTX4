import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.BreenDeligne.Suitable

#align_import pseudo_normed_group.breen_deligne

/-!

# Universal maps and pseudo-normed groups

This file contains the definition of the action of a basic universal map
on powers of a pseudo-normed group and related types.

## Main definitions

- `f.eval_png : (M^m) →+ (M^n)` : the group homomorphism induced by a basic universal map.
- `f.eval_png₀ : M_{c₁}^m → M_{c₂}^n` : the induced map if `f` is (c₁, c₂)-suitable.

-/


noncomputable section

attribute [local instance] typePow

open scoped NNReal BigOperators Matrix

namespace BreenDeligne

namespace BasicUniversalMap

variable {m n : ℕ} (f : BasicUniversalMap m n)

variable (M : Type _)

section PseudoNormedGroup

variable [PseudoNormedGroup M]

open AddMonoidHom PseudoNormedGroup

end PseudoNormedGroup

section ProfinitelyFilteredPseudoNormedGroup

open PseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup AddMonoidHom

open ComphausFilteredPseudoNormedGroupHom ComphausFilteredPseudoNormedGroup

variable [ProfinitelyFilteredPseudoNormedGroup M]

/-- `eval_png M f` is the homomorphism `M^m → M^n` of profinitely filtered pseudo-normed groups
obtained by matrix multiplication with the matrix `f`. -/
def evalPng : BasicUniversalMap m n →+ ComphausFilteredPseudoNormedGroupHom (M ^ m) (M ^ n) :=
  AddMonoidHom.mk'
    (fun f =>
      piLift (fun j => ∑ i, f j i • piProj i)
        (by
          let C : ℝ≥0 := finset.univ.sup fun j => ∑ i, (f j i).natAbs
          refine' ⟨C, fun j => _⟩
          intro c x hx
          have : ∑ i, ↑(f j i).natAbs * (1 * c) ≤ C * c := by rw [← Finset.sum_mul];
            exact mul_le_mul' (Finset.le_sup (Finset.mem_univ j)) (one_mul c).le
          refine' filtration_mono this _
          simp only [← coe_to_add_monoid_hom, ← to_add_monoid_hom_hom_apply, AddMonoidHom.map_sum,
            AddMonoidHom.map_zsmul, AddMonoidHom.finset_sum_apply]
          refine' sum_mem_filtration _ _ _ _
          rintro i -
          refine' int_smul_mem_filtration _ _ _ _
          exact @pi_proj_bound_by _ (fun _ => M) _ i _ _ hx))
    (by
      intro f g
      ext x j
      simp only [← coe_to_add_monoid_hom, ← to_add_monoid_hom_hom_apply, AddMonoidHom.map_add,
        AddMonoidHom.add_apply, Pi.add_apply]
      simp only [coe_to_add_monoid_hom, to_add_monoid_hom_hom_apply]
      simp only [pi_lift_to_fun, mk_to_pi_apply, ← to_add_monoid_hom_hom_apply,
        AddMonoidHom.map_sum, AddMonoidHom.map_zsmul, AddMonoidHom.finset_sum_apply]
      rw [← Finset.sum_add_distrib]
      simp only [pi_proj_to_fun, to_add_monoid_hom_hom_apply, coe_smul, coe_to_add_monoid_hom,
        Pi.smul_apply, add_smul]
      rfl)

theorem evalPng_apply (x : M ^ m) : evalPng M f x = fun j => ∑ i, f j i • x i :=
  by
  ext j
  simp only [eval_png, mk'_apply, pi_lift_to_fun, mk_to_pi_apply, ← to_add_monoid_hom_hom_apply]
  simp only [AddMonoidHom.map_sum, AddMonoidHom.map_zsmul, AddMonoidHom.finset_sum_apply]
  rfl

theorem evalPng_mem_filtration :
    (evalPng M f).toAddMonoidHom ∈
      filtration (M ^ m →+ M ^ n) (Finset.univ.sup fun i => ∑ j, (f i j).natAbs) :=
  by
  apply mk_to_pi_mem_filtration
  intro j
  let C : ℝ≥0 := finset.univ.sup fun j => ∑ i, (f j i).natAbs
  intro c x hx
  have : ∑ i, ↑(f j i).natAbs * (1 * c) ≤ C * c := by rw [← Finset.sum_mul];
    exact mul_le_mul' (Finset.le_sup (Finset.mem_univ j)) (one_mul c).le
  refine' filtration_mono this _
  simp only [← coe_to_add_monoid_hom, ← to_add_monoid_hom_hom_apply, AddMonoidHom.map_sum,
    AddMonoidHom.map_zsmul, AddMonoidHom.finset_sum_apply]
  refine' sum_mem_filtration _ _ _ _
  rintro i -
  refine' int_smul_mem_filtration _ _ _ _
  exact @pi_proj_bound_by _ (fun _ => M) _ i _ _ hx

theorem evalPng_mem_filtration' (c₁ c₂ : ℝ≥0) [h : f.Suitable c₁ c₂] (x : M ^ m)
    (hx : x ∈ filtration (M ^ m) c₁) : evalPng M f x ∈ filtration (M ^ n) c₂ :=
  filtration_mono (f.sup_hMul_le c₁ c₂) (f.evalPng_mem_filtration M hx)

/-- `f.eval_png₀ M` is the group homomorphism `(M^m) →+ (M^n)`
obtained by matrix multiplication with the matrix `f`,
but restricted to `(filtration M c₁)^m → (filtration M c₂)^n`. -/
@[simps (config := { fullyApplied := false })]
def evalPng₀ (c₁ c₂ : ℝ≥0) [h : f.Suitable c₁ c₂] (x : filtration (M ^ m) c₁) :
    filtration (M ^ n) c₂ :=
  ⟨evalPng M f x, evalPng_mem_filtration' f M c₁ c₂ x x.2⟩

theorem evalPng_comp {l m n} (g : BasicUniversalMap m n) (f : BasicUniversalMap l m) :
    evalPng M (BasicUniversalMap.comp g f) = (evalPng M g).comp (evalPng M f) :=
  by
  ext x j
  simp only [eval_png_apply, Function.comp_apply, coe_comp, basic_universal_map.comp, comp_to_fun,
    Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul, AddMonoidHom.mk'_apply]
  rw [Finset.sum_comm]

theorem evalPng₀_continuous (c₁ c₂ : ℝ≥0) [f.Suitable c₁ c₂] : Continuous (f.evalPng₀ M c₁ c₂) :=
  (evalPng M f).Continuous _ fun x => rfl

end ProfinitelyFilteredPseudoNormedGroup

end BasicUniversalMap

end BreenDeligne

#lint

