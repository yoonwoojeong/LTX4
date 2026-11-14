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

-- Porting note: Lean 4's instance search does not see through `M ^ m = Fin m → M`
-- (Lean 3 did), so the instances on the power are registered explicitly.
instance instPseudoNormedGroupPow : PseudoNormedGroup (M ^ m) :=
  PseudoNormedGroup.pi fun _ => M

instance instComphausFilteredPseudoNormedGroupPow : ComphausFilteredPseudoNormedGroup (M ^ m) :=
  ComphausFilteredPseudoNormedGroup.pi fun _ => M

instance instProfinitelyFilteredPseudoNormedGroupPow :
    ProfinitelyFilteredPseudoNormedGroup (M ^ m) :=
  ProfinitelyFilteredPseudoNormedGroup.pi fun _ => M

-- Porting note: helper lemmas replacing the long `simp only` chains of the Lean 3 proofs
-- (which no longer work verbatim in Lean 4).
theorem sum_smul_piProj_apply (a : Fin m → ℤ) (x : M ^ m) :
    (∑ i, a i • (ComphausFilteredPseudoNormedGroup.piProj i :
      ComphausFilteredPseudoNormedGroupHom (M ^ m) M)) x = ∑ i, a i • x i := by
  rw [← ComphausFilteredPseudoNormedGroupHom.coe_toAddMonoidHom,
    ← ComphausFilteredPseudoNormedGroupHom.toAddMonoidHomHom_apply, _root_.map_sum,
    AddMonoidHom.finset_sum_apply]
  refine' Finset.sum_congr rfl fun i _ => _
  rw [_root_.map_zsmul]
  rfl

theorem piLift_sum_smul_piProj_apply (a : Fin n → Fin m → ℤ) {hh} (x : M ^ m) (j : Fin n) :
    (ComphausFilteredPseudoNormedGroup.piLift
      (fun j => ∑ i, a j i • (ComphausFilteredPseudoNormedGroup.piProj i :
        ComphausFilteredPseudoNormedGroupHom (M ^ m) M)) hh :
      ComphausFilteredPseudoNormedGroupHom (M ^ m) (M ^ n)).toAddMonoidHom x j =
      ∑ i, a j i • x i :=
  sum_smul_piProj_apply M (a j) x

/-- `eval_png M f` is the homomorphism `M^m → M^n` of profinitely filtered pseudo-normed groups
obtained by matrix multiplication with the matrix `f`. -/
def evalPng : BasicUniversalMap m n →+ ComphausFilteredPseudoNormedGroupHom (M ^ m) (M ^ n) :=
  AddMonoidHom.mk'
    (fun f =>
      piLift (fun j => ∑ i, f j i • piProj i)
        (by
          let C : ℝ≥0 := Finset.univ.sup fun j => ∑ i, (f j i).natAbs
          refine' ⟨C, fun j => _⟩
          intro c x hx
          have : ∑ i, ↑(f j i).natAbs * (1 * c) ≤ C * c := by
            rw [← Finset.sum_mul]
            exact mul_le_mul' (Finset.le_sup (f := fun j => ∑ i, ((f j i).natAbs : ℝ≥0)) (Finset.mem_univ j))
              (one_mul c).le
          refine' filtration_mono this _
          simp only [← ComphausFilteredPseudoNormedGroupHom.coe_toAddMonoidHom, ← ComphausFilteredPseudoNormedGroupHom.toAddMonoidHomHom_apply, AddMonoidHom.map_sum,
            AddMonoidHom.map_zsmul, AddMonoidHom.finset_sum_apply]
          refine' sum_mem_filtration _ _ _ _
          rintro i -
          refine' int_smul_mem_filtration _ _ _ _
          exact @ComphausFilteredPseudoNormedGroup.piProjBoundBy _ (fun _ => M) _ i _ _ hx))
    (by
      intro f g
      ext x j
      -- Porting note: the Lean 3 `simp only` chain is replaced by a helper lemma
      refine' (piLift_sum_smul_piProj_apply M (f + g) x j).trans _
      refine' Eq.trans _ (congrArg₂ (· + ·) (piLift_sum_smul_piProj_apply M f x j)
        (piLift_sum_smul_piProj_apply M g x j)).symm
      refine' (Finset.sum_congr rfl fun i _ => add_smul (f j i) (g j i) (x i)).trans _
      exact Finset.sum_add_distrib)

theorem evalPng_apply (x : M ^ m) : evalPng M f x = fun j => ∑ i, f j i • x i :=
  by
  funext j
  simp only [evalPng, AddMonoidHom.mk'_apply]
  exact piLift_sum_smul_piProj_apply M f x j

theorem evalPng_mem_filtration :
    (evalPng M f).toAddMonoidHom ∈
      filtration (M ^ m →+ M ^ n) (Finset.univ.sup fun i => ∑ j, (f i j).natAbs) :=
  by
  refine' AddMonoidHom.mkToPi_mem_filtration (M := fun _ => M)
    (f := fun j => (∑ i, f j i • piProj (M := fun _ : Fin m => M) i).toAddMonoidHom) _
  intro j
  let C : ℝ≥0 := Finset.univ.sup fun j => ∑ i, (f j i).natAbs
  intro c x hx
  have : ∑ i, ↑(f j i).natAbs * (1 * c) ≤ C * c := by
    rw [← Finset.sum_mul]
    exact mul_le_mul' (Finset.le_sup (f := fun j => ∑ i, ((f j i).natAbs : ℝ≥0)) (Finset.mem_univ j))
      (one_mul c).le
  refine' filtration_mono this _
  simp only [← ComphausFilteredPseudoNormedGroupHom.coe_toAddMonoidHom, ← ComphausFilteredPseudoNormedGroupHom.toAddMonoidHomHom_apply, AddMonoidHom.map_sum,
    AddMonoidHom.map_zsmul, AddMonoidHom.finset_sum_apply]
  refine' sum_mem_filtration _ _ _ _
  rintro i -
  refine' int_smul_mem_filtration _ _ _ _
  exact @ComphausFilteredPseudoNormedGroup.piProjBoundBy _ (fun _ => M) _ i _ _ hx

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
  ext x
  funext j
  simp only [BreenDeligne.BasicUniversalMap.evalPng_apply, Function.comp_apply, coe_comp, BasicUniversalMap.comp, ComphausFilteredPseudoNormedGroupHom.comp_apply,
    Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul, AddMonoidHom.mk'_apply]
  rw [Finset.sum_comm]

theorem evalPng₀_continuous (c₁ c₂ : ℝ≥0) [f.Suitable c₁ c₂] : Continuous (f.evalPng₀ M c₁ c₂) :=
  (evalPng M f).continuous _ fun x => rfl

end ProfinitelyFilteredPseudoNormedGroup

end BasicUniversalMap

end BreenDeligne

#lint

