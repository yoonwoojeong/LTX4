import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.Lbar.PseudoNormedGroup
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import Lbar.functor

noncomputable section

open scoped NNReal

variable (r' : ℝ≥0) [Fact (0 < r')]

variable {S₁ S₂ : Type _} [Fintype S₁] [Fintype S₂]

namespace Lbar

open PseudoNormedGroup (filtration level)

open CategoryTheory CategoryTheory.Limits

theorem map_zero (f : S₁ → S₂) : map f (0 : Lbar r' S₁) = 0 := by ext;
  simp only [coe_zero, map_to_fun, Pi.zero_apply, Finset.sum_const_zero]

theorem map_add (f : S₁ → S₂) (x y : Lbar r' S₁) : map f (x + y) = map f x + map f y := by ext s n;
  simp only [map_to_fun, Pi.add_apply, coe_add, Finset.sum_add_distrib]

theorem map_strict (f : S₁ → S₂) ⦃c : ℝ≥0⦄ ⦃x : Lbar r' S₁⦄ (hx : x ∈ filtration (Lbar r' S₁) c) :
    map f x ∈ filtration (Lbar r' S₂) c :=
  Lbar.nnnorm_map_le_of_nnnorm_le f _ hx

theorem map_continuous (f : S₁ → S₂) (c : ℝ≥0) : Continuous (level (map f) (map_strict r' f) c) :=
  by
  let φ := level (map f) (map_strict r' f) c
  rw [LbarLe.continuous_iff]
  intro M
  have : LbarLe.truncate M ∘ φ = LbarBdd.map f ∘ LbarLe.truncate M := by ext; rfl
  rw [this]
  exact continuous_of_discrete_topology.comp LbarLe.continuous_truncate

theorem map_tinv (f : S₁ → S₂) (x : Lbar r' S₁) : map f (tinv x) = tinv (map f x) := by
  ext s ⟨_ | n⟩ <;> simp only [map_to_fun, Tinv_zero, Tinv_succ, Finset.sum_const_zero]

end Lbar

open Lbar

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/-- `Fintype_Lbar r' S` is functorial in the finite type `S`. -/
@[simps]
def fintypeLbar : FintypeCat ⥤ ProFiltPseuNormGrpWithTinv₁ r'
    where
  obj S :=
    { M := Lbar r' S
      exhaustive' := fun x => ⟨«expr∥ ∥₊» x, by rw [Lbar.mem_filtration_iff]⟩ }
  map S₁ S₂ f :=
    { toFun := map f
      map_zero' := map_zero r' f
      map_add' := map_add r' f
      strict' := map_strict r' f
      continuous' := map_continuous r' f
      map_Tinv' := map_tinv r' f }
  map_id' := by intros; ext1 x; exact map_id x
  map_comp' := by intro X Y Z f g; ext1 x; exact map_comp f x g

namespace Lbar

open CategoryTheory PseudoNormedGroup CategoryTheory.Limits

example (X : Profinite) : HasLimit (X.fintypeDiagram ⋙ fintypeLbar r') := by infer_instance

/-- `Lbar r' S` extends to a functor in `S`, for profinite `S`. -/
def functor : Profinite ⥤ ProFiltPseuNormGrpWithTinv₁ r' :=
  Profinite.extend (fintypeLbar r')

end Lbar

