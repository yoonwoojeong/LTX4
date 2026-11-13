import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.Invpoly.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import invpoly.functor

noncomputable section

universe u

open scoped NNReal

open CategoryTheory

open Invpoly

variable (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

open ProFiltPseuNormGrpWithTinv₁

/-- The functor represented by `ℤ[T⁻¹]`, i.e., sending a finite type `S` to the group
  `S → ℤ[T⁻¹]`, equipped with the filtration coming from the usual `r`-norm,
  i.e. the one sending `s ↦ ∑aₙ(s)T⁻ⁿ` to `∑_{s,n}∥aₙ(s)∥₊r⁻ⁿ`. We consider
  this object as a profinitely-filtered normed group equipped with an action of `T⁻¹`,
  given by multiplication. -/
@[simps]
def fintypeInvpoly : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r
    where
  obj S := ⟨Invpoly r S, fun F => ⟨‖F‖₊, le_rfl⟩⟩
  map S T f := mapHom f
  map_id' S := by ext1; simp only [map_hom, map_id]; rfl
  map_comp' S S' S'' f g := by ext1; simp only [map_hom, map_comp]; rfl

