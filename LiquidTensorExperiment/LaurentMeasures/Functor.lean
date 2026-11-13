import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.LaurentMeasures.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import laurent_measures.functor

noncomputable section

universe u

open scoped NNReal

open CategoryTheory

section LaurentMeasuresDef

open LaurentMeasures

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
def FintypeCat.laurentMeasure (r : ℝ≥0) [Fact (0 < r)] (S : FintypeCat.{u}) :
    ProFiltPseuNormGrpWithTinv₁.{u} r :=
  ⟨LaurentMeasures r S, fun F => ⟨«expr∥ ∥₊» F, le_rfl⟩⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/-- `Laurent_measures r'` is an explicit functor from finite types to the category of profinitely
  exhaustively-filtered pseudo-normed groups with an action of T⁻¹, and strict morphisms. It sends
  `S` to the Laurent measures on `S` with bound `r'`. -/
@[simps]
def fintypeLaurentMeasures (r : ℝ≥0) [Fact (0 < r)] :
    FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r
    where
  obj S := ⟨LaurentMeasures r S, fun F => ⟨«expr∥ ∥₊» F, le_rfl⟩⟩
  map S T f := mapHom f
  map_id' S := by ext1; simp only [map_hom, map_id]; rfl
  map_comp' S S' S'' f g := by ext1; simp only [map_hom, map_comp]; rfl

end LaurentMeasuresDef

namespace LaurentMeasures

variable (r' : ℝ≥0) [Fact (0 < r')]

open ProFiltPseuNormGrpWithTinv₁

@[simps]
def profinite : Profinite.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r' :=
  Profinite.extend (fintypeLaurentMeasures.{u} r')

@[simps]
def profiniteCH : Profinite.{u} ⥤ CompHausFiltPseuNormGrp₁.{u} :=
  Profinite.extend (fintypeLaurentMeasures.{u} r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r')

def profiniteCompPFPNGT₁ToCHFPNG₁ₑₗ :
    LaurentMeasures.profinite.{u} r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r' ≅ profiniteCH.{u} r' :=
  Profinite.extendCommutes _ _

end LaurentMeasures

