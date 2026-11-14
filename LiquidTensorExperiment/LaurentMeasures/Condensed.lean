import LiquidTensorExperiment.LaurentMeasures.Functor
import LiquidTensorExperiment.Condensed.Ab

#align_import LaurentMeasures.condensed

noncomputable section

universe u

open CategoryTheory

open scoped NNReal

namespace LaurentMeasures

def condensed (r' : ℝ≥0) [Fact (0 < r')] : Profinite.{u} ⥤ Condensed.{u} Ab.{u + 1} :=
  (LaurentMeasures.profinite.{u} r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r') ⋙
    CompHausFiltPseuNormGrp₁.toCondensed

def condensedCH (r' : ℝ≥0) [Fact (0 < r')] : Profinite.{u} ⥤ Condensed.{u} Ab.{u + 1} :=
  LaurentMeasures.profiniteCH.{u} r' ⋙ CompHausFiltPseuNormGrp₁.toCondensed

end LaurentMeasures

