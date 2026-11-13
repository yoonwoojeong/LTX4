import LiquidTensorExperiment.Rescale.PseudoNormedGroup
import LiquidTensorExperiment.PseudoNormedGroup.FP

#align_import rescale.FiltrationPow

open scoped Classical NNReal

open ProFiltPseuNormGrpWithTinv

universe u

@[simp]
theorem filtration_rescale (r' c N : ℝ≥0) [Fact (0 < r')] (M)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    ((filtration r').obj c).obj (of r' (Rescale N M)) =
      ((filtration r').obj (c * N⁻¹)).obj (of r' M) :=
  rfl

@[simps Hom inv]
def filtrationCastEq (r' c₁ c₂ : ℝ≥0) (h : c₁ = c₂) [Fact (0 < r')] (M) :
    ((filtration r').obj c₁).obj M ≅ ((filtration r').obj c₂).obj M :=
  ((filtration r').mapIso <| CategoryTheory.eqToIso h).app M

