import LiquidTensorExperiment.PseudoNormedGroup.CLC
import LiquidTensorExperiment.Rescale.LC

#align_import rescale.CLC

open scoped Classical NNReal

open Opposite ProFiltPseuNormGrpWithTinv

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup

universe u

variable (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0) [Fact (0 < r')]

variable (c c₁ c₂ c₃ c₄ : ℝ≥0) (m n : ℕ)

@[simp]
theorem cLCFP_rescale (N : ℝ≥0) (M) [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    (cLCFP V r' c n).obj (op (of r' (Rescale N M))) = (cLCFP V r' (c * N⁻¹) n).obj (op (of r' M)) :=
  rfl

namespace BreenDeligne

namespace UniversalMap

variable (ϕ : UniversalMap m n)

theorem evalCLCFP_rescale [ϕ.Suitable c₂ c₁] (N : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r') :
    Arrow.mk ((evalCLCFP V r' c₁ c₂ ϕ).app (op (of r' (Rescale N M)))) =
      Arrow.mk ((evalCLCFP V r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (op M)) :=
  by dsimp only [eval_CLCFP, whisker_right_app]; rw [eval_LCFP_rescale]; cases M; rfl

end UniversalMap

end BreenDeligne

