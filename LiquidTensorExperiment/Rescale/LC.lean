import LiquidTensorExperiment.Rescale.PseudoNormedGroup
import LiquidTensorExperiment.PseudoNormedGroup.LC

#align_import rescale.LC

open scoped Classical NNReal

open Opposite ProFiltPseuNormGrpWithTinv

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup

universe u

variable (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0) [Fact (0 < r')]

variable (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

@[simp]
theorem lCFP_rescale (N : ℝ≥0) (M) [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    (lCFP V r' c n).obj (op (of r' (Rescale N M))) = (lCFP V r' (c * N⁻¹) n).obj (op (of r' M)) :=
  rfl

namespace BreenDeligne

namespace BasicUniversalMap

variable (ϕ : BasicUniversalMap m n)

theorem evalFP_rescale [ϕ.Suitable c₁ c₂] (N : ℝ≥0) (M)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    (evalFP r' c₁ c₂ ϕ).app (of r' (Rescale N M)) =
      (evalFP r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (of r' M) :=
  by
  ext x i; dsimp only [eval_FP, ContinuousMap.coe_mk, eval_png₀, Subtype.coe_mk]
  simp only [eval_png_apply]

theorem evalLCFP_rescale [ϕ.Suitable c₂ c₁] (N : ℝ≥0) (M)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    (evalLCFP V r' ϕ c₁ c₂).app (op (of r' (Rescale N M))) = by
      clean @_root_.id _ ((eval_LCFP V r' ϕ (c₁ * N⁻¹) (c₂ * N⁻¹)).app (op (of r' M))) :=
  by
  dsimp only [eval_LCFP, whisker_right_app, nat_trans.op_app, unop_op]
  rw [eval_FP_rescale]

end BasicUniversalMap

namespace UniversalMap

variable (ϕ : UniversalMap m n)

theorem evalLCFP_rescale [ϕ.Suitable c₂ c₁] (N : ℝ≥0) (M)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    (evalLCFP V r' c₁ c₂ ϕ).app (op (of r' (Rescale N M))) = by
      clean @_root_.id _ ((eval_LCFP V r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (op (of r' M))) :=
  by
  simp only [eval_LCFP, ← nat_trans.app_hom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul]
  simp only [nat_trans.app_hom_apply, basic_universal_map.eval_LCFP_rescale]

end UniversalMap

end BreenDeligne

