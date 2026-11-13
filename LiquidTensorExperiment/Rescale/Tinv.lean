import LiquidTensorExperiment.PseudoNormedGroup.Tinv
import LiquidTensorExperiment.Rescale.CLC

#align_import rescale.Tinv

open scoped Classical NNReal

noncomputable section

attribute [local instance] typePow

open Opposite ProFiltPseuNormGrpWithTinv CategoryTheory

universe u

variable (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

variable (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)]

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (c c₁ c₂ c₃ c₄ : ℝ≥0) {m n : ℕ}

namespace BreenDeligne

open cLCFPTinv

namespace UniversalMap

variable (ϕ : UniversalMap m n)

attribute [local semireducible] cLCFPTinv₂ cLCFPTinv₂.res BreenDeligne.UniversalMap.evalCLCFPTinv₂

theorem evalCLCFPTinv₂_rescale [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] [ϕ.Suitable c₃ c₁]
    [ϕ.Suitable c₄ c₂] (N : ℝ≥0) [Fact (c₂ * N⁻¹ ≤ r' * (c₁ * N⁻¹))]
    [Fact (c₄ * N⁻¹ ≤ r' * (c₃ * N⁻¹))] (M : ProFiltPseuNormGrpWithTinv r') :
    Arrow.mk ((evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ ϕ).app (op (of r' (Rescale N M)))) =
      Arrow.mk ((evalCLCFPTinv₂ r V r' (c₁ * N⁻¹) (c₂ * N⁻¹) (c₃ * N⁻¹) (c₄ * N⁻¹) ϕ).app (op M)) :=
  by
  dsimp only [universal_map.eval_CLCFPTinv₂, _root_.id, SemiNormedGroupCat.equalizer.mapNat_app]
  refine' SemiNormedGroupCat.equalizer.map_congr _ _ rfl rfl rfl rfl <;>
    · exact universal_map.eval_CLCFP_rescale V r' _ _ _ _ _ N M

end UniversalMap

end BreenDeligne

