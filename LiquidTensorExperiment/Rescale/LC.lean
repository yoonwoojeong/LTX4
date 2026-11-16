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
  ext x i
  -- Porting note: the Lean 3 final `simp only [eval_png_apply]` closes this by unfolding
  -- `evalPng` on `Rescale N M`, which is definitionally `M`.
  dsimp only [evalFP, ContinuousMap.coe_mk, Subtype.coe_mk]
  unfold BreenDeligne.BasicUniversalMap.evalPng₀
  first
    | exact Subtype.ext (by simp only [BreenDeligne.BasicUniversalMap.evalPng_apply]; rfl)
    | exact Subtype.ext (by rfl)
    | rfl

theorem evalLCFP_rescale [ϕ.Suitable c₂ c₁] (N : ℝ≥0) (M)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    -- Porting note: Lean 3 wrote the right-hand side as `by clean @id _ (…)`, which only cleans up
    -- the term; we write the term directly.
    (evalLCFP V r' ϕ c₁ c₂).app (op (of r' (Rescale N M))) =
      (evalLCFP V r' ϕ (c₁ * N⁻¹) (c₂ * N⁻¹)).app (op (of r' M)) :=
  by
  dsimp only [evalLCFP, CategoryTheory.whiskerRight_app, NatTrans.op_app, Opposite.unop_op]
  rw [evalFP_rescale]

end BasicUniversalMap

namespace UniversalMap

variable (ϕ : UniversalMap m n)

theorem evalLCFP_rescale [ϕ.Suitable c₂ c₁] (N : ℝ≥0) (M)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    -- Porting note: as above, the Lean 3 `by clean @id _ (…)` right-hand side is written directly.
    (evalLCFP V r' c₁ c₂ ϕ).app (op (of r' (Rescale N M))) =
      (evalLCFP V r' (c₁ * N⁻¹) (c₂ * N⁻¹) ϕ).app (op (of r' M)) :=
  by
  simp only [evalLCFP, ← NatTrans.appHom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul]
  refine Finset.sum_congr rfl fun g _ => ?_
  -- Porting note: the `Suitable` instance for each summand has to be supplied explicitly
  haveI := suitable_of_mem_support ϕ c₂ c₁ g g.2
  exact congrArg (fun F => FreeAbelianGroup.coeff (g : BreenDeligne.BasicUniversalMap m n) ϕ • F)
    (BasicUniversalMap.evalLCFP_rescale (r' := r') (V := V) (c₁ := c₁) (c₂ := c₂)
      (ϕ := (g : BreenDeligne.BasicUniversalMap m n)) (N := N) (M := M))

end UniversalMap

end BreenDeligne

