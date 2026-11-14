import LiquidTensorExperiment.PseudoNormedGroup.WithTinv
import LiquidTensorExperiment.Lbar.LbarLe

#align_import Lbar.pseudoNormedGroup

/-!

# Lbar_r(S) is a profinitely filtered pseudo-normed group with T⁻¹

This file constructs this instance.

-/


universe u

noncomputable section

open scoped BigOperators NNReal

variable {r' : ℝ≥0} {S : Type u} [Fact (0 < r')] [Fintype S] {c c₁ c₂ c₃ : ℝ≥0}

namespace Lbar

-- Porting note: Lean 3 referred to the instance of `Lbar/LbarLe.lean` by its automatically
-- generated name `Lbar.profinitely_filtered_pseudo_normed_group`; Lean 4 generates a different
-- name, so we refer to it via `inferInstance`.
instance : ProfinitelyFilteredPseudoNormedGroupWithTinv r' (Lbar r' S) :=
  {
    (inferInstance : ProfinitelyFilteredPseudoNormedGroup (Lbar r' S)) with
    tinv :=
      ComphausFilteredPseudoNormedGroupHom.mk' Lbar.tinv
        (by
          refine' ⟨r'⁻¹, fun c => ⟨_, _⟩⟩
          · intro x hx; exact Lbar.tinv_mem_filtration hx
          · exact LbarLe.continuous_tinv _ _ _ _)
    tinv_mem_filtration := fun c x hx => Lbar.tinv_mem_filtration hx }

@[simp]
theorem tinv_apply (F : Lbar r' S) : ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv F = Lbar.tinv F :=
  -- Porting note: `F.tinv` does not elaborate in Lean 4, as `Lbar.tinv` is a bundled hom with no
  -- explicit argument of type `Lbar r' S`
  rfl

end Lbar

#lint

