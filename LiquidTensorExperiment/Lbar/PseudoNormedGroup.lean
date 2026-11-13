import LiquidTensorExperiment.PseudoNormedGroup.WithTinv
import LiquidTensorExperiment.Lbar.LbarLe

#align_import Lbar.pseudo_normed_group

/-!

# Lbar_r(S) is a profinitely filtered pseudo-normed group with T⁻¹

This file constructs this instance.

-/


universe u

noncomputable section

open scoped BigOperators NNReal

variable {r' : ℝ≥0} {S : Type u} [Fact (0 < r')] [Fintype S] {c c₁ c₂ c₃ : ℝ≥0}

namespace Lbar

instance : ProfinitelyFilteredPseudoNormedGroupWithTinv r' (Lbar r' S) :=
  {
    Lbar.profinitelyFilteredPseudoNormedGroup with
    tinv :=
      ComphausFilteredPseudoNormedGroupHom.mk' Lbar.tinv
        (by
          refine' ⟨r'⁻¹, fun c => ⟨_, _⟩⟩
          · intro x hx; exact Lbar.tinv_mem_filtration hx
          · exact LbarLe.continuous_tinv _ _ _ _)
    tinv_mem_filtration := fun c x hx => Lbar.tinv_mem_filtration hx }

@[simp]
theorem tinv_apply (F : Lbar r' S) : ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv F = F.tinv :=
  rfl

end Lbar

#lint

