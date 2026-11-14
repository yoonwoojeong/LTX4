import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Homeomorph

#align_import for_mathlib.quotient_map

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

noncomputable section

def QuotientMap.homeomorph {f : α → β} (hf : QuotientMap f) : Quotient (Setoid.ker f) ≃ₜ β :=
  {
    Setoid.quotientKerEquivOfSurjective _
      hf.surjective with
    continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr hf.continuous
    continuous_invFun := by
      rw [hf.continuous_iff]
      convert continuous_quotient_mk'
      ext
      -- Porting note: Lean 3 used
      -- `simpa [(setoid.quotient_ker_equiv_of_surjective f _).symm_apply_eq]`; same lemma, applied directly.
      exact (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq.mpr rfl }

