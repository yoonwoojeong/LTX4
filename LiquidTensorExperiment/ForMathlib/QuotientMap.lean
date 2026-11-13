import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Homeomorph

#align_import for_mathlib.quotient_map

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

noncomputable section

#print QuotientMap.homeomorph /-
def QuotientMap.homeomorph {f : α → β} (hf : QuotientMap f) : Quotient (Setoid.ker f) ≃ₜ β :=
  {
    Setoid.quotientKerEquivOfSurjective _
      hf.Surjective with
    continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr hf.Continuous
    continuous_invFun := by
      rw [hf.continuous_iff]
      convert continuous_quotient_mk'
      ext
      simpa [(Setoid.quotientKerEquivOfSurjective f (QuotientMap.surjective hf)).symm_apply_eq] }
-/

