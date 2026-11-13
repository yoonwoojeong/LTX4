import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective

#align_import for_mathlib.Profinite.quotient_map

namespace Profinite

-- A surjective map of compact Hausdorff spaces is a quotient map
-- TODO: This certainly belongs in mathlib, if not already there...
theorem quotientMap {X Y : Profinite} (f : X ⟶ Y) (hf : Function.Surjective f) : QuotientMap f :=
  by
  rw [quotientMap_iff]
  refine' ⟨hf, _⟩
  intro S
  refine' ⟨fun hS => hS.preimage f.continuous, fun hS => _⟩
  rw [← isClosed_compl_iff] at *
  rw [← Set.preimage_compl] at hS 
  have : Sᶜ = f '' (f ⁻¹' Sᶜ) := by
    ext
    constructor
    · intro h
      obtain ⟨y, rfl⟩ := hf x
      refine' ⟨y, h, rfl⟩
    · rintro ⟨y, h, rfl⟩
      exact h
  rw [this]
  exact Profinite.isClosedMap f (⇑f ⁻¹' Sᶜ) hS

end Profinite

