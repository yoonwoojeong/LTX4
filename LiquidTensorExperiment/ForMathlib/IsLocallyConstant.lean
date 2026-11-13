import Mathlib.Topology.Separation
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Data.Setoid.Partition

#align_import for_mathlib.is_locally_constant

noncomputable section

variable {X : Type _} [TopologicalSpace X]

open Set

section

variable {Y : Type _}

theorem isLocallyConstant_iff_clopen_fibers {f : X → Y} :
    IsLocallyConstant f ↔ ∀ y, IsClopen (f ⁻¹' {y}) :=
  ⟨fun h y => h.isClopen_fiber y, fun h s =>
    by
    rw [← bUnion_of_singleton s, preimage_Union₂]
    exact isOpen_biUnion fun x _ => (h x).1⟩

end

section

variable {Y : Type _}

def IndexedPartition.discreteQuotient {ι : Type _} {s : ι → Set X} (h_part : IndexedPartition s)
    (h_cl : ∀ i, IsClopen <| s i) : DiscreteQuotient X
    where
  Rel := h_part.Setoid.Rel
  Equiv := h_part.Setoid.iseqv
  clopen := by
    intro x
    rw [h_part.class_of]
    apply h_cl

variable {ι : Type _} {s : ι → Set X} (h_cl : ∀ i, IsClopen <| s i) (h_part : IndexedPartition s)

def IndexedPartition.discreteQuotientEquiv : ι ≃ h_part.DiscreteQuotient h_cl :=
  h_part.equivQuotient

theorem IndexedPartition.discreteQuotient_fiber (x : h_part.DiscreteQuotient h_cl) :
    (h_part.DiscreteQuotient h_cl).proj ⁻¹' {x} = s ((h_part.discreteQuotientEquiv h_cl).symm x) :=
  h_part.proj_fiber _

end

