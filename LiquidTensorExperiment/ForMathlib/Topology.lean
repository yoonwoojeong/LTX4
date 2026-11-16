import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph

#align_import for_mathlib.topology

namespace Homeomorph

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] (e : α ≃ₜ β)
  [TotallyDisconnectedSpace α]

--TODO: Golf and add to mathlib
protected theorem totallyDisconnectedSpace : TotallyDisconnectedSpace β :=
  by
  constructor
  rintro A - hA
  suffices (e.symm '' A).Subsingleton by
    intro x hx y hy
    apply e.symm.injective
    apply this
    exact ⟨x, hx, rfl⟩
    exact ⟨y, hy, rfl⟩
  obtain ⟨h⟩ := (inferInstance : TotallyDisconnectedSpace α)
  apply h
  · tauto
  · exact IsPreconnected.image hA _ e.symm.continuous.continuousOn

end Homeomorph

