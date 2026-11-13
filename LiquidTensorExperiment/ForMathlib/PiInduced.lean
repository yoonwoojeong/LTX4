import Mathlib.Topology.Constructions

#align_import for_mathlib.pi_induced

open TopologicalSpace

theorem pi_induced_induced {ι : Sort _} {X Y : ι → Type _} [t : ∀ i : ι, TopologicalSpace <| Y i]
    (f : ∀ i, X i → Y i) :
    (@Pi.topologicalSpace ι X fun i => induced (f i) (t i)) =
      induced (fun x : ∀ i, X i => (fun j => f j (x j) : ∀ i, Y i)) Pi.topologicalSpace :=
  by
  dsimp [Pi.topologicalSpace]
  rw [induced_iInf]
  simp [induced_compose]

