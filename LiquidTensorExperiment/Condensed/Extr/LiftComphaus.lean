import LiquidTensorExperiment.Condensed.Extr.Basic
import Mathlib.Topology.Category.CompHaus.Projective

#align_import condensed.extr.lift_comphaus

noncomputable section

open CategoryTheory

namespace ExtrDisc

theorem lift_exists' {X Y : CompHaus} {P : ExtrDisc} (f : X ⟶ Y) (hf : Function.Surjective f)
    (e : P.val.toCompHaus ⟶ Y) : ∃ g : P.val.toCompHaus ⟶ X, g ≫ f = e :=
  by
  have : epi f := by rwa [CompHaus.epi_iff_surjective f]
  let B : Profinite := Profinite.of (Ultrafilter P.val)
  let π : B ⟶ P.val := ⟨_, continuous_ultrafilter_extend id⟩
  have : epi π := by
    rw [Profinite.epi_iff_surjective]
    intro x; refine' ⟨(pure x : Ultrafilter P.val), _⟩
    have := @ultrafilter_extend_extends P.val _ _ _ id
    exact congr_fun this x
  skip
  choose s hs using Projective.factors (𝟙 _) π
  let φ : CompHaus.of (Ultrafilter P.val.toCompHaus) ⟶ Y := π ≫ e
  choose g h using Projective.factors φ f
  refine' ⟨s ≫ g, _⟩
  erw [Category.assoc, h, ← Category.assoc, hs, Category.id_comp]

def lift' {X Y : CompHaus} {P : ExtrDisc} (f : X ⟶ Y) (hf : Function.Surjective f)
    (e : P.val.toCompHaus ⟶ Y) : P.val.toCompHaus ⟶ X :=
  (lift_exists' f hf e).some

@[reassoc (attr := simp)]
theorem lift_lifts' {X Y : CompHaus} {P : ExtrDisc} (f : X ⟶ Y) (hf : Function.Surjective f)
    (e : P.val.toCompHaus ⟶ Y) : lift' f hf e ≫ f = e :=
  (lift_exists' f hf e).choose_spec

end ExtrDisc

