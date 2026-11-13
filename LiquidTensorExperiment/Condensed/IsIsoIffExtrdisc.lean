import LiquidTensorExperiment.Condensed.TopComparison

#align_import condensed.is_iso_iff_extrdisc

open CategoryTheory

namespace Condensed

universe u

variable {X Y : Condensed.{u} Ab.{u + 1}} (f : X ⟶ Y)

theorem isIso_iff_extrDisc : IsIso f ↔ ∀ S : ExtrDisc, IsIso (f.val.app (Opposite.op S.val)) :=
  by
  constructor
  · intro h S
    change is_iso ((Condensed.evaluation _ _).map f)
    infer_instance
  · intro h
    suffices is_iso ((condensedExtrSheafProdEquiv Ab).Functor.map f)
      by
      skip
      apply CategoryTheory.isIso_of_fully_faithful (condensedExtrSheafProdEquiv Ab.{u + 1}).Functor f
    suffices
      is_iso
        ((extrSheafProdToPresheaf Ab.{u + 1}).map
          ((condensedExtrSheafProdEquiv Ab.{u + 1}).Functor.map f))
      by
      skip
      apply CategoryTheory.isIso_of_fully_faithful (extrSheafProdToPresheaf Ab.{u + 1})
    apply (config := { instances := false }) NatIso.isIso_of_isIso_app
    intro S; apply h

end Condensed

