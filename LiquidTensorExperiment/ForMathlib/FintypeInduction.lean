import Mathlib.Data.Fintype.Basic
import Mathlib.CategoryTheory.FintypeCat

#align_import for_mathlib.fintype_induction

open scoped Classical

universe u

-- This is an awkward hybrid: we should state the induction principle for unbundled fintype
-- and then if it is necessary provide an interface for using it with `Fintype`.
theorem FintypeCat.induction_empty_sum {P : FintypeCat.{u} → Prop}
    (of_equiv : ∀ {α β : FintypeCat.{u}}, α ≃ β → P α → P β) (h_empty : P (FintypeCat.of PEmpty))
    (h_option : ∀ {α : FintypeCat.{u}}, P α → P (FintypeCat.of (Sum α (PUnit : Type u))))
    (α : FintypeCat.{u}) : P α :=
  by
  let Q : ∀ (α : Type u) [Fintype α], Prop := fun a h => P ⟨a, h⟩
  have H := @Fintype.induction_empty_option Q _ _ _ α α.str
  · cases α; exact H
  · intro α β _ e h
    haveI : Fintype α := Fintype.ofEquiv _ e.symm
    let e' : FintypeCat.of α ≃ FintypeCat.of β := e
    apply of_equiv e'
    convert h
  · assumption
  · intro α _ h
    let e : Option α ≃ Sum α (PUnit : Type u) := Equiv.optionEquivSumPUnit _
    let e' : FintypeCat.of (Option α) ≃ FintypeCat.of (Sum α PUnit) := e
    apply of_equiv e'.symm
    exact h_option h

