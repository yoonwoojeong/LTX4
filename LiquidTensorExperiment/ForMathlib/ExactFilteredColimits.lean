import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import LiquidTensorExperiment.ForMathlib.Ab5

#align_import for_mathlib.exact_filtered_colimits

open CategoryTheory

namespace AddCommGroupCat

universe u

variable {J : Type u} [SmallCategory J] [IsFiltered J]

noncomputable section

-- Axiom AB5 for `AddCommGroup`
theorem exact_colim_of_exact_of_isFiltered (F G H : J ⥤ AddCommGroupCat.{u}) (η : F ⟶ G)
    (γ : G ⟶ H) :
    (∀ j, Exact (η.app j) (γ.app j)) → Exact (Limits.colimMap η) (Limits.colimMap γ) :=
  by
  intro h
  rw [AddCommGroupCat.exact_iff']; constructor
  · ext1 j; simp [reassoc_of (h j).1]
  · rintro x (hx : _ = _)
    obtain ⟨j, y, rfl⟩ := limits.concrete.colimit_exists_rep _ x
    erw [← comp_apply, limits.colimit.ι_desc] at hx ; dsimp at hx 
    rw [comp_apply] at hx 
    have : (0 : limits.colimit H) = limits.colimit.ι H j 0 := by simp; rw [this] at hx ; clear this
    obtain ⟨k, e₁, e₂, hk⟩ := limits.concrete.colimit_exists_of_rep_eq _ _ _ hx
    simp only [map_zero, ← comp_apply, ← nat_trans.naturality] at hk ; rw [comp_apply] at hk 
    obtain ⟨t, ht⟩ := ((AddCommGroupCat.exact_iff' _ _).1 (h k)).2 hk
    use limits.colimit.ι F k t
    erw [← comp_apply, limits.colimit.ι_map, comp_apply, ht, ← comp_apply]
    congr 1; simp

instance aB5 : AB5 AddCommGroupCat.{u} := by
  constructor; intro J _ _; intro F G H f g h
  apply exact_colim_of_exact_of_is_filtered
  exact (NatTrans.exact_iff_forall.{u + 1, u, u} f g).1 h

end AddCommGroupCat

