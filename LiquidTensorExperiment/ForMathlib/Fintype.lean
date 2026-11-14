import Mathlib.CategoryTheory.FintypeCat

#align_import for_mathlib.Fintype

-- Remove when #13984 lands, and use `Fintype.equiv_equiv_iso` instead.
-- Remove when #13984 lands, and use `Fintype.equiv_equiv_iso` instead.
namespace FintypeCat

/-- An equivalence between finite types induces an isomorphism in `Fintype`. -/
@[simps]
def isoOfEquiv {A B : FintypeCat} (e : A ≃ B) : A ≅ B
    where
  hom := e
  inv := e.symm
  hom_inv_id := by ext t; change e.symm (e t) = t; simp
  inv_hom_id := by ext t; change e (e.symm t) = t; simp

end FintypeCat

