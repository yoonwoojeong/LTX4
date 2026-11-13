import Mathlib.CategoryTheory.Limits.Shapes.Terminal

#align_import for_mathlib.is_iso_iota

namespace CategoryTheory.Limits

open CategoryTheory

universe v u

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C] (F : J ⥤ C)

noncomputable section

@[simps]
def IsInitial.colimitCocone {j : J} (hj : IsInitial j) [HasColimit F]
    [∀ (a b : J) (f : a ⟶ b), IsIso (F.map f)] : Cocone F
    where
  pt := F.obj j
  ι :=
    { app := fun i => inv (F.map <| hj.to _)
      naturality := by
        intro a b f
        dsimp
        simp only [IsIso.eq_inv_comp, IsIso.comp_inv_eq, Category.comp_id]
        simp_rw [← F.map_comp]
        congr 1
        apply hj.hom_ext }

def IsInitial.isColimitColimitCocone {j : J} (hj : IsInitial j) [HasColimit F]
    [∀ (a b : J) (f : a ⟶ b), IsIso (F.map f)] : IsColimit (hj.colimitCocone F)
    where desc S := S.ι.app _

theorem IsInitial.isIso_ι {j : J} (hj : IsInitial j) [HasColimit F]
    [∀ (a b : J) (f : a ⟶ b), IsIso (F.map f)] : IsIso (colimit.ι F j) :=
  by
  let e := (colimit.isColimit F).coconePointUniqueUpToIso (hj.isColimitColimitCocone F)
  change is_iso e.inv
  infer_instance

end CategoryTheory.Limits

