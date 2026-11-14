import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Lifting
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Adjunction.Whiskering

#align_import for_mathlib.whisker_adjunction

namespace CategoryTheory.Adjunction

open CategoryTheory

variable (C : Type _) {D E : Type _} [Category C] [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D}

def whiskeringRight (adj : F ⊣ G) : (whiskeringRight C D E).obj F ⊣ (whiskeringRight C E D).obj G :=
  mkOfUnitCounit
    { Unit :=
        { app := fun X =>
            (Functor.rightUnitor _).inv ≫ whiskerLeft X adj.Unit ≫ (Functor.associator _ _ _).inv
          naturality := by intros; ext; dsimp; simp }
      counit :=
        { app := fun X =>
            (Functor.associator _ _ _).hom ≫ whiskerLeft X adj.counit ≫ (Functor.rightUnitor _).hom
          naturality := by intros; ext; dsimp; simp }
      left_triangle := by ext; dsimp; simp
      right_triangle := by ext; dsimp; simp }

@[simp]
theorem whiskeringRight_unit (adj : F ⊣ G) (X : C ⥤ D) :
    (adj.whiskeringRight C).Unit.app X =
      (Functor.rightUnitor _).inv ≫ whiskerLeft X adj.Unit ≫ (Functor.associator _ _ _).inv :=
  rfl

@[simp]
theorem whiskeringRight_counit (adj : F ⊣ G) (X : C ⥤ E) :
    (adj.whiskeringRight C).counit.app X =
      (Functor.associator _ _ _).hom ≫ whiskerLeft X adj.counit ≫ (Functor.rightUnitor _).hom :=
  rfl

end CategoryTheory.Adjunction

