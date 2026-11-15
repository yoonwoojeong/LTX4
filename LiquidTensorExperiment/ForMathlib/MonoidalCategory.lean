import Mathlib.CategoryTheory.Monoidal.Functor

#align_import for_mathlib.monoidal_category

open CategoryTheory

-- Porting note: notation `⊗`, `α_` is scoped in Lean 4
open scoped MonoidalCategory

variable {C D : Type _} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

namespace CategoryTheory.MonoidalFunctor

variable (F : MonoidalFunctor C D)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_associator_hom {X Y Z : C} :
    F.map (α_ X Y Z).hom =
      inv (F.μ (X ⊗ Y) Z) ≫
        inv (F.μ X Y ⊗ 𝟙 (F.obj Z)) ≫
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) :=
  by
  rw [CategoryTheory.IsIso.eq_inv_comp, IsIso.eq_inv_comp]
  exact F.toLaxMonoidalFunctor.associativity X Y Z

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_associator_inv {X Y Z : C} :
    F.map (α_ X Y Z).inv =
      inv (F.μ X (Y ⊗ Z)) ≫
        inv (𝟙 (F.obj X) ⊗ F.μ Y Z) ≫
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ (F.μ X Y ⊗ 𝟙 (F.obj Z)) ≫ F.μ (X ⊗ Y) Z :=
  by
  rw [CategoryTheory.IsIso.eq_inv_comp, IsIso.eq_inv_comp]
  exact F.toLaxMonoidalFunctor.associativity_inv X Y Z

end CategoryTheory.MonoidalFunctor

