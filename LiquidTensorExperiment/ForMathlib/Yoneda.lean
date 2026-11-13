import Mathlib.Tactic
import Mathlib.CategoryTheory.Yoneda

#align_import for_mathlib.yoneda

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

#print CategoryTheory.yoneda' /-
@[simps]
def yoneda' : C ⥤ Cᵒᵖ ⥤ Type max w v
    where
  obj X := yoneda.obj X ⋙ uliftFunctor.{w}
  map X Y f := whiskerRight (yoneda.map f) _
  map_id' X := by erw [Functor.map_id, whisker_right_id]; rfl
  map_comp' X Y Z f g := by rw [functor.map_comp, whisker_right_comp]
-/

open Opposite

@[simps]
def yoneda'Equiv (X : C) (F : Cᵒᵖ ⥤ Type max w v) : (yoneda'.{w}.obj X ⟶ F) ≃ F.obj (op X)
    where
  toFun e := e.app _ ⟨𝟙 _⟩
  invFun t := { app := fun Y f => F.map f.down.op t }
  left_inv := by
    intro f
    ext Y ⟨t⟩
    have := (f.naturality t.op).symm
    apply_fun fun e => e ⟨𝟙 _⟩ at this 
    dsimp at t this ⊢
    rw [this, category.comp_id]
  right_inv := by tidy

end CategoryTheory

