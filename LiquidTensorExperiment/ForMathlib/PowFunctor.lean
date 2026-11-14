import Mathlib.CategoryTheory.Limits.Shapes.Products

#align_import for_mathlib.pow_functor

open CategoryTheory

-- Porting note: `noncomputable theory` moved before the first namespace so that the
-- `end`s match
noncomputable section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C] (α : Type v) [HasProductsOfShape α C]

def powFunctor : C ⥤ C where
  obj X := ∏ fun i : α => X
  map {X Y} f := Pi.map fun i => f
  map_id X := by
    ext j
    simp only [limMap_π, Discrete.natTrans_app, Category.id_comp]
    dsimp
    simp
  map_comp {X Y Z} f g := by ext; simp

end CategoryTheory.Limits

