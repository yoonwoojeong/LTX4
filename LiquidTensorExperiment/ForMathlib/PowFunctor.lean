import Mathlib.CategoryTheory.Limits.Shapes.Products

#align_import for_mathlib.powFunctor

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C] (α : Type v) [HasProductsOfShape α C]

noncomputable section

def powFunctor : C ⥤ C where
  obj X := ∏ fun i : α => X
  map X Y f := Pi.map fun i => f
  map_id X := by
    ext
    rcases j with ⟨⟩
    simp only [lim_map_π, Discrete.natTrans_app, Category.id_comp]
    dsimp
    simp
  map_comp X Y Z f g := by ext; simp

end CategoryTheory.Limits

