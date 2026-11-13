import Mathlib.CategoryTheory.Arrow

#align_import for_mathlib.arrow.split

namespace CategoryTheory

namespace Arrow

universe v u

variable {C : Type u} [Category.{v} C]

/-- Split arrows. -/
class Split (f : Arrow C) where
  σ : f.right ⟶ f.left
  is_splitting' : σ ≫ f.hom = 𝟙 _ := by obviously

attribute [simp, reassoc] Split.is_splitting

end Arrow

end CategoryTheory

