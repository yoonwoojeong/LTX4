import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Additive categories (compatibility)

`category_theory.additive_category` existed in mathlib3 at LTE's pinned commit
(`5947fb69`, file `category_theory/additive/basic.lean`, author Luke Kershaw) but was
removed from mathlib before the end of mathlib3, so it has no mathlib4 counterpart.
The definition is reproduced here verbatim so that the LTE files using it port faithfully.
-/

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

/-- A preadditive category `C` is called additive if it has all finite biproducts.
See <https://stacks.math.columbia.edu/tag/0104>. -/
class AdditiveCategory (C : Type u) [Category.{v} C] extends Preadditive C,
  HasFiniteBiproducts C

#align CategoryTheory.additiveCategory CategoryTheory.AdditiveCategory

end CategoryTheory
