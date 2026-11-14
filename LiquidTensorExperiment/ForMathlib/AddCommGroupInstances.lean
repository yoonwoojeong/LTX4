import Mathlib.Algebra.Category.GroupCat.Abelian

#align_import for_mathlib.AddCommGroup_instances

open CategoryTheory

open CategoryTheory.Limits

namespace AddCommGroupCat

universe u

instance : HasColimitsOfSize.{u} Ab.{u + 1} :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} Ab.{u + 1}

instance : HasLimitsOfSize.{u} Ab.{u + 1} :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} Ab.{u + 1}

end AddCommGroupCat

