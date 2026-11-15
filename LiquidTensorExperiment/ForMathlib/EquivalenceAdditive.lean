import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits

#align_import for_mathlib.equivalence_additive

namespace CategoryTheory

universe v u u'

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]

instance additive_equivalence_functor (E : A ≌ B) : E.functor.Additive :=
  by
  -- Porting note: Lean 3 used `apply_with … {instances := ff}`; we provide the instances first.
  haveI : Limits.PreservesColimits E.functor :=
    Adjunction.leftAdjointPreservesColimits E.toAdjunction
  haveI : Limits.PreservesBinaryBiproducts E.functor :=
    Limits.preservesBinaryBiproductsOfPreservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

instance additive_equivalence_inverse (E : A ≌ B) : E.inverse.Additive :=
  CategoryTheory.additive_equivalence_functor E.symm

end CategoryTheory

