import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits

#align_import for_mathlib.equivalence_additive

namespace CategoryTheory

universe v u u'

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]

instance additive_equivalence_functor (E : A ≌ B) : E.functor.Additive :=
  by
  apply (config := { instances := false }) Functor.additive_of_preservesBinaryBiproducts
  infer_instance
  have : limits.preservesColimits E.functor :=
    by
    apply Adjunction.leftAdjointPreservesColimits
    exact E.to_adjunction
  apply Limits.preservesBinaryBiproductsOfPreservesBinaryCoproducts
  infer_instance

instance additive_equivalence_inverse (E : A ≌ B) : E.inverse.Additive :=
  CategoryTheory.additive_equivalence_functor E.symm

end CategoryTheory

