import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits

#align_import for_mathlib.equivalence_additive

namespace CategoryTheory

universe v u u'

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]

instance additive_equivalence_functor (E : A ≌ B) : E.functor.Additive :=
  by
  apply (config := { instances := false }) functor.additive_of_preserves_binary_biproducts
  infer_instance
  have : limits.preserves_colimits E.functor :=
    by
    apply adjunction.left_adjoint_preserves_colimits
    exact E.to_adjunction
  apply limits.preserves_binary_biproducts_of_preserves_binary_coproducts
  infer_instance

instance additive_equivalence_inverse (E : A ≌ B) : E.inverse.Additive :=
  CategoryTheory.additive_equivalence_functor E.symm

end CategoryTheory

