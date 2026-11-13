import Mathlib.Analysis.NormedSpace.Basic

#align_import Lbar.nnnorm_add_class

/-!
#  The typeclass `nnnorm_add_class α`

In this file, we introduce the typeclass `nnnorm_add_class α`.

Let `α` be a type with a non-negative norm `∥_∥₊`, a zero `0`, an addition `+` and a negation `-`.

The typeclass `nnnorm_add_class α` requires to prove the identities:
* the nnnorm of `0` is `0` : `∥0∥₊ = 0`;
* the nnnorm of `-x` is equal to the nnnorm of `x`: `∥- x∥₊ = ∥x∥₊`;
* the nnnorm of a sum is at most the sum of the nnnorms: `∥x + y∥₊ ≤ ∥x∥₊ + ∥y∥₊`.
-/


open scoped NNReal

variable (α : Type _) [NNNorm α]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/-- A typeclass for an additive monoid `α` with a nnnorm.
Its fields `nnn_zero, nnn_neg, nnn_add_le` assert that
* `∥0∥₊ = 0`;
* `∥- x∥₊ = ∥x∥₊`;
* `∥x + y∥₊ ≤ ∥x∥₊ + ∥y∥₊`.

The class only assumes that `α` has `0, +, -`. -/
class NnnormAddClass [Zero α] [Add α] [Neg α] : Prop where
  nnn_zero : «expr∥ ∥₊» (0 : α) = 0
  nnn_neg : ∀ ⦃x : α⦄, «expr∥ ∥₊» (-x) = «expr∥ ∥₊» x
  nnn_add_le : ∀ ⦃x y : α⦄, «expr∥ ∥₊» (x + y) ≤ «expr∥ ∥₊» x + «expr∥ ∥₊» y

namespace NnnormAddClass

variable {α}

section DefLemmas

variable [Zero α] [Add α] [Neg α] [NnnormAddClass α]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
@[simp]
theorem nnnorm_zero : «expr∥ ∥₊» (0 : α) = 0 :=
  nnn_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
@[simp]
theorem nnnorm_neg (x : α) : «expr∥ ∥₊» (-x) = «expr∥ ∥₊» x := by apply nnn_neg

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem nnnorm_add_le (x y : α) : «expr∥ ∥₊» (x + y) ≤ «expr∥ ∥₊» x + «expr∥ ∥₊» y := by
  apply nnn_add_le

end DefLemmas

variable [AddGroup α] [NnnormAddClass α]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem nnnorm_sub (x y : α) : «expr∥ ∥₊» (x - y) = «expr∥ ∥₊» (y - x) :=
  (nnnorm_neg _).symm.trans (congr_arg _ (neg_sub _ _))

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem nnnorm_triangle (x y z : α) :
    «expr∥ ∥₊» (x - z) ≤ «expr∥ ∥₊» (x - y) + «expr∥ ∥₊» (y - z) :=
  (le_of_eq (by simp only [sub_add_sub_cancel])).trans (nnnorm_add_le _ _)

end NnnormAddClass

