import LiquidTensorExperiment.ChallengeNotations
import LiquidTensorExperiment.ChallengePrerequisites
import Mathlib.Algebra.Order.CompleteField

#align_import examples.real

/-!

This file shows that `ℝ` is a conditionally complete linearly ordered field.

Key result from mathlib:
[#3292](https://github.com/leanprover-community/mathlib/pull/3292)

-/


noncomputable section

open scoped LiquidTensorExperiment NNReal ZeroObject

open LiquidTensorExperiment CategoryTheory CategoryTheory.Limits Opposite

/-!
The real numbers `ℝ` are a conditionally complete linearly ordered field.
-/


example : ConditionallyCompleteLinearOrderedField ℝ :=
  inferInstance

/-!
The type of nonnegative real numbers is denoted by `ℝ≥0`.
-/


example : ℝ≥0 = { r : ℝ // r ≥ 0 } :=
  rfl

/-!
Any conditionally complete linear ordered field is isomorphic (as an ordered ring) to `ℝ`.
-/


example {R : Type} [ConditionallyCompleteLinearOrderedField R] : R ≃+*o ℝ :=
  default

/-!
The isomorphism above is unique.
-/


example {R : Type} [ConditionallyCompleteLinearOrderedField R] (e₁ e₂ : R ≃+*o ℝ) : e₁ = e₂ :=
  Subsingleton.elim _ _

