import LiquidTensorExperiment.PseudoNormedGroup.Basic
import Mathlib.Analysis.NormedSpace.Basic

#align_import normed_group.pseudo_normed_group

/-!

# A seminormed group is pseudo-normed

This file contains the construction of a pseudo-normed group from a seminormed group.

-/


open scoped NNReal

namespace SeminormedAddCommGroup

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
instance (V : Type _) [SeminormedAddCommGroup V] : PseudoNormedGroup V
    where
  filtration c := {v | «expr∥ ∥₊» v ≤ c}
  filtration_mono c₁ c₂ h v (hv : «expr∥ ∥» v ≤ c₁) := le_trans hv h
  zero_mem_filtration c := by simp only [Set.mem_setOf_eq, nnnorm_zero, zero_le]
  neg_mem_filtration c v hv := by simpa only [Set.mem_setOf_eq, nnnorm_neg] using hv
  add_mem_filtration c₁ c₂ v₁ v₂ hv₁ hv₂ :=
    calc
      «expr∥ ∥» (v₁ + v₂) ≤ «expr∥ ∥» v₁ + «expr∥ ∥» v₂ := norm_add_le _ _
      _ ≤ c₁ + c₂ := add_le_add hv₁ hv₂

variable {V : Type _} [SeminormedAddCommGroup V]

open PseudoNormedGroup

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem mem_filtration_nnnorm (v : V) : v ∈ filtration V («expr∥ ∥₊» v) :=
  show «expr∥ ∥₊» v ≤ «expr∥ ∥₊» v from le_rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
@[simp]
theorem mem_filtration_iff (v : V) (c : ℝ≥0) : v ∈ filtration V c ↔ «expr∥ ∥₊» v ≤ c :=
  Iff.rfl

end SeminormedAddCommGroup

