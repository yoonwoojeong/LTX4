import LiquidTensorExperiment.PseudoNormedGroup.Basic
import Mathlib.Analysis.NormedSpace.Basic

#align_import normed_group.pseudoNormedGroup

/-!

# A seminormed group is pseudo-normed

This file contains the construction of a pseudo-normed group from a seminormed group.

-/


open scoped NNReal

namespace SeminormedAddCommGroup

instance (V : Type _) [SeminormedAddCommGroup V] : PseudoNormedGroup V
    where
  filtration' c := {v | ‖v‖₊ ≤ c}
  filtration_mono c₁ c₂ h v (hv : ‖v‖ ≤ c₁) := le_trans hv h
  zero_mem_filtration' c := by simp only [Set.mem_setOf_eq, nnnorm_zero, zero_le]
  neg_mem_filtration' c v hv := by simpa only [Set.mem_setOf_eq, nnnorm_neg] using hv
  add_mem_filtration' c₁ c₂ v₁ v₂ hv₁ hv₂ :=
    calc
      ‖v₁ + v₂‖ ≤ ‖v₁‖ + ‖v₂‖ := norm_add_le _ _
      _ ≤ c₁ + c₂ := add_le_add hv₁ hv₂

variable {V : Type _} [SeminormedAddCommGroup V]

open PseudoNormedGroup

theorem mem_filtration_nnnorm (v : V) : v ∈ filtration V (‖v‖₊) :=
  show ‖v‖₊ ≤ ‖v‖₊ from le_rfl

@[simp]
theorem mem_filtration_iff (v : V) (c : ℝ≥0) : v ∈ filtration V c ↔ ‖v‖₊ ≤ c :=
  Iff.rfl

end SeminormedAddCommGroup

