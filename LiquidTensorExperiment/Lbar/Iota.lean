import LiquidTensorExperiment.BreenDeligne.Eg
import LiquidTensorExperiment.Thm95.Constants.Default
import LiquidTensorExperiment.PolyhedralLattice.Int
import LiquidTensorExperiment.SystemOfComplexes.ShiftSubId

#align_import Lbar.iota

open BreenDeligne Thm95.UniversalConstants

open scoped NNReal

namespace Lbar

variable (r r' : ℝ≥0)

variable [Fact (0 < r')] [Fact (r < 1)]

variable (i : ℕ)

-- move me
theorem κ_pos : ∀ m, 0 < eg.κ r r' m
  | 0 => zero_lt_one
  | m + 1 => by
    dsimp only [eg.κ, data.κ]
    refine' mul_pos _ _
    · refine' nnreal.inv_pos.mpr (lt_max_of_lt_left zero_lt_one)
    · refine' mul_pos (pow_pos (Fact.out _) _) (κ_pos _)

variable [Fact (0 < r)] [Fact (r < r')] [Fact (r' < 1)]

noncomputable def ι' : ℕ → ℝ≥0
  | 0 =>
    max (c₀ r r' eg (fun n : ℕ => eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩)
      (c₀ r r' eg (fun n : ℕ => eg.κ r r' n) (eg.κ' r r') (i + 1 + 1) ⟨ℤ⟩)
  | j + 1 =>
    max (max (j + 1) (ι' j))
      (max (max (k (eg.κ' r r') i ^ 2 * ι' j) (k (eg.κ' r r') (i + 1) ^ 2 * ι' j))
        (k (eg.κ' r r') (i + 1 + 1) ^ 2 * ι' j))

theorem hι' : Monotone (ι' r r' i) :=
  by
  apply monotone_nat_of_le_succ
  rintro (_ | j) <;> refine' le_trans (le_max_right _ _) (le_max_left _ _)

theorem Hι1 : ∀ j, c₀ r r' eg (fun n : ℕ => eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩ ≤ ι' r r' i j
  | 0 => le_max_left _ _
  | j + 1 => (Hι1 j).trans <| by apply hι'; apply Nat.le_succ

theorem Hι1' : ∀ j, c₀ r r' eg (fun n : ℕ => eg.κ r r' n) (eg.κ' r r') (i + 1 + 1) ⟨ℤ⟩ ≤ ι' r r' i j
  | 0 => le_max_right _ _
  | j + 1 => (Hι1' j).trans <| by apply hι'; apply Nat.le_succ

theorem Hι2a : ∀ j, k (eg.κ' r r') i ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) := by
  rintro (_ | j) <;> simp only [ι', le_max_iff, le_rfl, true_or_iff, or_true_iff]

theorem Hι2b : ∀ j, k (eg.κ' r r') (i + 1) ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) := by
  rintro (_ | j) <;> simp only [ι', le_max_iff, le_rfl, true_or_iff, or_true_iff]

theorem Hι2c : ∀ j, k (eg.κ' r r') (i + 1 + 1) ^ 2 * ι' r r' i j ≤ ι' r r' i (j + 1) := by
  rintro (_ | j) <;> simp only [ι', le_max_iff, le_rfl, true_or_iff, or_true_iff]

noncomputable def ι : ULift.{1} ℕ → ℝ≥0 :=
  ι' r r' i ∘ ULift.down

theorem hι : Monotone (ι r r' i) := fun j₁ j₂ h => by delta ι; apply hι'; exact h

theorem hι'_self_le : ∀ j : ℕ, (j : ℝ≥0) ≤ ι' r r' i j
  | 0 => by norm_cast; exact zero_le'
  | j + 1 => by simp only [ι', le_max_iff, Nat.cast_add, Nat.cast_one, le_refl, true_or_iff]

theorem sufficiently_increasing_eg (s : ℝ≥0) (m : ℕ) : ∃ n : ℕ, s ≤ ι' r r' i n * eg.κ r r' m :=
  by
  let κ := eg.κ r r' m
  let n := ⌈s * κ⁻¹⌉₊
  let ι := ι' r r' i n
  refine' ⟨n, _⟩
  calc
    s = s * κ⁻¹ * κ := _
    _ ≤ ι * κ := mul_le_mul' _ le_rfl
  · rw [inv_mul_cancel_right₀]; apply ne_of_gt; apply κ_pos
  · refine' (Nat.le_ceil _).trans (hι'_self_le _ _ _ _)

theorem sufficiently_increasing_eg' (s : ℝ≥0) (m : ℕ) :
    ∃ n : ℕ, s ≤ r' * (ι' r r' i n * eg.κ r r' m) :=
  by
  obtain ⟨n, hn⟩ := sufficiently_increasing_eg r r' i (s / r') m
  use n
  replace hn := mul_le_mul (le_refl r') hn (zero_le (s / r')) (zero_le _)
  refine' le_trans (le_of_eq _) hn
  have : r' ≠ 0 := by symm; exact ne_of_lt (Fact.out (0 < r'))
  rw [mul_comm]
  exact (div_eq_iff this).mp rfl

def SufficientlyIncreasing (κ : ℝ≥0 → ℕ → ℝ≥0) (ι : ULift ℕ → ℝ≥0) : Prop :=
  ∀ (r : ℝ≥0) (m : ℕ), ∃ n : ℕ, r ≤ κ (ι ⟨n⟩) m

end Lbar

