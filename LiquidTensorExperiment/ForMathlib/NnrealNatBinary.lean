-- non-negative reals
-- non-negative reals
import Mathlib.Data.Real.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LiquidTensorExperiment.ForMathlib.Nnreal

#align_import for_mathlib.nnreal_nat_binary

-- infinite sums
-- infinite sums
open scoped NNReal

-- notation for non-negative reals
open scoped BigOperators

-- notation for infinite sums
/-

# Binary stuff

Binary expansion of `nnreal` works great. If `r : ℝ≥0` then you get a
`digits` function `d(r) : ℕ → ℕ` with `d(0)=⌊r⌋₊` and all the `d(n.succ)`
are 0 or 1, and the theorem is that `r = ∑ n, 2⁻¹ ^ n * b n`.

TODO : relationship between `binary r`
and `binary (2 * r)` or `binary (2⁻¹ * r)`?

-/
/-

## Random stuff

-/
-- move
theorem two_hMul_lt_two {r : ℝ≥0} (hr : r < 1) : 2 * r < 2 :=
  by
  suffices 2 * r < 2 * 1 by simpa
  exact (mul_lt_mul_left (by norm_num)).mpr hr

-- probably true in more generality than nnreal.
theorem NNReal.tsub_lt {a b c : ℝ≥0} (hc : c ≠ 0) (h : a < b + c) : a - b < c :=
  by
  cases' le_or_lt a b with hab hab
  · rw [tsub_eq_zero_of_le hab]
    exact zero_lt_iff.mpr hc
  · rwa [tsub_lt_iff_left hab.le]

theorem NNReal.inv_pos_le_iff_one_le_hMul {a b : ℝ≥0} (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
  by
  suffices : (a : ℝ)⁻¹ ≤ b ↔ (1 : ℝ) ≤ b * a
  assumption_mod_cast
  rw [inv_pos_le_iff_one_le_mul]
  assumption_mod_cast

/-

# binary

An auxiliary function which computes the digits and remainders in the binary
expanion of a non-negative real.

-/
/-- An auxiliary function which computes binary expansion of a non-negative real
and also carries around the remainder. -/
noncomputable def NNReal.Nat.binary (r : ℝ≥0) : ℕ → ℕ × ℝ≥0
  | 0 => (⌊r⌋₊, r - ⌊r⌋₊)
  | n + 1 =>
    let digit := if (NNReal.Nat.binary n).2 < 2⁻¹ then 0 else 1
    (digit, 2 * (NNReal.Nat.binary n).2 - (digit : ℝ≥0))

namespace NNReal

namespace Nat

/-

would be nice to turn on computable reals mode with same notation


binary_aux 0.15
(0,0.15)
(0,0.3)
(0,0.6)
(1,0.2)
(0,0.4)
(0,0.8)
(1.0.6)
(1,1.2)
(1,0.4)

binary_aux 23.45
(23,0.45)
(0,0.9)
(1,0.8)

-/
namespace Binary

variable (r : ℝ≥0) (n : ℕ)

theorem zero_def : binary r 0 = (⌊r⌋₊, r - ⌊r⌋₊) :=
  binary.equations._eqn_1 r

/-- This is the units digit -/
theorem zero_fst_def : (binary r 0).1 = ⌊r⌋₊ := by rw [zero_def]

theorem zero_fst_le : ((binary r 0).1 : ℝ≥0) ≤ r :=
  by
  rw [zero_fst_def]
  apply Nat.floor_le
  exact coe_nonneg r

theorem zero_snd_def : (binary r 0).2 = r - (binary r 0).1 := by rw [zero_def]

theorem succ_fst_def : (binary r (n + 1)).1 = if (binary r n).2 < 2⁻¹ then 0 else 1 := by
  rw [binary.equations._eqn_2]

theorem succ_fst_le : ((binary r (n + 1)).1 : ℝ≥0) ≤ 2 * (binary r n).2 :=
  by
  rw [succ_fst_def]
  split_ifs
  · simp
  · push_neg at h 
    norm_cast
    rw [inv_pos_le_iff_one_le_mul] at h ; swap; norm_num
    rwa [mul_comm]

theorem succ_snd_def : (binary r (n + 1)).2 = 2 * (binary r n).2 - (binary r (n + 1)).1 := by
  rw [binary.equations._eqn_2]

/-- A slightly mathematically stronger version of `succ_snd_def`. -/
theorem succ_snd_def' : (binary r (n + 1)).2 + (binary r (n + 1)).1 = 2 * (binary r n).2 :=
  by
  rw [succ_snd_def r n]
  exact tsub_add_cancel_of_le (succ_fst_le r n)

-- note: the zeroth digit can be any natural.
theorem succ_fst_le_one : (binary r (n + 1)).1 ≤ 1 :=
  by
  rw [succ_fst_def]
  split_ifs <;> linarith

/-- The remainder is bounded. -/
theorem snd_bdd : (binary r n).2 < 1 :=
  by
  induction' n with d hd
  · simp [zero_def]
    have := Nat.lt_floor_add_one r
    have foo : (⌊r⌋₊ : ℝ≥0) ≤ r := Nat.floor_le zero_le'
    exact (tsub_lt_iff_left foo).mpr this
  · simp only [succ_snd_def, succ_fst_def, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    split_ifs with LEM
    · simp
      rw [← mul_lt_mul_left (show (0 : ℝ≥0) < 2 by norm_num)] at LEM 
      convert LEM
      simp
    · push_neg at LEM 
      revert hd
      generalize hx : (binary r d).snd = x; rw [hx] at LEM ; clear hx
      intro hx
      rw [← mul_lt_mul_left (show (0 : ℝ≥0) < 2 by norm_num), mul_one] at hx 
      apply NNReal.tsub_lt; norm_num
      convert hx

theorem fund_thm (B : ℕ) :
    ∑ n in Finset.range B.succ, ((binary r n).1 : ℝ≥0) * 2⁻¹ ^ n + (binary r B).2 * 2⁻¹ ^ B = r :=
  by
  induction' B with d hd
  · simp only [zero_snd_def, zero_fst_def, Finset.range_one, Finset.sum_singleton, pow_zero,
      mul_one]
    rw [← add_tsub_assoc_of_le]; swap; apply Nat.floor_le; apply zero_le
    exact add_tsub_cancel_left (↑⌊r⌋₊) r
  · rw [Finset.sum_range_succ, add_assoc]
    convert hd
    rw [← add_mul, add_comm, succ_snd_def', Nat.succ_eq_add_one, pow_add, pow_one]
    rw [mul_comm (2 : ℝ≥0), mul_assoc]
    congr
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    norm_num

theorem fund_thm' (B : ℕ) :
    (binary r B).2 + (∑ n in Finset.range B.succ, (binary r n).1 * 2 ^ (B - n) : ℕ) = r * 2 ^ B :=
  by
  have := fund_thm r B
  apply_fun fun x => x * (2 : ℝ≥0) ^ B at this 
  convert this
  rw [add_comm, add_mul]
  congr
  · rw [Finset.sum_mul]
    push_cast
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_range_succ_iff] at hn 
    rw [mul_assoc, zero_add, one_add_one_eq_two]
    congr
    simp
    rw [pow_sub₀ (2 : ℝ≥0) _ hn, mul_comm]
    norm_num
  · rw [mul_assoc, ← mul_pow, inv_mul_cancel]
    · simp
    · norm_num

end Binary

-- in `nnreal` namespace
noncomputable def digit (r : ℝ≥0) (n : ℕ) : ℕ :=
  (binary r n).1

namespace Digit

variable (r : ℝ≥0) (n B : ℕ)

theorem zero_def : digit r 0 = ⌊r⌋₊ :=
  binary.zero_fst_def r

theorem zero_le : (digit r 0 : ℝ≥0) ≤ r :=
  binary.zero_fst_le r

theorem succ_le_one : digit r (n + 1) ≤ 1 :=
  binary.succ_fst_le_one r n

theorem sum_le_r : ∑ n in Finset.range B.succ, (digit r n : ℝ≥0) * 2⁻¹ ^ n ≤ r :=
  by
  conv_rhs => rw [← binary.fund_thm r B]
  apply le_add_right
  rfl

theorem r_le_pow_add_sum : r < 2⁻¹ ^ B + ∑ n in Finset.range B.succ, (digit r n : ℝ≥0) * 2⁻¹ ^ n :=
  by
  conv_lhs => rw [← binary.fund_thm r B]
  rw [add_comm]
  refine' add_lt_add_right _ _
  rw [mul_lt_iff_lt_one_left]
  · exact binary.snd_bdd r B
  · apply pow_pos
    norm_num

theorem r_sub_sum_small : r - ∑ n in Finset.range B.succ, (digit r n : ℝ≥0) * 2⁻¹ ^ n < 2⁻¹ ^ B :=
  by
  have := r_le_pow_add_sum r B
  rw [← tsub_lt_tsub_iff_right (sum_le_r r B)] at this 
  convert this
  simp

--theorem r_bounds :
--   r ∈ set.Ico
--   (∑ n in finset.range B.succ, ((digit r n) : ℝ≥0) * 2⁻¹ ^ n)
--   (2⁻¹ ^ B + ∑ n in finset.range B.succ, ((binary r n).1 : ℝ≥0) * 2⁻¹ ^ n)
--   :=
-- ⟨sum_le_r r B, r_le_pow_add_sum r B⟩
theorem summable : Summable fun n : ℕ => (NNReal.Nat.digit r n : ℝ≥0) * 2⁻¹ ^ n :=
  by
  have foo : ∀ n, (NNReal.Nat.digit r n : ℝ≥0) ≤ max (NNReal.Nat.digit r 0) 1 :=
    by
    rintro (rfl | n)
    · apply le_max_left
    · refine' le_trans _ (le_max_right _ _)
      exact_mod_cast succ_le_one r n
  have bar : ∀ n, (NNReal.Nat.digit r n : ℝ≥0) * 2⁻¹ ^ n ≤ max (NNReal.Nat.digit r 0) 1 * 2⁻¹ ^ n :=
    by
    intro n
    rw [mul_le_mul_right₀]; exact foo n
    apply pow_ne_zero
    norm_num
  apply summable_of_le bar
  apply Summable.mul_left
  apply summable_geometric
  apply two_inv_lt_one

theorem hasSum : HasSum (fun n => (digit r n : ℝ≥0) * 2⁻¹ ^ n) r :=
  by
  rw [Summable.hasSum_iff_tendsto_nat (Summable r)]
  dsimp
  intro X hX
  rw [mem_nhds_iff] at hX 
  rcases hX with ⟨V, hVX, hV1, hVr⟩
  rw [Filter.mem_map]
  rw [Filter.mem_atTop_sets]
  -- choose a large enough such that (r-2⁻¹^a,r] ⊆ V
  obtain ⟨ε, hε, hεV⟩ := metric.isOpen_iff.mp hV1 r hVr
  change 0 < ε at hε 
  have foo : ∃ a : ℕ, (2⁻¹ : ℝ≥0) ^ a ≤ ⟨ε, hε.le⟩ :=
    by
    by_cases hε1 : 1 ≤ ε
    · use 0; simp; exact_mod_cast hε1
    · push_neg at hε1 
      use⌈Real.log ε / Real.log 2⁻¹⌉₊
      have := Nat.le_ceil (Real.log ε / Real.log 2⁻¹)
      have moo : (2⁻¹ : ℝ≥0) ^ ↑⌈Real.log ε / Real.log 2⁻¹⌉₊ ≤ 2⁻¹ ^ (Real.log ε / Real.log 2⁻¹) :=
        rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) this
      convert le_trans moo _ using 1; norm_cast
      -- now coerce to real
      suffices : (2⁻¹ : ℝ) ^ (Real.log ε / Real.log 2⁻¹) ≤ ε
      assumption_mod_cast
      -- convenient thing
      have inv_two_pos : (0 : ℝ) < 2⁻¹ := by rw [_root_.inv_pos]; apply zero_lt_two
      rw [← Real.log_le_log (Real.rpow_pos_of_pos inv_two_pos _) hε]
      apply le_of_eq
      rw [Real.log_rpow inv_two_pos]
      rw [div_mul_cancel]
      apply Real.log_ne_zero_of_pos_of_ne_one inv_two_pos
      norm_num
  cases' foo with B hB
  use B + 1
  intro m hm; cases' m with m; cases hm
  rw [Set.mem_preimage]
  have h_le_r := sum_le_r r m
  have h_r_lt := r_le_pow_add_sum r m
  apply hVX
  apply hεV
  rw [Metric.mem_ball]
  change |_ - _| < ε
  rw [abs_lt]
  rw [← NNReal.coe_lt_coe] at h_r_lt 
  push_cast at h_r_lt ⊢
  constructor
  · suffices : (2⁻¹ : ℝ) ^ m ≤ ε
    linarith
    have hB' : (2⁻¹ : ℝ) ^ B ≤ ε; assumption_mod_cast
    refine' le_trans _ hB'
    refine' pow_le_pow_of_le_one (by norm_num) (by norm_num) _
    change B + 1 ≤ m + 1 at hm 
    linarith
  · rw [← NNReal.coe_le_coe] at h_le_r 
    push_cast at h_le_r 
    linarith

theorem tsum : ∑' n, (digit r n : ℝ≥0) * 2⁻¹ ^ n = r :=
  HasSum.tsum_eq (hasSum r)

end Digit

end Nat

end NNReal

