import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LiquidTensorExperiment.PolyhedralLattice.Cosimplicial
import LiquidTensorExperiment.CombinatorialLemma.Default
import LiquidTensorExperiment.BreenDeligne.Eg
import LiquidTensorExperiment.Thm95.Constants.SpectralConstants
import LiquidTensorExperiment.ForMathlib.Nnreal

#align_import thm95.constants.default

/-!
# Explicit formulas for the constants used in Theorem 9.5 of Analytic.pdf

Fix the following notation.

* `r` and `r'` are real numbers satisfying `0 < r < r' ≤ 1`
* `BD` denotes a Breen-Deligne package
* `κ'` is a sequence of nonnegative real numbers
* `Λ` denotes a polyhedral lattice

The main goal of this file is to define sequences of constants `k₁`, `K₁`, `k'`, `N₂`, `b`, `H`,
satisfying the inequalities below.
But first we make some abbreviations:

* `k₀ m := normed_spectral.k₀ m (k₁ m)`
* `K₀ m := normed_spectral.K₀ m (K₁ m)`
* `ε m := normed_spectral.ε m (K₁ m)`
* `k m := (k' m)^2`
* `K m := 2 * K₀ m * H m`

It is known that:

* `normed_spectral.k₀` always returns a number larger or equal to `1`.
* `normed_spectral.K₀` always returns a number larger or equal to `1`.
* `normed_spectral.ε` always returns a positive number.

The following inequalities are imposed on these constants
by the normed homological algebra of the rest of the proof:

* `1 < k₁ m`
* `1 ≤ K₁ m`
* `1 ≤ k' m`
* `k (m - 1) ≤ k₁ m`, for `m > 0`
* `K (m - 1) ≤ K₁ m`, for `m > 0`
* `m + 2 + (r + 1) / (r * (1 - r)) * (m + 2) ^ 2 ≤ K₁ m`
* `k₀ m ≤ k' m`
* `κ' i ≤ k' m` for all `i ≤ m+1`
* `(2 * k' m) * (r / r') ^ (b m) ≤ ε m`
* `k' m ≤ 2 ^ N₂ m`
* `k' m / (2 ^ N₂ m) ≤ r' ^ (b m)`
* `r ^ (b m) * (2 ^ N₂ m) ≤ 2 * k' m * (r / r') ^ (b m)`
* For `q ≤ m`, the technical condition
  `((BD.data.homotopy_mul BD.homotopy (N₂ m)).hom q (q + 1)).bound_by (H m)`
  saying that `H m` should be larger than a list of `m + 1` numbers depending on `BD` and `N₂ m`.

-/


noncomputable section

open scoped NNReal

open Real Finset

namespace Helper

/-- Given real numbers `r`, `r'`, `k'`, and `ε`, we define `b` to be the smallest natural number
larger than `log(ε / (2 * k')) / log(r/r')`. -/
def b (r r' k' ε : ℝ) : ℕ :=
  Nat.ceil ((log <| ε / (2 * k')) / log (r / r'))

/-- Under the constraints that `r`, `r'`, `k'`, and `ε` are positive real numbers
satisfying `r < r'`, the natural number `b = b r r' k' ε` satisfies
`(2 * k') * (r/r') ^ b ≤ ε`. -/
theorem b_spec {r r' k' ε : ℝ} (hr : 0 < r) (hr' : 0 < r') (hrr' : r < r') (hk' : 0 < k')
    (hε : 0 < ε) : 2 * k' * (r / r') ^ b r r' k' ε ≤ ε :=
  by
  have f₁ : 0 < 2 * k' := mul_pos zero_lt_two hk'
  have f₂ : r / r' < 1 := (div_lt_one hr').mpr hrr'
  have f₃ : 0 < r / r' := div_pos hr hr'
  have f₄ : 0 < (r / r') ^ b r r' k' ε := pow_pos f₃ _
  rw [← le_div_iff' f₁, ← log_le_log f₄ (div_pos hε f₁), log_pow, ←
    div_le_iff_of_neg (log_neg f₃ f₂)]
  exact Nat.le_ceil (log (ε / (2 * k')) / log (r / r'))

/-- Given real numbers `r'`, `k'`, and `b`, we define `N₂` to be the smallest natural number
larger than `log(k' / r'^b) / log(2)`. -/
def n₂ (r' k' b : ℝ) :=
  Nat.ceil (log (k' / r' ^ b) / log 2)

/-- Under the constraints that `r'` and `k'` are positive real numbers,
the natural number `N₂ = N₂ r' k' b` satisfies `k' / (2 ^ N₂) ≤ r' ^ b`. -/
theorem n₂_spec {r' k' b : ℝ} (hr' : 0 < r') (hk' : 0 < k') : k' / 2 ^ n₂ r' k' b ≤ r' ^ b :=
  by
  have f₁ : (0 : ℝ) < 2 ^ N₂ r' k' b := pow_pos zero_lt_two _
  have f₂ : (0 : ℝ) < r' ^ b := rpow_pos_of_pos hr' _
  have f₃ : 0 < k' / r' ^ b := div_pos hk' f₂
  have f₄ : 0 < log 2 := log_pos one_lt_two
  rw [div_le_iff' f₁, ← div_le_iff f₂, ← log_le_log f₃ f₁, log_pow, ← div_le_iff f₄]
  apply Nat.le_ceil

/-- Under the constraints that `r'` is a positive real number and `k'` is nonnegative,
the natural number `N₂ = N₂ r' k' b` satisfies `r' ^b < 2 * k' / (2 ^ N₂)`. -/
theorem n₂_spec_of_pos' {r' k' b} (h : 0 < n₂ r' k' b) (hr' : 0 < r') (hk' : 0 ≤ k') :
    r' ^ b < 2 * k' / 2 ^ n₂ r' k' b :=
  by
  have h' := nat.lt_ceil.mp h
  have : 0 < log (k' / r' ^ b) / log 2 := by exact_mod_cast nat.lt_ceil.mp h
  have f₁ : 0 < 2 ^ N₂ r' k' b := pow_pos zero_lt_two _
  have Hk' : k' ≠ 0 := by
    intro H
    simpa [H, N₂] using h
  have f₂ : 0 < r' ^ b := rpow_pos_of_pos hr' b
  have f₃ : 0 < k' / r' ^ b := div_pos ((Ne.symm Hk').le_iff_lt.mp hk') f₂
  have f₃' : k' / r' ^ b ≠ 0 := f₃.ne.symm
  have f₄ : (N₂ r' k' b : ℝ) < _ := Nat.ceil_lt_add_one this.le
  rwa [lt_div_iff, ← lt_div_iff', mul_div_assoc, ← log_lt_log_iff, log_mul, log_pow, ←
    lt_div_iff (log_pos one_lt_two), add_div, div_self (log_pos one_lt_two).Ne.symm, add_comm]
  all_goals
    first
    | assumption
    | norm_num
  assumption

end Helper

section

/-!
In the rest of this file, we fix once and for all the following parameters:

* `r` and `r'` are nonnegative real numbers
* `BD` denotes a Breen-Deligne package
* `κ` and `κ'` are sequences of nonnegative real numbers,
  that are assumed to be "adept" with respect to `BD`
  and "very suitable" with respect to `BD`, `r`, and `r'`.
* `Λ` denotes a polyhedral lattice
-/


parameter (r r' : ℝ≥0)

parameter (BD : BreenDeligne.Package) (κ κ' : ℕ → ℝ≥0)

parameter (Λ : PolyhedralLatticeCat)

/-!
We also let `m` denote a variable natural number.
-/


variable (m : ℕ)

namespace Thm95

open SystemOfDoubleComplexes

namespace UniversalConstants

open BreenDeligne

/-- `k₁ m` is a sequence of nonnegative real numbers, defined recursively via
* `k₁ 0 = 2` (the important property being `k₁ 0 > 1`) and
* `k₁ (m+1)` is the maximum of `2` and `c`,
  where `c` is the square of the maximum of `k₀ m (k₁ m)`, and `κ' 0`, `κ' 1`, ..., `κ' (m+1)`.
  Here `k₀ m k` is the sequence of constants used in the proof of `normed_spectral`. -/
noncomputable def k₁ : ℕ → ℝ≥0
  | 0 => 2
  |-- should be anything > 1
      m +
      1 =>
    max 2 ((max (NormedSpectral.k₀ m (k₁ m)) <| (range <| m + 2).sup κ') ^ 2)

/-- All the numbers `k₁ m` are larger than `1`. -/
instance one_lt_k₁ : ∀ m : ℕ, Fact (1 < k₁ m)
  | 0 => ⟨one_lt_two⟩
  | m + 1 => ⟨lt_of_lt_of_le one_lt_two (le_max_left _ _)⟩

/-- `k₀ m` is the constant `k₀ m (k m)` used in the proof of `normed_spectral`. -/
abbrev k₀ : ℝ≥0 :=
  NormedSpectral.k₀ m (k₁ m)

/-- `k' m` is the maximum of `k₀ m` and the constants `κ' 0`, `κ' 1`, ..., `κ' m`, `κ' (m+1)` -/
def k' : ℝ≥0 :=
  max (k₀ m) <| (range <| m + 2).sup κ'

/-- For indices `i` ranging over `0` up to `m+1`, we have `κ' i ≤ k' m`. -/
theorem κ'_le_k' {i : ℕ} (hi : i ≤ m + 1) : κ' i ≤ k' m :=
  le_max_iff.mpr <| Or.inr <| le_sup <| mem_range.mpr <| Nat.lt_succ_iff.mpr hi

-- A different way of telling Lean the same fact as the previous lemma.
instance fact_κ'_le_k' {i : ℕ} (hi : Fact (i ≤ m + 1)) : Fact (κ' i ≤ k' m) :=
  ⟨κ'_le_k' _ hi.1⟩

/-- We always have `1 ≤ k' m` for all `m`, since `1 ≤ k₀ m`. -/
instance one_le_k' : Fact (1 ≤ k' m) :=
  ⟨le_trans (Fact.out _) <| le_max_left _ _⟩

/-- We always `k₀ m ≤ k' m`. -/
instance k₀_le_k' : Fact (k₀ m ≤ k' m) :=
  ⟨le_max_left _ _⟩

/-- `k m` is the square of `k' m`. -/
def k : ℝ≥0 :=
  k' m * k' m

instance one_le_k : Fact (1 ≤ k m) := by delta k; infer_instance

/-- For positive `m`, we have `k (m-1) ≤ k₁ m`. -/
instance k_le_k₁ [Fact (0 < m)] : Fact (k (m - 1) ≤ k₁ m) :=
  by
  cases m
  · exact False.elim (lt_irrefl 0 (Fact.elim inferInstance))
  · apply Fact.mk
    simp only [k₁]
    convert le_max_right _ _
    rw [pow_two]
    rfl

/-- `k₁_sqrt m` denotes the square root of `k₁ m`. -/
def k₁Sqrt : ℝ≥0 :=
  ⟨Real.sqrt (k₁ m), Real.sqrt_nonneg _⟩

instance one_lt_k₁Sqrt : Fact (1 < k₁_sqrt m) :=
  ⟨by
    change (1 : ℝ) < Real.sqrt (k₁ κ' m)
    rw [Real.lt_sqrt zero_le_one, pow_two, mul_one]
    exact (universal_constants.one_lt_k₁ κ' m).elim⟩

/-- `y m r` denotes `m + 2 + (r + 1) / (r - r^2) * (m + 2)^2`. -/
def y (m : ℕ) (r : ℝ≥0) :=
  (m + 2 : ℝ≥0) + (r + 1) / (r * (1 - r)) * (m + 2) ^ 2

/-- `H' m n` is the maximum of `1` and `c`, where `c` bounds the first `m+1` maps in the
`n`-th iteration of the homotopy of the Breen-Deligne package `BD`. -/
def h' (n : ℕ) :=
  max 1 ((range <| m + 1).sup fun q => ((BD.data.homotopyMul BD.Homotopy n).hom q (q + 1)).bound)

/- warning: thm95.universal_constants.K₁ clashes with thm95.universal_constants.k₁ -> Thm95.UniversalConstants.k₁
Case conversion may be inaccurate. Consider using '#align thm95.universal_constants.K₁ Thm95.UniversalConstants.k₁ₓ'. -/
/-- `K₁` is a sequence of nonnegative real numbers, defined recursively via
* `K₁ 0 = 2 + (r + 1) / (r * (1 - r)) * 4`
* `K₁ (m+1) = max (y (m+1) r) c`, where
  - `y (m+1) r` is defined to be `m + 3 + (r + 1) / (r - r^2) * (m + 3)^2`
  - `c` is `2 * K₀ m (K₁ m) * (H' m N₂)`
  - `K₀ m K₁` denotes one of the constants used in the proof of `normed_spectral`
  - `N₂` denotes the natural number `N₂ r' (k' m) (b r r' (k' m) ε)` defined before
  - `ε` denotes the constant `ε m (K₁ m)` used in the proof of `normed_spectral`. -/
noncomputable def k₁ : ℕ → ℝ≥0
  | 0 => 2 + (r + 1) / (r * (1 - r)) * 4
  | m + 1 =>
    max (y (m + 1) r)
      (2 * NormedSpectral.k₀ m (K₁ m) *
        (H' m <| Helper.n₂ r' (k' m) (Helper.b r r' (k' m) (NormedSpectral.ε m (K₁ m)))))

/-- For all `m`, the number `K₁ m` is larger than `1`. -/
instance one_le_k₁ : ∀ m, Fact (1 ≤ K₁ m)
  | 0 =>
    ⟨by
      dsimp [K₁]
      apply le_add_right
      exact one_le_two⟩
  | m + 1 =>
    ⟨by
      dsimp [K₁]
      refine' le_max_iff.mpr (Or.inl _)
      dsimp [y]
      apply le_add_right
      norm_cast
      exact le_add_self⟩

/- warning: thm95.universal_constants.K₀ clashes with thm95.universal_constants.k₀ -> Thm95.UniversalConstants.k₀
Case conversion may be inaccurate. Consider using '#align thm95.universal_constants.K₀ Thm95.UniversalConstants.k₀ₓ'. -/
/-- `K₀ m` is the constant `K₀ m (K m)` used in the proof of `normed_spectral` -/
abbrev k₀ : ℝ≥0 :=
  NormedSpectral.k₀ m (K₁ m)

/-- `ε m` is the constant `ε m (K m)` used in the proof of `normed_spectral` -/
abbrev ε : ℝ≥0 :=
  NormedSpectral.ε m (K₁ m)

instance ε_pos : Fact (0 < ε m) :=
  ⟨NormedSpectral.ε_pos _ _⟩

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' ≤ 1)]

/-- `b κ' r r' m` is the smallest `b` such that `2 * (k' m) * (r / r') ^ b ≤ (ε m)`. -/
def b : ℕ :=
  Helper.b r r' (k' m) (ε m)

/-- `b κ' r r' m` is the smallest `b` such that `2 * (k' m) * (r / r') ^ b ≤ (ε m)`.
This lemma proves that `b` indeed satisfies the property claimed at its definition. -/
theorem b_spec : 2 * k' m * (r / r') ^ b m ≤ ε m :=
  by
  suffices : 2 * (k' κ' m : ℝ) * (r / r') ^ b r r' BD κ' m ≤ ε r r' BD κ' m
  exact_mod_cast this
  apply Helper.b_spec ‹Fact (0 < r)›.out ‹Fact (0 < r')›.out ‹Fact (r < r')›.out <;> norm_cast <;>
    apply Fact.out

/-- `N₂ κ' r r' m` is the smallest `N₂` such that `N = 2 ^ N₂` satisfies
`(k' m) / N ≤ r' ^ (b κ' r r' m)`. -/
def n₂ : ℕ :=
  Helper.n₂ r' (k' m) (b m)

/-- `N₂ κ' r r' m` is the smallest `N₂` such that `N = 2 ^ N₂` satisfies
`(k' m) / N ≤ r' ^ (b κ' r r' m)`.
This lemma proves that `N₂` indeed satisfies the property claimed at its definition. -/
theorem n₂_spec : k' m / 2 ^ N₂ m ≤ r' ^ b m :=
  by
  suffices : (k' κ' m : ℝ) / 2 ^ N₂ r r' BD κ' m ≤ r' ^ (b r r' BD κ' m : ℝ)
  exact_mod_cast this
  apply Helper.n₂_spec ‹Fact (0 < r')›.out <;> norm_cast <;> apply Fact.out

/-- `N₂ = N₂ κ' r r' m` is defined in such a way that `r' ^ b < 2 * k' m / 2 ^ N₂`,
where `b = b κ' r r' m`. -/
theorem n₂_spec_of_pos' (h : 0 < N₂ m) : r' ^ b m < 2 * k' m / 2 ^ N₂ m :=
  by
  suffices : (r' : ℝ) ^ (b r r' BD κ' m : ℝ) < 2 * k' κ' m / 2 ^ N₂ r r' BD κ' m
  exact_mod_cast this
  apply Helper.n₂_spec_of_pos' h
  · norm_cast
    exact ‹Fact (0 < r')›.out
  apply NNReal.coe_nonneg

theorem k'_eq_one_of_n₂_spec_eq_zero (h : N₂ m = 0) : k' m = 1 :=
  by
  refine' le_antisymm _ (universal_constants.one_le_k' _ _).1
  obtain F := N₂_spec r r' BD κ' m
  rw [h, pow_zero, div_one] at F 
  refine' F.trans (pow_le_one (b r r' BD κ' m) (le_of_lt _) _) <;>
    · apply Fact.out _
      assumption

/-- `N m = 2 ^ N₂ m` is the smallest `N` that satisfies `(k' m) / N ≤ r' ^ (b m)` -/
def n : ℕ :=
  2 ^ N₂ m

instance n_pos : Fact (0 < N m) :=
  ⟨pow_pos zero_lt_two _⟩

/-- For all `m` we have `k' m ≤ N m = 2 ^ N₂ m`. -/
instance k'_le_two_pow_N : Fact (k' m ≤ 2 ^ N₂ m)
    where out := by
    rw [← mul_one ((2 : ℝ≥0) ^ _)]
    obtain F := N₂_spec r r' BD κ' m
    rw [NNReal.div_le_iff (pow_pos zero_lt_two _).ne', mul_comm] at F 
    refine' F.trans (mul_le_mul rfl.le _ _ _)
    · refine' pow_le_one _ (zero_le r') _
      apply Fact.out _
      assumption
    repeat' exact pow_nonneg (zero_le _) _

/-- For all `m` we have `r ^ (b m) * (N m) ≤ 2 * k' m * (r / r') ^ (b m)`. -/
theorem r_pow_b_hMul_n_le : r ^ b m * N m ≤ 2 * k' m * (r / r') ^ b m :=
  by
  rw [mul_comm _ (_ ^ _), N, div_pow, Nat.cast_pow, Nat.cast_bit0, Nat.cast_one, div_eq_mul_one_div,
    mul_assoc, div_mul_comm, mul_one]
  refine' mul_le_mul_left' _ _
  rw [NNReal.le_div_iff_mul_le, mul_comm, ← NNReal.le_div_iff_mul_le]
  · by_cases N0 : N₂ r r' BD κ' m = 0
    · rw [k'_eq_one_of_N₂_spec_eq_zero _ _ BD _ _ N0, mul_one, N0, pow_zero, div_one]
      refine' le_trans (pow_le_one _ (NNReal.coe_nonneg _) _) one_le_two
      apply Fact.out _
      assumption
    · exact le_of_lt (N₂_spec_of_pos' _ _ BD _ _ (zero_lt_iff.mpr N0))
  · exact pow_ne_zero _ two_ne_zero
  · exact pow_ne_zero _ (ne_of_gt (Fact.out _))

/-- For all `m` we have `r ^ b m * N m ≤ ε m`. -/
theorem r_pow_b_le_ε : r ^ b m * N m ≤ ε m :=
  (r_pow_b_mul_N_le _).trans (b_spec _)

/-- For all `m` we have `k' m * (2 ^ N₂ m)⁻¹ ≤ r' ^ b m`. -/
theorem n₂_spec' : k' m * (2 ^ N₂ m)⁻¹ ≤ r' ^ b m := by rw [inv_eq_one_div, mul_one_div];
  exact N₂_spec r r' BD κ' m

/-- `H BD κ' r r' m` is the universal bound on the norm of the `N₂`th Breen--Deligne homotopy
in the first `m` degrees. Here `N₂ = N₂ κ' r r' m`. -/
def h : ℕ :=
  H' m (N₂ m)

theorem one_le_h : 1 ≤ H m :=
  le_max_left _ _

instance h_pos : Fact (0 < H m) :=
  ⟨zero_lt_one.trans_le <| one_le_H _⟩

instance h_pos' : Fact ((0 : ℝ≥0) < H m) := by norm_cast; infer_instance

theorem boundBy_h {q : ℕ} (h : q ≤ m) :
    ((BD.data.homotopyMul BD.Homotopy (N₂ m)).hom q (q + 1)).BoundBy (H m) :=
  by
  rw [H, H', universal_map.bound_by, le_max_iff]
  right
  refine'
    @le_sup _ _ _ _ (range <| m + 1)
      (fun q => ((BD.data.homotopy_mul BD.homotopy (N₂ r r' BD κ' m)).hom q (q + 1)).bound) _ _
  rwa [mem_range, Nat.lt_succ_iff]

/- warning: thm95.universal_constants.K clashes with thm95.universal_constants.k -> Thm95.UniversalConstants.k
Case conversion may be inaccurate. Consider using '#align thm95.universal_constants.K Thm95.UniversalConstants.kₓ'. -/
/-- `K m` is defined to be `2 * K₀ m (K₁ m) * H m`,
where `K₀ m (K₁ m)` is one of the constants used in the proof of `normed_spectral`. -/
def k : ℝ≥0 :=
  2 * NormedSpectral.k₀ m (K₁ m) * H m

/- warning: thm95.universal_constants.one_le_K clashes with thm95.universal_constants.one_le_k -> Thm95.UniversalConstants.one_le_k
Case conversion may be inaccurate. Consider using '#align thm95.universal_constants.one_le_K Thm95.UniversalConstants.one_le_kₓ'. -/
instance one_le_k : Fact (1 ≤ K m) :=
  Fact.mk <|
    calc
      1 = 1 * 1 * 1 := by simp
      _ ≤ 2 * NormedSpectral.k₀ m (K₁ m) * H m :=
        by
        refine' mul_le_mul' (mul_le_mul' one_le_two <| (normed_spectral.one_le_K₀ _ _).1) _
        norm_cast
        apply one_le_H

/- warning: thm95.universal_constants.K_le_K₁ clashes with thm95.universal_constants.k_le_k₁ -> Thm95.UniversalConstants.k_le_k₁
Case conversion may be inaccurate. Consider using '#align thm95.universal_constants.K_le_K₁ Thm95.UniversalConstants.k_le_k₁ₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.unfreeze_local_instances -/
/-- For all positive `m`, we have `K (m - 1) ≤ K₁ m`. -/
instance k_le_k₁ [Fact (0 < m)] : Fact (K (m - 1) ≤ K₁ m) :=
  ⟨by
    run_tac
      tactic.unfreeze_local_instances
    have hm : 0 < m := Fact.out _
    cases m
    · exfalso; exact Nat.lt_asymm hm hm
    simp only [K₁, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, le_max_iff]
    right
    apply le_refl⟩

theorem k₁_spec : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2) ^ 2 : ℝ≥0) ≤ K₁ m :=
  by
  cases m
  · norm_num [K₁]
  · simp only [K₁, le_max_iff]
    left
    apply le_refl

section

open SimplexCategory

def c₀Aux (m : ℕ) (Λ : PolyhedralLatticeCat) : ℝ≥0 :=
  N m * Lem98.d Λ (N m) / (k₁_sqrt m - 1) / r' / (range <| m + 1).inf' ⟨0, by simp⟩ κ

-- define this such that the lemmas below hold
noncomputable def c₀ : ℕ → PolyhedralLatticeCat → ℝ≥0
  | 0, Λ => c₀_aux 0 Λ
  | m + 1, Λ =>
    max (c₀_aux (m + 1) Λ)
      (max (c₀ m Λ)
        (max (c₀ m ((Λ.cosimplicial (N (m + 1))).obj (mk 0)))
          ((range (m + 1)).sup fun i => c₀ m ((Λ.cosimplicial (N (m + 1))).obj (mk (i + 1))))))

theorem c₀_mono : Fact (c₀ (m - 1) Λ ≤ c₀ m Λ) :=
  by
  fconstructor
  cases m
  · apply le_refl
  · dsimp [c₀]
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_left _ _)
    simp

theorem c₀_pred_le (hm : 0 < m) : Fact (c₀ (m - 1) ((Λ.cosimplicial (N m)).obj (mk 0)) ≤ c₀ m Λ) :=
  by
  fconstructor
  cases m
  · cases hm
  · dsimp [c₀]
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_left _ _)
    simp

theorem c₀_pred_le_of_le (i : ℕ) (hi : i + 2 ≤ m + 1) :
    Fact (c₀ (m - 1) ((Λ.cosimplicial (N m)).obj (mk (i + 1))) ≤ c₀ m Λ) :=
  by
  fconstructor
  cases m
  · simpa using nat.succ_le_succ_iff.mp hi
  · dsimp [c₀]
    replace hi : i ∈ range (m + 1) :=
      mem_range.mpr (nat.succ_le_iff.mp (nat.succ_le_succ_iff.mp hi))
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.succ_eq_add_one]
    exact le_sup hi

theorem fix_this_in_mathlib : NNReal.semilatticeInf = Lattice.toSemilatticeInf ℝ≥0 := by
  apply SemilatticeInf.ext; intros; rfl

theorem c₀_spec [BD.data.VerySuitable r r' κ] (j : ℕ) (hj : j ≤ m) :
    Lem98.d Λ (N m) ≤ (k₁_sqrt m - 1) * (r' * (κ j * c₀ m Λ)) / N m :=
  by
  have w := BD.data.pos κ
  rw [NNReal.le_div_iff', ← NNReal.div_le_iff', ← NNReal.div_le_iff', ← NNReal.div_le_iff']
  rotate_left
  · exact (w _).ne'
  · apply ne_of_gt; exact Fact.out _
  ·
    rw [← pos_iff_ne_zero, ← add_lt_add_iff_right (1 : ℝ≥0), tsub_add_cancel_of_le, zero_add] <;>
      apply Fact.out
  · apply ne_of_gt; exact Fact.out _
  cases m; · cases hj; apply le_refl
  refine' le_trans _ (le_max_left _ _)
  dsimp [c₀_aux]
  apply NNReal.div_le_div_left_of
  · rw [fix_this_in_mathlib, lt_inf'_iff]; intro b mem; exact w b
  · refine' inf'_le _ _; exact mem_range_succ_iff.mpr hj

end

end UniversalConstants

end Thm95

end

