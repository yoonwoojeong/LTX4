import LiquidTensorExperiment.Facts.Nnreal

#align_import thm95.constants.spectral_constants

/-!
# Explicit formulas for the constants used in Proposition 9.6 of Analytic.pdf
-/


open scoped NNReal

namespace SystemOfDoubleComplexes

namespace NormedSpectral

/-- `ε m K` is a sequence of nonnegative real constants,
depending on a natural number `m` and a nonnegative real number `K`.
It is defined recursively, via `ε 0 K = (2 * K)⁻¹` and `ε (m+1) K = ε m (K^3 + K)`. -/
noncomputable def ε : ∀ (m : ℕ) (K : ℝ≥0), ℝ≥0
  | 0, K => (2 * K)⁻¹
  | m + 1, K => ε m (K * (K * K + 1))

/-- The number `ε m K` is always positive. -/
theorem ε_pos : ∀ (m K) [Fact (0 < K)], 0 < ε m K
  | 0, K, hK => nnreal.inv_pos.mpr (mul_pos zero_lt_two hK.out)
  | m + 1, K, hK => by dsimp [ε]; exact ε_pos m _

/-- `k₀ m k` is a sequence of nonnegative real constants,
depending on a natural number `m` and a nonnegative real number `k`.
It is defined recursively, via `k₀ 0 k = k` and `k₀ (m+1) k = k₀ m (k^3)`. -/
def k₀ : ∀ (m : ℕ) (k : ℝ≥0), ℝ≥0
  | 0, k => k
  | m + 1, k => k₀ m (k * k * k)

/-- We have `1 ≤ k₀ m k` whenever `1 ≤ k` holds. -/
instance one_le_k₀ : ∀ (m k) [Fact (1 ≤ k)], Fact (1 ≤ k₀ m k)
  | 0, k, hk => hk
  | m + 1, k, hk => by dsimp [k₀]; exact one_le_k₀ m _

/- warning: system_of_double_complexes.normed_spectral.K₀ clashes with system_of_double_complexes.normed_spectral.k₀ -> SystemOfDoubleComplexes.NormedSpectral.k₀
Case conversion may be inaccurate. Consider using '#align system_of_double_complexes.normed_spectral.K₀ SystemOfDoubleComplexes.NormedSpectral.k₀ₓ'. -/
/-- `K₀ m k` is a sequence of nonnegative real constants,
depending on a natural number `m` and a nonnegative real number `K`.
It is defined recursively, via `K₀ 0 K = K` and `K₀ (m+1) K = K₀ m (K^3 + K)`. -/
def k₀ : ∀ (m : ℕ) (K : ℝ≥0), ℝ≥0
  | 0, K => K
  | m + 1, K => K₀ m (K * (K * K + 1))

/- warning: system_of_double_complexes.normed_spectral.one_le_K₀ clashes with system_of_double_complexes.normed_spectral.one_le_k₀ -> SystemOfDoubleComplexes.NormedSpectral.one_le_k₀
Case conversion may be inaccurate. Consider using '#align system_of_double_complexes.normed_spectral.one_le_K₀ SystemOfDoubleComplexes.NormedSpectral.one_le_k₀ₓ'. -/
/-- We have `1 ≤ K₀ m K` whenever `1 ≤ K` holds. -/
instance one_le_k₀ : ∀ (m K) [Fact (1 ≤ K)], Fact (1 ≤ k₀ m K)
  | 0, K, hK => hK
  | m + 1, K, hK => by dsimp [K₀]; exact one_le_K₀ m _

end NormedSpectral

end SystemOfDoubleComplexes

