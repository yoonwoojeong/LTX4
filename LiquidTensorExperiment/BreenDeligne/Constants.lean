import LiquidTensorExperiment.BreenDeligne.Homotopy

#align_import breen_deligne.constants

noncomputable section

open scoped NNReal BigOperators

namespace BreenDeligne

namespace Data

variable (BD : Data) (r r' : ℝ≥0)

theorem b_exists [hr : Fact (r < 1)] (x : ℝ≥0) [Fact (0 < x)] : ∃ b : ℕ, r ^ b ≤ x⁻¹ :=
  by
  suffices ∃ b : ℕ, (r ^ b : ℝ) < x⁻¹ by
    rcases this with ⟨b, hb⟩
    refine' ⟨b, le_of_lt _⟩
    rwa [← NNReal.coe_lt_coe, NNReal.coe_pow, NNReal.coe_inv]
  refine' exists_pow_lt_of_lt_one _ hr.out
  simp only [NNReal.coe_pos, inv_pos]
  exact ‹Fact (0 < x)›.out

/-- The smallest `b` such that `r ^ b ≤ x⁻¹`.  -/
def b [hr : Fact (r < 1)] (x : ℝ≥0) [Fact (0 < x)] :=
  Nat.find (b_exists r x)

/-- Example of a very suitable sequence of constants for given Breen--Deligne data. -/
noncomputable def κ (BD : Data) (r r' : ℝ≥0) [hr : Fact (r < 1)] : ℕ → ℝ≥0
  | 0 => 1
  | n + 1 => (max 1 (BD.d (n + 1) n).factor)⁻¹ * (r' ^ (b r <| max 1 (BD.d (n + 1) n).bound) * κ n)

instance c__pos [hr : Fact (r < 1)] [hr' : Fact (0 < r')] : ∀ n : ℕ, Fact (0 < κ BD r r' n)
  | 0 => ⟨zero_lt_one⟩
  | n + 1 => by
    dsimp [κ]
    refine' ⟨mul_pos (nnreal.inv_pos.mpr _) (mul_pos (pow_pos hr'.1 _) <| (c__pos _).1)⟩
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

instance cVerySuitable [hr : Fact (r < 1)] [hr' : Fact (0 < r')] :
    BD.VerySuitable r r' (BD.κ r r') :=
  VerySuitable.ofSucc _ _ _ _
    (by
      intro n
      let N := max 1 (BD.d (n + 1) n).bound
      let b : ℕ := b r (max 1 (BD.d (n + 1) n).bound)
      let c : ℝ≥0 := max 1 (BD.d (n + 1) n).factor
      refine' ⟨N, b, c * BD.κ r r' (n + 1), le_max_right _ _, _, _, _⟩
      · intro g hg i
        exact mul_le_mul' ((universal_map.le_factor _ _ hg _).trans <| le_max_right _ _) le_rfl
      · rw [mul_comm, NNReal.mul_le_iff_le_inv, mul_one]
        convert Nat.find_spec (b_exists r (max 1 (BD.d (n + 1) n).bound))
        · simp only [Nat.cast_max, Nat.cast_one]
        · apply ne_of_gt
          simp only [lt_max_iff, Nat.cast_max, Nat.cast_one, Nat.cast_pos, zero_lt_one, true_or_iff]
      · by_cases hc : c = 0
        · simp only [hc, MulZeroClass.zero_mul, zero_le']
        rw [NNReal.mul_le_iff_le_inv hc]
        dsimp [κ]; exact le_rfl)
    fun i => (Data.c__pos _ _ _ i).1

end Data

namespace Package

variable (BD : Package) (r r' : ℝ≥0)

/-- Example of an adept sequence of constants for
a given Breen--Deligne package `BD` and constants `κ`. -/
def κ' (BD : Package) (κ : ℕ → ℝ≥0) : ℕ → ℝ≥0
  | 0 => 1
  | n + 1 => (BD.Homotopy.Hom n (n + 1)).factor * rescaleConstants κ 2 n * (κ (n + 1))⁻¹

instance κ'Adept (κ : ℕ → ℝ≥0) [∀ i, Fact (0 < κ i)] : Package.Adept BD κ (κ' BD κ)
    where htpy_suitable' := by
    intro n
    apply universal_map.suitable_of_factor_le
    dsimp [κ']
    rw [inv_mul_cancel_right₀, mul_inv_cancel_right₀]
    · dsimp [rescaleConstants]; refine' mul_ne_zero (ne_of_gt <| Fact.out _) _; norm_num
    · exact ne_of_gt (Fact.out _)

end Package

end BreenDeligne

#lint

