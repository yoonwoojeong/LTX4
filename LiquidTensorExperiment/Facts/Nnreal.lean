import Mathlib.Data.Real.NNReal

#align_import facts.nnreal

open scoped NNReal

namespace NNReal

variable (r r' k c c₁ c₂ c₃ : ℝ≥0)

instance fact_le_of_lt [h : Fact (c₁ < c₂)] : Fact (c₁ ≤ c₂) :=
  ⟨h.1.le⟩

instance fact_pos_of_one_le [hk : Fact (1 ≤ c)] : Fact (0 < c) :=
  ⟨lt_of_lt_of_le zero_lt_one hk.1⟩

instance fact_hMul_pos [h1 : Fact (0 < c₁)] [h2 : Fact (0 < c₂)] : Fact (0 < c₁ * c₂) :=
  ⟨mul_pos h1.out h2.out⟩

instance fact_le_hMul_of_one_le_left [hk : Fact (1 ≤ k)] [hc : Fact (c₁ ≤ c₂)] :
    Fact (c₁ ≤ k * c₂) :=
  ⟨calc
      c₁ = 1 * c₁ := (one_mul _).symm
      _ ≤ k * c₂ := mul_le_mul' hk.1 hc.1⟩

instance fact_le_hMul_of_one_le_right [hc : Fact (c₁ ≤ c₂)] [hk : Fact (1 ≤ k)] :
    Fact (c₁ ≤ c₂ * k) :=
  ⟨calc
      c₁ = c₁ * 1 := (mul_one _).symm
      _ ≤ c₂ * k := mul_le_mul' hc.1 hk.1⟩

instance fact_hMul_le_of_le_one_left [hk : Fact (k ≤ 1)] [hc : Fact (c₁ ≤ c₂)] :
    Fact (k * c₁ ≤ c₂) :=
  ⟨calc
      k * c₁ ≤ 1 * c₂ := mul_le_mul' hk.1 hc.1
      _ = c₂ := one_mul _⟩

instance fact_hMul_le_of_le_one_right [hk : Fact (k ≤ 1)] [hc : Fact (c₁ ≤ c₂)] :
    Fact (c₁ * k ≤ c₂) :=
  ⟨calc
      c₁ * k ≤ c₂ * 1 := mul_le_mul' hc.1 hk.1
      _ = c₂ := mul_one _⟩

instance fact_one_le_add_one : Fact (1 ≤ k + 1) :=
  ⟨self_le_add_left 1 k⟩

instance fact_le_refl : Fact (c ≤ c) :=
  ⟨le_rfl⟩

-- Porting note: was an `instance` in Lean 3; Lean 4 cannot find a synthesization order
-- (the middle term appears only in the hypotheses), so it is a plain theorem.
theorem fact_le_subst_right [Fact (c₁ ≤ c₂)] [h : Fact (c₂ = c₃)] : Fact (c₁ ≤ c₃) := by
  rwa [← h.1]

-- Porting note: was an `instance` in Lean 3; Lean 4 cannot find a synthesization order
-- (the middle term appears only in the hypotheses), so it is a plain theorem.
theorem fact_le_subst_right' [Fact (c₁ ≤ c₂)] [h : Fact (c₃ = c₂)] : Fact (c₁ ≤ c₃) := by
  rwa [← h.1.symm]

-- Porting note: was an `instance` in Lean 3; Lean 4 cannot find a synthesization order
-- (the middle term appears only in the hypotheses), so it is a plain theorem.
theorem fact_le_subst_left [Fact (c₁ ≤ c₂)] [h : Fact (c₁ = c₃)] : Fact (c₃ ≤ c₂) := by rwa [← h.1]

-- Porting note: was an `instance` in Lean 3; Lean 4 cannot find a synthesization order
-- (the middle term appears only in the hypotheses), so it is a plain theorem.
theorem fact_le_subst_left' [Fact (c₁ ≤ c₂)] [h : Fact (c₃ = c₁)] : Fact (c₃ ≤ c₂) := by
  rwa [← h.1.symm]

instance fact_inv_hMul_le [h : Fact (0 < r')] : Fact (r'⁻¹ * (r' * c) ≤ c) :=
  ⟨le_of_eq <| inv_mul_cancel_left₀ (ne_of_gt h.1) _⟩

instance fact_hMul_le_hMul_left [h : Fact (c₁ ≤ c₂)] : Fact (r' * c₁ ≤ r' * c₂) :=
  ⟨mul_le_mul' le_rfl h.1⟩

instance fact_hMul_le_hMul_right [h : Fact (c₁ ≤ c₂)] : Fact (c₁ * r' ≤ c₂ * r') :=
  ⟨mul_le_mul' h.1 le_rfl⟩

instance fact_le_inv_hMul_self [h1 : Fact (0 < r')] [h2 : Fact (r' ≤ 1)] : Fact (c ≤ r'⁻¹ * c) :=
  by
  constructor
  rw [mul_comm]
  apply le_mul_inv_of_mul_le (ne_of_gt h1.1)
  nth_rw 2 [← mul_one c]
  exact mul_le_mul (le_of_eq rfl) h2.1 (le_of_lt h1.1) zero_le'

instance fact_le_max_left (a b c : ℝ≥0) [h : Fact (a ≤ b)] : Fact (a ≤ max b c) :=
  ⟨h.1.trans <| le_max_left _ _⟩

instance fact_one_le_hMul_self (a : ℝ≥0) [h : Fact (1 ≤ a)] : Fact (1 ≤ a * a) :=
  ⟨calc
      (1 : ℝ≥0) = 1 * 1 := (mul_one 1).symm
      _ ≤ a * a := mul_le_mul' h.1 h.1⟩

instance one_le_add {a b : ℝ≥0} [ha : Fact (1 ≤ a)] : Fact (1 ≤ a + b) :=
  ⟨le_trans ha.1 <| by simp⟩

instance one_le_add' {a b : ℝ≥0} [hb : Fact (1 ≤ b)] : Fact (1 ≤ a + b) :=
  ⟨le_trans hb.1 <| by simp⟩

instance fact_one_le_pow {n : ℕ} {a : ℝ≥0} [h : Fact (1 ≤ a)] : Fact (1 ≤ a ^ n) :=
  by
  cases n
  · simpa only [pow_zero] using NNReal.fact_le_refl _
  · rwa [@one_le_pow_iff _ _ _ NNReal.covariant_mul]; apply Nat.succ_ne_zero

instance fact_pow_le_one {n : ℕ} {a : ℝ≥0} [h : Fact (a ≤ 1)] : Fact (a ^ n ≤ 1) :=
  by
  cases n
  · simpa only [pow_zero] using NNReal.fact_le_refl _
  · rwa [@pow_le_one_iff _ _ _ NNReal.covariant_mul]; apply Nat.succ_ne_zero

theorem fact_le_pow_hMul_of_le_pow_succ_hMul {n : ℕ} (r : ℝ≥0) [Fact (r ≤ 1)]
    [h : Fact (c₂ ≤ r ^ (n + 1) * c₁)] : Fact (c₂ ≤ r ^ n * c₁) :=
  by
  refine' ⟨h.1.trans _⟩
  rw [pow_succ, mul_assoc]
  apply Fact.out

instance fact_le_hMul_add : Fact (c * c₁ + c * c₂ ≤ c * (c₁ + c₂)) := by
  rw [mul_add]; exact NNReal.fact_le_refl _

instance fact_nat_cast_pos (N : ℕ) [hN : Fact (0 < N)] : Fact (0 < (N : ℝ≥0)) :=
  ⟨Nat.cast_pos.mpr hN.1⟩

instance fact_nat_cast_inv_le_one (N : ℕ) : Fact ((N : ℝ≥0)⁻¹ ≤ 1) :=
  by
  by_cases hN : N = 0
  · subst hN; simp only [Nat.cast_zero, inv_zero, zero_le']; exact ⟨trivial⟩
  · rw [inv_le, mul_one]; swap; · exact_mod_cast hN
    norm_cast
    rw [Nat.add_one_le_iff]
    exact ⟨Nat.pos_of_ne_zero hN⟩

instance fact_inv_le_one [H : Fact (1 ≤ c)] : Fact (c⁻¹ ≤ 1) :=
  by
  by_cases hc : c = 0
  · rw [hc] at H ; exact (not_le_of_lt zero_lt_one H.1).elim
  rwa [inv_le hc, mul_one]

instance fact_one_le_two : Fact ((1 : ℝ≥0) ≤ 2) :=
  ⟨one_le_two⟩

instance fact_two_pow_inv_le_two_pow_inv (N : ℕ) : Fact ((2 ^ N : ℝ≥0)⁻¹ ≤ ((2 ^ N : ℕ) : ℝ≥0)⁻¹) :=
  ⟨le_of_eq <| by norm_cast⟩

instance fact_two_pow_inv_le_one (N : ℕ) : Fact ((2 ^ N : ℝ≥0)⁻¹ ≤ 1) :=
  ⟨le_trans (NNReal.fact_two_pow_inv_le_two_pow_inv N).1 <| Fact.out⟩

end NNReal

#lint

