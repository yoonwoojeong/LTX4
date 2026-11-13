import Mathlib.Data.Rat.NNRat

#align_import for_mathlib.nnrat

/-!
# Nonnegative rationals

## TODO

* Rename `nnrat.to_nnrat_mono` to `rat.to_nnrat_mono`.
* Coercion to `nnreal`.
-/


open scoped BigOperators NNRat

namespace NNRat

deriving instance CanonicallyLinearOrderedAddCommMonoid for NNRat

theorem bot_eq_zero : (⊥ : ℚ≥0) = 0 :=
  rfl

theorem hMul_sup (a b c : ℚ≥0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  by
  cases' le_total b c with h h
  · simp [sup_eq_max, max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (zero_le a))]
  · simp [sup_eq_max, max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (zero_le a))]

theorem hMul_finset_sup {α} {f : α → ℚ≥0} {s : Finset α} (r : ℚ≥0) :
    r * s.sup f = s.sup fun a => r * f a := by
  classical
  refine' s.induction_on _ _
  · simp [bot_eq_zero]
  · intro a s has ih; simp [has, ih, mul_sup]

section Inv

theorem sum_div {ι} (s : Finset ι) (f : ι → ℚ≥0) (b : ℚ≥0) :
    (∑ i in s, f i) / b = ∑ i in s, f i / b := by simp only [div_eq_mul_inv, Finset.sum_mul]

@[simp]
theorem inv_le {r p : ℚ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_left h.bot_lt, mul_inv_cancel h]

theorem inv_le_of_le_hMul {r p : ℚ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases r = 0 <;> simp [*, inv_le]

@[simp]
theorem le_inv_iff_hMul_le {r p : ℚ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_left h.bot_lt, mul_inv_cancel h, mul_comm]

@[simp]
theorem lt_inv_iff_hMul_lt {r p : ℚ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_left h.bot_lt, mul_inv_cancel h, mul_comm]

theorem hMul_le_iff_le_inv {a b r : ℚ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
  by
  have : 0 < r := lt_of_le_of_ne (zero_le r) hr.symm
  rw [← mul_le_mul_left (inv_pos.2 this), ← mul_assoc, inv_mul_cancel hr, one_mul]

theorem lt_div_iff {a b r : ℚ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff₀ hr)

theorem hMul_lt_of_lt_div {a b r : ℚ≥0} (h : a < b / r) : a * r < b :=
  (lt_div_iff <| by rintro rfl; simpa using h).1 h

theorem le_of_forall_lt_one_hMul_le {x y : ℚ≥0} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense fun a ha =>
    by
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha)
    have hx' : x⁻¹ ≠ 0 := by rwa [(· ≠ ·), inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x ≤ y := h _ this
    rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this 

theorem half_lt_self {a : ℚ≥0} (h : a ≠ 0) : a / 2 < a :=
  half_lt_self h.bot_lt

theorem two_inv_lt_one : (2⁻¹ : ℚ≥0) < 1 := by simpa using half_lt_self zero_ne_one.symm

theorem div_lt_iff {a b c : ℚ≥0} (hc : c ≠ 0) : b / c < a ↔ b < a * c :=
  lt_iff_lt_of_le_iff_le <| le_div_iff₀ hc

theorem div_lt_one_of_lt {a b : ℚ≥0} (h : a < b) : a / b < 1 :=
  by
  rwa [div_lt_iff, one_mul]
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)

end Inv

@[simp]
theorem abs_eq (x : ℚ≥0) : abs (x : ℚ) = x :=
  abs_of_nonneg x.property

end NNRat

