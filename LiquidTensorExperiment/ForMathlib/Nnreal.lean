import Mathlib.Data.Real.NNReal
import Mathlib.Analysis.MeanInequalitiesPow
import LiquidTensorExperiment.ForMathlib.Ennreal

#align_import for_mathlib.nnreal

open scoped NNReal

-- There doesn't seem to be a real analogue of this one, but probably should be?
theorem NNReal.div_le_div_left_of {a b c : ℝ≥0} (w : 0 < c) (h : c ≤ b) : a / b ≤ a / c :=
  by
  rcases a with ⟨a, a_pos⟩
  rcases b with ⟨b, b_pos⟩
  rcases c with ⟨c, c_pos⟩
  change a / b ≤ a / c
  change 0 < c at w 
  change c ≤ b at h 
  by_cases p : 0 < a
  · rw [div_le_div_left p (lt_of_lt_of_le w h) w]
    exact h
  · have q : a = 0; linarith
    subst q
    simp

attribute [norm_cast] NNReal.coe_zpow

open scoped ENNReal BigOperators

/-- sum of row sums equals sum of column sums -/
theorem NNReal.summable_symm {α β : Type _} (F : α → β → ℝ≥0)
    (h_rows : ∀ n, Summable fun k => F n k) (h_cols : ∀ k, Summable fun n => F n k)
    (h_col_row : Summable fun k => ∑' n, F n k) : Summable fun n => ∑' k, F n k :=
  by
  cases' h_col_row with a ha
  use a
  rw [← ENNReal.hasSum_coe]
  convert_to HasSum (fun n => ∑' k, (F n k : ℝ≥0∞)) a
  · ext1 n
    exact ENNReal.coe_tsum (h_rows n)
  · rw [ENNReal.hasSum_comm]
    rw [← ENNReal.hasSum_coe] at ha 
    convert ha
    ext1 k
    exact (ENNReal.coe_tsum (h_cols k)).symm

open NNReal

theorem NNReal.summable_of_comp_injective {α β : Type _} {f : α → ℝ≥0} {i : β → α}
    (hi : Function.Injective i) (hi' : ∀ a, a ∉ Set.range i → f a = 0) (hfi : Summable (f ∘ i)) :
    Summable f := by
  rw [← summable_coe] at hfi ⊢
  let e : β ≃ ({x : α | x ∈ Set.range i} : Set α) :=
    { toFun := fun b => ⟨i b, b, rfl⟩
      invFun := fun x => x.2.some
      left_inv := by intro b; simp; apply hi; exact Exists.choose_spec (⟨b, rfl⟩ : ∃ y, i y = i b)
      right_inv := by rintro ⟨x, b, rfl⟩; simp;
        exact Exists.choose_spec (⟨b, rfl⟩ : ∃ y, i y = i b) }
  have this2 : Summable ((fun x : { x : α // x ∈ Set.range i } => (f x.1 : ℝ)) ∘ ⇑e : β → ℝ) :=
    by
    convert (summable_congr _).1 hfi
    intro b; rfl
  rw [e.summable_iff] at this2 
  change Summable ((fun a => (f a : ℝ)) ∘ (coe : { x // x ∈ Set.range i } → α)) at this2 
  rw [← this2.summable_compl_iff]
  convert summable_zero
  ext1 ⟨x, hx⟩
  simp [hi' x hx]

theorem NNReal.summable_subtype {β : Type _} {f : β → ℝ≥0} (hf : Summable f) (s : Set β) :
    Summable (f ∘ (coe : s → β)) := by
  rw [← summable_coe] at hf ⊢
  exact hf.subtype s

theorem NNReal.hMul_le_hMul_right {a b : ℝ≥0} (h : a ≤ b) (c : ℝ≥0) : a * c ≤ b * c :=
  by
  suffices (a : ℝ) * c ≤ b * c by assumption_mod_cast
  apply mul_le_mul_of_nonneg_right (by assumption_mod_cast)
  apply zero_le'

theorem NNReal.hMul_le_hMul_left {a b : ℝ≥0} (h : a ≤ b) (c : ℝ≥0) : c * a ≤ c * b := by
  simpa [mul_comm] using NNReal.hMul_le_hMul_right h c

theorem NNReal.rpow_sum_le_sum_rpow {ι : Type _} (s : Finset ι) {p : ℝ} (a : ι → ℝ≥0)
    (hp_pos : 0 < p) (hp1 : p ≤ 1) : (∑ i in s, a i) ^ p ≤ ∑ i in s, a i ^ p := by
  classical
  induction' s using Finset.induction_on with i s his IH
  · simp only [NNReal.zero_rpow hp_pos.ne', Finset.sum_empty, le_zero_iff]
  · simp only [his, Finset.sum_insert, not_false_iff]
    exact (NNReal.rpow_add_le_add_rpow _ _ hp_pos.le hp1).trans (add_le_add le_rfl IH)

theorem NNReal.le_self_rpow {a : ℝ≥0} {m : ℝ} (ha : 1 ≤ a) (hm : 1 ≤ m) : a ≤ a ^ m :=
  by
  suffices : a ^ (1 : ℝ) ≤ a ^ m
  simpa
  exact rpow_le_rpow_of_exponent_le ha hm

theorem NNReal.le_self_rpow' {a : ℝ≥0} {m : ℝ} (ha : a ≤ 1) (hm : m ≤ 1) : a ≤ a ^ m :=
  by
  obtain rfl | ⟨u, rfl⟩ := GroupWithZero.eq_zero_or_unit a; apply zero_le
  -- a=0 special case
  suffices : (u : ℝ≥0) ^ (1 : ℝ) ≤ u ^ m
  simpa
  exact rpow_le_rpow_of_exponent_ge (by simp) ha hm

-- no need to prove for nnreal because need positive (not non-negative)
theorem Real.injective_log {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (h : Real.log r = Real.log s) :
    r = s := by
  apply_fun Real.exp at h 
  rwa [Real.exp_log hr, Real.exp_log hs] at h 

theorem NNReal.pow_log_div_log_self {r : ℝ} {s : ℝ} (hr : 0 < r) (hs : 0 < s) (hs' : s ≠ 1) :
    s ^ (Real.log r / Real.log s) = r :=
  by
  apply Real.injective_log (Real.rpow_pos_of_pos hs _) hr
  rw [Real.log_rpow hs]
  rw [← eq_div_iff]
  apply mt (fun h => _) hs'
  rw [Real.log_eq_zero] at h 
  rcases h with (h | h | h) <;> linarith

theorem NNReal.div_inv {a b : ℝ≥0} : a / b⁻¹ = a * b :=
  by
  rcases eq_or_ne b 0 with (rfl | hb)
  · rw [inv_zero, div_zero, MulZeroClass.mul_zero]
  rw [div_eq_iff (inv_ne_zero hb), mul_assoc, mul_inv_cancel hb, mul_one]

theorem NNReal.tsum_le_tsum {X : Type _} {f g : X → ℝ≥0} (hle : ∀ x, f x ≤ g x)
    (hsummable : Summable g) : ∑' x, f x ≤ ∑' x, g x :=
  tsum_le_tsum hle (summable_of_le hle hsummable) hsummable

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem NNReal.summable_iff_summable_nnnorm {X : Type _} {f : X → ℝ} :
    Summable f ↔ Summable fun x => «expr∥ ∥₊» (f x) :=
  by
  rw [← summable_norm_iff]
  rw [← summable_coe]
  congr

theorem NNReal.le_zero_iff {a : ℝ≥0} : a ≤ 0 ↔ a = 0 :=
  le_bot_iff

theorem NNReal.sub_pos {a b : ℝ≥0} : 0 < a - b ↔ b < a :=
  by
  rw [← not_iff_not]
  push_neg
  rw [NNReal.le_zero_iff]
  apply tsub_eq_zero_iff_le

theorem NNReal.inv_lt_of_inv_lt {a b : ℝ≥0} (ha : a ≠ 0) (hab : a⁻¹ < b) : b⁻¹ < a :=
  by
  suffices : (b : ℝ)⁻¹ < a
  exact_mod_cast this
  apply inv_lt_of_inv_lt
  · norm_cast
    rwa [zero_lt_iff]
  · exact_mod_cast hab

