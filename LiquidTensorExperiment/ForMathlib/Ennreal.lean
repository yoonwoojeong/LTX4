import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.ENNReal

#align_import for_mathlib.ennreal

open scoped ENNReal

open scoped NNReal

-- don't need it but maybe useful?
theorem ENNReal.summable_of_coe_sum_eq {X : Type _} (f g : X → ℝ≥0)
    (h : ∑' x, (f x : ℝ≥0∞) = ∑' x, (g x : ℝ≥0∞)) : Summable f ↔ Summable g := by
  rw [← ENNReal.tsum_coe_ne_top_iff_summable, h, ENNReal.tsum_coe_ne_top_iff_summable]

theorem ENNReal.hasSum_comm {α β : Type _} (F : α → β → ℝ≥0∞) (s : ℝ≥0∞) :
    HasSum (fun n => ∑' k, F n k) s ↔ HasSum (fun k => ∑' n, F n k) s := by
  rw [Summable.hasSum_iff ENNReal.summable, Summable.hasSum_iff ENNReal.summable, ENNReal.tsum_comm]

-- do we need the `real` version?
-- /-- sum of row sums equals sum of column sums -/
-- lemma real.summable_snd_of_summable_fst {α β: Type*} (F : α → β → ℝ) (h_nonneg : ∀ n k, 0 ≤ F n k)
--   (h_rows : ∀ n, summable (λ k, F n k)) (h_cols : ∀ k, summable (λ n, F n k))
--   (h_col_row : summable (λ k, ∑' n, F n k)) : summable (λ n, ∑' k, F n k) :=
-- begin
--   -- wrong idea have := summable (λ ab : α × β, F ab.1 ab.2),
--   admit,
-- end
-- could go in ennreal line 684 or so
theorem ENNReal.hMul_le_hMul_of_right {a b c : ℝ≥0∞} (hab : a ≤ b) : a * c ≤ b * c :=
  by
  rcases eq_or_ne c 0 with (rfl | hc0)
  · simp
  · rcases eq_or_ne c ⊤ with (rfl | hctop)
    · rw [@ENNReal.mul_top' b]
      split_ifs with hb
      · subst hb
        change a ≤ ⊥ at hab 
        rw [le_bot_iff] at hab 
        simp [hab]
      · exact le_top
    · rwa [ENNReal.mul_le_mul_right hc0 hctop]

-- could go in ennreal line 684 or so
theorem ENNReal.hMul_le_hMul_of_left {a b c : ℝ≥0∞} (hab : a ≤ b) : c * a ≤ c * b :=
  by
  rw [mul_comm, mul_comm c]
  exact ENNReal.hMul_le_hMul_of_right hab

-- might not need this
theorem NNReal.inv_hMul_le_iff {a b c : ℝ≥0} (hb0 : b ≠ 0) : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
  by
  rw [← NNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe]
  push_cast
  apply inv_mul_le_iff
  obtain hb | (hb : 0 < b) := eq_zero_or_pos
  · subst hb; exfalso; apply hb0; rfl
  · assumption_mod_cast

theorem ENNReal.inv_hMul_le_iff {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ∞) :
    b⁻¹ * a ≤ c ↔ a ≤ b * c := by
  rw [mul_comm, mul_comm b]
  apply ENNReal.div_le_iff_le_mul <;> cc

theorem ENNReal.zero_le (a : ℝ≥0∞) : 0 ≤ a :=
  bot_le

theorem ENNReal.zero_le' {a : ℝ≥0∞} : 0 ≤ a :=
  bot_le

theorem ENNReal.inv_eq_of_hMul_eq_one {a b : ℝ≥0∞} (h : a * b = 1) : a⁻¹ = b :=
  by
  induction b using WithTop.recTopCoe
  · exfalso
    rw [ENNReal.mul_top'] at h 
    split_ifs at h  with ha <;> · revert h; norm_num
  induction a using WithTop.recTopCoe
  · exfalso
    rw [ENNReal.top_mul'] at h 
    split_ifs at h  with ha <;> · revert h; norm_num
  norm_cast at h 
  have ha : a ≠ 0 := by rintro rfl; rw [MulZeroClass.zero_mul] at h ; revert h; norm_num
  rw [← ENNReal.coe_inv ha]
  norm_cast
  rwa [← inv_mul_eq_one₀, inv_inv]
  exact inv_ne_zero ha

theorem ENNReal.hMul_inv_eq_of_eq_hMul {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤)
    (h : a = c * b) : a * b⁻¹ = c := by rw [h, mul_assoc, ENNReal.mul_inv_cancel hb0 hbtop, mul_one]

theorem ENNReal.eq_hMul_of_hMul_inv_eq {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤)
    (h : a * b⁻¹ = c) : a = c * b := by
  rw [← h, mul_assoc, ENNReal.inv_mul_cancel hb0 hbtop, mul_one]

theorem ENNReal.hMul_eq_of_hMul_inv_eq {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤)
    (h : a * b⁻¹ = c) : c * b = a :=
  (ENNReal.eq_hMul_of_hMul_inv_eq hb0 hbtop h).symm

theorem ENNReal.hMul_inv_eq_iff_eq_hMul {a b c : ℝ≥0∞} (hb0 : b ≠ 0) (hbtop : b ≠ ⊤) :
    a * b⁻¹ = c ↔ a = c * b :=
  ⟨ENNReal.eq_hMul_of_hMul_inv_eq hb0 hbtop, ENNReal.hMul_inv_eq_of_eq_hMul hb0 hbtop⟩

theorem ENNReal.le_zero_iff {a : ℝ≥0∞} : a ≤ 0 ↔ a = 0 :=
  le_bot_iff

theorem ENNReal.sub_pos {a b : ℝ≥0∞} : 0 < a - b ↔ b < a :=
  by
  rw [← not_iff_not]
  push_neg
  rw [ENNReal.le_zero_iff]
  apply tsub_eq_zero_iff_le

theorem ENNReal.top_zpow_of_pos {n : ℤ} (hn : 0 < n) : (⊤ : ℝ≥0∞) ^ n = ⊤ :=
  by
  let m := n.nat_abs
  have hm : n = m := by rw [Int.natAbs_of_nonneg hn.le]
  rw [hm] at hn ⊢
  apply ENNReal.top_pow
  exact_mod_cast hn

-- can't do!
--lemma ennreal.zpow_neg (a : ℝ≥0∞) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹ := by admit
-- lemma ennreal.top_zpow_of_neg {n : ℤ} (hn : n < 0) : (⊤ : ℝ≥0∞) ^ n = 0 :=
-- begin
--   let m := n.nat_abs,
--   have hm : n = -m,
--   { rw [int.of_nat_nat_abs_of_nonpos hn.le, neg_neg] },
--   rw hm at hn ⊢,
--   rw neg_lt_zero at hn,
--   have hm' : 0 < m, by exact_mod_cast hn,
--   rw [ennreal.zpow_neg, zpow_coe_nat, ennreal.inv_eq_zero, ennreal.top_pow hm'],
-- end
