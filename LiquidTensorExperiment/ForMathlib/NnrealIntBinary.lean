import LiquidTensorExperiment.ForMathlib.NnrealNatBinary

#align_import for_mathlib.nnreal_int_binary

def Nat.equivLeInt (d : ℤ) : ℕ ≃ ({n : ℤ | d ≤ n} : Set ℤ)
    where
  toFun m := ⟨m + d, by simp⟩
  invFun n := ((n : ℤ) - d).natAbs
  left_inv m := by simp
  right_inv := by
    rintro ⟨n, hn⟩
    have hdn : 0 ≤ n - d := sub_nonneg.mpr hn
    simp [hn, Int.natAbs_of_nonneg hdn]

def Nat.equivIntLtCompl (d : ℤ) : ℕ ≃ ({n : ℤ | n < d}ᶜ : Set ℤ)
    where
  toFun m := ⟨m + d, by simp⟩
  invFun n := ((n : ℤ) - d).natAbs
  left_inv m := by simp
  right_inv := by
    rintro ⟨n, hn : ¬n < d⟩
    have hn := le_of_not_lt hn
    have hdn : 0 ≤ n - d := sub_nonneg.mpr hn
    simp [hn, Int.natAbs_of_nonneg hdn]

def Nat.equivLeIntCompl (d : ℤ) : ℕ ≃ ({n : ℤ | d ≤ n}ᶜ : Set ℤ)
    where
  toFun m := ⟨d - (m + 1), show ¬d ≤ d - (m + 1) by push_neg <;> exact sub_lt_self d (by linarith)⟩
  invFun n := (d - ((n : ℤ) + 1)).natAbs
  left_inv m := by simp <;> ring_nf
  -- `ring` is noisy for some reason?
  right_inv := by
    rintro ⟨n, hn : ¬d ≤ n⟩
    simp
    rw [Int.natAbs_of_nonneg]; ring; linarith

theorem Int.summable_iff_nat_summable_and_nat_summable {α : Type _} [AddCommGroup α]
    [UniformSpace α] [UniformAddGroup α] [CompleteSpace α] (d : ℤ) (f : ℤ → α) :
    Summable f ↔ (Summable fun n : ℕ => f (n + d)) ∧ Summable fun n : ℕ => f (d - (n + 1)) :=
  by
  refine' (@summable_subtype_and_compl α _ _ _ _ _ _ {z : ℤ | d ≤ z}).symm.trans _
  apply and_congr
  · rw [← (Nat.equivLeInt d).summable_iff]
    rfl
  · rw [← (Nat.equivLeIntCompl d).summable_iff]
    rfl

-- is this worthy of mathlib?
theorem Int.tsum_eq_nat_tsum_of_bdd_below {α : Type _} [AddCommMonoid α] [TopologicalSpace α]
    [ContinuousAdd α] [T2Space α] (f : ℤ → α) (d : ℤ) (hd : ∀ n, n < d → f n = 0)
    (hsum : Summable fun n : ℕ => f (n + d)) : ∑' m, f m = ∑' n : ℕ, f (n + d) :=
  by
  have summable_small : Summable fun n : {n : ℤ | n < d} => (f ∘ (coe : _ → ℤ)) n :=
    by
    convert summable_zero
    ext ⟨n, hn⟩
    exact hd n hn
  have tsum_small : ∑' n : {n : ℤ | n < d}, f n = 0 :=
    by
    convert tsum_zero
    ext ⟨n, hn⟩
    exact hd n hn
    infer_instance
  have summable_big : Summable fun n : {n : ℤ | n < d}ᶜ => (f ∘ (coe : _ → ℤ)) n := by
    rwa [← (Nat.equivIntLtCompl d).summable_iff]
  rw [← tsum_add_tsum_compl summable_small summable_big, tsum_small, zero_add, ←
    (Nat.equivIntLtCompl d).tsum_eq]
  rfl; infer_instance

open scoped NNReal

/-
zpow_le_zpow' :
  ∀ {α : Type u_1} [_inst_1 : ordered_comm_group α] {n : ℤ} {a b : α}, 0 ≤ n → a ≤ b → a ^ n ≤ b ^ n
-/
def NNReal.zpow_le_zpow' {n : ℤ} {a b : ℝ≥0} (hn : 0 ≤ n) (hab : a ≤ b) : a ^ n ≤ b ^ n :=
  by
  let m := n.natAbs
  rw [Int.eq_natAbs_of_zero_le hn]
  suffices : a ^ m ≤ b ^ m
  assumption_mod_cast
  generalize m = d
  induction' d with d hd
  -- I can't believe I'm doing this. Where is this??
  · rfl
  · rw [pow_succ, pow_succ]
    exact mul_le_mul' hab hd

-- lemma is false if w = 1 and n = any and r = 0
-- lemma is false if w = 0 and n ≠ 0 and r = 2⁻¹
theorem NNReal.zpow_le_iff_log {w r : ℝ≥0} (hw : 0 < w) (hr : 0 < r) {n : ℤ} :
    w ^ n ≤ r ↔ (w : ℝ).log * n ≤ (r : ℝ).log :=
  by
  rw [mul_comm, ← Real.log_zpow]
  rw [show w ^ n ≤ r ↔ (w : ℝ) ^ n ≤ (r : ℝ) by norm_cast]
  rw [Real.log_le_log] <;> norm_cast
  · exact NNReal.zpow_pos hw.ne.symm _
  · exact hr

-- → is false if w = 1 and n = any and r = 0
-- ← is false if w = 0 and n ≠ 0 and r = 2⁻¹
theorem NNReal.lt_zpow_iff_log {w r : ℝ≥0} (hw : 0 < w) (hr : 0 < r) {n : ℤ} :
    r < w ^ n ↔ (r : ℝ).log < (w : ℝ).log * n :=
  by
  rw [mul_comm, ← Real.log_zpow]
  rw [Real.log_lt_log_iff]
  · norm_cast
  · assumption_mod_cast
  · apply zpow_pos_of_pos
    assumption_mod_cast

-- the useful lower and upper bounds on 2⁻¹ ^ ⌈z.log / (2⁻¹ : ℝ).log⌉
theorem pow_d_le_z {z : ℝ≥0} (hz : 0 < z) : (2⁻¹ : ℝ≥0) ^ ⌈(z : ℝ).log / (2⁻¹ : ℝ).log⌉ ≤ z :=
  by
  rw [NNReal.zpow_le_iff_log (by norm_num : (0 : ℝ≥0) < 2⁻¹) hz]
  rw [← div_le_iff_of_neg']
  · convert Int.le_ceil _
  · apply Real.log_neg <;> norm_num

theorem Int.ceil_sub_one_lt {α : Type _} [LinearOrderedRing α] [FloorRing α] (a : α) :
    (⌈a⌉ : α) - 1 < a :=
  sub_lt_iff_lt_add.mpr (Int.ceil_lt_add_one a)

theorem z_lt_pow_d_succ {z : ℝ≥0} (hz : 0 < z) :
    z < (2⁻¹ : ℝ≥0) ^ (⌈(z : ℝ).log / (2⁻¹ : ℝ).log⌉ - 1) :=
  by
  rw [NNReal.lt_zpow_iff_log (by norm_num : (0 : ℝ≥0) < 2⁻¹) hz]
  rw [← lt_div_iff_of_neg']
  · push_cast
    convert Int.ceil_sub_one_lt _
  · apply Real.log_neg <;> norm_num

namespace NNReal

namespace Int

/-- The stream of 0s and 1s (always 0 for n<<0, not always 1 for n>>0)
such that r = ∑ (binary r n) * 2⁻¹ ^ n -/
noncomputable def binary (r : ℝ≥0) : ℤ → ℕ :=
  if r = 0 then 0
  else fun n =>
    let d : ℤ := ⌈(r : ℝ).log / (2⁻¹ : ℝ).log⌉
    if n < d then 0 else NNReal.Nat.digit (r * 2 ^ d) (n - d).natAbs

example (n m : ℤ) : n ≤ m ↔ n < m + 1 :=
  Int.lt_add_one_iff.symm

theorem binary_le_one (r : ℝ≥0) (n : ℤ) : binary r n ≤ 1 :=
  by
  let d : ℤ := ⌈(r : ℝ).log / (2⁻¹ : ℝ).log⌉
  rw [binary]; split_ifs with hr hn; exact zero_le_one; exact zero_le_one
  push_neg at hn 
  rcases lt_or_eq_of_le hn with (h1 | h2)
  · rw [Int.lt_iff_add_one_le, le_iff_exists_nonneg_add] at h1 
    rcases h1 with ⟨c, hc1, rfl⟩
    convert NNReal.Nat.digit.succ_le_one (r * 2 ^ d) c.natAbs
    suffices (c + 1).natAbs = c.natAbs + 1 by convert this; ring
    exact Int.natAbs_add_nonneg hc1 zero_le_one
  · clear hn
    rw [← h2]
    rw [Nat.digit, sub_self, Int.natAbs_zero, Nat.binary.zero_fst_def, ← Nat.lt_add_one_iff]
    rw [Nat.floor_lt']; swap; norm_num
    have := z_lt_pow_d_succ (zero_lt_iff.mpr hr)
    have h : (2⁻¹ : ℝ≥0) ≠ 0; norm_num
    rw [zpow_sub_one₀ h, inv_inv] at this 
    replace this := inv_mul_lt_of_lt_mul₀ this
    rw [mul_comm] at this ; simpa

@[simp]
theorem binary_zero (z : ℤ) : binary 0 z = 0 := by rw [binary, if_pos] <;> rfl

-- d = ⌈real.log r / real.log (2⁻¹ : ℝ≥0)⌉ is
-- the unique solution to 2^{-d} ≤ r < 2^{1-d} if r>0
-- and hence the point beyond with all digits are 0
theorem binary_eq_zero (r : ℝ≥0) (n : ℤ) (hsmall : n < ⌈Real.log r / Real.log (2⁻¹ : ℝ≥0)⌉) :
    binary r n = 0 := by
  rw [binary]
  split_ifs <;> rfl

theorem binary_summable (r : ℝ≥0) {s : ℝ≥0} (hs : s < 1) :
    Summable fun n : ℤ => (binary r n : ℝ≥0) * s ^ n :=
  by
  rcases eq_or_ne s 0 with (rfl | hspos)
  · apply summable_of_ne_finset_zero
    rintro n (hn : n ∉ ({0} : Finset ℤ))
    rw [Finset.not_mem_singleton] at hn 
    simp [zero_zpow n hn]
  rw [← NNReal.summable_coe]
  let d := ⌈Real.log r / Real.log (2⁻¹ : ℝ≥0)⌉
  rw [Int.summable_iff_nat_summable_and_nat_summable d (_ : _ → ℝ)]
  constructor
  · simp_rw [zpow_add₀ hspos, ← mul_assoc]
    norm_cast
    apply Summable.mul_right
    refine' summable_of_le (fun b => _) (summable_geometric hs)
    refine' mul_le_of_le_one_left (pow_nonneg zero_le' _) _
    norm_cast
    apply binary_le_one
  · convert summable_zero; ext k
    norm_cast
    convert MulZeroClass.zero_mul _
    norm_cast
    convert binary_eq_zero r _ _
    apply sub_lt_self
    norm_cast
    apply Nat.succ_pos

theorem tsum_add_tsum_compl' {β : Type _} {f : β → ℝ≥0} (s : Set β) (hf : Summable f) :
    ∑' x : ↥s, f ↑x + ∑' x : ↥(sᶜ), f ↑x = ∑' x : β, f x := by
  apply tsum_add_tsum_compl <;> apply summable_comp_injective hf <;> exact Subtype.coe_injective

theorem binary_sum (r : ℝ≥0) : ∑' n : ℤ, (binary r n : ℝ≥0) * 2⁻¹ ^ n = r :=
  by
  let d := ⌈Real.log r / Real.log (2⁻¹ : ℝ≥0)⌉
  rw [← tsum_add_tsum_compl' {n : ℤ | n < d} (binary_summable _ two_inv_lt_one)]
  convert zero_add r
  · convert (tsum_zero : _ = (0 : ℝ≥0))
    ext ⟨b, hb : b < d⟩
    simp [binary_eq_zero r b hb]
  · rw [← (Nat.equivIntLtCompl d).tsum_eq]; swap; infer_instance
    simp only [Nat.equivIntLtCompl, binary, Equiv.coe_fn_mk, Subtype.coe_mk, neg_add_rev,
      zpow_add₀ (show (2⁻¹ : ℝ≥0) ≠ 0 by norm_num), ← mul_assoc, tsum_mul_right]
    split_ifs with hr hr
    · subst hr
      convert (tsum_zero : ∑' n : ℕ, _ = (0 : ℝ≥0))
      ext n; simp
    · rw [← eq_div_iff (zpow_ne_zero _ (show (2⁻¹ : ℝ≥0) ≠ 0 by norm_num))]
      convert NNReal.Nat.digit.tsum (r * 2 ^ d)
      · ext n
        rw [if_neg]
        · norm_cast
          congr
          convert Int.natAbs_ofNat n
          exact add_sub_cancel _ d
        · push_neg
          change d ≤ n + d
          linarith
      · rw [inv_zpow, NNReal.div_inv]

end Int

end NNReal

