import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import LiquidTensorExperiment.LaurentMeasures.IntNatShifts

#align_import laurent_measures.aux_lemmas

noncomputable section

open Metric Finset NormedField

--filter
open scoped NNReal Classical BigOperators TopologicalSpace

namespace AuxThm69

section EquivalencesDef

-- for mathlib?
def rangeEquivIcc {n d : ℤ} (m : ℕ) (hm : n - d = m) : range m.succ ≃ Icc d n :=
  by
  refine' ⟨fun a => ⟨a + d, mem_Icc.mpr ⟨_, _⟩⟩, _, _, _⟩
  · exact (le_add_iff_nonneg_left _).mpr (Int.ofNat_nonneg _)
  · refine' add_le_of_le_sub_right _
    exact (int.ofNat_le.mpr (Nat.le_of_lt_succ <| (@mem_range m.succ a).mp a.2)).trans hm.ge
  · rintro ⟨a, hha⟩
    refine' ⟨(a - d).natAbs, mem_range_succ_iff.mpr _⟩
    lift a - d to ℕ using sub_nonneg.mpr (mem_Icc.mp hha).1 with ad had
    rw [Int.natAbs_ofNat, ← Int.ofNat_le _ _, had, ← hm]
    exact sub_le_sub_right (mem_Icc.mp hha).2 _
  · exact fun x => Subtype.ext (by simp)
  · rintro ⟨x, hx⟩
    simp [Int.natAbs_of_nonneg (sub_nonneg.mpr (mem_Icc.mp hx).1), sub_add_cancel]

--for `mathlib`?
def equivBddIntegerNat (N : ℤ) : ℕ ≃ { x // N ≤ x }
    where
  toFun n := ⟨n + N, le_add_of_nonneg_left (Int.coe_nat_nonneg n)⟩
  invFun x := (x.1 - N).natAbs
  left_inv n := by simp
  right_inv := fun ⟨x, hx⟩ => Subtype.ext (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hx)])

def equivIccBddNonneg {d : ℤ} (hd : 0 ≤ d) :
    { x // d ≤ x } ≃ { x // x ∉ range (Int.eq_ofNat_of_zero_le hd).some } :=
  by
  fconstructor
  · rintro ⟨_, h⟩
    have := (Int.eq_ofNat_of_zero_le (hd.trans h)).choose_spec
    rw [(Int.eq_ofNat_of_zero_le hd).choose_spec, this, Int.ofNat_le, ← not_lt, ← mem_range] at h 
    exact ⟨_, h⟩
  · rintro ⟨_, h⟩
    rw [mem_range, Nat.lt_iff_add_one_le, not_le, Nat.lt_add_one_iff, ← Int.ofNat_le, ←
      (Int.eq_ofNat_of_zero_le hd).choose_spec] at h 
    exact ⟨_, h⟩
  · rintro ⟨_, h⟩
    simp only [Int.coe_nat_inj', Int.ofNat_eq_coe]
    exact (Int.eq_ofNat_of_zero_le (hd.trans h)).choose_spec.symm
  · rintro ⟨_, h⟩
    simp only [Int.coe_nat_inj', Int.ofNat_eq_coe]
    exact (@exists_eq' _ _).choose_spec.symm

def t {d : ℤ} (hd : d < 0) : Finset { x : ℤ // d ≤ x } :=
  Ico ⟨d, le_of_eq rfl⟩ ⟨0, le_of_lt hd⟩

theorem t.zero_le {d : ℤ} (hd : d < 0) {y : { x // d ≤ x }} (h : y ∉ t hd) : 0 ≤ y.1 :=
  by
  suffices (⟨d, rfl.le⟩ : { x // d ≤ x }) ≤ y → (⟨_, hd.le⟩ : { x // d ≤ x }) ≤ y from this y.2
  simpa [T, hd] using h

def r {d n : ℤ} (hn : 0 ≤ n - d) : Finset { x : ℤ // d ≤ x } :=
  Icc ⟨d, le_of_eq rfl⟩ ⟨n, Int.le_of_sub_nonneg hn⟩

def equivIccR {d n : ℤ} (hn : 0 ≤ n - d) : Icc d n ≃ r hn :=
  by
  fconstructor
  · rintro ⟨m, hm⟩
    replace hm := mem_Icc.mp hm
    use⟨m, hm.1⟩
    dsimp [R]
    rw [mem_Icc]
    use And.intro (subtype.mk_le_mk.mpr hm.1) (subtype.mk_le_mk.mpr hm.2)
  · dsimp [R]
    rintro ⟨⟨x, hx⟩, h⟩
    rw [mem_Icc] at h 
    use x
    rw [mem_Icc]
    use And.intro hx (subtype.mk_le_mk.mp h.2)
  · simp only [id.def]
    rintro ⟨⟨x, hx⟩, h⟩
    all_goals simp only
  · simp only [id.def]
    dsimp [R]
    rintro ⟨⟨x, hx⟩, h⟩
    simp only

def equivComplRBdd {d n : ℤ} (hn : 0 ≤ n - d) :
    { a : ℤ // n.succ ≤ a } ≃ (r hnᶜ : Set { x : ℤ // d ≤ x }) :=
  by
  fconstructor
  · rintro ⟨m, hm⟩
    have hd : d ≤ m := (Int.le_add_one (Int.le_of_sub_nonneg hn)).trans hm
    use⟨m, hd⟩
    dsimp only [R]
    simpa [mem_coe, mem_Icc, Subtype.mk_le_mk, not_and, hd, forall_true_left, not_le,
      Int.lt_iff_add_one_le, hm]
  · rintro ⟨⟨x, hx⟩, h_mem⟩
    dsimp only [R] at h_mem 
    simp only [Subtype.mk_le_mk, coe_Icc, not_and, not_le, Set.mem_Icc, hx, forall_true_left,
      Int.lt_iff_add_one_le, Set.mem_compl_iff] at h_mem 
    use⟨x, h_mem⟩
  · rintro ⟨_, _⟩; simp only [id.def]
  · rintro ⟨⟨_, _⟩, _⟩; simpa

end EquivalencesDef

section EquivalencesLemma

--for mathlib?
theorem sum_reverse {β : Type _} [AddCommGroup β] (f : ℤ → β) (n : ℕ) :
    ∑ l in range n.succ, f (n - l) = ∑ l in range n.succ, f l :=
  by
  induction' n with n hn generalizing f
  · simp only [zero_sub, Int.ofNat_zero, sum_singleton, neg_zero, range_one]
  · rw [sum_range_succ', sum_range_succ (f ∘ coe)]
    simp only [← hn, Int.ofNat_zero, add_sub_add_right_eq_sub, Function.comp_apply, sub_zero,
      Int.ofNat_succ]

theorem sum_range_sum_Icc' {α : Type _} [Field α] (f : ℤ → α) {n d : ℤ} (hn : 0 ≤ n - d) :
    ∑ l in range (Int.eq_ofNat_of_zero_le hn).some.succ, f (n - l) * 2 ^ l =
      ∑ k in Icc d n, f k * 2 ^ (n - k) :=
  by
  let m := (Int.eq_ofNat_of_zero_le hn).some
  have h := (Int.eq_ofNat_of_zero_le hn).choose_spec.symm
  have sum_swap :
    ∑ l : ℕ in range m.succ, f (n - l) * 2 ^ l = ∑ l : ℕ in range m.succ, f (l + d) * 2 ^ (m - l) :=
    by
    convert (sum_reverse (fun l => f (n - l) * 2 ^ l) m).symm using 1
    · simp_rw [← zpow_ofNat]
    refine' sum_congr rfl fun x hx => _
    rw [mem_range, Nat.lt_succ_iff] at hx 
    rw [← zpow_ofNat, Int.ofNat_sub hx]
    congr 2
    rw [h]; ring
  rw [sum_swap, ← sum_finset_coe, ← sum_finset_coe _ (Icc _ _)]
  refine' Fintype.sum_equiv (range_equiv_Icc _ h.symm) _ _ fun x => _
  dsimp [range_equiv_Icc]
  rw [← sub_sub, sub_right_comm, ← zpow_ofNat]
  refine' congr_arg ((· * ·) _) (congr_arg (pow 2) _)
  have := @Nat.cast_sub ℤ _ _ _ (mem_range_succ_iff.mp x.2)
  simpa only [this, h, sub_left_inj, Subtype.val_eq_coe]

theorem sum_range_sum_Icc (f : ℤ → ℝ) (n d : ℤ) (hn : 0 ≤ n - d) :
    ∑ l in range (Int.eq_ofNat_of_zero_le hn).some.succ, f (n - l) * 2 ^ l =
      ∑ k in Icc d n, f k * 2 ^ (n - k) :=
  sum_range_sum_Icc' f hn

theorem equivIccBddNonneg_apply {d : ℤ} (hd : 0 ≤ d) (x : { x // d ≤ x }) :
    (equivIccBddNonneg hd x : ℤ) = x.1 :=
  by
  rcases x with ⟨_, h⟩
  exact (Exists.choose_spec (Int.eq_ofNat_of_zero_le (hd.trans h))).symm

theorem equivIccR_apply {d n : ℤ} (hn : 0 ≤ n - d) (x : Icc d n) : (equivIccR hn x : ℤ) = (x : ℤ) :=
  by rcases x with ⟨⟩; rfl

theorem equivComplRBdd_apply {d n : ℤ} (hn : 0 ≤ n - d) (x : { a : ℤ // n.succ ≤ a }) :
    (equivComplRBdd hn x : ℤ) = (x : ℤ) := by rcases x with ⟨y, hy⟩; simpa

theorem sum_Icc_sum_tail (f : ℤ → ℤ) (n d : ℤ) (hf : HasSum (fun x : ℤ => (f x : ℝ) * (2 ^ x)⁻¹) 0)
    (hd : ∀ n : ℤ, n < d → f n = 0) (hn : 0 ≤ n - d) :
    -∑ k in Icc d n, (f k : ℝ) * 2 ^ (n - k) =
      2 ^ n * tsum fun x : { a : ℤ // n.succ ≤ a } => (f x : ℝ) * (2 ^ x.1)⁻¹ :=
  by
  simp_rw [zpow_sub₀ (@two_ne_zero ℝ _ _), div_eq_mul_inv, ← mul_assoc, mul_comm _ ((2 : ℝ) ^ n),
    mul_assoc, ← mul_sum, neg_mul_eq_mul_neg, mul_eq_mul_left_iff]
  apply Or.intro_left
  have H_supp : (Function.support fun n : ℤ => (f n : ℝ) * (2 ^ n)⁻¹) ⊆ {a : ℤ | d ≤ a} :=
    by
    rw [Function.support_subset_iff]
    intro
    rw [← not_imp_not, Classical.not_not, mul_eq_zero]
    intro hx
    simp only [not_le, Set.mem_setOf_eq] at hx 
    apply Or.intro_left
    exact int.cast_eq_zero.mpr (hd _ hx)
  rw [← @hasSum_subtype_iff_of_support_subset ℝ ℤ _ _ (fun n : ℤ => f n * (2 ^ n)⁻¹) _ _ H_supp] at
    hf 
  let g := fun n : { x : ℤ // d ≤ x } => (f n : ℝ) * (2 ^ n.1)⁻¹
  have hg : HasSum g 0 := hf
  have := @sum_add_tsum_compl _ _ _ _ _ g _ (R hn) hg.summable
  rw [hg.tsum_eq, add_eq_zero_iff_eq_neg] at this 
  replace this := neg_eq_iff_neg_eq.mpr this.symm
  convert this using 1
  · simp only [neg_inj]
    have h_R :=
      @Fintype.sum_equiv (Icc d n) (R hn) _ _ _ _ (equiv_Icc_R hn)
        ((fun x : ℤ => (f x : ℝ) * (2 ^ x)⁻¹) ∘ coe) (g ∘ coe)
    rw [@sum_subtype ℝ ℤ _ (· ∈ Icc d n) _ (Icc d n) _ fun x => (f x : ℝ) * (2 ^ x)⁻¹]
    rw [@sum_subtype ℝ _ _ (· ∈ R hn) _ (R hn) _ fun x => g x]
    simp only
    refine' h_R _
    · intro x
      dsimp [g]
      rw [← coe_coe, equiv_Icc_R_apply hn x]
    all_goals intro; rfl
  · dsimp only [g]
    refine'
      Eq.trans _
        (@Equiv.tsum_eq _ _ _ _ _ _ (equiv_compl_R_bdd hn) fun x => (f x : ℝ) * (2 ^ (x.1 : ℤ))⁻¹)
    apply tsum_congr
    intro x
    simp_rw [← coe_coe]
    nth_rw_rhs 1 [Subtype.val_eq_coe]
    rw [← coe_coe, equiv_compl_R_bdd_apply hn x, ← Subtype.val_eq_coe]

end EquivalencesLemma

section Summability

theorem summable_shift (f : ℤ → ℝ) (N : ℤ) :
    (Summable fun x : ℕ => f (x + N)) ↔ Summable fun x : { x // N ≤ x } => f x :=
  @Equiv.summable_iff _ _ _ _ _ (fun x : { x // N ≤ x } => f x) (equivBddIntegerNat N)

theorem int_tsum_shift (f : ℤ → ℝ) (N : ℤ) : ∑' x : ℕ, f (x + N) = ∑' x : { x // N ≤ x }, f x :=
  by
  apply tsum_eq_tsum_of_hasSum_iff_hasSum
  intro
  apply @Equiv.hasSum_iff ℝ _ ℕ _ _ (f ∘ coe) _ (AuxThm69.equivBddIntegerNat N)

theorem summable_of_eventually_zero (f : ℤ → ℝ) (d : ℤ) (hd : ∀ n : ℤ, n < d → f n = 0) :
    Summable fun n : ℕ => f (-↑n - 1) :=
  by
  refine' Summable.of_norm_bounded_eventually _ summable_zero _
  suffices {x : ℕ | ¬f (-↑x - 1) = 0}.Finite by simpa
  apply (range (Int.toNat (-d))).finite_toSet.Subset _
  refine' fun x h => mem_coe.mpr (mem_range.mpr (int.lt_to_nat.mpr (not_le.mp fun H => _)))
  simpa [hd _ (int.sub_one_lt_iff.mpr (neg_le.mp H))] using h

theorem summable_iff_on_nat_less {f : ℤ → ℝ} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
    Summable f ↔ Summable fun n : ℕ => f n :=
  int_summable_iff.trans <|
    and_iff_left_iff_imp.mpr fun hh => summable_of_eventually_zero f d fun n nd => by simp [h _ nd]

theorem Nnreal.summable_iff_on_nat_less {f : ℤ → ℝ≥0} (d : ℤ) (h : ∀ {n : ℤ}, n < d → f n = 0) :
    Summable f ↔ Summable fun n : ℕ => f n :=
  NNReal.summable_coe.symm.trans <|
    (summable_iff_on_nat_less d fun n nd => (f n).val_eq_zero.mpr (h nd)).trans NNReal.summable_coe

theorem Int.summable_iff_on_nat {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
    (Summable fun n => ‖f n‖ * ρ ^ n) ↔
      Summable fun n : ℕ => ‖f n‖ * ρ ^ (n : ℤ) :=
  summable_iff_on_nat_less d fun n nd => by simp [h _ nd]

theorem Nnreal.summable_iff_on_nat_less_shift {f : ℤ → ℝ≥0} (d : ℤ) (h : ∀ {n : ℤ}, n < d → f n = 0)
    (M : ℤ) : Summable f ↔ Summable fun n : ℕ => f (M + n) :=
  by
  rw [← NNReal.summable_coe, ← NNReal.summable_coe]
  constructor
  · intro hf
    have hinj : Function.Injective fun n : ℕ => M + n :=
      by
      rintro a b (h2 : M + a = M + b)
      simpa using h2
    convert hf.comp_injective hinj
  · intro hs
    rw [← (Equiv.addLeft M).summable_iff]
    rw [← @summable_iff_on_nat_less (fun a : ℤ => ↑(f (M + a))) (d - M) _] at hs 
    · exact (summable_congr fun k => rfl).1 hs
    · intro n hn
      dsimp only
      rw [h]; norm_num; linarith

-- nnreal.summable_coe.symm.trans $ (summable_iff_on_nat_less d (λ n nd,
--   ((f n).coe_eq_zero.mpr (h nd)))).trans nnreal.summable_coe
theorem summable_smaller_radius_norm {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ) (ρ_half : 2⁻¹ < ρ)
    (hf : Summable fun n : ℤ => ‖f n‖ * ρ ^ n)
    (hd : ∀ n : ℤ, n < d → f n = 0) :--(F : ℒ S) (s : S) :
      Summable
      fun n => ‖f n‖ * 2⁻¹ ^ n :=
  by
  refine' int_summable_iff.mpr ⟨_, _⟩
  · apply (int_summable_iff.mp hf).1.smaller_radius ρ_half.le (by simp)
  ·
    apply
      summable_of_eventually_zero (fun n => ‖f n‖ * 2⁻¹ ^ n) d fun n nd => by
        simp [hd _ nd]

theorem summable_smaller_radius {f : ℤ → ℤ} {ρ : ℝ≥0} (d : ℤ)
    (hf : Summable fun n : ℤ => ‖f n‖ * ρ ^ n) (hd : ∀ n : ℤ, n < d → f n = 0)
    (hρ : 2⁻¹ < ρ) : Summable fun n => (f n : ℝ) * 2⁻¹ ^ n :=
  by
  refine' Summable.of_norm _
  simp_rw [norm_mul, norm_zpow, norm_inv, Real.norm_two]
  apply (summable_iff_on_nat_less d _).mpr
  apply Summable.smaller_radius _ hρ.le
  · exact fun x => norm_nonneg _
  · simpa using (int_summable_iff.mp hf).1
  · exact fun n nd => by simp [hd _ nd]

theorem prod_nat_summable {f : ℤ → ℤ} {r : ℝ≥0} (half_lt_r : 2⁻¹ < r)
    (hf : Summable fun n : ℤ => ‖f n‖ * r ^ n) :
    Summable fun lj : ℕ × ℕ =>
      (2⁻¹ : ℝ) * ‖((f (lj.fst + 1 + lj.snd) : ℝ) * 2⁻¹ ^ lj.snd)‖ * r ^ lj.fst :=
  by
  have r0 : r ≠ 0 := by rintro rfl; simpa only [not_lt_zero'] using half_lt_r
  have : Summable fun n : ℤ => ‖((f n : ℝ) * (2 * r)⁻¹)‖ * r ^ n :=
    by
    convert_to Summable fun z : ℤ => (2⁻¹ * r⁻¹ : ℝ) • (‖f z‖ * ↑r ^ z)
    · ext
      field_simp
      congr 0
    · exact Summable.const_smul hf
  convert prod_nat_summable_aux (_ : 2⁻¹ * r⁻¹ < 1) this
  · ext
    field_simp [r0]
    ring
  · exact NNReal.div_lt_one_of_lt half_lt_r

-- lemma fiberwise_summable_norm {f : ℤ → ℤ} {r : ℝ≥0} (d : ℤ) (half_lt_r : 1 / 2 < r)
--   (hf : summable (λ n : ℤ, ∥ f n ∥ * r ^ n))
--   (hd : ∀ n : ℤ, n < d → f n = 0) :
--   summable (λ (n : ℕ), 1 / 2 * ∥ ∑' (i : ℕ), (f (n + 1 + i) : ℝ) * (1 / 2) ^ i ∥ * ↑r ^ n) :=
-- begin
--   have r_pos : ∀ (b : ℕ), 0 < (r : ℝ) ^ b :=
--     pow_pos (lt_trans (by exact nnreal.coe_pos.mp (one_div_pos.mpr zero_lt_two)) half_lt_r),
--   have smaller_shift : ∀ (b : ℕ), summable (λ j : ℕ, ∥ (f (b + 1 + j) : ℝ)  * (1 / 2) ^ j ∥),
--   { intro b,
--     refine (summable_mul_right_iff (by norm_num : (1 / 2 : ℝ) ^ (b + 1) ≠ 0)).mpr _,
--     obtain hff := (equiv.add_group_add (b+1 : ℤ)).summable_iff.mpr (summable_smaller_radius_norm d
--       half_lt_r hf hd),
--     convert (summable_iff_on_nat_less (d - (b + 1)) _).mp hff,
--     { ext,
--       simp [mul_assoc, zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0) (b+1), mul_inv, zpow_coe_nat,
--         mul_comm ((2 : ℝ) ^ x)⁻¹], refl },
--     { exact λ n nd, by simp [hd _ (lt_sub_iff_add_lt'.mp nd)] } },
--   set ϕ := λ lj: ℕ × ℕ,
--     (1 / 2 : ℝ) * ∥ (f (lj.fst + 1 + lj.snd) : ℝ) * (1/2)^(lj.snd) ∥ * r ^ (lj.fst),
--   have H : ∀ b : ℕ, summable (λ i : ℕ, ϕ(b, i)) :=
--     λ n, (summable_mul_right_iff (r_pos n).ne').mp ((smaller_shift n).mul_left (1 / 2)),
--   have := (has_sum.prod_fiberwise (prod_nat_summable half_lt_r hf).has_sum
--     (λ b, (H b).has_sum)).summable,
--   dsimp [ϕ] at this,
--   apply summable_of_nonneg_of_le (λ b, _) (λ b, _) this,
--   { exact mul_nonneg (mul_nonneg one_half_pos.le (norm_nonneg _)) (r_pos b).le },
--   { simp_rw mul_assoc,
--     rw [tsum_mul_left, mul_le_mul_left (@one_half_pos ℝ _), tsum_mul_right,
--       mul_le_mul_right (r_pos b)],
--     exact norm_tsum_le_tsum_norm (smaller_shift b) }
-- end
-- lemma summable_convolution {r : ℝ≥0} (half_lt_r : 1 / 2 < r) (f : ℤ → ℤ) (d : ℤ)
--   (hf : summable (λ n, ∥ f n ∥ * r ^ n)) (hd : ∀ n : ℤ, n < d → f n = 0)
--   (hd_shift : ∀ (n : ℤ), n < d → ∥∑' (i : ℕ), (f (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ = 0) :
--   summable (λ n : ℤ, (1 / 2) * ∥ tsum (λ i : ℕ, ((f (n + 1 + i)) : ℝ) * (1 / 2) ^ i) ∥ * r ^ n) :=
-- begin
--   suffices h_on_nat : summable (λ (n : ℕ),
--     (1 / 2) * ∥∑' (i : ℕ), (f (n + 1 + i) : ℝ) * (1 / 2) ^ i∥ * (r : ℝ) ^ n),
--   { simp_rw mul_assoc at ⊢ h_on_nat,
--     rw [← summable_mul_left_iff (ne_of_gt (@one_half_pos ℝ _))] at ⊢ h_on_nat,
--     refine (summable_iff_on_nat_less d (λ n hn, _)).mpr _,
--     { rw [hd_shift _ hn, zero_mul] },
--     { exact_mod_cast h_on_nat } },
--   apply fiberwise_summable_norm d half_lt_r hf hd,
-- end
end Summability

end AuxThm69

