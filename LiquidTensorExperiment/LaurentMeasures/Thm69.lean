import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.NatAntidiagonal
import LiquidTensorExperiment.LaurentMeasures.AuxLemmas
import LiquidTensorExperiment.LaurentMeasures.Basic
import LiquidTensorExperiment.LaurentMeasures.Theta
import Mathlib.LinearAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic.Linarith
import LiquidTensorExperiment.ForMathlib.Nnreal

#align_import laurent_measures.thm69

/-!
This file introduces the maps
* `θ`, which is the specialization of evaluation-at-ξ map `ϑ` from `laurent_measures.theta`
  at `ξ=2⁻¹`.
* `ϕ` which corresponds to multiplying a Laurent series in `ℒ S = (laurent_measures r S)`
  for `r = 2^(1/p)` by `T⁻¹-2`.
* `ψ` corresponds to dividing a Laurent series by `(T⁻¹-2)`. It is defined only on series
  vanishing at `2⁻¹`, so that it again takes values in `ℒ S`
* The maps `Θ`, `Φ` and `Ψ` are the "measurifications" of `θ`, `ϕ` and `ψ`,
  so they are morphisms in the right category (**[FAE]** Not here any more!)

The main results are
* `injective_ϕ` stating that `ϕ` is injective;
* `θ_ϕ_complex` stating that `ϕ ∘ θ = 0`; and
* `θ_ϕ_exact` stating that the kernel of `θ` coincides with the image of `ϕ`.
Together with `ϑ_surjective` from `laurent_measures.theta` (specialized at `ξ=2⁻¹`, so that `ϑ` is
`θ`) this is the statement of Theorem 6.9 of `Analytic.pdf` of interest to us, although only "on
elements" and not yet as a Short Exact Sequence in the right category.
-/


noncomputable section

open NNReal Theta LaurentMeasures AuxThm69 Finset

open scoped NNReal Classical BigOperators TopologicalSpace

section Phi

parameter {r : ℝ≥0}

local notation "ℒ" => LaurentMeasures r

variable [Fact (0 < r)]

variable {S : FintypeCat}

def ϕ : ℒ S → ℒ S := fun F => shift 1 F - 2 • F

theorem ϕ_apply (F : ℒ S) (s : S) (n : ℤ) : ϕ F s n = F s (n + 1) - 2 * F s n := by
  simp only [ϕ, sub_apply, nsmul_apply, shift_to_fun_to_fun, nsmul_eq_mul] <;> rfl

theorem ϕ_natural (S T : FintypeCat)
    (f : S ⟶ T) :--[fact (0 < p)] [fact ( p ≤ 1)] :
        ϕ ∘
        LaurentMeasures.mapHom f =
      LaurentMeasures.mapHom f ∘ ϕ :=
  by
  ext F t n
  simp only [ϕ, sum_sub_distrib, mul_sum, Function.comp_apply, map_hom_to_fun, sub_apply,
    nsmul_apply, shift_to_fun_to_fun, map_apply, nsmul_eq_mul, mul_ite, MulZeroClass.mul_zero]

-- squeezed for time
-- #check @ϕ
-- lemma tsum_reindex (F : ℒ S) (N : ℤ) (s : S) : ∑' (l : ℕ), (F s (N + l) : ℝ) * (2 ^ l)⁻¹ =
--  2 ^ N * ∑' (m : {m : ℤ // N ≤ m}), (F s m : ℝ) * (2 ^ m.1)⁻¹ :=
-- begin
--   have h_shift := int_tsum_shift (λ n, (F s n : ℝ) * (2 ^ (-n))) N,
--   simp only at h_shift,
--   simp_rw [subtype.val_eq_coe, ← zpow_neg],
--   rw [← h_shift, ← _root_.tsum_mul_left, tsum_congr],
--   intro n,
--   rw [mul_comm (_ ^ N), mul_assoc, ← (zpow_add₀ (@two_ne_zero ℝ _ _)), neg_add_rev,
--     neg_add_cancel_comm, zpow_neg, zpow_coe_nat, add_comm],
-- end
variable [Fact (r < 1)]

theorem injective_ϕ (F : ℒ S) (H : ϕ F = 0) : F = 0 :=
  by
  dsimp only [ϕ] at H ; rw [sub_eq_zero] at H 
  replace H : ∀ n : ℤ, ∀ s : S, 2 * F s (n - 1) = F s n
  · intro n s
    rw [LaurentMeasures.ext_iff] at H 
    convert (H s (n - 1)).symm using 1
    · rw [two_smul, two_mul]; rfl
    · simp [shift]
  ext s n
  apply Int.inductionOn' n (F.d - 1)
  · refine' lt_d_eq_zero _ _ (F.d - 1) _
    simp only [sub_lt_self_iff, zero_lt_one]
  · intro k h hk₀
    simp [← H (k + 1) s, add_sub_cancel, hk₀, MulZeroClass.mul_zero]
  · intro k h hk₀
    simpa only [hk₀, mul_eq_zero, bit0_eq_zero, one_ne_zero, false_or_iff, zero_apply] using H k s

theorem injective_ϕ' : Function.Injective (ϕ : ℒ S → ℒ S) :=
  by
  let PHI : ComphausFilteredPseudoNormedGroupHom (ℒ S) (ℒ S) :=
    shift 1 - 2 • ComphausFilteredPseudoNormedGroupHom.id
  apply (injective_iff_map_eq_zero PHI.to_add_monoid_hom).mpr
  exact injective_ϕ

end Phi

section MemExact

parameter {p : ℝ≥0}

/-- `r`, or `r(p)`, is `2⁻ᵖ`. -/
def r : ℝ≥0 :=
  2⁻¹ ^ (p : ℝ)

theorem r_pos : 0 < r :=
  suffices 0 < (2 : ℝ≥0)⁻¹ ^ (p : ℝ) by simpa [r]
  rpow_pos (nnreal.inv_pos.mpr zero_lt_two)

instance r_pos' : Fact (0 < r) :=
  ⟨r_pos⟩

theorem r_coe : (2⁻¹ : ℝ) ^ (p : ℝ) = r :=
  by
  have : (2⁻¹ : ℝ) = ((2⁻¹ : ℝ≥0) : ℝ)
  simp only [one_div, Nonneg.coe_inv, NNReal.coe_bit0, Nonneg.coe_one]
  rw [this, ← NNReal.coe_rpow, NNReal.coe_eq]
  rfl

variable [Fact (0 < p)]

theorem r_lt_one : r < 1 := by
  refine' rpow_lt_one nnreal.two_inv_lt_one _
  rw [NNReal.coe_pos]
  exact Fact.out _

instance r_lt_one' : Fact (r < 1) :=
  ⟨r_lt_one⟩

variable {S : FintypeCat}

local notation "ℒ" => LaurentMeasures r

local notation "ℳ" => RealMeasures p

theorem NNReal.rpow_int_cast (x : NNReal) (n : ℤ) : x ^ (n : ℝ) = x ^ n :=
  by
  apply Subtype.ext
  simp

def θ : ℒ S → ℳ S :=
  ϑ 2⁻¹ r p S

theorem θ_natural [Fact (0 < p)] [Fact (p ≤ 1)] (S T : FintypeCat) (f : S ⟶ T) (F : ℒ S) (t : T) :
    θ (map f F) t = RealMeasures.map f (θ F) t :=
  by
  simp only [θ, ϑ, one_div, map_apply, Int.cast_sum, inv_zpow', zpow_neg, RealMeasures.map_apply]
  rw [← tsum_sum]
  · congr; ext n; exact sum_mul
  intros
  rw [mem_filter] at H 
  rcases H with ⟨-, rfl⟩
  have := F.summable i
  refine' Summable.add_compl (_ : Summable (_ ∘ (coe : {n : ℤ | 0 ≤ n} → ℤ))) _
  · have moo :=
      Summable.comp_injective this
        (Subtype.coe_injective : Function.Injective (coe : {n : ℤ | 0 ≤ n} → ℤ))
    refine' Summable.of_norm_bounded _ moo _; clear moo this
    rintro ⟨n, hn : 0 ≤ n⟩
    simp only [Function.comp_apply, Subtype.coe_mk, norm_mul, norm_inv, norm_zpow, Real.norm_two]
    rw [(F i n).norm_cast_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    delta r
    delta r
    rw [(by push_cast : ((2 : ℝ) ^ n)⁻¹ = ((2 ^ n)⁻¹ : NNReal))]
    norm_cast
    rw [← NNReal.rpow_int_cast, ← inv_rpow]
    rw [NNReal.rpow_int_cast]
    set m := n.natAbs with hm
    have hmn : n = m := by rw [hm]; exact Int.eq_natAbs_of_zero_le hn
    rw [hmn]
    norm_cast
    apply pow_le_pow_of_le_left'; clear hn hmn hm m n
    apply NNReal.le_self_rpow' nnreal.two_inv_lt_one.le
    norm_cast
    exact Fact.out _
  · obtain ⟨d, hd⟩ := exists_bdd_filtration r_pos r_lt_one F
    apply summable_of_ne_finset_zero
    -- missing finset
    swap;
    exact Finset.subtype _ (Finset.Ico d 0)
    rintro ⟨z, hz : ¬0 ≤ z⟩ hz2
    simp only [Subtype.coe_mk, mul_eq_zero, Int.cast_eq_zero, inv_eq_zero]
    left
    apply hd
    simp only [mem_subtype, Subtype.coe_mk, mem_Ico, not_and, not_le] at hz2 
    by_contra h
    push_neg at h 
    apply hz
    specialize hz2 h
    push_neg at hz2 
    exact hz2

variable [Fact (p < 1)]

theorem half_lt_r : 2⁻¹ < r :=
  calc
    (2⁻¹ : ℝ≥0) = 2⁻¹ ^ (1 : ℝ) := (rpow_one (2⁻¹ : ℝ≥0)).symm
    _ < r :=
      rpow_lt_rpow_of_exponent_gt (by rw [nnreal.inv_pos]; norm_num)
          (by apply nnreal.inv_lt_one; norm_num) <|
        (NNReal.coe_lt_coe.mpr (Fact.out _)).trans_le NNReal.coe_one.le

theorem one_lt_two_r : 1 < 2 * r := by
  have := half_lt_r
  have this2 : (2⁻¹ : ℝ) < r
  assumption_mod_cast
  rw [inv_pos_lt_iff_one_lt_mul'] at this2 ; assumption_mod_cast
  norm_num

theorem r_inv_lt_2 : r⁻¹ < 2 := by
  rw [← inv_inv (2 : ℝ≥0)]
  exact NNReal.inv_lt_inv (by norm_num) half_lt_r

theorem LaurentMeasures.summable_half (F : ℒ S) (s : S) : Summable fun n => (F s n : ℝ) * 2⁻¹ ^ n :=
  AuxThm69.summable_smaller_radius F.d (F.Summable s) (fun n hn => lt_d_eq_zero _ _ _ hn) half_lt_r

theorem θ_ϕ_complex (F : ℒ S) : (θ ∘ ϕ) F = 0 :=
  by
  have t0 : (2 : ℝ)⁻¹ ≠ 0 := inv_ne_zero two_ne_zero
  funext s
  convert_to ∑' n : ℤ, (F s (n + 1) - 2 * F s n : ℝ) * 2⁻¹ ^ n = 0
  · apply tsum_congr
    intro b
    field_simp [ϕ]
  simp_rw [sub_mul]
  rw [tsum_sub, sub_eq_zero]
  -- old proof was slicker :-(
  · refine' tsum_eq_tsum_of_ne_zero_bij (fun i => (i.val : ℤ) - 1) _ _ _
    · rintro ⟨x, _⟩ ⟨y, _⟩ h; dsimp at *; linarith
    · rintro x hx
      refine' ⟨⟨x + 1, _⟩, _⟩
      · rw [Function.mem_support] at hx ⊢
        convert hx using 1
        simp [zpow_add₀]
        ring
      · simp
    · rintro ⟨i, hi⟩
      simp [zpow_sub₀]
      ring
  · rw [← (Equiv.addGroupAdd (-1 : ℤ)).summable_iff]
    simp only [Function.comp, one_div, inv_zpow', Equiv.addGroupAdd_apply, neg_add_cancel_comm]
    convert Summable.mul_right 2 (F.summable_half s)
    ext x
    simp [zpow_add₀]; ring
  · simp_rw [mul_assoc]
    convert (F.summable_half s).mul_left 2

/-!

### Definition of ψ

This involves dividing by T⁻¹ - 2 and we have to check that this process converges.
The proof below is pretty icky. It's "do some trivial rearrangements and it boils
down to the fact that you can interchange the order of summation in a ℝ≥0-valued
sum of sums"

-/


theorem NNReal.summable_hMul_left_iff {X : Type _} {f : X → ℝ≥0} {a : ℝ≥0} (ha : a ≠ 0) :
    Summable f ↔ Summable fun x : X => a * f x :=
  by
  rw [← NNReal.summable_coe, ← NNReal.summable_coe]
  rw [summable_mul_left_iff (by exact_mod_cast ha : (a : ℝ) ≠ 0)]
  apply summable_congr
  intro b
  norm_cast

theorem psi_def_summable {S : FintypeCat} (n : ℕ) (F : ℒ S) (s : S) :
    Summable fun k : ℕ => r ^ (F.d + ↑n) * (2⁻¹ ^ (k : ℤ) * ‖(F s (F.d + ↑n + ↑k))‖₊) :=
  by
  have := F.summable_half s
  apply Summable.mul_left
  have h : (2⁻¹ : ℝ≥0) ≠ 0 := by norm_num
  rw [NNReal.summable_hMul_left_iff (show (2⁻¹ : ℝ≥0) ^ (F.d + n) ≠ 0 from zpow_ne_zero _ h)]
  simp only [← mul_assoc, ← zpow_add₀ h]
  have this2 := lt_d_eq_zero F s
  rw [← summable_norm_iff] at this 
  simp_rw [← _root_.coe_nnnorm] at this 
  rw [summable_coe] at this 
  rw [Nnreal.summable_iff_on_nat_less_shift F.d _ (F.d + n)] at this 
  · convert this
    ext1 k
    rw [mul_comm]
    simp only [inv_zpow', neg_add_rev, nnnorm_mul, nnnorm_zpow, Real.nnnorm_two]
    congr
  · intro n hn
    simp [this2 n hn]

theorem psi_def_summable2 {S : FintypeCat} [Fact (0 < p)] [Fact (p < 1)] (F : ℒ S) (s : ↥S) :
    ∀ k : ℕ,
      Summable fun n : ℕ =>
        r ^ (F.d + ↑n) * ((2⁻¹ : ℝ≥0) ^ (k : ℤ) * ‖(F s (F.d + ↑n + ↑k))‖₊) :=
  by
  intro k
  have hhalf : (2⁻¹ : ℝ≥0) ≠ 0 := by norm_num
  have hhalf' : (2⁻¹ : ℝ≥0) ≠ 0 := by norm_num
  have hr : r ≠ 0 := r_pos.ne.symm
  rw [NNReal.summable_hMul_left_iff
      (show (2⁻¹ : ℝ≥0) ^ (-(k : ℤ)) * r ^ (k : ℤ) ≠ 0 from
        mul_ne_zero (zpow_ne_zero _ hhalf') (zpow_ne_zero _ hr))]
  have :
    ∀ x : ℕ,
      2⁻¹ ^ (-(k : ℤ)) * r ^ (k : ℤ) *
          (r ^ (F.d + ↑x) * (2⁻¹ ^ (k : ℤ) * ‖(F s (F.d + ↑x + ↑k))‖₊)) =
        r ^ (F.d + x + k) * ‖(F s (F.d + ↑x + ↑k))‖₊ :=
    by
    intro x
    rw [show
        (2⁻¹ : ℝ≥0) ^ (-(k : ℤ)) * r ^ (k : ℤ) *
            (r ^ (F.d + ↑x) * (2⁻¹ ^ (k : ℤ) * ‖(F s (F.d + ↑x + ↑k))‖₊)) =
          (2⁻¹ : ℝ≥0) ^ (-(k : ℤ)) * 2⁻¹ ^ (k : ℤ) * r ^ (k : ℤ) * r ^ (F.d + ↑x) *
            ‖(F s (F.d + ↑x + ↑k))‖₊
        by ring]
    simp only [zpow_add₀ hr, ← zpow_add₀ hhalf']
    simp
    left
    ring
  rw [summable_congr this]; clear this
  have := F.summable' s
  rw [Nnreal.summable_iff_on_nat_less_shift F.d _ (F.d + k)] at this 
  · convert this
    ext n
    rw [mul_comm, add_right_comm]
    rfl
  · intro n hn
    convert MulZeroClass.zero_mul _
    convert nnnorm_zero
    exact lt_d_eq_zero F s n hn

theorem psi_def_summable3 {S : FintypeCat} [Fact (0 < p)] [Fact (p < 1)] (F : ℒ S) (s : ↥S) :
    Summable fun k : ℕ =>
      ∑' n : ℕ, r ^ (F.d + ↑n) * (2⁻¹ ^ (k : ℤ) * ‖(F s (F.d + ↑n + ↑k))‖₊) :=
  by
  -- take 2⁻¹^k out the tsum,
  -- put r^k into the tsum,
  -- bounded by sum of GP,
  have bdd :
    ∀ k : ℕ,
      ∑' n : ℕ, r ^ (F.d + ↑n + k) * ‖(F s (F.d + ↑n + ↑k))‖₊ ≤
        ∑' t : ℤ, r ^ t * ‖F s t‖₊ :=
    by
    intro k
    simp_rw [add_right_comm]
    have hinj : Function.Injective fun m : ℕ => F.d + k + m :=
      by
      rintro a b (h2 : F.d + k + a = F.d + k + b)
      simpa using h2
    refine' tsum_le_tsum_of_inj _ hinj _ _ _ _
    · intros; apply zero_le'
    · intro; rfl
    · rw [←
        @Nnreal.summable_iff_on_nat_less_shift (fun z : ℤ => r ^ z * ‖F s z‖₊) F.d _
          (F.d + k)]
      · convert F.summable' s
        ext z
        rw [mul_comm]
        rfl
      · intro n hn
        simp [lt_d_eq_zero F s n hn]
    · convert F.summable' s
      ext z
      rw [mul_comm]
      rfl
  have :
    ∀ k : ℕ,
      ∑' n : ℕ, r ^ (F.d + ↑n) * (2⁻¹ ^ (k : ℤ) * ‖(F s (F.d + ↑n + ↑k))‖₊) =
        (∑' n : ℕ, r ^ (F.d + ↑n + k) * ‖(F s (F.d + ↑n + ↑k))‖₊) * (2⁻¹ * r⁻¹) ^ (k : ℤ) :=
    by
    intro k
    rw [← NNReal.tsum_mul_right]
    apply tsum_congr
    intro n
    simp only [zpow_add₀ r_pos.ne.symm, zpow_ofNat, one_div, inv_pow, div_zpow]
    have foo : (2 * r) ^ k ≠ 0 := by
      apply pow_ne_zero; apply mul_ne_zero
      · norm_num
      · exact r_pos.ne.symm
    field_simp [foo]
    rw [mul_pow]
    ring
  rw [summable_congr this]; clear this
  suffices Summable fun k : ℕ => (∑' t : ℤ, r ^ t * ‖F s t‖₊) * (2⁻¹ * r⁻¹) ^ k
    by
    refine' summable_of_le _ this
    intro k
    rw [zpow_ofNat]
    apply NNReal.hMul_le_hMul_right (bdd k)
  apply Summable.mul_left
  apply summable_geometric
  exact div_lt_one_of_lt half_lt_r

theorem psi_def_aux_4 {S : FintypeCat} [Fact (0 < p)] [Fact (p < 1)] (F : ℒ S) (s : ↥S) :
    Summable fun m : ℕ =>
      ‖((2 : ℝ) ^ (F.d + ↑m))‖₊ *
        ((∑' k : ℕ, ‖(F s (F.d + ↑m + ↑k))‖₊ * 2⁻¹ ^ (F.d + ↑m + ↑k)) * r ^ (F.d + ↑m)) :=
  by
  -- tidy up
  simp_rw [nnnorm_zpow, Real.nnnorm_two]
  have :
    ∀ m : ℕ,
      (2 : ℝ≥0) ^ (F.d + ↑m) *
          ((∑' k : ℕ, ‖(F s (F.d + ↑m + ↑k))‖₊ * 2⁻¹ ^ (F.d + ↑m + ↑k)) * r ^ (F.d + ↑m)) =
        ∑' k : ℕ,
          (2 : ℝ≥0) ^ (F.d + ↑m) * ‖(F s (F.d + ↑m + ↑k))‖₊ * 2⁻¹ ^ (F.d + ↑m + ↑k) *
            r ^ (F.d + ↑m) :=
    by
    intro m
    rw [← NNReal.tsum_mul_right, ← NNReal.tsum_mul_left]
    apply tsum_congr
    intro b
    ring
  rw [summable_congr this]; clear this
  -- TODO : maybe now is the time to tidy up a bit (e.g. cancel the 2^x and 2⁻¹^x)
  suffices
    Summable fun m : ℕ =>
      ∑' k : ℕ, ‖(F s (F.d + ↑m + ↑k))‖₊ * 2⁻¹ ^ (k : ℤ) * r ^ (F.d + ↑m)
    by
    refine' (summable_congr _).2 this
    intro m
    apply tsum_congr
    intro b
    rw [inv_zpow, inv_zpow]
    rw [← zpow_neg, ← zpow_neg]
    have h2 : (2 : ℝ≥0) ≠ 0 := two_ne_zero
    simp only [zpow_add₀, Ne.def, bit0_eq_zero, one_ne_zero, not_false_iff, zpow_ofNat, neg_add_rev,
      zpow_neg, mul_eq_mul_right_iff]
    field_simp [zpow_ne_zero _ h2]; left
    ring
  simp_rw [mul_comm]
  -- change order of summation
  apply NNReal.summable_symm
  -- check various things are summable
  have := F.summable_half s
  · intro n
    apply psi_def_summable
  · apply psi_def_summable2
  -- sum is then bounded above by a GP.
  · apply psi_def_summable3

theorem psi_def_aux_3 {S : FintypeCat} [Fact (0 < p)] [Fact (p < 1)] (F : ℒ S) (s : ↥S) :
    Summable fun n : ℤ =>
      ‖(-(2 : ℝ) ^ (n - 1))‖₊ *
        ite (F.d ≤ n) ((∑' k : ℕ, ‖(F s (n + ↑k))‖₊ * 2⁻¹ ^ (n + ↑k)) * r ^ n) 0 :=
  by
  -- get rid of factor of -2⁻¹
  simp_rw [_root_.nnnorm_neg, zpow_sub₀ (two_ne_zero : (2 : ℝ) ≠ 0), nnnorm_div, zpow_one,
    div_eq_mul_inv _ (‖2 : ℝ‖₊), mul_comm _ (‖2 : ℝ‖₊)⁻¹, mul_assoc]
  apply Summable.mul_left
  have hinj : Function.Injective fun m : ℕ => F.d + m :=
    by
    rintro a b (h2 : F.d + a = F.d + b)
    simpa using h2
  -- change outer sum to m : ℕ with n : ℤ = F.d + m
  suffices :
    Summable fun m : ℕ =>
      ‖((2 : ℝ) ^ (F.d + m))‖₊ *
        ((∑' k : ℕ, ‖(F s (F.d + m + ↑k))‖₊ * 2⁻¹ ^ (F.d + m + ↑k)) * r ^ (F.d + m))
  refine' NNReal.summable_of_comp_injective hinj _ _
  · intro a ha
    rw [if_neg]; simp
    intro hda; apply ha
    use(a - F.d).toNat
    simp; rw [Int.toNat_of_nonneg]; ring; linarith
  · refine' (summable_congr _).1 this
    simp
  exact psi_def_aux_4 F s

theorem psi_def_aux_2 {S : FintypeCat} [Fact (0 < p)] [Fact (p < 1)] (F : ℒ S) (s : ↥S) :
    Summable fun n : ℤ =>
      ite (F.d ≤ n)
        (‖(-(2 : ℝ) ^ (n - 1) * ∑' k : ℕ, ↑(F s (n + ↑k)) * 2⁻¹ ^ (n + ↑k) * r ^ n)‖₊) 0 :=
  by
  simp_rw [nnnorm_mul]
  -- next : put norm inside inner tsum (a one way implication)
  suffices :
    Summable fun n : ℤ =>
      ‖(-(2 : ℝ) ^ (n - 1))‖₊ *
        ite (F.d ≤ n) ((∑' k : ℕ, ‖(F s (n + ↑k))‖₊ * 2⁻¹ ^ (n + ↑k)) * r ^ n) 0
  refine' summable_of_le _ this
  · intro n
    split_ifs
    · simp only [_root_.nnnorm_neg, nnnorm_zpow, Real.nnnorm_two, one_div, inv_zpow', neg_add_rev]
      refine' mul_le_mul_of_nonneg_left _ _
      · refine' le_trans (nnnorm_tsum_le _) _
        · clear this; have := F.summable_half s
          simp_rw [nnnorm_mul]
          apply Summable.mul_right
          rw [← summable_norm_iff] at this 
          simp_rw [← _root_.coe_nnnorm] at this 
          rw [NNReal.summable_coe] at this 
          have hinj : Function.Injective fun b : ℕ => n + b :=
            by
            rintro a b (h2 : n + a = n + b)
            simpa using h2
          convert summable_comp_injective this hinj
          ext1 k
          simp [← zpow_neg]
        · rw [← NNReal.tsum_mul_right]
          apply le_of_eq
          apply tsum_congr
          · intro k
            simp only [nnnorm_mul, nnnorm_zpow, Real.nnnorm_two, nnnorm_eq, mul_eq_mul_right_iff]
            left; left
            congr
      · simp
    · simp
  exact psi_def_aux_3 _ _

theorem psi_def_aux {S : FintypeCat} [Fact (0 < p)] [Fact (p < 1)] (F : ℒ S) (s : ↥S) :
    Summable fun n : ℤ =>
      ‖(ite (F.d ≤ n) (-(2 : ℝ) ^ (n - 1) * ∑' k : ℕ, ↑(F s (n + ↑k)) * 2⁻¹ ^ (n + ↑k)) 0)‖₊ *
        r ^ n :=
  by
  suffices :
    Summable fun n : ℤ =>
      ite (F.d ≤ n)
        (‖(-(2 : ℝ) ^ (n - 1) * ∑' k : ℕ, ↑(F s (n + ↑k)) * 2⁻¹ ^ (n + ↑k) * r ^ n)‖₊) 0
  refine' summable_of_le _ this
  · intro n
    split_ifs
    · apply le_of_eq
      simp_rw [_root_.tsum_mul_right]
      rw [← mul_assoc, nnnorm_mul _ ((r : ℝ) ^ n)]
      simp
    · simp
  exact psi_def_aux_2 _ _

def ψ (F : ℒ S) (hF : θ F = 0) : ℒ S
    where
  toFun s n := if F.d ≤ n then ∑ l in range (n - F.d).natAbs.succ, F s (n - 1 - l) * 2 ^ l else 0
  summable' s :=
    by
    -- make everything real
    change
      Summable fun n : ℤ =>
        ‖((ite (F.d ≤ n) (∑ l : ℕ in range (n - F.d).natAbs.succ, F s (n - 1 - ↑l) * 2 ^ l) 0 :
                ℤ) :
              ℝ)‖₊ *
          r ^ n
    push_cast
    -- hypothesis that infinite sum converges at r>2⁻¹
    -- get hypothesis that infinite sum is 0 at 2⁻¹
    simp only [θ, ϑ] at hF 
    replace hF := congr_fun hF s; dsimp at hF 
    -- change sum from ℤ to ℕ
    --rw nnreal.summable_iff_on_nat_less F.d, swap,
    --{ intros n hn, simp [if_neg hn.not_le] },
    have h1 :
      ∀ n : ℤ,
        ite (F.d ≤ n) (∑ l : ℕ in range (n - F.d).natAbs.succ, (F s (n - 1 - ↑l) : ℝ) * 2 ^ l) 0 =
          ite (F.d ≤ n) (-(2 : ℝ) ^ (n - 1) * ∑' k : ℕ, F s (n + k) * 2⁻¹ ^ (n + k)) 0 :=
      by
      intro n
      split_ifs with hn; swap; rfl
      rw [← inv_mul_eq_iff_eq_mul₀, ← neg_inv, neg_mul, mul_sum, neg_eq_iff_add_eq_zero, ← hF]
      swap; exact neg_ne_zero.2 (zpow_ne_zero _ two_ne_zero)
      convert
        @tsum_add_tsum_compl ℝ ℤ _ _ _ _ _ {x : ℤ | x < n} (Summable.subtype (F.summable_half s) _)
          (Summable.subtype (F.summable_half s) _) using
        2
      · simp_rw [← inv_zpow, mul_comm ((2⁻¹ : ℝ) ^ (n - 1)), mul_assoc]
        simp_rw [show ∀ x : ℕ, (2 : ℝ) ^ x = 2⁻¹ ^ (-(x : ℤ)) by intros; simp]
        simp_rw [← zpow_add₀ (by norm_num : (2⁻¹ : ℝ) ≠ 0), add_comm, ← sub_eq_add_neg]
        rw [← tsum_eq_sum]
        convert
          @Equiv.tsum_eq ℝ _ _ _ _ _
            (⟨fun m =>
                ⟨n - 1 - m, lt_of_le_of_lt (sub_le_self _ (Int.ofNat_zero_le m)) (sub_one_lt n)⟩,
                fun z => (n - 1 - z.1).natAbs, fun m => by simp, fun ⟨z, hz⟩ =>
                Subtype.ext
                  (by
                    --             squeeze_simp,
                    change n - 1 - (n - 1 - z).natAbs = z
                    rw [← Int.eq_natAbs_of_zero_le (sub_nonneg_of_le (Int.le_sub_one_of_lt hz))]
                    ring)⟩ :
              ℕ ≃ { z : ℤ // z < n })
            _
        · ext; rfl
        · intro b hb
          rw [mul_eq_zero]; left
          norm_cast
          apply lt_d_eq_zero
          by_contra h; push_neg at h ; apply hb
          rw [mem_range, Nat.succ_eq_add_one, ← Int.ofNat_lt, Int.ofNat_add, ←
              Int.eq_natAbs_of_zero_le] <;>
            linarith
      · convert
          @Equiv.tsum_eq ℝ _ _ _ _ _
            (⟨fun x => ⟨n + x, (Int.le.intro rfl).not_lt⟩, fun z => (z.1 - n).natAbs, fun x => by
                simp, fun ⟨x, hx⟩ =>
                Subtype.ext
                  (by
                    change n + _ = x
                    rw [← Int.eq_natAbs_of_zero_le (sub_nonneg.2 (le_of_not_lt hx))]
                    exact add_eq_of_eq_sub' rfl)⟩ :
              ℕ ≃ { z : ℤ // ¬z < n })
            _
        ext; rfl
    suffices
      Summable fun n : ℤ =>
        ‖(ite (F.d ≤ n) (-(2 : ℝ) ^ (n - 1) * ∑' k : ℕ, ↑(F s (n + k)) * 2⁻¹ ^ (n + k)) 0)‖₊ *
          r ^ n
      by
      refine' (summable_congr _).2 this
      intro n
      congr 2
      apply h1 n
    clear h1
    clear hF
    exact psi_def_aux F s

theorem θ_ϕ_split_exact (F : ℒ S) (hF : θ F = 0) : ϕ (ψ F hF) = F :=
  by
  ext s n
  simp only [ϕ, ψ, sub_apply, shift_to_fun_to_fun, LaurentMeasures.coe_mk, nsmul_apply,
    nsmul_eq_mul, Int.ofNat_succ, Int.ofNat_zero, zero_add]
  split_ifs with h1 h2
  · rw [sum_range_succ', (by norm_num : (1 : ℤ) + 1 = 2), mul_sum]
    convert add_sub_cancel' _ _
    · rw [Nat.succ_eq_add_one, (by ring : n + 1 - F.d = n - F.d + 1)]
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h2)
      rw [hm]
      norm_cast
    · ext
      push_cast
      ring
      congr 2
      ring
    · simp
  · have hF : F.d = n + 1; linarith
    simp [hF]
  · linarith
  · exact (lt_d_eq_zero F s n (not_le.mp h)).symm

theorem θ_ϕ_exact (F : ℒ S) (hF : θ F = 0) : ∃ G, ϕ G = F :=
  ⟨ψ F hF, θ_ϕ_split_exact F hF⟩

end MemExact

