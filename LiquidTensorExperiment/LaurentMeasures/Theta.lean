import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Data.Real.NNReal
import LiquidTensorExperiment.LaurentMeasures.Basic
import Mathlib.Order.Filter.AtTopBot
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.RealMeasures.Default
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.PowerSeries.Basic

#align_import laurent_measures.theta

/-! SECTIONS
Everything takes place in the `namespace theta`

* Section `aux_lemmas` contain some technicalities concerning convergent sequence
* Section `summability` shows that the series defining `ϑ` converges
* In Section `theta_surjective` We define the map ϑ : (laurent_measures r `S`) → ℝ and we
  show it is surjective.
* Section `ker_theta` studies the kernel of `ϑ`, in particular showing it is principal.

   VARIABLES
* The variable `ξ : ℝ` here corresponds to `r'` of `Analytic.pdf`, so that, for every `r`, `ϑ ξ r`
  is`θ_r'` as a map from `r`-convergent Laurent measures to `ℝ`. It is supposed to be positive almost
everywhere, and this is recorded as a `fact`.
* The variable `x : ℝ` is defined globally in Sections `aux_lemmas` and `summability`.
* The variable `r : ℝ≥0` (specifying the radius of convergency of `laurent_measures` makes its
  first appearance in Section `theta_surjective`, but it is not globally defined. Whenever it occurs
  it is assumed to be positive and strictly smaller than `1`, both recorded as facts.
-/
noncomputable section

open Set Filter Function Classical Finset Nat

open scoped TopologicalSpace Classical NNReal BigOperators

-- def laurent_measures.to_Rfct (r : ℝ≥0) :
--   (laurent_measures r (Fintype.of punit)) → (ℤ → ℤ) := λ ⟨F, _⟩, (F punit.star)
namespace Theta

variable (ξ : ℝ)

/-- The basic function computing the **integer-valued** `ξ`-adic expansion of `x` -/
noncomputable def y (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => y n - (⌊(y n / ξ ^ n : ℝ)⌋ : ℝ) * ξ ^ n

section AuxLemmas

variable (x : ℝ)

variable [Fact (0 < ξ)]

theorem bdd_floor : BddAbove (range fun n : ℕ => (⌊y ξ x n / ξ ^ n⌋ : ℝ)) :=
  by
  use(max x ξ⁻¹ : ℝ)
  intro z hz
  obtain ⟨m, h_mz⟩ := Set.mem_range.mp hz
  by_cases hm : m = 0
  · rw [hm, pow_zero, div_one] at h_mz 
    rw [← h_mz, y, le_max_iff]
    apply Or.intro_left
    exact Int.floor_le x
  rw [← h_mz]
  apply (Int.floor_le _).trans
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm
  rw [hk, y]
  have : ξ ^ k ≠ 0 := ne_of_gt (pow_pos (Fact.out _) k)
  calc
    (y ξ x k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k) / ξ ^ (k + 1) =
        (y ξ x k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k) / (ξ ^ k * ξ) :=
      by rw [pow_add, pow_one]
    _ = (y ξ x k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k) / ξ ^ k / ξ := by field_simp
    _ = (y ξ x k / ξ ^ k - ↑⌊y ξ x k / ξ ^ k⌋ * ξ ^ k / ξ ^ k) / ξ := by rw [sub_div]
    _ = (y ξ x k / ξ ^ k - ↑⌊y ξ x k / ξ ^ k⌋) / ξ := by
      simp only [mul_div_cancel, this, Ne.def, not_false_iff]
    _ ≤ 1 / ξ := (div_le_div_of_le (le_of_lt _) (le_of_lt _))
    _ ≤ max x ξ⁻¹ := by field_simp
  exact Fact.out _
  · rw [sub_lt_iff_lt_add, add_comm]; exact Int.lt_floor_add_one _

theorem eventually_pos_y : ∀ n : ℕ, n ≥ 1 → 0 ≤ y ξ x n :=
  by
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := fun n _ => pow_pos (Fact.out _) n
  have : ∀ n : ℕ, n ≥ 1 → y ξ x n / ξ ^ n ≥ ⌊(y ξ x n / ξ ^ n : ℝ)⌋ := fun n _ => Int.floor_le _
  intro n hn₁
  by_cases hn₀ : n = 1
  · rw [hn₀, y, pow_zero, div_one, mul_one, sub_nonneg]; apply Int.floor_le
  · replace hn₁ : n > 1; · apply lt_of_le_of_ne hn₁; tauto
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m ≥ 1 ∧ n = m + 1
    use⟨n - 1, And.intro (Nat.le_pred_of_lt hn₁) (Nat.sub_add_cancel (le_of_lt hn₁)).symm⟩
    rw [hm.2, y]
    replace this := (le_div_iff (h_pos m hm.1)).mp (this m hm.1)
    rwa [← sub_nonneg] at this 

theorem eventually_pos_floor : ∀ n : ℕ, n ≥ 1 → (⌊y ξ x n / ξ ^ n⌋ : ℝ) ≥ 0 :=
  by
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := fun n _ => pow_pos (Fact.out _) n
  intro n hn
  norm_cast
  apply int.floor_nonneg.mpr
  exact div_nonneg (eventually_pos_y ξ x n hn) (le_of_lt (h_pos n hn))

theorem eventually_le : ∀ n, n ≥ 1 → y ξ x (n + 1) ≤ y ξ x n :=
  by
  have h_pos : ∀ n : ℕ, n ≥ 1 → ξ ^ n > 0 := fun n _ => pow_pos (Fact.out _) n
  intro n hn
  rw [y]
  apply sub_le_self (y ξ x n)
  apply mul_nonneg _ (le_of_lt (h_pos n hn))
  exact eventually_pos_floor ξ x n hn

theorem eventually_le_one {n : ℕ} (hn : n ≥ 1) : y ξ x n ≤ y ξ x 1 :=
  by
  induction' hn with n hn h_ind
  exact le_of_eq (refl _)
  have := (eventually_le ξ x n hn).trans h_ind
  rwa [Nat.succ_eq_add_one]

def auxY : ℕ → ℝ := fun n => if n = 0 then y ξ x 1 else y ξ x n

theorem eventually_antitone : Antitone (auxY ξ x) :=
  by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn : n = 0
  · rw [hn, zero_add, Theta.auxY]
    simp only [Nat.one_ne_zero, if_true, eq_self_iff_true, if_false]
  · simp only [Theta.auxY, if_neg hn, Function.comp_apply, Nat.succ_ne_zero, if_false]
    replace hn : n ≥ 1 := le_of_not_gt ((not_iff_not.mpr Nat.lt_one_iff).mpr hn)
    exact eventually_le ξ x n hn

theorem limit_neg_geometric [Fact (ξ < 1)] : Tendsto (fun i : ℕ => -ξ ^ i) atTop (𝓝 0) :=
  by
  apply Summable.tendsto_atTop_zero
  rw [summable_neg_iff]
  apply summable_geometric_of_abs_lt_1
  rw [abs_of_pos]
  all_goals exact Fact.out _

end AuxLemmas

section Summability

variable (x : ℝ)

theorem finite_sum (n : ℕ) :
    (y ξ x (n + 1) : ℝ) = x - ∑ i in range (n + 1), (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i :=
  by
  induction' n with n h_ind
  · rw [zero_add, range_one, sum_singleton]; rfl
  · replace h_ind :
      (x - y ξ x (n + 1) : ℝ) = ∑ i in range (n + 1), (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i := by
      rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', h_ind]
    nth_rw_rhs 3 [Nat.succ_eq_add_one, ← Nat.succ_eq_add_one, range_succ]
    rw [sum_insert, Nat.succ_eq_add_one, ← sub_sub, ← h_ind, sub_sub, add_sub, add_comm _ x, ←
      add_sub, ← sub_sub, sub_self, zero_sub, neg_sub]
    rfl
    simp

theorem finite_sum' (n : ℕ) :
    x - (y ξ x n : ℝ) = ∑ i in range n, (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i :=
  by
  by_cases hn : n = 0
  · rw [hn, range_zero, sum_empty, sub_eq_zero]; rfl
  · replace hn : n ≥ 1 := le_of_not_gt ((not_iff_not.mpr Nat.lt_one_iff).mpr hn)
    rw [← Nat.sub_add_cancel hn, finite_sum ξ x (n - 1)]
    simp only [sub_sub_cancel] at *

variable [Fact (0 < ξ)]

theorem exists_limit_y : ∃ a, Tendsto (fun n => y ξ x n) atTop (𝓝 a) :=
  by
  have h_bdd : BddBelow (range (Theta.auxY ξ x)) := by
    use 0
    intro z hz
    obtain ⟨m, h_mz⟩ := Set.mem_range.mp hz
    by_cases hm : m = 0
    · simp_rw [hm, Theta.auxY, if_pos] at h_mz 
      rw [← h_mz]
      exact eventually_pos_y ξ x 1 (le_of_eq (refl _))
    simp_rw [Theta.auxY, if_neg hm] at h_mz 
    rw [← h_mz]
    replace hm : m ≥ 1 := le_of_not_gt ((not_iff_not.mpr Nat.lt_one_iff).mpr hm)
    exact eventually_pos_y ξ x m hm
  have := tendsto_atTop_ciInf (eventually_antitone ξ x) h_bdd
  use⨅ i : ℕ, Theta.auxY ξ x i
  apply @Tendsto.congr' _ _ (Theta.auxY ξ x) _ _ _ _ this
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  use{n | n ≥ 1}
  simp only [Filter.mem_atTop_sets, ge_iff_le, Set.mem_setOf_eq]
  use 1
  simp only [imp_self, forall_const]
  intro n hn
  replace hn : n ≥ 1 := by simp_all only [ge_iff_le, Set.mem_setOf_eq]
  have := ne_of_lt (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Theta.auxY, ite_eq_right_iff]
  tauto

theorem summable_norm (r : ℝ≥0) (hr₁ : r < 1) :
    Summable fun i => ‖⌊‖(y ξ x i / ξ ^ i : ℝ)⌋ * r ^ i :=
  by
  by_cases hr₀ : r = 0
  · rw [hr₀]
    apply @summable_of_ne_finset_zero _ _ _ _ _ (range 1)
    simp only [Int.cast_eq_zero, NNReal.coe_zero, zero_pow_eq_zero, Finset.mem_singleton,
      mul_eq_zero, range_one]
    intro _ hb
    exact Or.intro_right _ (Nat.pos_of_ne_zero hb)
  have h_nonneg : ∀ n : ℕ, n ≥ 1 → (r ^ n : ℝ) ≥ 0 := fun n _ => pow_nonneg r.2 n
  have H : ∀ j : { i // i ∉ range 1 }, j.1 ≥ 1 :=
    by
    rintro ⟨n, h_n⟩
    simp only [ge_iff_le, Finset.mem_singleton, range_one] at h_n 
    exact le_of_not_gt ((not_iff_not.mpr Nat.lt_one_iff).mpr h_n)
  apply (Finset.summable_compl_iff (Finset.range 1)).mp
  swap; infer_instance
  have h_nonneg : ∀ i : { i // i ∉ range 1 }, ‖⌊‖(y ξ x i.1 / ξ ^ i.1 : ℝ)⌋ * r ^ i.1 ≥ 0 :=
    by
    intro i
    apply mul_nonneg _ (h_nonneg i.1 (H i))
    simp only [norm_nonneg]
  obtain ⟨μ, hμ⟩ := bdd_floor ξ x
  have h_bdd : ∀ i : { i // i ∉ range 1 }, ‖⌊‖(y ξ x i.1 / ξ ^ i.1 : ℝ)⌋ ≤ μ :=
    by
    rw [upperBounds] at hμ 
    simp_all only [forall_apply_eq_imp_iff, lt_one_iff, Set.mem_range, forall_const,
      forall_exists_index, NNReal.zero_le_coe, ge_iff_le, Set.mem_setOf_eq, imp_true_iff,
      instNonempty, Subtype.forall, pow_nonneg, Finset.mem_range, Subtype.val_eq_coe]
    intro a ha
    rw [Subtype.coe_mk, Int.norm_eq_abs]
    replace ha : a ≥ 1 := le_of_not_gt ((not_iff_not.mpr Nat.lt_one_iff).mpr ha)
    rwa [abs_eq_self.mpr (eventually_pos_floor ξ x a ha)]
    exact hμ a
  replace h_bdd :
    ∀ i : { i // i ∉ range 1 }, ‖⌊‖(y ξ x i.1 / ξ ^ i.1 : ℝ)⌋ * r ^ i.1 ≤ μ * r ^ i.1
  · intro i
    rw [mul_le_mul_right]
    exacts [h_bdd i, pow_pos ((Ne.symm hr₀).le_iff_lt.mp r.2) i.1]
  apply Summable.of_nonneg_of_le h_nonneg h_bdd
  apply (@Finset.summable_compl_iff _ _ _ _ _ (fun i => μ * r ^ i) (Finset.range 1)).mpr
  apply Summable.mul_left
  apply summable_geometric_of_abs_lt_1
  rwa [← NNReal.val_eq_coe, abs_eq_self.mpr r.2]

theorem summable_nnnorm (r : ℝ≥0) (hr₁ : r < 1) :
    Summable fun i => ‖⌊‖₊(y ξ x i / ξ ^ i : ℝ)⌋ * r ^ i := by
  simpa only [← NNReal.summable_coe, Nonneg.coe_mul, coe_nnnorm, NNReal.coe_pow] using
    summable_norm ξ x r hr₁

theorem summable_floor (r : ℝ≥0) (hr₁ : r < 1) :
    Summable fun i => (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * r ^ i :=
  by
  have h_norm_eq :
    (fun i : ℕ => ‖⌊y‖ ξ x i / ξ ^ i⌋ * (r ^ i : ℝ)) = fun i : ℕ =>
      ‖((⌊y ξ x i / ξ ^ i⌋ : ℝ) * r ^ i)‖ :=
    by
    funext
    simp only [norm_mul, norm_pow, NNReal.norm_eq, mul_eq_mul_right_iff]
    rw [Real.norm_eq_abs, Int.norm_eq_abs]
    tauto
  have := summable_norm ξ x r hr₁
  rw [h_norm_eq] at this 
  apply Summable.of_norm this

theorem limit_y [Fact (ξ < 1)] : Tendsto (fun n => y ξ x n) atTop (𝓝 0) :=
  by
  have h_pos : 0 < ξ := Fact.out _
  let ξ₀ : ℝ≥0 := ⟨ξ, le_of_lt (Fact.out _)⟩
  have h_right : ∀ n, n ≥ 1 → (⌊y ξ x n / ξ ^ n⌋ : ℝ) ≤ y ξ x n / ξ ^ n := fun _ _ => Int.floor_le _
  replace h_right : ∀ n, n ≥ 1 → (⌊y ξ x n / ξ ^ n⌋ : ℝ) * ξ ^ n ≤ y ξ x n := fun n hn =>
    (le_div_iff (pow_pos h_pos n)).mp (h_right n hn)
  replace h_right : ∀ᶠ n in Filter.atTop, (⌊y ξ x n / ξ ^ n⌋ : ℝ) * ξ ^ n ≤ y ξ x n
  · simp only [ge_iff_le, Filter.eventually_atTop]; use 1, h_right
  have h_left : ∀ n, n ≥ 1 → y ξ x n / ξ ^ n - 1 ≤ ⌊y ξ x n / ξ ^ n⌋ := fun n hn =>
    le_of_lt (Int.sub_one_lt_floor _)
  replace h_left : ∀ n, n ≥ 1 → y ξ x n - ξ ^ n ≤ ⌊y ξ x n / ξ ^ n⌋ * ξ ^ n
  · have h_one : ∀ n : ℕ, 0 < ξ ^ n := fun n => pow_pos h_pos n
    intro n hn
    calc
      y ξ x n - ξ ^ n = (y ξ x n / ξ ^ n - 1) * ξ ^ n := by
        rw [sub_mul, one_mul, div_mul_cancel _ (h_one _).ne']
      _ ≤ ⌊y ξ x n / ξ ^ n⌋ * ξ ^ n := (mul_le_mul_right (h_one n)).mpr (h_left n hn)
  replace h_left : ∀ᶠ n in Filter.atTop, y ξ x n - ξ ^ n ≤ (⌊y ξ x n / ξ ^ n⌋ : ℝ) * ξ ^ n
  · simp only [Filter.eventually_atTop]; use 1, h_left
  have : tendsto (fun n => y ξ x n - ξ ^ n) Filter.atTop (𝓝 (exists_limit_y ξ x).some) :=
    by
    convert Tendsto.add (exists_limit_y ξ x).choose_spec (limit_neg_geometric ξ)
    rw [add_zero]
  have h₁ :=
    (le_of_tendsto_of_tendsto this (summable_floor ξ x ξ₀ _).tendsto_atTop_zero h_left).antisymm
      (le_of_tendsto_of_tendsto (summable_floor ξ x ξ₀ _).tendsto_atTop_zero
        (exists_limit_y ξ x).choose_spec h_right)
  have := (exists_limit_y ξ x).choose_spec
  rwa [h₁] at this 
  all_goals rw [← NNReal.coe_lt_coe, NNReal.coe_one, Subtype.coe_mk]; exact Fact.out _

theorem hasSum_x [Fact (ξ < 1)] : HasSum (fun i => (⌊(y ξ x i / ξ ^ i : ℝ)⌋ : ℝ) * ξ ^ i) x :=
  by
  let ξ₀ : ℝ≥0 := ⟨ξ, le_of_lt (Fact.out _)⟩
  apply (summable_floor ξ x ξ₀ _).hasSum_iff_tendsto_nat.mpr
  simp_rw [Subtype.coe_mk, ← finite_sum' ξ x, sub_eq_add_neg]
  nth_rw_rhs 1 [← add_zero x]
  apply @Tendsto.const_add ℕ ℝ _ _ _ x 0 _ Filter.atTop
  rw [← neg_zero]
  refine' Tendsto.neg (limit_y ξ x)
  · rw [← NNReal.coe_lt_coe, NNReal.coe_one, Subtype.coe_mk]
    exact Fact.out _

end Summability

section ThetaSurj

/--
The map `ϑ` defined in Theorem 6.9 of Analytic.pdf. Given the definition of `tsum` we do not need
 to require that `r ≤ ξ` to simply define `ϑ`.-/
def sevalℒ {r : ℝ≥0} (S : FintypeCat) (s : S) :
    LaurentMeasures r S → LaurentMeasures r (FintypeCat.of PUnit) := fun F =>
  ⟨fun _ => F s, fun _ => F.2 s⟩

def ϑ₀ (r : ℝ≥0) : LaurentMeasures r (FintypeCat.of PUnit) → ℝ := fun F =>
  tsum fun n => F PUnit.unit n * ξ ^ n

--TODO: remove this
def ϑ (r p : ℝ≥0) (S : FintypeCat) : LaurentMeasures r S → RealMeasures p S := fun F s =>
  tsum fun n => F s n * ξ ^ n

@[nolint unused_arguments]
def ϑ' (r p : ℝ≥0) (S : FintypeCat) : LaurentMeasures r S → S → ℝ := fun F s =>
  (ϑ₀ ξ r) (sevalℒ S s F)

theorem ϑ_eq_ϑ' : ϑ = ϑ' :=
  rfl

def ϑSection (r p : ℝ≥0) (S : FintypeCat) (g : RealMeasures p S) [Fact (r < 1)] [Fact (0 < ξ)]
    [Fact (ξ < 1)] : S → ℤ → ℤ := fun s m => Int.recOn m (fun i => ⌊y ξ (g s) i / ξ ^ i⌋) 0

theorem summable_ϑSection (r p : ℝ≥0) (S : FintypeCat) (g : RealMeasures p S) [Fact (r < 1)]
    [Fact (0 < ξ)] [Fact (ξ < 1)] :
    ∀ s, Summable fun n => ‖((ϑSection ξ r p S g) s n)‖₊ * r ^ n :=
  by
  let F₀ := ϑ_section ξ r p S g
  have hinj : Function.Injective (coe : ℕ → ℤ) := by apply Int.ofNat.inj
  have h_aux : ∀ s : S, ∀ n : ℤ, n ∉ Set.range (coe : ℕ → ℤ) → F₀ s n = 0 :=
    by
    rintro s (_ | _)
    simp only [IsEmpty.forall_iff, Set.mem_range_self, not_true, Int.ofNat_eq_coe]
    intro
    rfl
  have h_range_norm :
    ∀ s : S, ∀ n : ℤ, n ∉ Set.range (coe : ℕ → ℤ) → ‖F₀ s n‖₊ * r ^ n = 0 :=
    by
    intro s n
    specialize h_aux s n
    simp only [h_aux, Int.cast_eq_zero, mul_eq_zero, nnnorm_eq_zero]
    tauto
  intro s
  apply (@Function.Injective.summable_iff _ _ _ _ _ _ _ hinj (h_range_norm s)).mp
  exact summable_nnnorm ξ (g s) r (Fact.out _)

theorem ϑ_surjective (r p : ℝ≥0) (S : FintypeCat) (g : RealMeasures p S) [Fact (r < 1)]
    [Fact (0 < ξ)] [Fact (ξ < 1)] : ∃ F : LaurentMeasures r S, ϑ ξ r p S F = g :=
  by
  have hinj : Function.Injective (coe : ℕ → ℤ) := by apply Int.ofNat.inj
  let F : LaurentMeasures r S := ⟨ϑ_section ξ r p S g, summable_ϑ_section ξ r p S g⟩
  have h_aux : ∀ s : S, ∀ n : ℤ, n ∉ Set.range (coe : ℕ → ℤ) → F s n = 0 :=
    by
    rintro s (_ | _)
    simp only [IsEmpty.forall_iff, Set.mem_range_self, not_true, Int.ofNat_eq_coe]
    intro
    rfl
  have h_range : ∀ s : S, ∀ n : ℤ, n ∉ Set.range (coe : ℕ → ℤ) → (F s n : ℝ) * ξ ^ n = 0 :=
    by
    intro n hn
    specialize h_aux n hn
    simp only [h_aux, Int.cast_eq_zero, mul_eq_zero, nnnorm_eq_zero]
    tauto
  use F
  have : ∀ s : S, HasSum (fun n => (F s n : ℝ) * ξ ^ n) (g s) :=
    by
    intro s
    apply (@Function.Injective.hasSum_iff _ _ _ _ _ _ (g s) _ hinj (h_range s)).mp
    exact Theta.hasSum_x ξ (g s)
  funext
  apply HasSum.tsum_eq
  exact this s

end ThetaSurj

-- theorem ϑ₀_surjective (x : ℝ) (r : ℝ≥0) [fact (r < 1)] [fact (0 < ξ)] [fact (ξ < 1)] :
--   ∃ (F : laurent_measures r (Fintype.of punit)), (ϑ₀ ξ r F) = x :=
-- begin
--   let f₀ : ℤ → ℤ := λ m, int.rec_on m (λ i, ⌊((y ξ x i) / ξ ^ i)⌋) (0),
--   let F₀ : Fintype.of punit → ℤ → ℤ := λ a, f₀,
--   have hinj : function.injective (coe : ℕ → ℤ) := by {apply int.coe_nat_inj},
--   have h_aux : ∀ n : ℤ, n ∉ set.range (coe : ℕ → ℤ) → f₀ n = 0,
--   { rintro ( _ | _ ),
--     simp only [is_empty.forall_iff, set.mem_range_self, not_true, int.of_nat_eq_coe],
--     intro,
--     refl },
--   have h_range : ∀ n : ℤ,
--     n ∉ set.range (coe : ℕ → ℤ) → (F₀ punit.star n : ℝ) * ξ ^ n = 0,
--   swap,
--   have h_range_norm : ∀ n : ℤ,
--     n ∉ set.range (coe : ℕ → ℤ) → ∥F₀ punit.star n ∥ * r ^ n = 0,
--   swap,
--   { have HF₀ : ∀ (s : Fintype.of punit), summable (λ (n : ℤ), ∥F₀ s n∥ * r ^ n),
--     { intro s,
--       apply (@function.injective.summable_iff _ _ _ _ _ _ _ hinj h_range_norm).mp,
--       apply summable_norm ξ x r (fact.out _) },
--     let F : laurent_measures r (Fintype.of punit) := ⟨F₀, HF₀⟩,
--     use F,
--     have : has_sum (λ n, ((F₀ punit.star n) : ℝ) * ξ ^ n) x,
--     { apply (@function.injective.has_sum_iff _ _ _ _ _ _ x _ hinj h_range).mp,
--       exact has_sum_x ξ x },
--     apply has_sum.tsum_eq,
--     exact this },
--   all_goals { intros n hn,
--     specialize h_aux n hn,
--     simp only [h_aux, int.cast_eq_zero, mul_eq_zero, norm_eq_zero],
--     tauto },
-- end
end Theta

