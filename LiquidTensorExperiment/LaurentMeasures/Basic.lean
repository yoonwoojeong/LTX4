import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Analysis.NormedSpace.Basic
import LiquidTensorExperiment.LaurentMeasures.Bounded
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import laurent_measures.basic

universe u

noncomputable section

open scoped BigOperators NNReal Classical

/-
structure c_measures (r : ℝ≥0) (c : ℝ≥0) (S : Fintype) :=
(to_fun     : S → ℤ → ℤ)
(summable   : ∀ s, summable (λ n, (∥ to_fun s n ∥₊ * r ^ n)))
(bdd        : ∀ s, tsum (λ n, (∥ to_fun s n ∥₊ * r ^ n)) ≤ c)
-/
/-- A term of type `laurent_measures r S` is, for each `s : S`, a function `φ : ℤ → ℤ`
  (typically thought of as a power series `∑ φ(n)Tⁿ`) such that `∑ |φ(n)|rⁿ` converges.
  Note that if `0<r<1` then the support of φ can only contain finitely many negative integers.  -/
structure LaurentMeasures (r : ℝ≥0) (S : FintypeCat) where
  toFun : S → ℤ → ℤ
  summable' : ∀ s, Summable fun n => ‖to_fun s n‖₊ * r ^ n

variable {r : ℝ≥0} {S S' : FintypeCat.{u}}

local notation "ℒ" => LaurentMeasures r

namespace LaurentMeasures

instance : CoeFun (ℒ S) fun F => S → ℤ → ℤ :=
  ⟨fun F => F.toFun⟩

@[simp]
theorem coe_mk (f : S → ℤ → ℤ) (hf) (s : S) (n : ℤ) : (@LaurentMeasures.mk r S f hf) s n = f s n :=
  rfl

@[ext]
theorem ext (F G : ℒ S) : (F : S → ℤ → ℤ) = G → F = G := by intro h; cases F; cases G; simpa

theorem ext_iff (F G : ℒ S) : F = G ↔ ∀ s n, F s n = G s n :=
  ⟨fun h => by intros <;> rw [h], fun h => LaurentMeasures.ext F G <| by ext <;> apply h⟩

protected theorem nNReal_summable (F : ℒ S) (s : S) :
    Summable fun n => ‖F s n‖₊ * r ^ n :=
  F.2 _

protected theorem summable (F : ℒ S) (s : S) : Summable fun n => ‖F s n‖ * r ^ n := by
  simpa only [← NNReal.summable_coe, NNReal.coe_mul, coe_nnnorm, NNReal.coe_zpow] using
    F.nnreal_summable s

-- Move me
theorem nonneg_of_norm_hMul_zpow (k n : ℤ) (r : ℝ≥0) : 0 ≤ ‖k‖ * (r : ℝ) ^ n :=
  mul_nonneg (norm_nonneg _) (zpow_nonneg (NNReal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℒ S → ℒ S' := fun F =>
  { toFun := fun s' k => ∑ s in Finset.univ.filterₓ fun t => f t = s', F s k
    summable' := by
      intro s'
      have :
        ∀ n : ℤ,
          ‖∑ s in finset.univ.filter fun t => f t = s', F s n‖₊ * r ^ n ≤
            ∑ s in finset.univ.filter fun t => f t = s', ‖F s n‖₊ * r ^ n :=
        fun n =>
        calc
          ‖∑ s in finset.univ.filter fun t => f t = s', F s n‖₊ * r ^ n ≤
              (∑ s in finset.univ.filter fun t => f t = s', ‖F s n‖₊) * r ^ n :=
            mul_le_mul' (nnnorm_sum_le _ _) le_rfl
          _ = _ := by rw [Finset.sum_mul]
      exact NNReal.summable_of_le this (summable_sum fun (s : S) _ => F.nnreal_summable s) }

@[simp]
theorem map_apply (f : S ⟶ S') (F : ℒ S) (s' : S') (k : ℤ) :
    map f F s' k = ∑ s in Finset.univ.filterₓ fun t => f t = s', F s k :=
  rfl

@[simp]
theorem map_id : (map (𝟙 S) : ℒ S → ℒ S) = id :=
  by
  ext F s k
  simp only [map_apply, FintypeCat.id_apply, id.def, Finset.sum_filter, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

@[simp]
theorem map_comp {S'' : FintypeCat.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    (map (f ≫ g) : ℒ S → ℒ S'') = map g ∘ map f :=
  by
  ext F s k
  simp only [Function.comp_apply, map_apply, Finset.sum_congr]
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr
    · change (finset.univ.filter fun t => g (f t) = s) = _
      ext i
      constructor <;>
        · intro hi;
          simpa only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and_iff,
            exists_prop, exists_eq_right'] using hi
    · intros; rfl
  · intro i hi j hj h k hk
    simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and_iff, Finset.coe_filter, Finset.coe_univ, Set.sep_univ, Set.mem_setOf_eq] at hi hj hk 
    refine' h _
    rw [← hk.1, ← hk.2]

def add : ℒ S → ℒ S → ℒ S := fun F G =>
  { toFun := F + G
    summable' := fun s =>
      by
      refine' NNReal.summable_of_le _ ((F.nnreal_summable s).add (G.nnreal_summable s))
      intro n
      rw [← add_mul]
      exact mul_le_mul' (nnnorm_add_le _ _) le_rfl }

instance : Add (ℒ S) :=
  ⟨add⟩

@[simp]
theorem add_apply (F G : ℒ S) (s : S) (n : ℤ) : (F + G) s n = F s n + G s n :=
  rfl

def zero : ℒ S where
  toFun := 0
  summable' s := by simp [summable_zero]

instance : Zero (ℒ S) :=
  ⟨zero⟩

@[simp]
theorem zero_apply (s : S) (n : ℤ) : (0 : ℒ S) s n = 0 :=
  rfl

def neg : ℒ S → ℒ S := fun F =>
  { toFun := -F
    summable' := fun s => by simp [F.nnreal_summable] }

instance : Neg (ℒ S) :=
  ⟨neg⟩

@[simp]
theorem neg_apply (F : ℒ S) (s : S) (n : ℤ) : (-F) s n = -F s n :=
  rfl

def sub : ℒ S → ℒ S → ℒ S := fun F G =>
  { toFun := F - G
    summable' := (add F (neg G)).nNReal_summable }

instance : Sub (ℒ S) :=
  ⟨sub⟩

@[simp]
theorem sub_apply (F G : ℒ S) (s : S) (n : ℤ) : (F - G) s n = F s n - G s n :=
  rfl

example (a m : ℤ) : -a * m = a * -m :=
  neg_mul_comm a m

-- move me
instance : ContinuousSMul ℕ ℝ≥0
    where continuous_smul :=
    by
    let f : ℕ × ℝ≥0 → ℝ≥0 × ℝ≥0 := Prod.map coe id
    have hf : Continuous f := Continuous.prod_map continuous_bot continuous_id
    simpa only [nsmul_eq_mul] using continuous_mul.comp hf

-- move me
@[simp]
theorem Int.norm_hMul (m n : ℤ) : ‖m * n‖ = ‖m‖ * ‖n‖ := by
  simp only [Int.norm_eq_abs, Int.cast_mul, abs_mul]

-- move me
@[simp]
theorem Int.nnnorm_hMul (m n : ℤ) : ‖m * n‖₊ = ‖m‖₊ * ‖n‖₊ := by
  ext <;> simp only [coe_nnnorm, Int.norm_hMul, Nonneg.coe_mul]

-- move me
@[simp]
theorem Nat.norm_coe_int (n : ℕ) : ‖n : ℤ‖ = n := by
  simp only [Int.norm_eq_abs, Int.cast_ofNat, Nat.abs_cast]

-- move me
@[simp]
theorem Nat.nnnorm_coe_int (n : ℕ) : ‖n : ℤ‖₊ = n := by
  ext <;> simp only [coe_nnnorm, Nat.norm_coe_int, NNReal.coe_nat_cast]

instance : AddCommMonoid (ℒ S) :=
  {-- aahrg, why is `n` an implicit variable here???
    (inferInstance : Add _),
    (inferInstance :
      Zero _) with
    add_assoc := fun a b c => by ext; simp only [add_assoc, add_apply]
    add_comm := fun F G => by ext; simp only [add_comm, add_apply]
    zero_add := fun a => by ext; simp only [zero_add, add_apply, zero_apply]
    add_zero := fun a => by ext; simp only [add_zero, add_apply, zero_apply]
    nsmul := fun n F =>
      { toFun := fun s k => n • F s k
        summable' := fun s =>
          by
          have := @Summable.const_smul _ _ _ _ _ _ _ _ _ n (F.nnreal_summable s)
          simpa only [nsmul_eq_mul, Int.nnnorm_hMul, Nat.nnnorm_coe_int, mul_assoc] }
    nsmul_zero := fun F => by ext; rfl
    nsmul_succ := fun n F => by ext; rfl }

instance : AddCommGroup (ℒ S) :=
  {-- aahrg, why is `n.nat_abs` an implicit variable here???
    (inferInstance : AddCommMonoid _),
    (inferInstance : Neg _),
    (inferInstance : Sub _) with
    neg := neg
    sub := sub
    sub_eq_add_neg := fun F G => by ext; rfl
    zsmul := fun n F =>
      { toFun := fun s m => n • F s m
        summable' := fun s =>
          by
          have := @Summable.const_smul _ _ _ _ _ _ _ _ _ n.nat_abs (F.nnreal_summable s)
          simpa only [nsmul_eq_mul, NNReal.coe_natAbs, Algebra.id.smul_eq_mul, Int.nnnorm_hMul,
            mul_assoc] }
    zsmul_zero' := fun F => by ext;
      simp only [Algebra.id.smul_eq_mul, MulZeroClass.zero_mul, coe_mk, zero_apply]
    zsmul_succ' := fun n F => by ext;
      simp only [add_apply, Int.ofNat_succ, Int.ofNat_eq_coe, zsmul_eq_smul, smul_eq_mul, add_mul,
        add_comm, one_mul, coe_mk]
    zsmul_neg' := fun n F => by
      ext; rw [neg_apply];
      simp only [neg_apply, Int.ofNat_succ, Int.ofNat_eq_coe, Int.negSucc_coe, add_comm,
        zsmul_eq_smul, smul_eq_mul]
      dsimp; ring_nf
    add_left_neg := fun F => by ext; simp only [zero_apply, add_apply, neg_apply, add_left_neg]
    add_comm := fun a b => by ext; dsimp; rw [add_comm] }

instance : Norm (ℒ S) :=
  ⟨fun F => ∑ s, ∑' n, ‖F s n‖ * (r : ℝ) ^ n⟩

theorem norm_def (F : ℒ S) : ‖F‖ = ∑ s, ∑' n, ‖F s n‖ * (r : ℝ) ^ n :=
  rfl

instance : NNNorm (ℒ S) :=
  ⟨fun F => ∑ s, ∑' n, ‖F s n‖₊ * r ^ n⟩

theorem nnnorm_def (F : ℒ S) : ‖F‖₊ = ∑ s, ∑' n, ‖F s n‖₊ * r ^ n :=
  rfl

@[simp]
theorem coe_nnnorm (F : ℒ S) : (‖F‖₊ : ℝ) = ‖F‖ := by
  simp only [nnnorm_def, norm_def, NNReal.coe_sum, NNReal.coe_tsum, Nonneg.coe_mul, coe_nnnorm,
    NNReal.coe_zpow]

@[simp]
theorem LaurentMeasures.norm_nonneg (F : ℒ S) : 0 ≤ ‖F‖ := by
  rw [← coe_nnnorm] <;> exact (‖F‖₊).coe_nonneg

@[simp]
theorem nnnorm_neg (F : ℒ S) : ‖-F‖₊ = ‖F‖₊ := by
  simp only [nnnorm_def, neg_apply, nnnorm_neg]

theorem nnnorm_add (F G : ℒ S) : ‖F + G‖₊ ≤ ‖F‖₊ + ‖G‖₊ :=
  by
  simp only [nnnorm_def, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  rintro s -
  rw [← tsum_add (F.nnreal_summable _) (G.nnreal_summable _)]
  refine'
    tsum_le_tsum _ ((F + G).nNReal_summable _) ((F.nnreal_summable s).add (G.nnreal_summable s))
  intro b
  simp [← add_mul]
  refine' mul_le_mul' (nnnorm_add_le _ _) le_rfl

theorem norm_add (F G : ℒ S) : ‖F + G‖ ≤ ‖F‖ + ‖G‖ := by
  simpa only [← coe_nnnorm, ← NNReal.coe_add, NNReal.coe_le_coe] using nnnorm_add F G

@[simp]
theorem nsmul_apply (k : ℕ) (F : ℒ S) (s : S) (n : ℤ) : (k • F) s n = k • F s n :=
  rfl

@[simp]
theorem zsmul_apply (k : ℤ) (F : ℒ S) (s : S) (n : ℤ) : (k • F) s n = k • F s n :=
  rfl

section

open Finset

theorem map_bound (f : S ⟶ S') (F : ℒ S) : ‖map f F‖₊ ≤ ‖F‖₊ :=
  calc
    ‖map f F‖₊ =
        ∑ s', ∑' n, ‖∑ s in univ.filterₓ fun t => f t = s', F s n‖₊ * _ :=
      rfl
    _ ≤ ∑ s', ∑' n, ∑ s in univ.filterₓ fun t => f t = s', ‖F s n‖₊ * r ^ n :=
      by
      apply sum_le_sum
      rintro s' -
      have h1 :
        Summable fun n : ℤ =>
          ∑ s : S.α in univ.filter fun t => f t = s', ‖F s n‖₊ * r ^ n :=
        summable_sum fun s _ => F.nnreal_summable s
      have h2 :
        ∀ b : ℤ,
          ‖∑ s : S.α in univ.filter fun t => f t = s', F s b‖₊ * r ^ b ≤
            ∑ s : S.α in univ.filter fun t => f t = s', ‖F s b‖₊ * r ^ b :=
        by intro b; rw [← sum_mul]; exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl
      apply tsum_le_tsum h2 (NNReal.summable_of_le h2 h1) h1
    _ = ∑ s', ∑ s in univ.filterₓ fun t => f t = s', ∑' n, ‖F s n‖₊ * r ^ n :=
      (sum_congr rfl fun s' _ => tsum_sum fun s _ => F.nNReal_summable _)
    _ = _ := by
      rw [← sum_bUnion]
      refine' sum_congr _ _
      · ext s;
        simp only [mem_bUnion, mem_univ, mem_filter, true_and_iff, exists_true_left, exists_eq']
      · intros; rfl
      · rintro x - y - h i hi
        apply h
        simp only [inf_eq_inter, mem_inter, mem_filter, mem_univ, true_and_iff] at hi 
        rw [← hi.1, ← hi.2]

end

theorem map_bound' (f : S ⟶ S') (F : ℒ S) : ‖map f F‖ ≤ ‖F‖ := by
  simpa only [← coe_nnnorm, ← NNReal.coe_add, NNReal.coe_le_coe] using map_bound f F

/-
lemma exists_c (F : ℒ S) : ∃ (c : ℝ≥0),
  ∀ s : S, ∑' n, ∥ F s n ∥ * r ^ n ≤ c :=
begin
  use ∑ s, ∑' n, ∥ F s n ∥ * r ^ n,
  { apply finset.sum_nonneg,
    rintros s -,
    apply tsum_nonneg,
    intros n,
    refine mul_nonneg (norm_nonneg _) (zpow_nonneg _ _),
    exact nnreal.coe_nonneg r, },
  { admit },
end
-/
/-- This lemma puts bounds on where `F s n` can be nonzero. -/
theorem eq_zero_of_filtration (F : ℒ S) (c : ℝ≥0) :
    ‖F‖₊ ≤ c → ∀ (s : S) (n : ℤ), c < r ^ n → F s n = 0 :=
  by
  intro hF s n h
  suffices ‖F s n‖₊ < 1
    by
    change abs (F s n : ℝ) < 1 at this 
    norm_cast at this 
    rwa [← Int.abs_lt_one_iff]
  have : ‖F s n‖₊ * r ^ n ≤ ∑' k, ‖F s k‖₊ * r ^ k :=
    le_tsum (F.nnreal_summable s) _ fun k _ => zero_le'
  replace this := lt_of_le_of_lt (this.trans _) h
  · have hr₁ : 0 < r ^ n := lt_of_le_of_lt zero_le' h
    have hr₂ : r ^ n ≠ 0 := hr₁.ne'
    convert mul_lt_mul this (le_refl (r ^ n)⁻¹) _ hr₁.le
    · exact (mul_inv_cancel_right₀ hr₂ _).symm
    · exact (mul_inv_cancel hr₂).symm
    · rwa [nnreal.inv_pos]
  · refine' le_trans _ hF
    apply @Finset.single_le_sum S ℝ≥0 _ fun s => ∑' n, ‖F s n‖₊ * r ^ n
    · rintro s -; exact zero_le'
    · exact Finset.mem_univ _

-- move me
theorem zpow_strictAnti {K : Type} [LinearOrderedField K] {x : K} (hx₀ : 0 < x) (hx₁ : x < 1) :
    StrictAnti fun n : ℤ => x ^ n := by
  intro n m H
  rw [← inv_inv x]
  simp only [inv_zpow x⁻¹,
    inv_lt_inv (zpow_pos_of_pos (inv_pos.mpr hx₀) _) (zpow_pos_of_pos (inv_pos.mpr hx₀) _)]
  exact zpow_strictMono (one_lt_inv hx₀ hx₁) H

open Real

--For every F, d F is a bound whose existence is established in `eq_zero_of_filtration`
theorem exists_bdd_filtration {S : FintypeCat} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℒ S) :
    ∃ d : ℤ, ∀ s : S, ∀ n : ℤ, n < d → F s n = 0 :=
  by
  have h_logr : log r < 0 := log_neg hr₀ hr₁
  let d := if log (‖F‖) ≥ 0 then ⌊log (‖F‖) / log (r : ℝ)⌋ - 1 else -1
  use d
  intro s n hn
  have H1 := zpow_strictAnti hr₀ hr₁ hn
  suffices H2 : ‖F‖₊ < r ^ d
  · refine' eq_zero_of_filtration F (‖F‖₊) le_rfl s n (H2.trans _)
    rw [← NNReal.coe_lt_coe, NNReal.coe_zpow, NNReal.coe_zpow]
    exact zpow_strictAnti hr₀ hr₁ hn
  have hd1 : 0 < -(d : ℝ) :=
    by
    rw [lt_neg, neg_zero, ← Int.cast_zero, Int.cast_lt]
    apply Int.lt_of_le_sub_one
    dsimp only [d]
    split_ifs
    · rw [tsub_le_iff_right, sub_add, sub_self, sub_zero]
      exact Int.floor_nonpos (div_nonpos_of_nonneg_of_nonpos h (le_of_lt h_logr))
    · simp only [zero_sub]
  have hFd1 : log (‖F‖) < d * log (r : ℝ) :=
    by
    rw [← zsmul_eq_mul]
    rw [ite_smul]
    split_ifs
    · rw [zsmul_eq_mul]
      calc
        log (‖F‖) = log (‖F‖) / log r * log r :=
          (div_mul_cancel (log (‖F‖)) (ne_of_lt h_logr)).symm
        _ ≤ ⌊log (‖F‖) / log r⌋ * log r :=
          ((mul_le_mul_right_of_neg h_logr).mpr (Int.floor_le _))
        _ < (⌊log (‖F‖) / log r⌋ - 1) * log r :=
          ((mul_lt_mul_right_of_neg h_logr).mpr (sub_one_lt _))
        _ = ↑(⌊log (‖F‖) / log r⌋ - 1) * log r := by simp only [Int.cast_one, Int.cast_sub]
    · rw [neg_smul, one_smul]
      rw [ge_iff_le, not_le] at h 
      apply h.trans
      rwa [lt_neg, neg_zero]
  rw [← NNReal.coe_lt_coe, NNReal.coe_zpow, coe_nnnorm]
  have := Real.lt_rpow_of_log_lt (laurent_measures.norm_nonneg F) hr₀ hFd1
  rwa [Real.rpow_int_cast _ d] at this 

def bddFiltration {S : FintypeCat} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℒ S) : ℤ :=
  (exists_bdd_filtration hr₀ hr₁ F).some

def bddFiltration_spec {S : FintypeCat} (hr₀ : 0 < (r : ℝ)) (hr₁ : (r : ℝ) < 1) (F : ℒ S) :
    ∀ s n, n < bddFiltration hr₀ hr₁ F → F s n = 0 :=
  (exists_bdd_filtration hr₀ hr₁ F).choose_spec

section ProfiniteStructure

@[simps]
def truncate {c : ℝ≥0} (A : Finset ℤ) : {F : ℒ S | ‖F‖₊ ≤ c} → LaurentMeasuresBdd r S A c :=
  fun F =>
  { toFun := fun s i => F s i
    bound' := by
      refine' (Finset.sum_le_sum fun s _ => _).trans F.2
      convert sum_le_tsum A _ ((F : ℒ S).nNReal_summable s) using 1
      · conv_rhs => rw [← Finset.sum_attach]; rfl
      · intro b hb; exact zero_le' }

theorem eq_iff_truncate_eq (c : ℝ≥0) (F G : {F : ℒ S | ‖F‖₊ ≤ c}) :
    (∀ k, truncate k F = truncate k G) → F = G :=
  by
  intro h
  ext s i
  specialize h {i}
  apply_fun fun e => e s ⟨i, by simp⟩ at h 
  exact h

def finsetMap {A B : Finset ℤ} (h : B ≤ A) : B → A := fun i => ⟨i, h i.2⟩

def transition {c : ℝ≥0} {A B : Finset ℤ} (h : B ≤ A) :
    LaurentMeasuresBdd r S A c → LaurentMeasuresBdd r S B c := fun F =>
  ⟨fun s i => F s (finsetMap h i),
    by
    refine' (Finset.sum_le_sum fun s _ => _).trans F.2
    have :
      ∑ i : B, ‖(F s (finset_map h i))‖₊ * r ^ (i : ℤ) =
        ∑ i in finset.univ.image (finset_map h), ‖F s i‖₊ * r ^ (i : ℤ) :=
      by
      rw [Finset.sum_image]
      · rfl
      · rintro i - j - hh
        apply Subtype.ext
        apply_fun fun e => e.val at hh 
        exact hh
    rw [this]
    refine' Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => zero_le'⟩

def mkSeq {c} (F : ∀ A : Finset ℤ, LaurentMeasuresBdd r S A c) : S → ℤ → ℤ := fun s i =>
  F {i} s ⟨i, by simp⟩

theorem mkSeq_compat {c} (F : ∀ A : Finset ℤ, LaurentMeasuresBdd r S A c)
    (compat : ∀ (A B : Finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S) (A : Finset ℤ)
    (i : A) : mkSeq F s i = F A s i :=
  by
  have : ({i} : Finset ℤ) ≤ A := by simp
  specialize compat _ _ this
  dsimp [mk_seq]
  rw [← compat]
  change (F A) s _ = _
  congr
  ext
  rfl

theorem mkSeq_compat_summable {c} (F : ∀ A : Finset ℤ, LaurentMeasuresBdd r S A c)
    (compat : ∀ (A B : Finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
    Summable fun k : ℤ => ‖mkSeq F s k‖ * (r : ℝ) ^ k :=
  by
  apply summable_of_sum_le
  · intro k
    dsimp
    refine' mul_nonneg (norm_nonneg _) (zpow_nonneg (NNReal.coe_nonneg _) _)
  · intro A
    rw [← Finset.sum_attach]
    refine' le_trans _ (F A).bound
    simp_rw [mk_seq_compat _ compat]
    simp only [LaurentMeasuresBdd.nnnorm_def, Finset.univ_eq_attach, NNReal.coe_sum, NNReal.coe_mul,
      NNReal.coe_zpow]
    apply @Finset.single_le_sum S ℝ _ fun s => ∑ i : A, ‖F A s i‖ * (r : ℝ) ^ (i : ℤ)
    swap; · simp
    rintro s -
    apply Finset.sum_nonneg
    rintro a -
    refine' mul_nonneg (norm_nonneg _) (zpow_nonneg (NNReal.coe_nonneg _) _)

theorem mkSeq_compat_nNReal_summable {c} (F : ∀ A : Finset ℤ, LaurentMeasuresBdd r S A c)
    (compat : ∀ (A B : Finset ℤ) (h : B ≤ A), transition h (F _) = F _) (s : S) :
    Summable fun k : ℤ => ‖mkSeq F s k‖₊ * r ^ k :=
  by
  rw [← NNReal.summable_coe]
  simpa only [Nonneg.coe_mul, coe_nnnorm, NNReal.coe_zpow] using mk_seq_compat_summable F compat s

theorem mkSeq_compat_sum_le {c} (F : ∀ A : Finset ℤ, LaurentMeasuresBdd r S A c)
    (compat : ∀ (A B : Finset ℤ) (h : B ≤ A), transition h (F _) = F _) :
    ∑ s : S, ∑' k : ℤ, ‖mkSeq F s k‖₊ * r ^ k ≤ c :=
  by
  rw [← tsum_sum]
  swap; · intro s hs; apply mk_seq_compat_nnreal_summable _ compat
  have : ∀ A : Finset ℤ, ∑ b : A, ∑ s : S, ‖F A s b‖₊ * r ^ (b : ℤ) ≤ c :=
    by
    intro A
    rw [Finset.sum_comm]
    exact (F A).bound
  apply tsum_le_of_sum_le
  · apply summable_sum
    intro s hs
    apply mk_seq_compat_nnreal_summable _ compat
  intro I
  rw [Finset.sum_comm]
  convert (F I).bound using 1
  dsimp
  apply Finset.sum_congr rfl
  rintro s -
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  rintro i -
  simp_rw [mk_seq_compat _ compat]

theorem exists_of_compat {c} (F : ∀ A : Finset ℤ, LaurentMeasuresBdd r S A c)
    (compat : ∀ (A B : Finset ℤ) (h : B ≤ A), transition h (F _) = F _) :
    ∃ G : {H : ℒ S | ‖H‖₊ ≤ c}, ∀ k : Finset ℤ, truncate k G = F k :=
  by
  let G : ℒ S := ⟨mk_seq F, mk_seq_compat_nnreal_summable _ compat⟩
  use G
  · apply mk_seq_compat_sum_le _ compat
  · intro k
    ext s i
    change F _ _ _ = _
    have := compat k {i} (by simp)
    apply_fun fun e => e s ⟨i, by simp⟩ at this 
    erw [← this]
    change F k _ _ = F k _ _
    congr
    ext; rfl

variable (r S)

open CategoryTheory

/-- `laurent_measures_bdd_functor r S c` is the contravariant functor sending `T : finset ℤ` to
  the finite type `laurent_measures_bdd r S T c`. Morphisms are given by throwing away
  coefficients. -/
def laurentMeasuresBddFunctor (c : ℝ≥0) [Fact (0 < r)] : (AsSmall (Finset ℤ))ᵒᵖ ⥤ FintypeCat
    where
  obj A := FintypeCat.of <| LaurentMeasuresBdd r S (ULift.down A.unop) c
  map A B f := transition (leOfHom <| ULift.down f.unop)

/-- The `equiv` between Laurent measures with norm at most `c` and the projective limit
over `T : finset ℤ` of the finite types `laurent_measures_bdd r S T c`. -/
def laurentMeasuresBddEquiv (c : ℝ≥0) [Fact (0 < r)] :
    {F : ℒ S | ‖F‖₊ ≤ c} ≃
      (Profinite.limitCone (laurentMeasuresBddFunctor r S c ⋙ FintypeCat.toProfinite)).X :=
  Equiv.ofBijective (fun F => ⟨fun A => truncate (ULift.down A.unop) F, fun A B f => by ext; rfl⟩)
    (by
      constructor
      · intro F G h
        apply eq_iff_truncate_eq
        intro k
        dsimp at h 
        apply_fun fun e => e.1 (Opposite.op ⟨k⟩) at h 
        exact h
      · rintro ⟨F, hF⟩
        dsimp at F hF 
        obtain ⟨G, hG⟩ := exists_of_compat (fun A => F (Opposite.op ⟨A⟩)) _
        · use G
          ext : 2
          dsimp
          have := hG (ULift.down x.unop)
          convert this
          rw [← x.op_unop]
          congr 1
          ext
          rfl
        · intro A B h
          let e : (Opposite.op <| as_small.up.obj A) ⟶ Opposite.op <| as_small.up.obj B :=
            Quiver.Hom.op (as_small.up.map (hom_of_le h))
          exact hF e)

/-- The profinite topology on the Laurent measures with norm at most `c`. -/
instance (c : ℝ≥0) [Fact (0 < r)] : TopologicalSpace {F : ℒ S | ‖F‖₊ ≤ c} :=
  TopologicalSpace.induced (laurentMeasuresBddEquiv r S c) inferInstance

def laurentMeasuresBddHomeo (c : ℝ≥0) [Fact (0 < r)] :
    {F : ℒ S | ‖F‖₊ ≤ c} ≃ₜ
      (Profinite.limitCone (laurentMeasuresBddFunctor r S c ⋙ FintypeCat.toProfinite)).X :=
  {
    laurentMeasuresBddEquiv _ _
      _ with
    continuous_toFun := continuous_induced_dom
    continuous_invFun :=
      by
      have : Inducing (laurent_measures_bdd_equiv r S c) := ⟨rfl⟩
      rw [this.continuous_iff]
      dsimp
      simp only [Equiv.self_comp_symm]
      exact continuous_id }

instance (c : ℝ≥0) [Fact (0 < r)] : T2Space {F : ℒ S | ‖F‖₊ ≤ c} :=
  (laurentMeasuresBddHomeo r S c).symm.T2Space

instance (c : ℝ≥0) [Fact (0 < r)] : TotallyDisconnectedSpace {F : ℒ S | ‖F‖₊ ≤ c} :=
  (laurentMeasuresBddHomeo r S c).symm.TotallyDisconnectedSpace

instance (c : ℝ≥0) [Fact (0 < r)] : CompactSpace {F : ℒ S | ‖F‖₊ ≤ c} :=
  (laurentMeasuresBddHomeo r S c).symm.CompactSpace

@[continuity]
theorem truncate_continuous (c : ℝ≥0) [Fact (0 < r)] (A : Finset ℤ) :
    Continuous (truncate A : _ → LaurentMeasuresBdd r S _ c) :=
  by
  let g₁ :=
    (Profinite.limitCone (laurentMeasuresBddFunctor.{u} r S c ⋙ FintypeCat.toProfinite)).π.app
      (Opposite.op <| ULift.up A)
  let g₂ := laurent_measures_bdd_homeo r S c
  change Continuous (g₁ ∘ g₂)
  continuity

theorem continuous_iff (c : ℝ≥0) [Fact (0 < r)] {α : Type _} [TopologicalSpace α]
    (f : α → {F : ℒ S | ‖F‖₊ ≤ c}) :
    Continuous f ↔ ∀ A : Finset ℤ, Continuous (truncate A ∘ f) :=
  by
  constructor
  · intro hf A; continuity
  · intro h
    rw [← (laurent_measures_bdd_homeo r S c).comp_continuous_iff]
    apply Continuous.subtype_mk
    apply continuous_pi
    intro A
    apply h

end ProfiniteStructure

/-
--should this be a coercion?
def c_measures_to_oc (r : ℝ≥0) (c : ℝ≥0) (S : Type*) (hS : fintype S) :
  c_measures r c S hS → ℒ S hS := λ f, ⟨f.to_fun, f.summable⟩

lemma laurent_measures_are_c (r : ℝ≥0) (S : Type*) (hS : fintype S) (F : ℒ S hS) :
  ∃ (c : ℝ≥0) (f : c_measures r c S hS),
  c_measures_to_oc r c S hS f = F := by admit
-/
--needed?
instance : PseudoNormedGroup (ℒ S)
    where
  filtration c := {F | ‖F‖₊ ≤ c}
  filtration_mono c₁ c₂ h F hF := by dsimp at *; exact le_trans hF h
  zero_mem_filtration c := by simp [nnnorm_def]
  neg_mem_filtration c F h := (nnnorm_neg F).le.trans h
  add_mem_filtration c₁ c₂ F₁ F₂ h₁ h₂ := (nnnorm_add _ _).trans (add_le_add h₁ h₂)

@[simp]
theorem mem_filtration_iff (F : ℒ S) (c : ℝ≥0) :
    F ∈ PseudoNormedGroup.filtration (ℒ S) c ↔ ‖F‖₊ ≤ c :=
  Iff.rfl

instance [Fact (0 < r)] : ProfinitelyFilteredPseudoNormedGroup (ℒ S) :=
  {
    (inferInstance :
      PseudoNormedGroup
        (ℒ
          S)) with
    continuous_add' := by
      intro c₁ c₂
      rw [continuous_iff]
      intro A
      let E :
        LaurentMeasuresBdd r S A c₁ × LaurentMeasuresBdd r S A c₂ →
          LaurentMeasuresBdd r S A (c₁ + c₂) :=
        fun G => ⟨G.1 + G.2, _⟩
      swap;
      · refine' le_trans _ (add_le_add G.fst.2 G.snd.2)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro j hj
        rw [← add_mul]
        refine' mul_le_mul' (norm_add_le _ _) le_rfl
      have :
        (truncate A : _ → LaurentMeasuresBdd r S A (c₁ + c₂)) ∘ PseudoNormedGroup.add' =
          E ∘ Prod.map (truncate A) (truncate A) :=
        by ext; rfl
      rw [this]
      apply Continuous.comp
      · exact continuous_of_discreteTopology
      · apply Continuous.prod_map
        all_goals apply truncate_continuous
    continuous_neg' := by
      intro c
      rw [continuous_iff]
      intro A
      let E : LaurentMeasuresBdd r S A c → LaurentMeasuresBdd r S A c := fun G => ⟨-G, _⟩
      swap;
      · convert G.2 using 1
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        simpa
      have :
        (truncate A : _ → LaurentMeasuresBdd r S A c) ∘ PseudoNormedGroup.neg' = E ∘ truncate A :=
        by ext; rfl
      rw [this]
      apply Continuous.comp
      · exact continuous_of_discreteTopology
      · apply truncate_continuous
    continuous_castLe := by
      intro c₁ c₂ h
      rw [continuous_iff]
      intro A
      let g : LaurentMeasuresBdd r S A c₁ → LaurentMeasuresBdd r S A c₂ := fun g =>
        ⟨g, le_trans g.2 h.out⟩
      have :
        (truncate A : _ → LaurentMeasuresBdd r S A c₂) ∘ PseudoNormedGroup.castLe =
          g ∘ truncate A :=
        by ext; rfl
      rw [this]
      apply Continuous.comp
      · exact continuous_of_discreteTopology
      · apply truncate_continuous }

/-- The additive group homomorphism on Laurent measures induced by division by `T^k` on `ℤ((T))ᵣ` -/
@[simps]
def shiftAddMonoidHom [hr : Fact (0 < r)] (k : ℤ) : ℒ S →+ ℒ S :=
  AddMonoidHom.mk'
    (fun F =>
      { toFun := fun s n => F s (n + k)
        summable' := fun s =>
          by
          convert
            (NNReal.summable_comp_injective (F.nnreal_summable s)
                  (add_left_injective (k : ℤ))).hMul_right
              (r ^ (-k))
          ext n
          simp only [Function.comp, ← zpow_add₀ hr.out.ne', mul_assoc, add_neg_cancel_right] })
    fun F G => by ext; rfl

-- move me
@[simp, to_additive]
theorem Finset.prod_attach' {α M : Type _} [CommMonoid M] (s : Finset α) (f : s → M) :
    ∏ a in s.attach, f a = ∏ a in s, if h : a ∈ s then f ⟨a, h⟩ else 1 :=
  by
  rw [eq_comm, ← Finset.prod_attach, Finset.prod_congr rfl]
  intros; simp only [Finset.coe_mem, Finset.mk_coe, dite_eq_ite, if_true]

@[simps]
def shift [hr : Fact (0 < r)] (k : ℤ) : ComphausFilteredPseudoNormedGroupHom (ℒ S) (ℒ S) :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBound (shiftAddMonoidHom k) (r ^ (-k))
    (by
      abstract shift_spec 
        intro c
        have H : _ := _
        refine' ⟨H, _⟩
        · rw [continuous_iff]
          intro A
          let B : Finset ℤ := A.map (Equiv.toEmbedding (Equiv.addLeft (k : ℤ)))
          let g : LaurentMeasuresBdd r S B c → LaurentMeasuresBdd r S A (r ^ (-k) * c) := fun F =>
            { toFun := fun s a => F s ⟨a + k, _⟩
              bound' := _ }
          · suffices truncate A ∘ _ = g ∘ truncate B by rw [this];
              exact continuous_of_discrete_topology.comp (truncate_continuous r S _ B)
            ext F s a; rfl
          ·
            simp only [Finset.mem_map_equiv, Equiv.addLeft_symm, neg_neg, Equiv.coe_addLeft,
              neg_add_cancel_comm_assoc, Finset.coe_mem]
          · refine' le_trans _ (mul_le_mul' le_rfl F.bound)
            rw [LaurentMeasuresBdd.nnnorm_def, mul_comm, Finset.sum_mul]
            refine' Finset.sum_le_sum fun s hs => _
            simp only [B, Finset.univ_eq_attach]
            erw [Finset.sum_mul, Finset.sum_attach', Finset.sum_attach', Finset.sum_map]
            refine' Finset.sum_le_sum fun n hn => _
            simp only [Finset.mem_map_equiv, Equiv.addLeft_symm, Equiv.coe_addLeft, Subtype.coe_mk,
              Equiv.toEmbedding_apply, neg_add_cancel_left]
            simp only [add_comm k, mul_assoc, ← zpow_add₀ hr.out.ne', add_neg_cancel_right]
        · intro F hF
          rw [mul_comm]
          refine' le_trans _ (mul_le_mul' hF le_rfl)
          simp only [nnnorm_def, Finset.sum_mul]
          refine' Finset.sum_le_sum fun s _ => le_of_eq _
          trans ∑' n, ‖F s n‖₊ * r ^ n * r ^ (-k)
          · refine' ((Equiv.addLeft (-k : ℤ)).tsum_eq _).symm.trans _
            simp only [Equiv.coe_addLeft, shift_add_monoid_hom_apply_to_fun, neg_add_cancel_comm,
              zpow_add₀ hr.out.ne', zpow_neg_one, mul_comm (r ^ (-k)), mul_assoc]
          ext
          simp only [Nonneg.coe_mul, NNReal.coe_tsum, coe_nnnorm, NNReal.coe_zpow, tsum_mul_right])

instance [Fact (0 < r)] : ProfinitelyFilteredPseudoNormedGroupWithTinv r (ℒ S) :=
  {
    (_ : ProfinitelyFilteredPseudoNormedGroup
        (ℒ S)) with
    tinv := shift 1
    tinv_mem_filtration := fun c F hF =>
      by
      refine' ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ _ _ hF
      intro c'
      have := @shift.shift_spec r S _ 1 c'
      rwa [zpow_neg_one] at this  }

@[simp]
theorem tinv_apply [Fact (0 < r)] (F : ℒ S) :
    ComphausFilteredPseudoNormedGroupWithTinv.tinv F = shift 1 F :=
  rfl

variable {α : Type _}

open PseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup ComphausFilteredPseudoNormedGroup

@[simps]
def mapHom [Fact (0 < r)] (f : S ⟶ S') : ComphausFilteredPseudoNormedGroupWithTinvHom r (ℒ S) (ℒ S')
    where
  toFun := map f
  map_zero' := by ext; simp only [map_apply, zero_apply, Finset.sum_const_zero]
  map_add' F G := by ext s i; simp only [← Finset.sum_add_distrib, map_apply, add_apply]
  map_Tinv' F := by ext s i; simp only [map_apply, Tinv_apply, shift_to_fun_to_fun]
  strict' c F (hF : ‖F‖₊ ≤ c) := (map_bound _ _).trans hF
  continuous' c := by
    rw [continuous_iff]
    intro T
    let f₀ : filtration (LaurentMeasures r S) c → filtration (LaurentMeasures r S') c :=
      level (map f) (fun c F (hF : ‖F‖₊ ≤ c) => (map_bound f F).trans hF) c
    have : truncate T ∘ f₀ = LaurentMeasuresBdd.map f ∘ truncate T := by ext F s' t; rfl
    rw [this]
    exact continuous_of_discrete_topology.comp (truncate_continuous r S _ T)

/-- Let `F : ℒ S` be a Laurent measure.  `laurent_measures.d` chooses a bound `d ∈ ℤ` for `F`,
such that, for all `s : S`, the sequence `F s` is zero from `d-1` and below. -/
def d [h0 : Fact (0 < r)] [h1 : Fact (r < 1)] (F : ℒ S) : ℤ :=
  (exists_bdd_filtration h0.out h1.out F).some

theorem lt_d_eq_zero [h0 : Fact (0 < r)] [h1 : Fact (r < 1)] (F : ℒ S) (s : S) (n : ℤ) :
    n < F.d → F s n = 0 :=
  (exists_bdd_filtration h0.out h1.out F).choose_spec s n

theorem lt_d_eq_zero' [h0 : Fact (0 < r)] [h1 : Fact (r < 1)] (F : ℒ S) (s : S) (n : ℤ) :
    n < F.d → (F s n : ℝ) = 0 := by exact_mod_cast lt_d_eq_zero F s n

end LaurentMeasures

