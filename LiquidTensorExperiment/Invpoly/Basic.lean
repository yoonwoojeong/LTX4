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
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.LaurentMeasures.Basic
import LiquidTensorExperiment.ForMathlib.Tsum
import LiquidTensorExperiment.ForMathlib.Nnreal

#align_import invpoly.basic

universe u

noncomputable section

open scoped BigOperators NNReal Classical

/-- `invpoly r S`, with notation `ℤ[T⁻¹] S`, is the functions `S → ℤ[T⁻¹]`. -/
def Invpoly (r : ℝ≥0) (S : FintypeCat) :=
  S → Polynomial ℤ
deriving AddCommGroup

variable {r : ℝ≥0} {S S' : FintypeCat.{u}}

local notation "ℤ[T⁻¹]" => Invpoly r

namespace Invpoly

@[simp]
theorem add_apply (F G : ℤ[T⁻¹] S) (s : S) : (F + G) s = F s + G s :=
  rfl

@[simp]
theorem sub_apply (F G : ℤ[T⁻¹] S) (s : S) : (F - G) s = F s - G s :=
  rfl

@[simp]
theorem neg_apply (F : ℤ[T⁻¹] S) (s : S) : (-F) s = -F s :=
  rfl

@[simp]
theorem zero_apply (s : S) : (0 : ℤ[T⁻¹] S) s = 0 :=
  rfl

@[simp]
theorem nsmul_apply (k : ℕ) (F : ℤ[T⁻¹] S) (s : S) : (k • F) s = k • F s :=
  rfl

@[simp]
theorem zsmul_apply (k : ℤ) (F : ℤ[T⁻¹] S) (s : S) : (k • F) s = k • F s :=
  rfl

-- @[ext]
-- lemma ext (F G : ℤ[T⁻¹] S) : (F : S → ) = G → F = G :=
-- by { intros h, funext s, ext, exact congr_fun (congr_fun h s) n }
protected theorem nNReal_summable (F : ℤ[T⁻¹] S) (s : S) :
    Summable fun n => ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
  by
  apply @summable_of_ne_finset_zero _ _ _ _ _ (F s).support
  intro n hn
  simp only [Polynomial.mem_support_iff, Classical.not_not] at hn 
  simp only [hn, nnnorm_zero, MulZeroClass.zero_mul]

protected theorem summable (F : ℤ[T⁻¹] S) (s : S) :
    Summable fun n => ‖((F s).Coeff n)‖ * r ^ (-n : ℤ) := by
  simpa only [← NNReal.summable_coe, NNReal.coe_mul, coe_nnnorm, NNReal.coe_zpow] using
    F.nnreal_summable s

-- Move me
theorem nonneg_of_norm_hMul_zpow (k n : ℤ) (r : ℝ≥0) : 0 ≤ ‖k‖ * (r : ℝ) ^ n :=
  mul_nonneg (norm_nonneg _) (zpow_nonneg (NNReal.coe_nonneg _) _)

def map (f : S ⟶ S') : ℤ[T⁻¹] S → ℤ[T⁻¹] S' := fun F => fun s' =>
  ∑ s in Finset.univ.filterₓ fun t => f t = s', F s

@[simp]
theorem map_apply (f : S ⟶ S') (F : ℤ[T⁻¹] S) (s' : S') (k : ℕ) :
    (map f F s').Coeff k = ∑ s in Finset.univ.filterₓ fun t => f t = s', (F s).Coeff k := by
  simp only [map, ← Polynomial.finset_sum_coeff]

@[simp]
theorem map_id : (map (𝟙 S) : ℤ[T⁻¹] S → ℤ[T⁻¹] S) = id :=
  by
  ext F s k
  simp only [map_apply, FintypeCat.id_apply, id.def, Finset.sum_filter, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

@[simp]
theorem map_comp {S'' : FintypeCat.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    (map (f ≫ g) : ℤ[T⁻¹] S → ℤ[T⁻¹] S'') = map g ∘ map f :=
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

instance : Norm (ℤ[T⁻¹] S) :=
  ⟨fun F => ∑ s, ∑' n, ‖((F s).Coeff n)‖ * (r : ℝ) ^ (-n : ℤ)⟩

theorem norm_def (F : ℤ[T⁻¹] S) :
    ‖F‖ = ∑ s, ∑' n, ‖((F s).Coeff n)‖ * (r : ℝ) ^ (-n : ℤ) :=
  rfl

/-- The norm on `ℤ[T⁻¹](S)` sending `s ↦ ∑ aₙ(s) T⁻ⁿ` to `∑_{s,n} ∥aₙ(s)∥₊r^⁻ⁿ`. -/
instance : NNNorm (ℤ[T⁻¹] S) :=
  ⟨fun F => ∑ s, ∑' n, ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ)⟩

theorem nnnorm_def (F : ℤ[T⁻¹] S) :
    ‖F‖₊ = ∑ s, ∑' n, ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
  rfl

@[simp]
theorem coe_nnnorm (F : ℤ[T⁻¹] S) : (‖F‖₊ : ℝ) = ‖F‖ := by
  simp only [nnnorm_def, norm_def, NNReal.coe_sum, NNReal.coe_tsum, Nonneg.coe_mul, coe_nnnorm,
    NNReal.coe_zpow]

@[simp]
theorem Invpoly.norm_nonneg (F : ℤ[T⁻¹] S) : 0 ≤ ‖F‖ := by
  rw [← coe_nnnorm] <;> exact (‖F‖₊).coe_nonneg

@[simp]
theorem nnnorm_neg (F : ℤ[T⁻¹] S) : ‖-F‖₊ = ‖F‖₊ := by
  simp only [nnnorm_def, nnnorm_neg, neg_apply, Polynomial.coeff_neg]

theorem nnnorm_add (F G : ℤ[T⁻¹] S) : ‖F + G‖₊ ≤ ‖F‖₊ + ‖G‖₊ :=
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

theorem norm_add (F G : ℤ[T⁻¹] S) : ‖F + G‖ ≤ ‖F‖ + ‖G‖ := by
  simpa only [← coe_nnnorm, ← NNReal.coe_add, NNReal.coe_le_coe] using nnnorm_add F G

instance : PseudoNormedGroup (ℤ[T⁻¹] S)
    where
  filtration c := {F | ‖F‖₊ ≤ c}
  filtration_mono c₁ c₂ h F hF := by dsimp at *; exact le_trans hF h
  zero_mem_filtration c := by simp [nnnorm_def]
  neg_mem_filtration c F h := (nnnorm_neg F).le.trans h
  add_mem_filtration c₁ c₂ F₁ F₂ h₁ h₂ := (nnnorm_add _ _).trans (add_le_add h₁ h₂)

@[simp]
theorem mem_filtration_iff (F : ℤ[T⁻¹] S) (c : ℝ≥0) :
    F ∈ PseudoNormedGroup.filtration (ℤ[T⁻¹] S) c ↔ ‖F‖₊ ≤ c :=
  Iff.rfl

section

open Finset

theorem map_bound (f : S ⟶ S') (F : ℤ[T⁻¹] S) : ‖map f F‖₊ ≤ ‖F‖₊ :=
  calc
    ‖map f F‖₊ =
        ∑ s',
          ∑' n, ‖(∑ s in univ.filterₓ fun t => f t = s', (F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
      by simp only [map, ← Polynomial.finset_sum_coeff] <;> rfl
    _ ≤
        ∑ s',
          ∑' n, ∑ s in univ.filterₓ fun t => f t = s', ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
      by
      apply sum_le_sum
      rintro s' -
      have h1 :
        Summable fun n : ℕ =>
          ∑ s : S.α in univ.filter fun t => f t = s', ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
        summable_sum fun s _ => F.nnreal_summable s
      have h2 :
        ∀ b : ℕ,
          ‖(∑ s : S.α in univ.filter fun t => f t = s', (F s).Coeff b)‖₊ * r ^ (-b : ℤ) ≤
            ∑ s : S.α in univ.filter fun t => f t = s', ‖((F s).Coeff b)‖₊ * r ^ (-b : ℤ) :=
        by intro b; rw [← sum_mul]; exact mul_le_mul' (nnnorm_sum_le _ _) le_rfl
      apply tsum_le_tsum h2 (NNReal.summable_of_le h2 h1) h1
    _ =
        ∑ s',
          ∑ s in univ.filterₓ fun t => f t = s', ∑' n, ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
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

theorem map_bound' (f : S ⟶ S') (F : ℤ[T⁻¹] S) : ‖map f F‖ ≤ ‖F‖ := by
  simpa only [← coe_nnnorm, ← NNReal.coe_add, NNReal.coe_le_coe] using map_bound f F

theorem bounded_of_filtration (F : ℤ[T⁻¹] S) (c : ℝ≥0) [hr : Fact (0 < r)] :
    ‖F‖₊ ≤ c → ∀ (s : S) (n : ℕ), ‖((F s).Coeff n)‖₊ ≤ c * r ^ n :=
  by
  intro hF s n
  have :
    ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) ≤ ∑' k, ‖((F s).Coeff k)‖₊ * r ^ (-k : ℤ) :=
    le_tsum (F.nnreal_summable s) _ fun k _ => zero_le'
  rw [mul_comm, NNReal.mul_le_iff_le_inv (zpow_ne_zero_of_ne_zero hr.elim.ne.symm _)] at this 
  simp only [zpow_neg, zpow_ofNat, inv_inv, mul_comm (r ^ n)] at this 
  refine' le_trans this _
  rw [mul_le_mul_right (pow_pos hr.elim n)]
  refine' le_trans _ hF
  unfold nnnorm
  simp only [zpow_neg, zpow_ofNat]
  apply @Finset.single_le_sum S ℝ≥0 _ fun s => ∑' n, ‖((F s).Coeff n)‖₊ * (r ^ n)⁻¹
  · rintro s -; exact zero_le'
  · exact Finset.mem_univ _

theorem bounded_of_filtration' (F : ℤ[T⁻¹] S) (c : ℝ≥0) [Fact (0 < r)] [hr : Fact (r < 1)] :
    ‖F‖₊ ≤ c → ∀ (s : S) (n : ℕ), |(F s).Coeff n| ≤ ⌊c⌋₊ :=
  by
  intro hF s n
  rw [Int.abs_le_floor_nnreal_iff]
  refine' le_trans (bounded_of_filtration F c hF s n) _
  exact mul_le_of_le_of_le_one (le_refl c) (pow_le_one' hr.elim.le n)

-- rather annoyingly, can't use `bounded_of_filtration` to prove this
-- more easily because it's true even if r=0 :-)
/-- This lemma puts bounds on where `(F s).coeff n` can be nonzero. -/
theorem eq_zero_of_filtration (F : ℤ[T⁻¹] S) (c : ℝ≥0) :
    ‖F‖₊ ≤ c → ∀ (s : S) (n : ℕ), c < r ^ (-n : ℤ) → (F s).Coeff n = 0 :=
  by
  intro hF s n h
  suffices ‖((F s).Coeff n)‖₊ < 1
    by
    change abs ((F s).Coeff n : ℝ) < 1 at this 
    norm_cast at this 
    rwa [← Int.abs_lt_one_iff]
  have :
    ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) ≤ ∑' k, ‖((F s).Coeff k)‖₊ * r ^ (-k : ℤ) :=
    le_tsum (F.nnreal_summable s) _ fun k _ => zero_le'
  replace this := lt_of_le_of_lt (this.trans _) h
  · have hr₁ : 0 < r ^ (-n : ℤ) := lt_of_le_of_lt zero_le' h
    have hr₂ : r ^ (-n : ℤ) ≠ 0 := hr₁.ne'
    convert mul_lt_mul this (le_refl (r ^ (-n : ℤ))⁻¹) _ hr₁.le
    · exact (mul_inv_cancel_right₀ hr₂ _).symm
    · exact (mul_inv_cancel hr₂).symm
    · rwa [nnreal.inv_pos]
  · refine' le_trans _ hF
    apply @Finset.single_le_sum S ℝ≥0 _ fun s => ∑' n, ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ)
    · rintro s -; exact zero_le'
    · exact Finset.mem_univ _

theorem log_div_log_lt {r : ℝ≥0} (c : ℝ≥0) (n : ℕ) (hr0 : 0 < r) (hr1 : r < 1)
    (h : -Real.log ↑c / Real.log ↑r < ↑n) : c < r ^ (-(n : ℤ)) :=
  by
  rcases(eq_zero_or_pos : c = 0 ∨ 0 < c) with (rfl | hc)
  · apply NNReal.zpow_pos hr0.ne.symm
  · rw [div_lt_iff_of_neg (Real.log_neg hr0 hr1), lt_neg, ← neg_mul] at h 
    rw [(by norm_cast : -(n : ℝ) = (-(n : ℤ) : ℤ)), ← Real.log_zpow] at h 
    rw [Real.log_lt_log_iff hc] at h 
    · exact_mod_cast h
    · norm_cast; apply NNReal.zpow_pos hr0.ne.symm

theorem eq_zero_of_filtration' {F : ℤ[T⁻¹] S} {c : ℝ≥0} [hr0 : Fact (0 < r)] [hr1 : Fact (r < 1)] :
    ‖F‖₊ ≤ c → ∀ (s : S) (n : ℕ), -Real.log c / Real.log r < n → (F s).Coeff n = 0 :=
  by
  intro hF s n h
  refine' eq_zero_of_filtration F c hF s n (log_div_log_lt c n hr0.elim hr1.elim h)

-- move me
theorem zpow_strictAnti {K : Type} [LinearOrderedField K] {x : K} (hx₀ : 0 < x) (hx₁ : x < 1) :
    StrictAnti fun n : ℤ => x ^ n := by
  intro n m H
  rw [← inv_inv x]
  simp only [inv_zpow x⁻¹,
    inv_lt_inv (zpow_pos_of_pos (inv_pos.mpr hx₀) _) (zpow_pos_of_pos (inv_pos.mpr hx₀) _)]
  exact zpow_strictMono (one_lt_inv hx₀ hx₁) H

section ProfiniteStructure

variable [Fact (0 < r)] (c : ℝ≥0)

instance [Fact (r < 1)] : Fintype {F : ℤ[T⁻¹] S | ‖F‖₊ ≤ c} :=
  let i :
    {F : ℤ[T⁻¹] S | ‖F‖₊ ≤ c} →
      S → Fin (⌊-Real.log ↑c / Real.log ↑r⌋₊ + 1) → Set.Icc (-⌊c⌋₊ : ℤ) ⌊c⌋₊ :=
    fun F s j => ⟨(F.1 s).Coeff j, abs_le.1 (bounded_of_filtration' _ _ F.2 _ _)⟩
  Fintype.ofInjective i
    (by
      intro F₁ F₂ h
      ext s n
      cases' le_or_lt (n : ℝ) (-Real.log c / Real.log r) with hn hn
      · replace hn := Nat.le_floor hn
        rw [← Nat.lt_add_one_iff] at hn 
        replace h := congr_fun (congr_fun h s) ⟨n, hn⟩
        exact congr_arg Subtype.val h
      · convert (rfl : (0 : ℤ) = 0)
        · apply eq_zero_of_filtration' F₁.2 _ _ hn
        · apply eq_zero_of_filtration' F₂.2 _ _ hn)

instance : TopologicalSpace {F : ℤ[T⁻¹] S | ‖F‖₊ ≤ c} :=
  ⊥

instance [Fact (0 < r)] [Fact (r < 1)] : ProfinitelyFilteredPseudoNormedGroup (ℤ[T⁻¹] S) :=
  {
    (inferInstance :
      PseudoNormedGroup
        (ℤ[T⁻¹] S)) with
    continuous_add' := fun _ _ => continuous_of_discreteTopology
    continuous_neg' := fun _ => continuous_of_discreteTopology
    continuous_castLe := fun _ _ _ => continuous_of_discreteTopology }

end ProfiniteStructure

/-- The `T⁻¹` action on `ℤ[T⁻¹] S`.
This is defined, essentially, as a shift in `ℕ` (accounting for the restriction at 0).
This is an additive group homomorphism.
-/
def tinvAux {S : FintypeCat.{u}} : ℤ[T⁻¹] S →+ ℤ[T⁻¹] S :=
  AddMonoidHom.mk' (fun F s => AddMonoidHom.mulLeft Polynomial.X (F s))
    (by intro F G; funext s; exact map_add _ _ _)

theorem tinvAux_coeff (F : ℤ[T⁻¹] S) (s : S) (n : ℕ) :
    (tinvAux F s).Coeff n = (Polynomial.X * F s).Coeff n :=
  rfl

@[simp]
theorem tinvAux_zero (F : ℤ[T⁻¹] S) (s : S) : (tinvAux F s).Coeff 0 = 0 := by
  simp only [Tinv_aux_coeff, Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero,
    MulZeroClass.zero_mul]

@[simp]
theorem tinvAux_succ (F : ℤ[T⁻¹] S) (s : S) (i : ℕ) : (tinvAux F s).Coeff (i + 1) = (F s).Coeff i :=
  by simp only [Tinv_aux_coeff, Polynomial.coeff_X_mul]

theorem tinvAux_summable [hr : Fact (0 < r)] (F : ℤ[T⁻¹] S) (s : S) :
    Summable fun n => ‖((tinvAux F s).Coeff n)‖₊ * r ^ (-n : ℤ) :=
  by
  rw [← NNReal.summable_nat_add_iff 1]
  simp only [Tinv_aux_succ, Int.ofNat_succ, neg_add, zpow_add₀ hr.out.ne', ← mul_assoc]
  apply Summable.mul_right
  exact F.nnreal_summable s

@[simps]
def tinvHom [hr : Fact (0 < r)] [Fact (r < 1)] :
    ComphausFilteredPseudoNormedGroupHom (ℤ[T⁻¹] S) (ℤ[T⁻¹] S) :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBound tinvAux r⁻¹
    (by
      abstract Tinv_spec 
        intro c
        refine' ⟨_, continuous_of_discreteTopology⟩
        intro F hF
        rw [mul_comm]
        refine' le_trans _ (mul_le_mul' hF le_rfl)
        simp only [nnnorm_def, Finset.sum_mul]
        refine' Finset.sum_le_sum fun s _ => _
        trans ∑' n, ‖((F s).Coeff n)‖₊ * r ^ (-n : ℤ) * r⁻¹
        · rw [← sum_add_tsum_nat_add' 1]
          swap; · apply Tinv_aux_summable
          simp only [Finset.range_one, zpow_neg, zpow_ofNat, Finset.sum_singleton, pow_zero,
            inv_one, mul_one, Int.ofNat_succ, neg_add, zpow_add₀ hr.out.ne', zpow_one, mul_assoc,
            Tinv_aux_zero, nnnorm_zero, Tinv_aux_succ, zero_add]
        refine' le_of_eq _; ext
        simp only [Nonneg.coe_mul, NNReal.coe_tsum, coe_nnnorm, NNReal.coe_zpow, tsum_mul_right])

instance [Fact (0 < r)] [Fact (r < 1)] :
    ProfinitelyFilteredPseudoNormedGroupWithTinv r (ℤ[T⁻¹] S) :=
  {
    (_ : ProfinitelyFilteredPseudoNormedGroup
        (ℤ[T⁻¹] S)) with
    tinv := tinvHom
    tinv_mem_filtration := fun c F hF =>
      ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ _ _ hF }

open ComphausFilteredPseudoNormedGroupWithTinv

theorem tinv_coeff [Fact (0 < r)] [Fact (r < 1)] (F : ℤ[T⁻¹] S) (s : S) (n : ℕ) :
    (tinv F s).Coeff n = (Polynomial.X * F s).Coeff n :=
  rfl

@[simp]
theorem tinv_zero [Fact (0 < r)] [Fact (r < 1)] (F : ℤ[T⁻¹] S) (s : S) : (tinv F s).Coeff 0 = 0 :=
  tinvAux_zero F s

@[simp]
theorem tinv_succ [Fact (0 < r)] [Fact (r < 1)] (F : ℤ[T⁻¹] S) (s : S) (i : ℕ) :
    (tinv F s).Coeff (i + 1) = (F s).Coeff i :=
  tinvAux_succ F s i

variable {α : Type _}

open PseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup ComphausFilteredPseudoNormedGroup

@[simps]
def mapHom [Fact (0 < r)] [Fact (r < 1)] (f : S ⟶ S') :
    ComphausFilteredPseudoNormedGroupWithTinvHom r (ℤ[T⁻¹] S) (ℤ[T⁻¹] S')
    where
  toFun := map f
  map_zero' := by
    ext s n
    simp only [map_apply, zero_apply, Polynomial.coeff_zero, Finset.sum_const_zero]
  map_add' F G := by
    ext s n
    simp only [map_apply, add_apply, Polynomial.coeff_add, Finset.sum_add_distrib]
  map_Tinv' F := by
    ext s (_ | n)
    · simp only [map_apply, Tinv_zero, Finset.sum_const_zero]
    · simp only [map_apply, Tinv_succ]
  strict' c F (hF : ‖F‖₊ ≤ c) := (map_bound _ _).trans hF
  continuous' c := continuous_of_discreteTopology

end Invpoly

