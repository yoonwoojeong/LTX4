import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import LiquidTensorExperiment.Lbar.Bounded
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.ForMathlib.Tsum

#align_import Lbar.basic

/-!

## $\overline{\mathcal{M}}_{r'}(S)$

This file contains a definition of `ℳ-bar_{r'}(S) as defined at the very beginning
of section 9 of `Analytic.pdf` (p57), and its action of `T⁻¹`.

## Implementation issues

We model Tℤ[[T]] as functions ℕ → ℤ which vanish at 0.

-/


universe u

noncomputable section

open scoped BigOperators NNReal

section Defs

/-- `Lbar r S` is the set of power series
`F_s = ∑ a_{s,n}T^n ∈ Tℤ[[T]]` such that `∑_{s,n} |a_{s,n}|r^n` converges
(or equivalently, because `S` is a finite type, such that for each `s : S`,
`∑_n |a_{s,n}|r^n` converges. ) -/
structure Lbar (r' : ℝ≥0) (S : Type u) [Fintype S] where
  toFun : S → ℕ → ℤ
  coeff_zero' : ∀ s, to_fun s 0 = 0
  summable' : ∀ s, Summable fun n => ↑(to_fun s n).natAbs * r' ^ n

end Defs

variable {r' : ℝ≥0} {S : Type u} [Fintype S]

namespace Lbar

instance hasCoeToFun : CoeFun (Lbar r' S) fun _ => S → ℕ → ℤ :=
  ⟨Lbar.toFun⟩

@[simp]
theorem coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : Lbar r' S) : S → ℕ → ℤ) = x :=
  rfl

@[simp]
protected theorem coeff_zero (x : Lbar r' S) (s : S) : x s 0 = 0 :=
  x.coeff_zero' s

protected theorem summable (x : Lbar r' S) (s : S) : Summable fun n => ↑(x s n).natAbs * r' ^ n :=
  x.summable' s

theorem summable_coe_real (x : Lbar r' S) (s : S) : Summable fun n => ‖x s n‖ * r' ^ n :=
  by
  simpa only [← NNReal.summable_coe, NNReal.coe_nat_cast, NNReal.coe_natAbs, NNReal.coe_mul,
    NNReal.coe_pow] using x.summable s

@[ext]
theorem ext (x y : Lbar r' S) (h : (⇑x : S → ℕ → ℤ) = y) : x = y := by cases x; cases y; congr;
  exact h

theorem ext_iff (x y : Lbar r' S) : x = y ↔ (x : S → ℕ → ℤ) = y :=
  ⟨congr_arg _, ext x y⟩

/-- The zero element of `Lbar r' S`, defined as the constant 0-function. -/
def zero : Lbar r' S where
  toFun := 0
  coeff_zero' s := rfl
  summable' s := by simpa using summable_zero

/-- Addition in `Lbar r' S`, defined as pointwise addition. -/
def add (F : Lbar r' S) (G : Lbar r' S) : Lbar r' S
    where
  toFun := F + G
  coeff_zero' s := by simp [F.coeff_zero s, G.coeff_zero s]
  summable' := by
    intro s
    apply NNReal.summable_of_le _ ((F.summable s).add (G.summable s))
    intro n
    rw [← add_mul, ← Nat.cast_add]
    apply mul_le_mul_right'
    rw [Nat.cast_le]
    exact Int.natAbs_add_le _ _

/-- Subtraction in `Lbar r' S`, defined as pointwise subtraction. -/
def sub (F : Lbar r' S) (G : Lbar r' S) : Lbar r' S
    where
  toFun := F - G
  coeff_zero' s := by simp [F.coeff_zero s, G.coeff_zero s]
  summable' := by
    intro s
    apply NNReal.summable_of_le _ ((F.summable s).add (G.summable s))
    intro n
    rw [← add_mul, ← Nat.cast_add]
    apply mul_le_mul_right'
    rw [Nat.cast_le]
    exact Int.natAbs_sub_le _ _

/-- Negation in `Lbar r' S`, defined as pointwise negation. -/
def neg (F : Lbar r' S) : Lbar r' S where
  toFun := -F
  coeff_zero' s := by simp [F.coeff_zero s]
  summable' := by
    intro s
    convert F.summable s using 1
    ext n
    simp only [Pi.neg_apply, Int.natAbs_neg]

instance : Zero (Lbar r' S) :=
  ⟨zero⟩

instance : Add (Lbar r' S) :=
  ⟨add⟩

instance : Sub (Lbar r' S) :=
  ⟨sub⟩

instance : Neg (Lbar r' S) :=
  ⟨neg⟩

instance : Inhabited (Lbar r' S) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : Lbar r' S) = 0 :=
  rfl

@[simp]
theorem coe_add (F G : Lbar r' S) : ⇑(F + G : Lbar r' S) = F + G :=
  rfl

@[simp]
theorem coe_sub (F G : Lbar r' S) : ⇑(F - G : Lbar r' S) = F - G :=
  rfl

@[simp]
theorem coe_neg (F : Lbar r' S) : ⇑(-F : Lbar r' S) = -F :=
  rfl

--instance fff : topological_ring ℝ≥0 :=
--{ continuous_add := continuous_add,
--  continuous_mul := continuous_mul }
/-- Tailored scalar multiplication by natural numbers. -/
protected def nsmul (N : ℕ) (F : Lbar r' S) : Lbar r' S
    where
  toFun s n := N • F s n
  coeff_zero' s := by simp only [F.coeff_zero, smul_zero]
  summable' s := by
    convert Summable.mul_left (↑N) (F.summable' s)
    ext
    simp only [← mul_assoc, nsmul_eq_mul, Nonneg.coe_mul, Int.natAbs_mul]
    norm_cast

/-- Tailored scalar multiplication by integers. -/
protected def zsmul (N : ℤ) (F : Lbar r' S) : Lbar r' S
    where
  toFun s n := N • F s n
  coeff_zero' s := by simp only [F.coeff_zero, smul_zero]
  summable' s := by
    refine' nnreal.summable_coe.mp _
    convert Summable.mul_left (↑N.nat_abs) (nnreal.summable_coe.mpr (F.summable' s))
    ext
    simp only [← mul_assoc, Int.natAbs_mul, smul_eq_mul, Nat.cast_mul, Nonneg.coe_mul]
    norm_cast

instance : AddCommGroup (Lbar r' S) where
  zero := 0
  add := (· + ·)
  sub := Sub.sub
  neg := Neg.neg
  zero_add := by intros; ext; simp only [coe_zero, zero_add, coe_add]
  add_zero := by intros; ext; simp only [coe_zero, add_zero, coe_add]
  add_assoc := by intros; ext; simp only [add_assoc, coe_add]
  add_left_neg := by
    intros; ext
    simp only [coe_add, coe_neg, coe_zero, Pi.add_apply, Pi.zero_apply, Pi.neg_apply, add_left_neg]
  add_comm := by intros; ext; simp only [coe_add, add_comm]
  sub_eq_add_neg := by intros; ext; simp only [coe_sub, coe_add, coe_neg, sub_eq_add_neg]
  nsmul n F := F.nsmul n
  nsmul_zero F := by ext; simp only [Lbar.nsmul, zero_smul]; rfl
  nsmul_succ n F := by
    ext
    simp only [Lbar.nsmul, Nat.succ_eq_add_one, add_smul, one_smul, add_comm, coe_mk, coe_add,
      Pi.add_apply]
  zsmul n F := F.zsmul n
  zsmul_zero' F := by ext; simp only [Lbar.zsmul, zero_smul]; rfl
  zsmul_succ' n F := by
    ext
    simp only [Lbar.zsmul, Nat.succ_eq_add_one, Algebra.id.smul_eq_mul, coe_mk, Pi.add_apply,
      Int.ofNat_succ, Int.ofNat_eq_coe, coe_add, add_mul, one_mul, add_comm]
  zsmul_neg' n F := by
    ext
    simp only [Lbar.zsmul, Algebra.id.smul_eq_mul, coe_mk, Pi.neg_apply, Int.ofNat_succ, coe_neg,
      add_mul, one_mul, neg_add_rev, Int.negSucc_coe, neg_mul, one_mul]

theorem zero_apply (s : S) (n : ℕ) : (0 : Lbar r' S) s n = 0 :=
  rfl

theorem zmul_apply (F : Lbar r' S) (c : ℤ) :
    ((c • F : Lbar r' S) : S → ℕ → ℤ) = fun s n => c • F s n :=
  rfl

theorem Fintype.lbar_noZeroSMulDivisors (T : FintypeCat.{u}) (r') :
    NoZeroSMulDivisors ℤ (Lbar r' T) := by
  fconstructor
  intro c F hF
  by_cases hc : c = 0
  · apply Or.intro_left; exact hc
  · apply Or.intro_right
    ext s n
    rw [ext_iff, zmul_apply, Function.funext_iff] at hF 
    specialize hF s
    rw [Function.funext_iff] at hF 
    specialize hF n
    simp only [smul_eq_zero, hc, false_or_iff, zero_apply] at hF ⊢
    exact hF

/-- The `coeff s n` is the additive homomorphism that sends `x : Lbar r' S`
to the coefficient `x_{s,n}`. -/
@[simps]
def coeff (s : S) (n : ℕ) : Lbar r' S →+ ℤ
    where
  toFun x := x s n
  map_zero' := rfl
  map_add' x y := rfl

/-- The norm of `F : Lbar r' S` as nonnegative real number.
It is defined as `∑ s, ∑' n, (↑(F s n).nat_abs * r' ^ n)`. -/
protected def nnnorm (F : Lbar r' S) : ℝ≥0 :=
  ∑ s, ∑' n, ↑(F s n).natAbs * r' ^ n

instance : NNNorm (Lbar r' S) :=
  ⟨Lbar.nnnorm⟩

theorem nnnorm_def (F : Lbar r' S) : ‖F‖₊ = ∑ s, ∑' n, ↑(F s n).natAbs * r' ^ n :=
  rfl

@[simp]
theorem nnnorm_zero : ‖0 : Lbar r' S‖₊ = 0 := by
  simp only [nnnorm_def, Lbar.coe_zero, tsum_zero, Nat.cast_zero, MulZeroClass.zero_mul,
    Pi.zero_apply, zero_le', Finset.sum_const_zero, Int.natAbs_zero]

@[simp]
theorem nnnorm_neg (F : Lbar r' S) : ‖-F‖₊ = ‖F‖₊ := by
  simp only [nnnorm_def, Lbar.coe_neg, Pi.neg_apply, Int.natAbs_neg, Int.natAbs, coe_neg,
    Set.mem_setOf_eq]

theorem nnnorm_add_le (F₁ F₂ : Lbar r' S) : ‖F₁ + F₂‖₊ ≤ ‖F₁‖₊ + ‖F₂‖₊ :=
  by
  simp only [nnnorm_def, ← Finset.sum_add_distrib]
  refine' Finset.sum_le_sum _
  rintro s -
  rw [← tsum_add (F₁.summable s) (F₂.summable s)]
  refine' tsum_le_tsum _ ((F₁ + F₂).Summable _) ((F₁.summable s).add (F₂.summable s))
  intro n
  dsimp
  rw [← add_mul, ← Nat.cast_add]
  apply mul_le_mul_right'
  rw [Nat.cast_le]
  exact Int.natAbs_add_le _ _

theorem nnnorm_sum_le {ι : Type _} (s : Finset ι) (F : ι → Lbar r' S) :
    ‖∑ i in s, F i‖₊ ≤ ∑ i in s, ‖F i‖₊ := by
  classical
  apply Finset.induction_on s <;> clear s
  · simp only [Finset.sum_empty, nnnorm_zero]
  intro i s his IH
  simp only [Finset.sum_insert his]
  exact (nnnorm_add_le _ _).trans (add_le_add le_rfl IH)

instance pseudoNormedGroup : PseudoNormedGroup (Lbar r' S)
    where
  filtration' c := {F | ‖F‖₊ ≤ c}
  filtration_mono' c₁ c₂ h F hF := le_trans hF h
  zero_mem_filtration' c := by dsimp; rw [nnnorm_zero]; apply zero_le'
  neg_mem_filtration' c F hF := by dsimp; rwa [nnnorm_neg]
  add_mem_filtration' c₁ c₂ F₁ F₂ hF₁ hF₂ := le_trans (nnnorm_add_le _ _) (add_le_add hF₁ hF₂)

theorem mem_filtration_iff (x : Lbar r' S) (c : ℝ≥0) :
    x ∈ PseudoNormedGroup.filtration (Lbar r' S) c ↔ ‖x‖₊ ≤ c :=
  Iff.rfl

/-- The coercion from `Lbar r' S` to functions `S → ℕ → ℤ`.
This is an additive group homomorphism.
-/
def coeHom : Lbar r' S →+ S → ℕ → ℤ :=
  AddMonoidHom.mk' coeFn <| coe_add

@[simp]
theorem coe_sum {ι : Type _} (s : Finset ι) (F : ι → Lbar r' S) :
    ⇑(∑ i in s, F i) = ∑ i in s, F i :=
  show coeHom (∑ i in s, F i) = ∑ i in s, coeHom (F i) from AddMonoidHom.map_sum _ _ _

@[simp]
theorem coe_zsmul (n : ℤ) (F : Lbar r' S) : ⇑(n • F) = n • F :=
  rfl

@[simp]
theorem coe_nsmul (n : ℕ) (F : Lbar r' S) : ⇑(n • F) = n • F :=
  rfl

@[simp]
theorem nnnorm_zsmul (N : ℤ) (F : Lbar r' S) : ‖N • F‖₊ = ‖N‖₊ * ‖F‖₊ :=
  by
  simp only [nnnorm_def, Finset.mul_sum]
  apply Fintype.sum_congr
  intro s
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_tsum, ← tsum_mul_left, ← mul_assoc, NNReal.coe_natAbs,
    coe_nnnorm, coe_zsmul, Pi.smul_apply, Int.norm_eq_abs, ← abs_mul, ← Int.cast_mul, smul_eq_mul]

theorem nnnorm_nsmul (x : Lbar r' S) (N : ℕ) : ‖N • x‖₊ = N • ‖x‖₊ := by
  rw [← coe_nat_zsmul, nnnorm_zsmul, nsmul_eq_mul, ← NNReal.coe_natAbs]; rfl

section Tinv

/-- The action of T⁻¹.
-/
def tinvAux {R : Type _} [Zero R] : (ℕ → R) → ℕ → R := fun F n => if n = 0 then 0 else F (n + 1)

@[simp]
theorem tinvAux_zero {R : Type _} [Zero R] (f : ℕ → R) : tinvAux f 0 = 0 :=
  rfl

@[simp]
theorem tinvAux_ne_zero {R : Type _} [Zero R] (f : ℕ → R) (i : ℕ) (hi : i ≠ 0) :
    tinvAux f i = f (i + 1) :=
  if_neg hi

@[simp]
theorem tinvAux_succ {R : Type _} [Zero R] (f : ℕ → R) (i : ℕ) : tinvAux f (i + 1) = f (i + 2) :=
  if_neg (Nat.succ_ne_zero i)

theorem tinvAux_summable [h0r : Fact (0 < r')] (F : Lbar r' S) (s : S) :
    Summable fun n => ↑(tinvAux (F s) n).natAbs * r' ^ n :=
  by
  have : ∀ n : ℕ, r' ^ n = r' ^ n * r' * r'⁻¹ := by intro; rw [mul_inv_cancel_right₀ h0r.out.ne']
  conv =>
    congr
    ext
    rw [this, ← mul_assoc]
  apply Summable.mul_right
  refine' NNReal.summable_of_le _ (NNReal.summable_nat_add _ (F.summable s) 1)
  rintro ⟨i⟩
  · simp only [Nat.cast_zero, MulZeroClass.zero_mul, Tinv_aux_zero, zero_le', Int.natAbs_zero]
  · simp only [Tinv_aux_succ, pow_add, mul_assoc, pow_one]

/-- The `T⁻¹` action on `Lbar r' S`.
This is defined, essentially, as a shift in `ℕ` (accounting for the restriction at 0).
This is an additive group homomorphism.
-/
def tinv {r : ℝ≥0} {S : Type u} [Fintype S] [h0r : Fact (0 < r)] : Lbar r S →+ Lbar r S :=
  AddMonoidHom.mk'
    (fun F =>
      { toFun := fun s => tinvAux (F s)
        coeff_zero' := fun s => rfl
        summable' := tinvAux_summable F })
    (by
      intro F G
      ext s (_ | n)
      · simp only [add_zero, Pi.add_apply, Lbar.coeff_zero]
      · simp only [coe_mk, Pi.add_apply, Tinv_aux_succ, coe_add])

@[simp]
theorem tinv_zero [Fact (0 < r')] (F : Lbar r' S) (s : S) : tinv F s 0 = 0 :=
  rfl

@[simp]
theorem tinv_ne_zero [Fact (0 < r')] (F : Lbar r' S) (s : S) (i : ℕ) (hi : i ≠ 0) :
    tinv F s i = F s (i + 1) :=
  if_neg hi

@[simp]
theorem tinv_succ [Fact (0 < r')] (F : Lbar r' S) (s : S) (i : ℕ) :
    tinv F s (i + 1) = F s (i + 2) :=
  tinvAux_succ (F s) i

open PseudoNormedGroup

theorem tinv_mem_filtration [h0r : Fact (0 < r')] :
    tinv ∈ filtration (Lbar r' S →+ Lbar r' S) r'⁻¹ :=
  by
  intro c F hF
  simp only [Tinv, AddMonoidHom.mk'_apply]
  change _ ≤ _ at hF 
  rw [mul_comm]
  apply le_mul_inv_of_mul_le h0r.out.ne'
  rw [nnnorm_def, Finset.sum_mul]
  apply le_trans _ hF
  apply Finset.sum_le_sum
  rintro s -
  rw [← NNReal.tsum_mul_right]
  conv_rhs => rw [← sum_add_tsum_nat_add' 1 (F.summable s)]
  refine' le_add_of_nonneg_of_le zero_le' _
  apply tsum_le_tsum
  · rintro (_ | i)
    · simp only [Nat.cast_zero, MulZeroClass.zero_mul, Lbar.coeff_zero, Int.natAbs_zero];
      exact zero_le'
    · simp only [Tinv_aux_succ, mul_assoc, coe_mk, pow_succ']
  · exact (Tinv_aux_summable F s).mulRight _
  · exact (NNReal.summable_nat_add_iff 1).mpr (F.summable s)

end Tinv

/-- `of_mask x mask : Lbar r' S` is `∑ a_{s,n}T^n ∈ Tℤ[[T]]`,
where `a_{s,n}` is `x_{s,n}` if `mask n s` is true and `0` otherwise. -/
@[simps]
def ofMask (x : Lbar r' S) (mask : S → ℕ → Prop) [∀ s n, Decidable (mask s n)] : Lbar r' S
    where
  toFun s n := if mask s n then x s n else 0
  coeff_zero' s := by split_ifs; · exact x.coeff_zero s; · rfl
  summable' s := by
    apply NNReal.summable_of_le _ (x.summable s)
    intro n
    refine' mul_le_mul' _ le_rfl
    norm_cast
    split_ifs
    · rfl
    · rw [Int.natAbs_zero]; exact zero_le'

variable (r' S)

/-- `geom r' S` is `∑ T^n ∈ Tℤ[[T]]`.
In other words, all non-constant coefficients are `1`. -/
@[simps]
def geom [hr' : Fact (r' < 1)] : Lbar r' S
    where
  toFun s n := if n = 0 then 0 else 1
  coeff_zero' s := if_pos rfl
  summable' s := by
    have := @summable_geometric_of_norm_lt_1 _ _ (r' : ℝ) _; swap
    · rw [NNReal.norm_eq]; exact hr'.out
    simp only [← NNReal.coe_pow, NNReal.summable_coe] at this 
    apply NNReal.summable_of_le _ this
    intro n
    refine' (mul_le_mul' _ le_rfl).trans (one_mul _).le
    split_ifs <;> simp

section Map

variable {r' S} {T : Type _} [Fintype T] (f : S → T)

open scoped Classical

theorem hasSum_aux (F : Lbar r' S) :
    HasSum (fun n : ℕ => (∑ s, ↑(F s n).natAbs) * r' ^ n) (∑ s, ∑' n, (F s n).natAbs * r' ^ n) :=
  by
  have :
    (fun n : ℕ => (∑ s : S, ↑(F s n).natAbs) * r' ^ n) = fun n : ℕ =>
      ∑ s : S, ↑(F s n).natAbs * r' ^ n :=
    by
    funext n
    rw [Finset.sum_mul]
  rw [this]; clear this
  exact hasSum_sum fun s _ => (F.summable s).HasSum

/-- Given an element of `Lbar r' S` and a function `f : S → T`, this
  constructs an associated element of `Lbar r' T`. -/
@[simps]
def map : Lbar r' S → Lbar r' T := fun F =>
  { toFun := fun t n => ∑ s in Finset.univ.filterₓ fun s' => f s' = t, F s n
    coeff_zero' := fun s => by simp
    summable' := fun t =>
      haveI :
        ∀ n : ℕ,
          ↑(∑ s : S in finset.univ.filter fun s' : S => f s' = t, F s n).natAbs * r' ^ n ≤
            (∑ s : S, (F s n).natAbs) * r' ^ n :=
        by
        intro n
        refine' mul_le_mul _ (le_refl _) zero_le' zero_le'
        simp_rw [← Nat.cast_sum]
        apply nat.cast_le.mpr
        have :
          (∑ s : S in finset.univ.filter fun s' : S => f s' = t, F s n).natAbs ≤
            ∑ s : S in finset.univ.filter fun s' => f s' = t, (F s n).natAbs :=
          by apply nat_abs_sum_le
        refine' le_trans this _
        apply Finset.sum_le_sum_of_subset
        · intro t ht; simp
        · infer_instance
      NNReal.summable_of_le this (HasSum.summable (Lbar.hasSum_aux _)) }

theorem map_id (F : Lbar r' S) : F.map id = F :=
  by
  ext s n
  simp [Finset.sum_filter]

theorem map_comp (F : Lbar r' S) {U : Type _} [Fintype U] (g : T → U) :
    F.map (g ∘ f) = (F.map f).map g := by
  ext u n
  dsimp
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr
    ext s
    constructor
    · intro hs
      simpa using hs
    · intro hs
      simpa using hs
    · tauto
  · rintro t1 ht1 t2 ht2 h s hs
    simp at ht1 ht2 hs ⊢
    refine' h _
    rw [← hs.1, ← hs.2]

theorem nnnorm_map_le_of_nnnorm_le {c : ℝ≥0} (F : Lbar r' S) (hF : ‖F‖₊ ≤ c) :
    ‖F.map f‖₊ ≤ c := by
  simp [Lbar.nnnorm_def] at *
  rw [← tsum_sum] at hF ⊢
  · refine' le_trans (tsum_le_tsum _ _ _) hF
    · intro n
      simp_rw [← Finset.sum_mul]
      refine' mul_le_mul _ (le_refl _) zero_le' zero_le'
      simp_rw [← Nat.cast_sum]
      rw [Nat.cast_le]
      have :
        ∑ x : T, (∑ s : S in finset.univ.filter fun s' : S => f s' = x, F s n).natAbs ≤
          ∑ x : T, ∑ s : S in finset.univ.filter fun s' => f s' = x, (F s n).natAbs :=
        by
        apply Finset.sum_le_sum
        intro t ht
        apply nat_abs_sum_le
      refine' le_trans this _
      rw [← Finset.sum_biUnion]
      apply Finset.sum_le_sum_of_subset
      · intro t ht; simp
      · intro t1 ht1 t2 ht2 h s hs
        simp at ht1 ht2 hs ⊢
        apply h
        rw [← hs.1, ← hs.2]
    · apply summable_sum
      intro t ht
      apply (F.map f).Summable
    · apply summable_sum
      intro s hs
      apply F.summable
  · intro t ht
    apply (F.map f).Summable
  · intro s hs
    apply F.summable

end Map

end Lbar

#lint

