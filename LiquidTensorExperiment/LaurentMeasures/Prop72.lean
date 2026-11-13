import Mathlib.Data.Real.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.NormedSpace.Basic
import LiquidTensorExperiment.ForMathlib.Nnreal
import LiquidTensorExperiment.ForMathlib.NnrealIntBinary

#align_import laurent_measures.prop72

-- basic binary expansion for nnreal.
-- basic binary expansion for nnreal.
open scoped NNReal

/-

# Two auxiliary lemmas.

In this file we prove two technical lemmas, needed in the proofs of parts (2) and (4)
of Proposition 7.2 of `Analytic.pdf`.

## Lemma 1 (needed in part 2)

Say `f : ℤ → ℝ` and `r : ℝ≥0` with `2⁻¹<r<1`.
Say the support of `f` is bounded below by `d` (i.e. `n < d → f n = 0`),
We think of `f` as a power series `∑ₙf(n)Tⁿ` in `ℤ⟦T⟧[T⁻¹]`.

Here's the set-up. Support that `∑' (n : ℤ), ∥f n∥₊ * r ^ n` converges and is `≤ c`
(so in particular `f(T)` converges for `∥T∥ ≤ c`). Suppose also that
`∑' (n : ℤ), f n * 2⁻¹ ^ n = 0` (so `f` has a zero at `2⁻¹`; note that the sum
converges because `0 ≤ 2⁻¹ < r`).

The conclusion is that `∑(n ≥ d) ∥∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ∥ * r^n`
also converges and is bounded above by `c * (2 - r⁻¹)⁻¹`.

The power series `∑(n≥d) (∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ) * Tⁱ` is the power
series of `f(T)/(T⁻¹-2)`, and the reason it behaves reasonsbly is the
assumption that T⁻¹-2 has a simple zero at 2⁻¹ and no other zeros in
the disc radius `r`.

### Implementation detail

In Lean the second sum is `∑' (n : ℤ), ∥ite (d ≤ n)`
  `((finset.range (n - d).nat_abs.succ).sum (λ (l : ℕ), f (n - 1 - ↑l) * 2 ^ l))`
  `0∥₊ * r ^ n`.

### The maths proof

  ∑(n ≥ d) ∥∑(0≤i≤(n-d)) f(n - 1 - i)*2ⁱ∥ * r^n
= ∑(n ≥ d) ∥∑(i≥0) f(n - 1 - i)2ⁱ∥ * rⁿ (as f(n-1-i) vanishes for i larger than n-d)
= ∑(n ≥ d) ∥(i<0) f(n - 1 - i)2ⁱ∥ * rⁿ (as sum f(x)2⁻ˣ=0)
= ∑(n ≥ d) ∥∑(k≥0) f(n + k) 2^(-1-k)∥ * rⁿ (set k=-1-i)
≤ ∑(n ≥ d) ∑(k≥0)∥ f(n+k)∥ 2^(-1-k) r^n (Cauchy-Schwarz)
= ∑(k≥0) ∑(n≥d) ∥f(n+k)∥2^(-1-k)r^n (turns out you can interchange the sums)
= 2⁻¹∑(k≥0) (∑(n≥d) ∥f(n+k)∥r^(n+k)) * (2r)^{-k} (rearranging)
≤ 2⁻¹∑(k≥0) c (2r)^{-k} (defining property of c)
= 2⁻¹ * c / (1-(2r)⁻¹) (sum of a GP)
= c * (2-r⁻¹)⁻¹ (rearranging)

### Comments on the maths proof

The logic in this proof is completely standard but needs a little thinking about
when formalising. Some of the manipulations we are doing in the earlier lines
of the proof (for example interchanging the sums) are only valid if the sum converges.
However ultimately the proof that the sum converges only happens on the last-but-one
line of  the computation, where we prove that it's bounded above by something finite
(the sum of a GP).

There are several ways to fix this.

* One can go through the proof twice. In the first pass one can prove that everything
is `summable`, and then in the second pass one can then prove the results about equality
or boundedness of sums. This has the disadvantage that you have to do everything twice.

* Another approach is to write the proof once, but backwards; start with the sum of a geometric
progression and then go upwards through the maths proof above to deduce convergence and boundedness
of the original sum simultaneously. This has the mild disadvantage that you have to write
the proof backwards.

* A third approach would be to work not with `tsum` and `summable` at all, but to work
with `has_sum`. This has the disadvantage that you need to stop working with
equalities `∑a(n)=∑b(n)` or inequalities `∑a(n) ≤ ∑b(n)` and to start working with more complex
statements such as `has_sum a s ↔ has_sum b s` or `has_sum a s → ∃ t, has_sum b t ∧ t ≤ s`.

* The fourth approach avoids all of this. Instead of working with sums valued in `ℝ≥0` we
can work with sums taking values in `ℝ≥0∞` a.k.a. the interval `[0,∞]`.

## TODO

Switch to ennreal and then prove 6 lemmas for the first result. All the
summability results are in `thm69` so it's simply a case of
refactoring all of them.

-/
theorem Real.nnnorm_int (n : ℤ) : ‖n : ℝ‖₊ = ‖n‖₊ :=
  Subtype.ext <| by simp [coe_nnnorm, Real.norm_eq_abs, Int.norm_eq_abs]

theorem Real.neg_nnnorm_of_neg {r : ℝ} (hr : r < 0) : -(‖r‖₊ : ℝ) = r := by
  rw [coe_nnnorm, neg_eq_iff_neg_eq, Real.norm_eq_abs, abs_of_neg hr]

namespace PsiAuxLemma

/-

## The first lemma

-/
open scoped ENNReal

-- line 7 ≤ line 10
theorem step7 {f : ℤ → ℝ} {d : ℤ} {r : ℝ≥0} (hr2 : 2⁻¹ < r)
    (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n) :-- do I use hconv??
      ∑' b : ℕ,
        (∑' i : ℕ, (‖(f (d + ↑b + ↑i))‖₊ : ℝ≥0∞) * r ^ (d + b + i)) * (2 * r)⁻¹ ^ b ≤
      2 * (↑(2 - r⁻¹)⁻¹ * ∑' a : ℤ, ‖f a‖₊ * r ^ a) :=
  by
  have bound :
    ∀ z : ℤ,
      ∑' i : ℕ, (‖(f (z + ↑i))‖₊ : ℝ≥0∞) * r ^ (z + ↑i) ≤
        ∑' a : ℤ, ‖f a‖₊ * r ^ a :=
    by
    intro z
    refine' tsum_le_tsum_of_inj (fun i => z + i) _ _ _ ENNReal.summable ENNReal.summable
    · intro a b h; simpa using h
    · intros; exact ENNReal.zero_le'
    · intros; apply le_refl _
  suffices
    ∑' b : ℕ, (∑' a : ℤ, (‖f a‖₊ : ℝ≥0∞) * r ^ a) * (2 * ↑r)⁻¹ ^ b =
      2 * (↑(2 - r⁻¹)⁻¹ * ∑' a : ℤ, ↑(‖f a‖₊) * ↑r ^ a)
    by
    rw [← this]
    apply ENNReal.tsum_le_tsum
    intro a
    apply ENNReal.hMul_le_hMul_of_right
    apply bound
  rw [ENNReal.tsum_mul_left, mul_comm, ← mul_assoc]
  congr
  rw [ENNReal.tsum_geometric]
  apply ENNReal.inv_eq_of_hMul_eq_one
  rw [← mul_assoc]
  have hr : 0 < 2 - r⁻¹ := by
    rw [NNReal.sub_pos]
    exact NNReal.inv_lt_of_inv_lt (by norm_num) hr2
  rw [ENNReal.coe_inv hr.ne']
  apply ENNReal.hMul_inv_eq_of_eq_hMul (by exact_mod_cast hr.ne') ENNReal.coe_ne_top
  rw [ENNReal.sub_mul, one_mul, one_mul, ENNReal.coe_sub]
  · congr
    refine' ENNReal.hMul_eq_of_hMul_inv_eq (by norm_num) (by norm_num) _
    rw [ENNReal.mul_inv, mul_comm, ENNReal.coe_inv]
    · refine' (lt_of_le_of_lt (by norm_num) hr2).ne'
    · left; norm_num
    · left; norm_num
  · intros; norm_num

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- line 5 ≤ line 10
theorem step6 {f : ℤ → ℝ} {d : ℤ} {r : ℝ≥0} (hr2 : 2⁻¹ < r) (hdf : ∀ n, n < d → f n = 0)
    (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n) :
    (2⁻¹ : ℝ≥0∞) * ∑' (i : ℕ) (j : ℕ), ↑(‖(f (d + ↑i + ↑j) * 2⁻¹ ^ j)‖₊) * ↑(r ^ (d + ↑i)) ≤
      ↑(2 - r⁻¹)⁻¹ * ∑' a : ℤ, ↑(‖f a‖₊ * r ^ a) :=
  by
  rw [ENNReal.tsum_comm]
  -- woohoo, I just interchanged the sums
  simp_rw [nnnorm_mul, nnnorm_pow, ENNReal.coe_mul,
    ENNReal.coe_zpow (lt_of_le_of_lt zero_le' hr2).ne']
  push_cast
  simp only [nnnorm_inv, Real.nnnorm_two, ENNReal.coe_inv, Ne.def, bit0_eq_zero, one_ne_zero,
    not_false_iff, ENNReal.coe_bit0, ENNReal.coe_one]
  have h2ne0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2netop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hrne0 : (r : ℝ≥0∞) ≠ 0 := by
    norm_cast
    refine' (lt_of_le_of_lt _ hr2).ne'
    norm_num
  have hrnetop : (r : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [ENNReal.inv_hMul_le_iff h2ne0 h2netop]
  have :
    ∀ a b : ℕ,
      (‖(f (d + ↑a + ↑b))‖₊ : ℝ≥0∞) * 2⁻¹ ^ b * ↑r ^ (d + ↑a) =
        ‖(f (d + ↑a + ↑b))‖₊ * r ^ (d + a + b) * (2 * r)⁻¹ ^ b :=
    by
    intro a b
    rw [ENNReal.mul_inv (Or.inl h2ne0) (Or.inl h2netop), mul_pow, ← zpow_ofNat (↑r)⁻¹]
    rw [ENNReal.zpow_add hrne0 hrnetop _ b]
    have :
      (‖(f (d + ↑a + ↑b))‖₊ : ℝ≥0∞) * (↑r ^ (d + ↑a) * ↑r ^ (b : ℤ)) *
          (2⁻¹ ^ b * (↑r)⁻¹ ^ (b : ℤ)) =
        ↑(‖(f (d + ↑a + ↑b))‖₊) * 2⁻¹ ^ b * ↑r ^ (d + ↑a) * (r ^ (b : ℤ) * r⁻¹ ^ (b : ℤ)) :=
      by ring
    rw [this]
    convert (mul_one _).symm
    rw [← ENNReal.coe_inv (by exact_mod_cast hrne0)]
    norm_cast
    rw [← mul_pow]
    rw [mul_inv_cancel (by exact_mod_cast hrne0)]
    apply one_pow
  simp_rw [this, ENNReal.tsum_mul_right, add_right_comm]
  exact step7 hr2 hconv

-- auxiliary convergence lemma
theorem step5 {f : ℤ → ℝ} {d : ℤ} {r : ℝ≥0} (hr2 : 2⁻¹ < r) (hdf : ∀ n, n < d → f n = 0)
    (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n) :
    Summable fun x : ℤ => f x * 2⁻¹ ^ x :=
  by
  rw [← summable_subtype_and_compl]
  change (Summable fun x : {n : ℤ | n < 0} => _) ∧ _
  constructor
  · let F : Finset ↥{n : ℤ | n < 0} :=
      Finset.preimage (Finset.Ico d 0 : Finset ℤ) coe
        (Set.injOn_of_injective Subtype.coe_injective _)
    apply summable_of_ne_finset_zero
    rintro b (hb : b ∉ F)
    convert MulZeroClass.zero_mul _
    apply hdf
    by_contra hbd; push_neg at hbd 
    apply hb
    rw [Finset.mem_preimage]
    rw [Finset.mem_Ico]
    exact ⟨hbd, b.2⟩
  · apply Summable.of_nnnorm
    have := NNReal.summable_subtype hconv ({n : ℤ | n < 0}ᶜ)
    refine' NNReal.summable_of_le _ this
    rintro ⟨b, hb : ¬b < 0⟩
    push_neg at hb 
    rw [nnnorm_mul]
    suffices ‖f b‖₊ * (2 ^ b)⁻¹ ≤ ‖f b‖₊ * r ^ b by simpa
    apply NNReal.hMul_le_hMul_left
    rw [← inv_zpow]
    apply NNReal.zpow_le_zpow' hb hr2.le

example (r : ℝ≥0) (n : ℕ) : r ^ (n : ℤ) = r ^ n :=
  zpow_ofNat r n

noncomputable instance xxx : DivInvMonoid ℝ≥0 :=
  inferInstance

-- second line is third line
theorem step4 {f : ℤ → ℝ} {n d : ℤ} {r : ℝ≥0} (hr1 : r < 1) (hr2 : 2⁻¹ < r)
    (hdf : ∀ n, n < d → f n = 0) (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n)
    (hzero : ∑' n, f n * 2⁻¹ ^ n = 0) :
    ∑' l : ℕ, f (n - 1 - ↑l) * 2 ^ l = 2⁻¹ * -∑' m : ℕ, f (n + m) * 2⁻¹ ^ m :=
  by
  have : ∀ l : ℕ, (2 : ℝ) ^ l = 2⁻¹ ^ (n - 1 - l) * (2⁻¹ * 2 ^ n) :=
    by
    intro l
    rw [inv_zpow, ← zpow_neg, ← zpow_neg_one, ← zpow_ofNat]
    push_cast
    rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    ring_nf
  conv_lhs =>
    congr
    ext
    rw [this, ← mul_assoc]
  clear this
  rw [tsum_mul_right]
  have : ∀ m : ℕ, (2⁻¹ : ℝ) ^ m = 2⁻¹ ^ (n + m) * 2 ^ n :=
    by
    intro m
    rw [inv_zpow, ← zpow_neg, ← zpow_ofNat, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), inv_zpow, ←
      zpow_neg]
    ring_nf
  conv_rhs =>
    congr
    skip
    congr
    congr
    ext
    rw [this, ← mul_assoc]
  clear this
  rw [mul_comm, mul_assoc, tsum_mul_right, ← neg_mul, mul_comm ((2 : ℝ) ^ n)]
  congr
  rw [eq_neg_iff_add_eq_zero, add_comm, ← hzero, ←
    tsum_add_tsum_compl
      ((step5 hr2 hdf hconv).comp_injective Subtype.coe_injective :
        Summable ((_ : ℤ → ℝ) ∘ (coe : {z : ℤ | n ≤ z} → ℤ)))
      ((step5 hr2 hdf hconv).comp_injective Subtype.coe_injective)]
  · congr 1
    · rw [← ((Nat.equivLeInt n).tsum_eq : _ → (_ : ℝ) = _)]
      congr; ext b
      rw [add_comm n]
      rfl
    · rw [← ((Nat.equivLeIntCompl n).tsum_eq : _ → (_ : ℝ) = _)]
      congr; ext b
      rw [show n - 1 - b = n - (b + 1) by ring]
      rfl

-- second line ≤ last line
theorem step3 {f : ℤ → ℝ} {r : ℝ≥0} (hr1 : r < 1) (hr2 : 2⁻¹ < r) {d : ℤ}
    (hdf : ∀ n, n < d → f n = 0) (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n)
    (hzero : ∑' n, f n * 2⁻¹ ^ n = 0) :
    ∑' n : ℤ,
        ((‖(ite (d ≤ n) (∑' l : ℕ, f (n - 1 - ↑l) * 2 ^ l) 0)‖₊ * r ^ n : ℝ≥0) : ℝ≥0∞) ≤
      ((2 - r⁻¹)⁻¹ * ∑' n : ℤ, ‖f n‖₊ * r ^ n : ℝ≥0) :=
  by
  simp_rw [step4 hr1 hr2 hdf hconv hzero]
  -- n - d = m
  rw [tsum_eq_tsum_of_ne_zero_bij
      fun m :
        Function.support fun m : ℕ =>
          ((‖((2⁻¹ : ℝ) * -∑' l : ℕ, f (d + m + ↑l) * 2⁻¹ ^ l)‖₊ * r ^ (d + m) : ℝ≥0) :
            ℝ≥0∞) =>
      d + m.1]
  · dsimp only
    simp_rw [nnnorm_mul, nnnorm_neg]
    push_cast
    simp only [nnnorm_inv, Real.nnnorm_two, ENNReal.coe_inv, Ne.def, bit0_eq_zero, one_ne_zero,
      not_false_iff, ENNReal.coe_bit0, ENNReal.coe_one]
    have summable_half : ∀ t : ℤ, Summable fun x : ℕ => f (t + ↑x) * 2⁻¹ ^ x :=
      by
      intro t
      rw [summable_mul_right_iff (show (2 : ℝ)⁻¹ ^ t ≠ 0 from zpow_ne_zero _ (by norm_num))]
      simp_rw [mul_assoc, ← zpow_ofNat]
      simp_rw [← zpow_add₀ (show (2 : ℝ)⁻¹ ≠ 0 by norm_num), add_comm _ t]
      exact
        (step5 hr2 hdf hconv).comp_injective
          (show Function.Injective fun x : ℕ => t + x by intro x y hxy; simpa using hxy)
    suffices
      ∑' m : ℕ,
          (2⁻¹ : ℝ≥0∞) * ↑(∑' l : ℕ, ‖(f (d + ↑m + ↑l) * 2⁻¹ ^ l)‖₊ : ℝ≥0) *
            ↑(r ^ (d + ↑m)) ≤
        ↑(2 - r⁻¹)⁻¹ * ↑(∑' n : ℤ, ‖f n‖₊ * r ^ n)
      by
      refine' le_trans _ this
      apply ENNReal.tsum_le_tsum
      intro m
      apply ENNReal.hMul_le_hMul_of_right
      apply ENNReal.hMul_le_hMul_of_left
      norm_cast
      apply nnnorm_tsum_le
      rw [← NNReal.summable_iff_summable_nnnorm]
      apply summable_half
    rw [ENNReal.coe_tsum hconv]; dsimp only
    conv_lhs =>
      congr
      ext
      rw [ENNReal.coe_tsum
          (show Summable fun l : ℕ => ‖(f (d + m + ↑l) * 2⁻¹ ^ l)‖₊
            by
            rw [← NNReal.summable_iff_summable_nnnorm]
            apply summable_half)]
    dsimp only
    simp_rw [mul_assoc]
    rw [ENNReal.tsum_mul_left]
    simp_rw [← ENNReal.tsum_mul_right]
    apply step6 hr2 hdf hconv
  · rintro ⟨x, _⟩ ⟨y, _⟩ h
    have hxy : x = y := by simpa using h
    subst hxy
  · rintro n hn
    rw [Function.mem_support] at hn 
    split_ifs at hn  with hdn
    · rw [Set.mem_range]
      let m := (n - d).natAbs
      have hm : d + m = n := by
        apply add_eq_of_eq_sub'
        rw [Int.natAbs_of_nonneg]
        exact sub_nonneg.mpr hdn
      refine' ⟨⟨m, _⟩, hm⟩
      rw [Function.mem_support]
      convert hn
      rw [hm]
    · exfalso
      apply hn
      simp
  · simp

-- first line equals second line
theorem step2 {f : ℤ → ℝ} {n d : ℤ} (hn : d ≤ n) (hdf : ∀ n, n < d → f n = 0) :
    ((Finset.range (n - d).natAbs.succ).Sum fun l : ℕ => f (n - 1 - ↑l) * 2 ^ l) =
      ∑' l : ℕ, f (n - 1 - l) * 2 ^ l :=
  by
  apply (tsum_eq_sum _ : (_ : ℝ) = _).symm
  intro b hb
  convert MulZeroClass.zero_mul ((2 : ℝ) ^ b)
  apply hdf
  by_contra hbd
  push_neg at hbd 
  apply hb
  rw [Finset.mem_range, Nat.lt_succ_iff]
  suffices (b : ℤ) ≤ ((n - d).natAbs : ℤ) by assumption_mod_cast
  rw [← Int.eq_natAbs_of_zero_le] <;> linarith

-- coerce to ℝ≥0∞
theorem step1 {f : ℤ → ℝ} {r : ℝ≥0} (hr1 : r < 1) (hr2 : 2⁻¹ < r) {d : ℤ}
    (hdf : ∀ n, n < d → f n = 0) (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n)
    (hzero : ∑' n, f n * 2⁻¹ ^ n = 0) :
    ∑' n : ℤ,
        ((‖(ite (d ≤ n)
                  ((Finset.range (n - d).natAbs.succ).Sum fun l : ℕ => f (n - 1 - ↑l) * 2 ^ l) 0)‖₊ *
              r ^ n :
            ℝ≥0) :
          ℝ≥0∞) ≤
      ((2 - r⁻¹)⁻¹ * ∑' n : ℤ, ‖f n‖₊ * r ^ n : ℝ≥0) :=
  by
  have :
    ∀ n,
      ‖(ite (d ≤ n)
              ((Finset.range (n - d).natAbs.succ).Sum fun l : ℕ => f (n - 1 - ↑l) * 2 ^ l) 0)‖₊ *
          r ^ n =
        ‖(ite (d ≤ n) (∑' l : ℕ, f (n - 1 - l) * 2 ^ l) 0)‖₊ * r ^ n :=
    by
    intro n
    congr 2
    split_ifs with hn
    · rw [step2 hn hdf]
    · rfl
  simp_rw [this]
  apply step3 hr1 hr2 hdf hconv hzero

-- first line ≤ last line
theorem key_tsum_lemma (f : ℤ → ℝ) (r : ℝ≥0) (hr1 : r < 1) (hr2 : 2⁻¹ < r) (d : ℤ)
    (hdf : ∀ n, n < d → f n = 0) (hconv : Summable fun n : ℤ => ‖f n‖₊ * r ^ n)
    (hzero : ∑' n, f n * 2⁻¹ ^ n = 0) :
    ∑' n : ℤ,
        ‖(ite (d ≤ n)
              ((Finset.range (n - d).natAbs.succ).Sum fun l : ℕ => f (n - 1 - ↑l) * 2 ^ l) 0)‖₊ *
          r ^ n ≤
      (2 - r⁻¹)⁻¹ * ∑' n, ‖f n‖₊ * r ^ n :=
  by
  have := step1 hr1 hr2 hdf hconv hzero
  have this2 :
    ∑' n : ℤ,
        ((‖(ite (d ≤ n)
                  ((Finset.range (n - d).natAbs.succ).Sum fun l : ℕ => f (n - 1 - ↑l) * 2 ^ l) 0)‖₊ *
              r ^ n :
            ℝ≥0) :
          ℝ≥0∞) <
      ⊤ :=
    by
    refine' lt_of_le_of_lt this _
    exact ENNReal.coe_lt_top
  have this3 :
    Summable fun n =>
      (‖(ite (d ≤ n)
              ((Finset.range (n - d).natAbs.succ).Sum fun l : ℕ => f (n - 1 - ↑l) * 2 ^ l) 0)‖₊ *
          r ^ n :
        ℝ≥0) :=
    ennreal.tsum_coe_ne_top_iff_summable.mp this2.ne
  rw [← ENNReal.coe_le_coe]
  convert this
  apply ENNReal.coe_tsum this3

end PsiAuxLemma

/-

## The second lemma

-/
namespace ThetaAuxLemma

-- Here is the fact which Clausen/Scholze need for the application to "splitting θ
-- in a bounded way".
theorem tsum_le (r : ℝ≥0) {s : ℝ≥0} (hs0 : 0 < s) (hs : s < 1) :
    ∑' n : ℤ, (NNReal.Int.binary r n : ℝ≥0) * s ^ n ≤
      s ^ ⌈Real.log r / Real.log (2⁻¹ : ℝ≥0)⌉ * (1 - s)⁻¹ :=
  by
  let d := ⌈Real.log r / Real.log (2⁻¹ : ℝ≥0)⌉
  rw [mul_comm]
  rw [← NNReal.Int.tsum_add_tsum_compl' {n : ℤ | n < d} (NNReal.Int.binary_summable r hs)]
  have h0 : ∑' x : ↥{n : ℤ | n < d}, (fun n : ℤ => ↑(NNReal.Int.binary r n) * s ^ n) ↑x = 0 :=
    by
    convert (tsum_zero : _ = (0 : ℝ≥0)); ext ⟨n, hn : n < d⟩
    simp [NNReal.Int.binary_eq_zero r n hn]
  rw [h0, zero_add]; clear h0
  rw [← (Nat.equivIntLtCompl d).tsum_eq]; swap; infer_instance
  simp only [Nat.equivIntLtCompl, zpow_add₀ hs0.ne', ← mul_assoc, Equiv.coe_fn_mk, Subtype.coe_mk,
    zpow_ofNat, Nonneg.coe_one, NNReal.tsum_mul_right]
  rw [mul_le_mul_right₀]
  · rw [← tsum_geometric_nnreal hs]
    refine' NNReal.tsum_le_tsum (fun n => _) (NNReal.summable_geometric hs)
    apply mul_le_of_le_one_left'
    norm_cast
    apply NNReal.Int.binary_le_one
  · exact zpow_ne_zero _ hs0.ne'

end ThetaAuxLemma

-- is `summable_subtype_and_compl` true for add_comm_monoids? Why is it stated for groups?
