import LiquidTensorExperiment.ForMathlib.Fintype
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.Lbar.NnnormAddClass

#align_import Lbar.finsupp_instance

/-!
#  The standard filtration `c : ℝ≥0 ↦ {z : α | ∥z∥₊ ≤ c}`

Let `α` be a nnnormed type.  We use the naming convention `std_flt` for the function `ℝ≥0 → set α`
taking a non-negative real number `c` to the subset of all the terms of `α` of nnnorm at most `c`:
```
ℝ≥0 → set α
  c ↦ {z : α | ∥z∥₊ ≤ c}.
```
The main construction is `std_flt.to_pseudo_normed_group` asserting that the typeclass
`nnnorm_add_class α` (i.e. `α` is a Type with `∥_∥₊, 0, +, -` and compatibilities among them),
gives rise to a `pseudo_normed_group α` under the standard filtration.

We use `std_flt.to_pseudo_normed_group` to give a `pseudo_normed_group` instance on
`S → (ℕ →₀ ℤ)`.

For a fixed `r : ℝ≥0`, the nnnorm on `S → (ℕ →₀ ℤ)` is
`∥(s ↦ (n ↦ F s n))∥₊ = ∑ s : S, ∑ n in F.support, ∥F s n∥₊ * r⁻¹ ^ n`, where the sum is "really" a
finite sum, extending over all `s : S` and over `n : ℕ` contained in the (finite) support of `F n`.

The reason for this choice of nnnorm is that it arises as the nnnorm on the "non-positive tails" of
Laurent series, the kernel of the projection map from Laurent series to the series of their terms of
strictly positive degree.

##  Warning/Formalization note
We use the `nnnorm_add_class` instance on `S → (ℕ →₀ ℤ)` to prove that the standard filtration
determined a `pseudo_normed_group (S → (ℕ →₀ ℤ))`.  Note that the `seminormed_add_comm_group` instance on
the same type is *not* the same: the norm on finitely indexed finsupps for the `seminormed_add_comm_group`
is the `sup`norm and not the `sum_nnnorm`.
-/


open Finset Finsupp

open scoped NNReal BigOperators

theorem mem_union_support_of_mem_support_add {α β : Type _} [AddZeroClass β] [DecidableEq α] {k : α}
    (F G : α →₀ β) (hk : k ∈ (F + G).support) : k ∈ F.support ∪ G.support :=
  by
  simp only [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply] at hk ⊢
  contrapose! hk
  simp only [hk, add_zero]

noncomputable section

section StdFltLemmas

variable (α : Type _) [NNNorm α]

theorem std_flt_mono ⦃c d : ℝ≥0⦄ (cd : c ≤ d) :
    {z : α | ‖z‖₊ ≤ c} ⊆ {z : α | ‖z‖₊ ≤ d} := fun x (hx : ‖x‖₊ ≤ c) =>
  hx.trans cd

theorem std_flt_zero_mem [Zero α] (n0 : ‖0 : α‖₊ = 0) (c : ℝ≥0) :
    (0 : α) ∈ {z : α | ‖z‖₊ ≤ c} := by simp only [n0, Set.mem_setOf_eq, zero_le']

theorem std_flt_neg_mem [Neg α] (nn : ∀ {x : α}, ‖-x‖₊ = ‖x‖₊) ⦃c : ℝ≥0⦄ ⦃x : α⦄
    (xc : x ∈ {z : α | ‖z‖₊ ≤ c}) : -x ∈ {z : α | ‖z‖₊ ≤ c} := by
  simpa only [nn, Set.mem_setOf_eq] using xc

theorem std_flt_add_mem [Add α]
    (n_le : ∀ {x y : α}, ‖x + y‖₊ ≤ ‖x‖₊ + ‖y‖₊) ⦃c d : ℝ≥0⦄ ⦃x y : α⦄
    (xc : x ∈ {z : α | ‖z‖₊ ≤ c}) (yd : y ∈ {z : α | ‖z‖₊ ≤ d}) :
    x + y ∈ {z : α | ‖z‖₊ ≤ c + d} :=
  n_le.trans (add_le_add xc yd)

open NnnormAddClass

variable {α}

/-- Given a type `α` with a `nnnorm_add_class` instance, `std_flt.to_pseudo_normed_group`
shows that the standard filtration `λ c, {z : α | ∥z∥₊ ≤ c}` endows `α` with a
`pseudo_normed_group` class. -/
def StdFlt.toPseudoNormedGroup [AddCommGroup α] [NnnormAddClass α] : PseudoNormedGroup α
    where
  filtration c := {z : α | ‖z‖₊ ≤ c}
  filtration_mono := std_flt_mono α
  zero_mem_filtration := std_flt_zero_mem α nnn_zero
  neg_mem_filtration := std_flt_neg_mem α nnn_neg
  add_mem_filtration := std_flt_add_mem α nnn_add_le

end StdFltLemmas

/-- Let `r : ℝ≥0` be a non-negative real number.  `nnreal.normed r` or `r.normed` is the type of
finsupps `ℕ →₀ ℤ` with an extra parameter `r`.

The non-negative real number `r` is used in defining a norm on `r.normed`: given `F : ℕ →₀ ℤ`,
define `∥F∥₊ = ∑ x in F.support, ∥F x∥₊ * r⁻¹ ^ x`. -/
@[nolint unused_arguments, reducible]
def NNReal.Normed (r : ℝ≥0) :=
  ℕ →₀ ℤ
deriving AddCommGroup

namespace NNReal.Normed

variable {r : ℝ≥0} (F G H : r.Normed)

instance (r : ℝ≥0) : NNNorm r.Normed :=
  ⟨fun F => ∑ x in F.support, ‖F x‖₊ * r⁻¹ ^ x⟩

@[simp]
theorem nnnorm_zero : ‖0 : r.Normed‖₊ = 0 := by
  simp only [NNNorm.nnnorm, support_zero, sum_empty]

@[simp]
theorem nnnorm_neg : ‖-F‖₊ = ‖F‖₊ := by
  simp only [NNNorm.nnnorm, Pi.neg_apply, Finsupp.coe_neg, support_neg, norm_neg]

theorem nnnorm_add_le : ‖F + G‖₊ ≤ ‖F‖₊ + ‖G‖₊ :=
  by
  unfold nnnorm
  rw [sum_subset (subset_union_left F.support G.support),
    sum_subset (subset_union_right F.support G.support),
    sum_subset (fun k => mem_union_support_of_mem_support_add F G : _ ⊆ F.support ∪ G.support), ←
    Finset.sum_add_distrib]
  · refine' sum_le_sum fun j hj => _
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (nnreal.coe_le_coe.mp (norm_add_le _ _)) (zero_le _)
  repeat'
    simp only [mem_support_iff, Classical.not_not, norm_zero, mul_eq_zero, Nonneg.mk_eq_zero,
      eq_self_iff_true, true_or_iff, imp_true_iff]

instance : NnnormAddClass r.Normed :=
  { (inferInstance : AddCommGroup _) with
    nnn_zero := nnnorm_zero
    nnn_neg := nnnorm_neg
    nnn_add_le := nnnorm_add_le }

instance : PseudoNormedGroup r.Normed :=
  StdFlt.toPseudoNormedGroup

end NNReal.Normed

open NnnormAddClass

variable {r : ℝ≥0} {α : Type _} [NNNorm α] {S : FintypeCat}

instance Fintype.sumNnnorm : NNNorm (S → α) where nnnorm F := ∑ b, ‖F b‖₊

@[simp]
theorem Fintype.sumNnnorm_def (F : S → α) : ‖F‖₊ = ∑ b, ‖F b‖₊ :=
  rfl

instance [AddGroup α] [NnnormAddClass α] : NnnormAddClass (S → α) :=
  { (inferInstance : AddCommGroup _) with
    nnn_zero := by simp
    nnn_neg := fun x => by simp [Fintype.sumNnnorm_def, Pi.neg_apply, nnn_neg]
    nnn_add_le := fun F G =>
      le_trans (sum_le_sum fun j hj => nnnorm_add_le _ _) sum_add_distrib.le }

/-- Let `r : ℝ≥0` be a non-negative real number and `S : Fintype` a finite type.
`invpoly' r S` is the type of `S`-indexed terms of type `r.normed`, that is, finsupps
`ℕ →₀ ℤ` with norm defined using `r⁻¹`. -/
def Invpoly' (r : ℝ≥0) (S : FintypeCat) :=
  S → r.Normed
deriving AddCommGroup

namespace Invpoly'

instance : Inhabited (Invpoly' r S) :=
  ⟨0⟩

instance : NNNorm (Invpoly' r S) :=
  @Fintype.sumNnnorm r.Normed ⟨nnnorm⟩ S

instance : NnnormAddClass (Invpoly' r S) :=
  Pi.nnnormAddClass

instance : PseudoNormedGroup (Invpoly' r S) :=
  StdFlt.toPseudoNormedGroup

end Invpoly'

