import LiquidTensorExperiment.Lbar.Ses
import LiquidTensorExperiment.Lbar.FinsuppInstance

#align_import Lbar.kernel_truncate

universe u

noncomputable section

open scoped BigOperators NNReal

open PseudoNormedGroup CategoryTheory CategoryTheory.Limits AuxThm69 LaurentMeasures

attribute [local instance] typePow

variable {r' : ℝ≥0} [Fact (0 < r')] [Fact (r' < 1)] {S : FintypeCat} (F : LaurentMeasures r' S)
  (s : S)

/-- Given `F : laurent_measures r' S`, for each `s : S`, `tail F s` is the restriction of `F s` to
the non-positive indices, with opposite sign, i.e. a finsupp `ℕ →₀ ℤ`.
Taken together `tail F` is a term of type `invpoly r' ⟨S⟩`. -/
def tail : Invpoly' r' ⟨S⟩ := fun s =>
  ⟨by
    refine' Set.Finite.toFinset (_ : {n : ℕ | ∃ m : ℤ, m = -n ∧ F s m ≠ 0}.Finite)
    obtain ⟨d, h⟩ := exists_bdd_filtration (Fact.out _ : 0 < r') (Fact.out _ : r' < 1) F
    refine' (Finset.range (-d + 1).toNat).finite_toSet.Subset fun n hn => _
    rw [Set.mem_setOf_eq, exists_eq_left] at hn 
    rw [Finset.mem_coe, Finset.mem_range, Int.lt_toNat]
    exact not_le.mp fun nd => hn <| h s (-n) <| neg_lt.mp <| int.add_one_le_iff.mp nd, fun n =>
    F s (-(n : ℤ)), by
    simp only [Set.mem_setOf_eq, exists_eq_left, Set.Finite.mem_toFinset, iff_self_iff,
      forall_const]⟩

theorem tail_of_nonneg {n : ℕ} : tail F s n = F s (-n) := by simp only [tail, Finsupp.coe_mk]

theorem Int.tail_of_nonneg {n : ℤ} (n0 : 0 ≤ n) : tail F s n.toNat = F s (-n) :=
  (tail_of_nonneg F s).trans <| congr_arg _ <| congr_arg _ <| Int.toNat_of_nonneg n0

theorem ite_toLbar_tail (n : ℤ) :
    ite (0 < n) ((toLbar r' S F).toFun s n.toNat) (tail F s (-n).toNat) = F s n :=
  by
  by_cases n0 : 0 < n
  · have : n.to_nat ≠ 0 := by simpa using (lt_of_lt_of_le n0 (Int.toNat_of_nonneg n0.le).ge).ne'
    simp only [n0, to_Lbar, if_true, this, Int.toNat_of_nonneg n0.le, if_false]
  · rw [if_neg n0, Int.tail_of_nonneg F s (neg_nonneg.mpr (not_lt.mp n0)), neg_neg]

