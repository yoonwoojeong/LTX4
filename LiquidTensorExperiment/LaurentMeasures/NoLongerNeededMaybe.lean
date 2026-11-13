import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import LiquidTensorExperiment.LaurentMeasures.AuxLemmas

#align_import laurent_measures.no_longer_needed_maybe

/-  These lemmas seem to no longer be needed for Theorem 6.9 or anywhere else in LTE. I ([FAE])
wonder if they might be useful somewhere-/
/-  These lemmas seem to no longer be needed for Theorem 6.9 or anywhere else in LTE. I ([FAE])
wonder if they might be useful somewhere-/
open AuxThm69

open Metric Finset NormedField

open scoped NNReal Classical BigOperators TopologicalSpace

def equivIcoNatNeg {d : ℤ} (hd : d < 0) : { y : { x : ℤ // d ≤ x } // y ∉ t hd } ≃ ℕ :=
  by
  fconstructor
  · rintro ⟨⟨a, ha⟩, hx⟩
    exact Int.toNat a
  · intro n
    refine' ⟨⟨n, hd.le.trans (Int.ofNat_zero_le n)⟩, _⟩
    apply (not_congr mem_Ico).mpr
    simp only [Subtype.mk_lt_mk, not_and, not_lt, Int.coe_nat_nonneg, imp_true_iff]
  · rintro ⟨⟨x, dx⟩, hx⟩
    simp [Int.toNat_of_nonneg (T.zero_le hd hx)]
  · exact fun n => by simp only [Int.toNat_coe_nat]

theorem equivIcoNatNeg_apply {d : ℤ} (hd : d < 0) {y : { x : ℤ // d ≤ x }} (h : y ∉ t hd) :
    y.1 = (equivIcoNatNeg hd) ⟨y, h⟩ := by cases y; simp [equivIcoNatNeg, T.zero_le hd h]

--  This lemma seems to not be used anywhere.
theorem summable_iff_on_nat {f : ℤ → ℝ} {ρ : ℝ≥0} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
    (Summable fun n => ‖f n‖ * ρ ^ n) ↔
      Summable fun n : ℕ => ‖f n‖ * ρ ^ (n : ℤ) :=
  Iff.trans (summable_iff_on_nat_less d fun n nd => by simp [h _ nd]) Iff.rfl

--  This lemma seems to not be used anywhere.
theorem aux_summable_iff_on_nat {f : ℤ → ℝ} {ρ : ℝ≥0} (d : ℤ) (h : ∀ n : ℤ, n < d → f n = 0) :
    (Summable fun n => ‖f n‖ * ρ ^ n) ↔
      Summable fun n : ℕ => ‖(f (n + d))‖ * ρ ^ (n + d : ℤ) :=
  by
  have hf : (Function.support fun n : ℤ => ‖f n‖ * ρ ^ n) ⊆ {a : ℤ | d ≤ a} :=
    by
    rw [Function.support_subset_iff]
    intro x
    rw [← not_imp_not, Classical.not_not, mul_eq_zero]
    intro hx
    simp only [not_le, Set.mem_setOf_eq] at hx 
    apply Or.intro_left
    rw [norm_eq_zero]
    exact h x hx
  have h1 := fun a : ℝ =>
    @hasSum_subtype_iff_of_support_subset ℝ ℤ _ _ (fun n : ℤ => ‖f n‖ * ρ ^ n) _ _ hf
  have h2 := fun a : ℝ =>
    @Equiv.hasSum_iff ℝ { b : ℤ // d ≤ b } ℕ _ _ ((fun n => ‖f n‖ * ρ ^ n) ∘ coe) _
      (equiv_bdd_integer_nat d)
  exact exists_congr fun a => ((h2 a).trans (h1 a)).symm

