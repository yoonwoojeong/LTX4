import LiquidTensorExperiment.LaurentMeasures.Basic
import LiquidTensorExperiment.LaurentMeasures.AuxLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LiquidTensorExperiment.LaurentMeasures.Thm69

#align_import laurent_measures.simpler_laurent_measures

open NNReal LaurentMeasures AuxThm69

open scoped NNReal

noncomputable section

section Slm

--  This is the same as before, from here to...
-- parameter {p : ℝ≥0}
-- def r : ℝ≥0 := 2⁻¹ ^ (p:ℝ)
-- lemma r_pos : 0 < r :=
-- suffices 0 < (2 : ℝ≥0)⁻¹ ^ (p : ℝ), by simpa [r],
-- rpow_pos (nnreal.inv_pos.mpr zero_lt_two)
-- lemma r_lt_one [fact(0 < p)] : r < 1 :=
-- begin
--   refine rpow_lt_one zero_le' (half_lt_self one_ne_zero) _,
--   rw nnreal.coe_pos,
--   exact fact.out _
-- end
variable {r : ℝ≥0} [Fact (0 < r)] [Fact (r < 1)]

local notation "ℒ" => LaurentMeasures r

variable {S : FintypeCat}

-- /--  Let `F : ℒ S` be a Laurent measure.  `laurent_measures.d` chooses a bound `d ∈ ℤ` for `F`,
-- such that, for all `s : S`, the sequence `F s` is zero from `d-1` and below. -/
-- def laurent_measures.d (F : ℒ S) : ℤ :=
-- (exists_bdd_filtration (fact.out _ : 0 < r) (fact.out _ : r < 1) F).some
-- lemma lt_d_eq_zero (F : ℒ S) (s : S) (n : ℤ) :
--   n < F.d → F s n = 0 :=
-- (exists_bdd_filtration (fact.out _ : 0 < r) (fact.out _ : r < 1) F).some_spec s n
--  ... here!
section NewStuff

/-- Simpler Laurent measures? -/
structure Slm (r : ℝ≥0) (S : FintypeCat) where
  toFun : S → ℤ → ℤ
  d : ℤ
  summable' : ∀ s, Summable fun n : ℕ => ‖to_fun s n‖₊ * r ^ n
  zero_lt_d : ∀ s n, n < d → to_fun s n = 0

/-- A "usual" Laurent Measure `F : ℒ S` gives rise to a Simple Laurent Measure of type `slm S`. -/
def LaurentMeasures.toSlm (F : ℒ S) : Slm r S
    where
  toFun := F.toFun
  d := F.d
  zero_lt_d n s := lt_d_eq_zero F _ _
  summable' := by
    refine' fun s => summable_coe.mp _
    convert ((@int_summable_iff _ _ _ _ _ fun n : ℤ => ‖F.to_fun s n‖ * r ^ n).mp _).1
    exact summable_coe.mpr (F.summable' s)

--  The "main" input is `int_summable_iff`, proving that a series over `ℤ` is summable if and only
--  if both its restrictions to `ℕ` and to "`-ℕ`" are summable.
/-- A Simple Laurent Measure `F : slm S` "usual" Laurent Measure of type `ℒ S`. -/
def Slm.toLaurentMeasures {r : ℝ≥0} (F : Slm r S) : LaurentMeasures r S
    where
  toFun := F.toFun
  summable' := by
    refine' fun s => summable_coe.mp _
    convert (@int_summable_iff _ _ _ _ _ fun n : ℤ => ‖F.to_fun s n‖ * r ^ n).mpr _
    refine'
      ⟨_,
        summable_of_eventually_zero (fun n : ℤ => ‖F.to_fun s n‖ * ↑r ^ n) F.d fun n nd =>
          _⟩
    · convert summable_coe.mpr (F.summable' s)
    · simp [F.zero_lt_d s n nd]

theorem slm_lm_toFun_eq {r : ℝ≥0} (F : Slm r S) : F.toFun = F.toLaurentMeasures.toFun :=
  rfl

theorem lm_slm_toFun_eq (F : ℒ S) : F.toFun = F.toSlm.toFun :=
  rfl

end NewStuff

end Slm

