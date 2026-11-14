import LiquidTensorExperiment.ChallengeNotations
import LiquidTensorExperiment.ChallengePrerequisites

#align_import challenge

/-!
# Liquid Tensor Experiment

## The main challenge

The main challenge of the liquid tensor experiment is
a formalisation of the first theorem in Peter Scholze's blogpost
https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/

Theorem 1.1 (Clausen--Scholze)
Let `0 < p' < p ≤ 1` be real numbers, let `S` be a profinite set, and let `V` be a `p`-Banach space.
Let `ℳ p' S` be the space of `p'`-measures on `S`. Then
$$ Ext^i (ℳ p' S, V) = 0 $$
for `i ≥ 1`.

-/


noncomputable section

open scoped liquidTensorExperiment NNReal ZeroObject

open liquidTensorExperiment CategoryTheory CategoryTheory.Limits

variable (p' p : ℝ≥0) [Fact (0 < p')] [Fact (p' < p)] [Fact (p ≤ 1)]

theorem liquidTensorExperiment (S : Profinite.{0}) (V : PBanachCat.{0} p) :
    ∀ i > 0, ext i (ℳ_{p'}S) V ≅ 0 := by
  intro i hi
  apply IsZero.isoZero
  revert i
  haveI : Fact (0 < (p : ℝ)) := ⟨lt_trans (Fact.out _ : 0 < p') (Fact.out _)⟩
  haveI : Fact (p' < 1) := ⟨lt_of_lt_of_le (Fact.out _ : p' < p) (Fact.out _)⟩
  erw [isZero_iff_epi_and_isIso _ _ (V : Condensed.{0, 1, 2} Ab) (LaurentMeasures.shortExact p' S)]
  let this.1 := PBanachCat.chooseSeminormedAddCommGroup V
  let this.1 := PBanachCat.chooseNormedWithAut V 2⁻¹
  haveI : Fact (0 < (2⁻¹ : ℝ≥0) ^ (p : ℝ)) := r_pos'
  convert LaurentMeasures.epi_and_isIso p' p S ⟨V⟩ _ using 1
  intro v
  rw [PBanachCat.chooseNormedWithAut_t_inv, inv_inv, two_smul, two_nsmul]

