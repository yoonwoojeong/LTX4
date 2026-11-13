import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.LaurentMeasures.Ses2
import LiquidTensorExperiment.Invpoly.Ses
import LiquidTensorExperiment.Lbar.Ses
import LiquidTensorExperiment.Lbar.Ext
import LiquidTensorExperiment.FreePfpng.Acyclic
import LiquidTensorExperiment.ChallengeNotations

#align_import laurent_measures.ext

universe u

open CategoryTheory

open scoped NNReal

namespace LaurentMeasures

variable (p' p : ℝ≥0) [Fact (0 < p')] [Fact (p' < p)] [Fact (p ≤ 1)]

variable (S : Profinite.{0})

local notation "r'" => @r p'

local notation "r" => @r p

-- move me
instance fact_half_pos : Fact ((0 : ℝ≥0) < 2⁻¹) :=
  ⟨by simp⟩

theorem epi_and_isIso (V : SemiNormedGroupCat.{0}) [NormedWithAut r V] [CompleteSpace V]
    [SeparatedSpace V] (hV : ∀ v : V, NormedWithAut.t.inv v = 2 • v) :
    Epi
        (((ext' 0).map ((condensifyTinv2 (fintypeLaurentMeasures r')).app S).op).app
          (Condensed.ofTopAb V)) ∧
      ∀ i > 0,
        IsIso
          (((ext' i).map ((condensifyTinv2 (fintypeLaurentMeasures r')).app S).op).app
            (Condensed.ofTopAb V)) :=
  by
  have SES := Lbar.shortExact.{0, 0} r' S
  have : Fact (r < r') :=
    by
    refine' ⟨NNReal.rpow_lt_rpow_of_exponent_gt _ _ _⟩
    · exact Fact.out _
    · apply nnreal.two_inv_lt_one
    · norm_cast; exact Fact.out _
  haveI : Fact (r < 1) := ⟨(Fact.out _ : r < r').trans (Fact.out _)⟩
  haveI : Fact (p' ≤ 1) := ⟨(Fact.out _ : p' < p).le.trans (Fact.out _)⟩
  haveI : Fact (p' < 1) := ⟨lt_of_lt_of_le (Fact.out _ : p' < p) (Fact.out _ : p ≤ 1)⟩
  rw [←
    epi_and_isIso_iff_of_isIso _ _ _ _ ((condensifyTinv2 _).app S) ((condensifyTinv2 _).app S)
      ((condensifyTinv2 _).app S) _ _ (Condensed.ofTopAb V) SES SES (Lbar.isIso_Tinv2 r r' S V hV)]
  · rw [← isZero_iff_epi_and_isIso _ _ (Condensed.ofTopAb V) (Invpoly.shortExact p' S)]
    intro i hi
    apply (free_pfpng_acyclic S V i hi).of_iso _
    apply iso.app _ _
    refine' (ext' i).mapIso _
    exact (as_iso ((condFreePfpngToNormedFreePfpng.{0, 0} p').app S)).op
  · rw [← nat_trans.comp_app, condensifyMap_comp_Tinv2, nat_trans.comp_app]
  · rw [← nat_trans.comp_app, condensifyMap_comp_Tinv2, nat_trans.comp_app]

end LaurentMeasures

