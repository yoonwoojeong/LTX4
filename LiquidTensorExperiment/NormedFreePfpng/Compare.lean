import LiquidTensorExperiment.NormedFreePfpng.Basic
import LiquidTensorExperiment.FreePfpng.Basic
import LiquidTensorExperiment.Condensed.Exact
import LiquidTensorExperiment.Condensed.Condensify

#align_import normed_free_pfpng.compare

open scoped NNReal BigOperators

variable (p : ℝ≥0) (S : FintypeCat)

variable [Fact (0 < p)] [Fact (p ≤ 1)]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem nnnorm_int_rpow_le (n : ℤ) : «expr∥ ∥₊» n ^ (p : ℝ) ≤ «expr∥ ∥₊» n :=
  by
  have h0p : 0 < p := Fact.out _
  have hp1 : p ≤ 1 := Fact.out _
  rcases eq_or_ne («expr∥ ∥₊» n) 0 with (h | h)
  · simp only [h, le_zero_iff, NNReal.rpow_eq_zero_iff, eq_self_iff_true, Ne.def,
      NNReal.coe_eq_zero, true_and_iff]
    exact h0p.ne'
  refine' (NNReal.rpow_le_rpow_of_exponent_le _ hp1).trans _
  swap; · rw [NNReal.coe_one, NNReal.rpow_one]
  rw [← NNReal.coe_natAbs] at h ⊢
  norm_cast at h ⊢
  exact Nat.one_le_of_lt (Ne.bot_lt h)

def freePfpngToNormedFreePfpng : freePfpngFunctor ⟶ normedFreePfpngFunctor p
    where
  app S :=
    { toFun := fun f => f
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      strict' := by
        have h0p : 0 < p := Fact.out _
        have hp1 : p ≤ 1 := Fact.out _
        rintro c f (hf : _ ≤ _)
        refine' le_trans (Finset.sum_le_sum _) hf
        rintro s -
        exact nnnorm_int_rpow_le p _
      Continuous' := fun c => continuous_of_discreteTopology }
  naturality' := by intro S T f; ext φ t; rfl

open CategoryTheory

noncomputable def condFreePfpngToNormedFreePfpng :
    condensify (freePfpngFunctor ⋙ pFPNG₁ToCHFPNG₁ₑₗ) ⟶
      condensify (normedFreePfpngFunctor p ⋙ pFPNG₁ToCHFPNG₁ₑₗ) :=
  condensifyMap <| whiskerRight (freePfpngToNormedFreePfpng p) _

open CompHausFiltPseuNormGrp₁

-- move me
theorem condensifyMap_zero (F G : FintypeCat ⥤ CompHausFiltPseuNormGrp₁) :
    condensifyMap (0 : F ⟶ G) = 0 :=
  by
  delta condensifyMap condensifyNonstrict
  suffices nonstrictExtend (whisker_right (0 : F ⟶ G) cHFPNG₁ToCHFPNGₑₗ) 1 _ = 0 by rw [this]; rfl
  rw [nonstrictExtend_whiskerRight_enlarging, Profinite.extend_nat_trans_zero]
  rfl

instance (S : Profinite) : Mono ((condFreePfpngToNormedFreePfpng p).app S) :=
  by
  simp only [condFreePfpngToNormedFreePfpng, condensifyMap, condensifyNonstrict]
  rw [nonstrictExtend_whiskerRight_enlarging]
  apply Condensed.mono_toCondensed_map
  apply strongly_exact_extend_zero_left
  intro S
  apply (config := { instances := false }) strongly_exact_of_mono
  rw [AddCommGroupCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro f hf
  exact hf

instance (S : Profinite) : Epi ((condFreePfpngToNormedFreePfpng p).app S) :=
  by
  simp only [condFreePfpngToNormedFreePfpng, condensifyMap, condensifyNonstrict]
  rw [nonstrictExtend_whiskerRight_enlarging]
  let κ : ℝ≥0 → ℝ≥0 := fun c => max c (c ^ (p⁻¹ : ℝ))
  have hκ : id ≤ κ := fun c => le_max_left _ _
  apply Condensed.epi_toCondensed_map _ κ
  apply strongly_exact_extend_zero_right
  intro S
  apply strongly_exact_of_epi _ _ _ hκ
  intro c f hf
  refine' ⟨f, _, rfl⟩
  change ∑ _, _ ≤ _ at hf 
  show ∑ _, _ ≤ _
  have h0p : 0 < p := Fact.out _
  have hp1 : p ≤ 1 := Fact.out _
  have h0pinv : 0 ≤ p⁻¹ := by rw [← nnreal.inv_pos] at h0p ; exact h0p.le
  have := (NNReal.rpow_sum_le_sum_rpow _ _ h0p hp1).trans hf
  replace this := NNReal.rpow_le_rpow this h0pinv
  rw [← NNReal.rpow_mul, ← NNReal.coe_mul, mul_inv_cancel h0p.ne', NNReal.coe_one,
    NNReal.rpow_one] at this 
  exact this.trans (le_max_right _ _)

instance (S : Profinite) : IsIso ((condFreePfpngToNormedFreePfpng p).app S) :=
  isIso_of_mono_of_epi _

