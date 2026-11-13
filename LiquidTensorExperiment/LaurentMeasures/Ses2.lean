import LiquidTensorExperiment.LaurentMeasures.Ses
import LiquidTensorExperiment.LaurentMeasures.Condensed
import LiquidTensorExperiment.RealMeasures.Condensed
import LiquidTensorExperiment.Condensed.Condensify
import LiquidTensorExperiment.LaurentMeasures.Prop72

#align_import laurent_measures.ses2

-- kmb's attempt to tidy up the analysis argument
-- kmb's attempt to tidy up the analysis argument
universe u

noncomputable section

open CategoryTheory

open scoped NNReal

namespace LaurentMeasures

open LaurentMeasuresSes ProFiltPseuNormGrpWithTinv₁

section Theta

variable (p : ℝ≥0) [Fact (0 < p)] [Fact (p < 1)]

local notation "r" => @r p

/-- If `0 < (p : ℝ≥0) < 1` and `S : Fintype` then `Θ p S` evaluates Laurent measures at 2⁻¹. -/
def Θ (S : FintypeCat.{u}) :
    (fintypeLaurentMeasures.{u} r ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r).obj S ⟶
      (RealMeasures.functor p).obj S :=
  StrictComphausFilteredPseudoNormedGroupHom.mk' (θToAdd p)
    (by
      intro c
      use θ_bound' p c
      convert continuous_θ_c p S c
      simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast]
      rfl)

def ΘFintypeNatTrans :
    fintypeLaurentMeasures.{u} r ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r ⟶ RealMeasures.functor.{u} p
    where
  app S := Θ p S
  naturality' S T f := by ext x t; apply θ_natural

end Theta

section Ses

variable (p : ℝ≥0) [Fact (0 < p)] [Fact (p < 1)]

local notation "r" => @r p

open CompHausFiltPseuNormGrp₁

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem psi_bound (S : FintypeCat) (c' : ℝ≥0) ⦃F : LaurentMeasures r S⦄ (hF1 : (Θ p S) F = 0)
    (hF2 : «expr∥ ∥₊» F ≤ c') : «expr∥ ∥₊» (ψ F hF1) ≤ c' * (2 - r⁻¹)⁻¹ :=
  by
  delta ψ
  rw [nnnorm_def] at hF2 ⊢
  simp only [coe_mk]
  delta Θ at hF1 
  have foo :
    ∀ s : S,
      ∑' n : ℤ,
          «expr∥ ∥₊»
              (ite (F.d ≤ n)
                ((Finset.range (n - F.d).natAbs.succ).Sum fun l : ℕ =>
                  (F s (n - 1 - l) : ℝ) * 2 ^ l)
                0) *
            r ^ n ≤
        (2 - r⁻¹)⁻¹ * ∑' n, «expr∥ ∥₊» (F s n : ℝ) * r ^ n :=
    fun s => by
    convert
      PsiAuxLemma.key_tsum_lemma (fun n => (F s n : ℝ)) r r_lt_one half_lt_r F.d
        (fun n hnd => lt_d_eq_zero' F s n hnd) (F.summable' s) (congr_fun hF1 s)
  convert le_trans (Finset.sum_le_sum fun (s : S) _ => foo s) _
  · norm_cast
  simp_rw [Real.nnnorm_int]
  rw [← Finset.mul_sum, mul_comm]
  exact NNReal.hMul_le_hMul_right hF2 _

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem shortExact (S : Profinite) :
    ShortExact ((condensifyTinv2 _).app S) ((condensifyMap <| ΘFintypeNatTrans p).app S) :=
  by
  refine'
    condensifyNonstrict_exact _ _ (r⁻¹ + 2) (tinv2BoundBy _)
      (-- C₂ bound (note that `2⁻¹ < r < 1` implies the max is always the left term)
      fun c => max (c * (r⁻¹ + 2) * (2 - r⁻¹)⁻¹) c)
      (-- C₄ bound (note that `2⁻¹ < r < 1` implies that the max is always the left term)
      fun c => max ((1 - r)⁻¹ * c) c)
      (-- if you want to remove `max` from C₂ then you do that here
      fun c => le_max_right _ c)
      (-- if you want to remove `max` from C₄ then you do that here
      fun c => le_max_right _ c)
      (fun S => injective_ϕ') (fun S => by ext1 F; apply θ_ϕ_complex) _ _ _
  -- now two goals left, basically corresponding to
  -- existence of a bounded splitting of ϕ (namely ψ)
  -- and existence of a bounded splitting of θ
  -- (namely binary expansion).
  -- Here's a proof of the ϕ goal using ψ.
  · clear S
    -- change to unbundled language
    rintro S c' (F : LaurentMeasures r S) ⟨hF1 : Θ p S F = 0, hF2 : «expr∥ ∥₊» F ≤ c'⟩
    simp only [Set.mem_image]
    refine' ⟨ψ F hF1, _, θ_ϕ_split_exact F hF1⟩
    change («expr∥ ∥₊» _ : ℝ≥0) ≤ _
    -- because of silly definition of `C₂` involving max :-)
    refine' le_trans _ (mul_le_mul_right' (le_max_left _ _) _)
    convert psi_bound p S c' hF1 hF2 using 1
    have h1 : 2⁻¹ < r := half_lt_r
    have h2 : 2 - 1 / r ≠ 0 := ne_of_gt (tsub_pos_of_lt (by rw [one_div]; exact r_inv_lt_2))
    have h3 : r ≠ 0 := ne_of_gt r_pos
    field_simp
    simp [mul_tsub, tsub_mul, one_div, mul_assoc, mul_inv_cancel h3]
    ring_nf
  -- Now here's a proof of the θ goal using binary expansions
  · clear S
    rintro S c' (f : RealMeasures p S) (hf : _ ≤ _)
    let measure_aux : LaurentMeasures r S :=
      { toFun := fun s n =>
          if 0 ≤ f s then NNReal.Int.binary («expr∥ ∥₊» (f s)) n
          else -NNReal.Int.binary («expr∥ ∥₊» (f s)) n
        summable' := fun s =>
          by
          convert NNReal.Int.binary_summable («expr∥ ∥₊» (f s)) (r_lt_one : r < 1)
          ext
          split_ifs <;> simp }
    refine' ⟨measure_aux, _⟩
    change _ ≤ _ ∧ _
    constructor
    · refine' le_trans _ (le_max_left _ _)
      refine' le_trans _ (mul_le_mul_of_nonneg_left hf zero_le')
      change Finset.sum _ _ ≤ _ * Finset.sum _ _
      rw [Finset.mul_sum]
      refine' Finset.sum_le_sum fun s _ => _
      rcases(eq_zero_or_pos : «expr∥ ∥₊» (f s) = 0 ∨ _) with (h0 | hpos)
      · simp [h0, measure_aux]
      · convert
          le_trans (ThetaAuxLemma.tsum_le («expr∥ ∥₊» (f s)) (r_pos : 0 < r) (r_lt_one : r < 1)) _
        · ext n; congr; dsimp [measure_aux]; split_ifs <;> simp
        · rw [mul_comm]
          apply NNReal.hMul_le_hMul_left
          rw [← NNReal.rpow_int_cast]
          convert
            NNReal.rpow_le_rpow_of_exponent_ge (r_pos : 0 < r) r_lt_one.le (Int.le_ceil _) using 1
          delta r
          rw [← NNReal.rpow_mul, mul_comm, NNReal.rpow_mul]
          congr; symm
          rw [← NNReal.coe_eq]
          exact NNReal.pow_log_div_log_self hpos (by norm_num) (by norm_num)
    · delta Θ_fintype_nat_trans Θ θ_to_add θ Theta.ϑ
      dsimp
      ext s
      split_ifs
      · convert NNReal.coe_eq.2 (NNReal.Int.binary_sum («expr∥ ∥₊» (f s)))
        push_cast; rw [Real.nnnorm_of_nonneg h]; rfl
      · convert neg_inj.2 (NNReal.coe_eq.2 (NNReal.Int.binary_sum («expr∥ ∥₊» (f s))))
        · push_cast; rw [← tsum_neg]; congr; ext; simp
        · push_neg at h 
          rw [Real.neg_nnnorm_of_neg h]

end Ses

end LaurentMeasures

