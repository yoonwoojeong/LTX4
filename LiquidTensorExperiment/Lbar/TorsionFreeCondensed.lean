import LiquidTensorExperiment.Lbar.TorsionFreeProfinite
import LiquidTensorExperiment.Condensed.Condensify

#align_import Lbar.torsion_free_condensed

noncomputable section

universe u

open CategoryTheory Opposite

open scoped NNReal

namespace CompHausFiltPseuNormGrp

theorem toCondensed_torsion_free (M : CompHausFiltPseuNormGrp) [NoZeroSMulDivisors ℤ M]
    (T : ExtrDisc) : NoZeroSMulDivisors ℤ ((toCondensed.obj M).val.obj (op T.val)) :=
  by
  dsimp; constructor
  intro n f hf
  rw [Classical.or_iff_not_imp_left]
  intro hn
  ext t
  apply_fun fun φ => φ.down.val t at hf 
  apply smul_right_injective M hn
  dsimp [presheaf.has_zero] at hf ⊢
  convert hf using 1
  apply smul_zero

end CompHausFiltPseuNormGrp

namespace Lbar

variable (r' : ℝ≥0) [Fact (0 < r')]

theorem fintypeLbar_torsion_free (X : FintypeCat) :
    NoZeroSMulDivisors ℤ ((fintypeLbar r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r').obj X) :=
  Fintype.lbar_noZeroSMulDivisors _ _

theorem condensify_torsion_free (A : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁)
    (hA : ∀ X, NoZeroSMulDivisors ℤ (A.obj X)) (S : Profinite) (T : ExtrDisc.{u}) :
    NoZeroSMulDivisors ℤ (((condensify A).obj S).val.obj (op T.val)) :=
  by
  apply (config := { instances := false }) CompHausFiltPseuNormGrp.toCondensed_torsion_free
  apply Profinite.extend_torsion_free
  apply hA

def condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u + 1} :=
  condensify (fintypeLbar.{u, u} r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r')

instance (S : Profinite.{u}) (T : ExtrDisc.{u}) :
    NoZeroSMulDivisors ℤ (((condensed.{u} r').obj S).val.obj (op T.val)) :=
  condensify_torsion_free _ (fintypeLbar_torsion_free r') _ _

end Lbar

