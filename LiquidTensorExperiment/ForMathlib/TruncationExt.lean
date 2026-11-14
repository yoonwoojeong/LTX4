import LiquidTensorExperiment.ForMathlib.Truncation
import LiquidTensorExperiment.ForMathlib.ExtQuasiIso

#align_import for_mathlib.truncation_Ext

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

open BoundedHomotopyCategory

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]

variable (C : CochainComplex 𝓐 ℤ)

theorem ext_ιSucc_five_term_exactSeq (B : BoundedHomotopyCategory 𝓐) (i j : ℤ) :
    let E n := (ext n).flip.obj B
    ExactSeq Ab.{v} <|
      [(E j).map (BoundedHomotopyCategory.ofHom (truncation.toImker C (i + 1))).op,
        (E j).map (BoundedHomotopyCategory.ofHom (truncation.ιSucc C i)).op,
        extδ _ _ j B (truncation.shortExact_ιSucc_toImker C i),
        (E (j + 1)).map (BoundedHomotopyCategory.ofHom (truncation.toImker C (i + 1))).op] :=
  ext_five_term_exact_seq' _ _ j B (truncation.shortExact_ιSucc_toImker C i)

end CochainComplex

