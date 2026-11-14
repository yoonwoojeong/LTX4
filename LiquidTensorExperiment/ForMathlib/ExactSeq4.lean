import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.ExactSeq3

#align_import for_mathlib.exact_seq4

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

-- lemma exact_seq.is_iso_of_is_zero_of_is_zero
--   {A B C D : 𝓐} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {L : list (arrow 𝓐)}
--   (H : exact_seq 𝓐 (f::g::h::L)) (hA : is_zero A) (hD : is_zero D) :
--   is_iso g :=
-- begin
--   admit
-- end
end CategoryTheory

