import LiquidTensorExperiment.ForMathlib.ExactSeq
import LiquidTensorExperiment.ForMathlib.AbelianCategory

#align_import for_mathlib.exact_seq2

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable {A B C : 𝒜} {f : A ⟶ B} {g : B ⟶ C}

namespace CategoryTheory

namespace ExactSeq

theorem drop : ∀ {L : List (Arrow 𝒜)} (h : ExactSeq 𝒜 L) (n : ℕ), ExactSeq 𝒜 (L.drop n)
  | _, nil, 0 => nil
  | _, nil, n + 1 => nil
  | _, single f, 0 => single f
  | _, single f, n + 1 => drop nil n
  | _, cons f g h L hL, 0 => cons f g h L hL
  | _, cons f g h L hL, n + 1 => hL.drop n

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem pair : ∀ {L : List (Arrow 𝒜)} (h : ExactSeq 𝒜 (f::g::L)), Exact f g
  | L, cons _ _ h _ _ => h

end ExactSeq

namespace Exact

theorem mono_of_eq_zero (h : Exact f g) (hf : f = 0) : Mono g := by
  rwa [(Abelian.tfae_mono A g).out 0 2, ← hf]

theorem eq_zero_of_mono (h : Exact f g) (hg : Mono g) : f = 0 := by
  rw [← cancel_mono g, h.w, zero_comp]

theorem mono_iff_eq_zero (h : Exact f g) : Mono g ↔ f = 0 :=
  ⟨h.eq_zero_of_mono, h.mono_of_eq_zero⟩

theorem epi_of_eq_zero (h : Exact f g) (hg : g = 0) : CategoryTheory.Epi f := by
  rwa [(Abelian.tfae_epi C f).out 0 2, ← hg]

theorem eq_zero_of_epi (h : Exact f g) (hf : CategoryTheory.Epi f) : g = 0 := by
  rw [← cancel_epi f, h.w, comp_zero]

theorem epi_iff_eq_zero (h : Exact f g) : CategoryTheory.Epi f ↔ g = 0 :=
  ⟨h.eq_zero_of_epi, h.epi_of_eq_zero⟩

theorem mono_of_isZero (h : Exact f g) (hA : IsZero A) : Mono g := by rw [h.mono_iff_eq_zero];
  exact hA.eq_of_src f _

theorem epi_of_isZero (h : Exact f g) (hA : IsZero C) : CategoryTheory.Epi f := by
  rw [h.epi_iff_eq_zero]; exact hA.eq_of_tgt g _

theorem isZero_of_eq_zero_eq_zero (h : Exact f g) (hf : f = 0) (hg : g = 0) : IsZero B :=
  isZero_of_exact_zero_zero' _ _ h hf hg

theorem isZero_of_isZero_isZero (h : Exact f g) (hA : IsZero A) (hC : IsZero C) : IsZero B :=
  isZero_of_exact_isZero_isZero _ _ h hA hC

protected theorem exactSeq (h : Exact f g) : ExactSeq 𝒜 [f, g] :=
  (exact_iff_exactSeq _ _).mp h

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons (h : Exact f g) {L : List (Arrow 𝒜)} (hL : ExactSeq 𝒜 (g::L)) : ExactSeq 𝒜 (f::g::L) :=
  ExactSeq.cons f g h L hL

end Exact

end CategoryTheory

