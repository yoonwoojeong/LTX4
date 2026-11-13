import Mathlib.Algebra.Homology.Exact
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.ExactSeq2

#align_import for_mathlib.homology_exact

noncomputable section

open CategoryTheory CategoryTheory.Limits

open Opposite

-- move me
namespace CategoryTheory

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ExactSeq.isIso_of_zero_of_zero {A B C D : 𝓐} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
    {L : List (Arrow 𝓐)} (H : ExactSeq 𝓐 (f::g::h::L)) (hf : f = 0) (hh : h = 0) : IsIso g :=
  by
  subst f; subst h
  have : Mono g := by rw [H.pair.mono_iff_eq_zero]
  have : Epi g := by rw [(H.drop 1).pair.epi_iff_eq_zero]
  exact isIso_of_mono_of_epi g

theorem Exact.homology'_isZero {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : Exact f g) :
    IsZero (homology' f g hfg.w) :=
  by
  rw [Preadditive.exact_iff_homology'_zero] at hfg 
  rcases hfg with ⟨w, ⟨e⟩⟩
  exact CategoryTheory.Limits.isZero_of_iso_of_zero (isZero_zero _) e.symm

theorem exact_of_homology'_isZero {X Y Z : 𝓐} {f : X ⟶ Y} {g : Y ⟶ Z} {w : f ≫ g = 0}
    (H : IsZero (homology' f g w)) : Exact f g :=
  by
  rw [Preadditive.exact_iff_homology'_zero]
  refine' ⟨w, ⟨_⟩⟩
  exact H.isoZero

namespace Limits

namespace IsZero

theorem exact {X Y Z : 𝓐} (hY : IsZero Y) (f : X ⟶ Y) (g : Y ⟶ Z) : Exact f g := by
  simp only [Abelian.exact_iff, hY.eq_of_tgt f 0, hY.eq_of_tgt (Limits.kernel.ι g) 0,
    Limits.zero_comp, eq_self_iff_true, and_true_iff]

theorem homology'_isZero {X Y Z : 𝓐} (hY : IsZero Y) (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    IsZero (homology' f g w) :=
  Exact.homology'_isZero f g <| hY.exact f g

theorem isIso {X Y : 𝓐} (hX : IsZero X) (hY : IsZero Y) (f : X ⟶ Y) : IsIso f :=
  { out := ⟨0, hX.eq_of_src _ _, hY.eq_of_tgt _ _⟩ }

/-
Porting note: LTE's `is_zero.op` and `is_zero.unop` were later added to mathlib with the same
statements (for any category); in Lean 4 they are `CategoryTheory.Limits.IsZero.op`/`unop`,
so they are not redeclared.
-/

end IsZero

@[simp]
theorem isZero_op {X : 𝓐} : IsZero (op X) ↔ IsZero X :=
  ⟨IsZero.unop, IsZero.op⟩

@[simp]
theorem isZero_unop {X : 𝓐ᵒᵖ} : IsZero (unop X) ↔ IsZero X :=
  ⟨IsZero.op, IsZero.unop⟩

end Limits

end CategoryTheory

