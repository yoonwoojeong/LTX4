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
  have : mono g := by rw [H.pair.mono_iff_eq_zero]
  have : epi g := by rw [(H.drop 1).pair.epi_iff_eq_zero]
  exact is_iso_of_mono_of_epi g

theorem Exact.homology'_isZero {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : Exact f g) :
    IsZero (homology' f g hfg.w) :=
  by
  rw [Preadditive.exact_iff_homology'_zero] at hfg 
  rcases hfg with ⟨w, ⟨e⟩⟩
  exact CategoryTheory.Limits.isZero_of_iso_of_zero (is_zero_zero _) e.symm

theorem exact_of_homology'_isZero {X Y Z : 𝓐} {f : X ⟶ Y} {g : Y ⟶ Z} {w : f ≫ g = 0}
    (H : IsZero (homology' f g w)) : Exact f g :=
  by
  rw [Preadditive.exact_iff_homology'_zero]
  refine' ⟨w, ⟨_⟩⟩
  exact H.iso_zero

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

theorem op {X : 𝓐} (h : IsZero X) : IsZero (op X) :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero] at h ⊢
  rw [← op_id, h, op_zero]

theorem unop {X : 𝓐ᵒᵖ} (h : IsZero X) : IsZero (unop X) :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero] at h ⊢
  rw [← unop_id, h, unop_zero]

end IsZero

@[simp]
theorem isZero_op {X : 𝓐} : IsZero (op X) ↔ IsZero X :=
  ⟨IsZero.unop, IsZero.op⟩

@[simp]
theorem isZero_unop {X : 𝓐ᵒᵖ} : IsZero (unop X) ↔ IsZero X :=
  ⟨IsZero.op, IsZero.unop⟩

end Limits

end CategoryTheory

