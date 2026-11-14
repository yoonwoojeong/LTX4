import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Abelian.Homology
import LiquidTensorExperiment.ForMathlib.HomologyExact

#align_import for_mathlib.homology

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

section

theorem exact_iff_imageToKernel'_isIso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
    Exact f g ↔ IsIso (imageToKernel' f g w) :=
  by
  refine' ⟨fun h => _, fun h => ⟨w, _⟩⟩
  · suffices is_iso (imageToKernel f g w)
      by
      have hiso : is_iso (imageToKernel f g w ≫ (CategoryTheory.Limits.kernelSubobjectIso g).hom) :=
        IsIso.comp_isIso
      rw [← imageSubobjectIso_imageToKernel'] at hiso 
      exact IsIso.of_isIso_comp_left (CategoryTheory.Limits.imageSubobjectIso f).hom _
    exact
      CategoryTheory.imageToKernel_isIso_of_image_eq_kernel _ _ ((Abelian.exact_iff_image_eq_kernel _ _).1 h)
  · have hiso : is_iso ((CategoryTheory.Limits.imageSubobjectIso f).hom ≫ imageToKernel' f g w) :=
      IsIso.comp_isIso
    rw [imageSubobjectIso_imageToKernel'] at hiso 
    suffices is_iso (imageToKernel f g w) by haveI := this; infer_instance
    exact IsIso.of_isIso_comp_right _ (CategoryTheory.Limits.kernelSubobjectIso g).hom

theorem homology'_isZero_iff_imageToKernel'_isIso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) : IsZero (homology' f g w) ↔ IsIso (imageToKernel' f g w) :=
  ⟨fun h => (exact_iff_imageToKernel'_isIso _ _ _).1 (exact_of_homology'_isZero h), fun h =>
    Exact.homology'_isZero _ _ ((exact_iff_imageToKernel'_isIso _ _ w).2 h)⟩

end

