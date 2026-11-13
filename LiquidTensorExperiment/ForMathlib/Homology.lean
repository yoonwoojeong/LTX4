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
      have hiso : is_iso (imageToKernel f g w ≫ (CategoryTheory.Limits.kernelSubobjectIso g).Hom) :=
        is_iso.comp_is_iso
      rw [← imageSubobjectIso_imageToKernel'] at hiso 
      exact is_iso.of_is_iso_comp_left (image_subobject_iso f).Hom _
    exact
      image_to_kernel_is_iso_of_image_eq_kernel _ _ ((abelian.exact_iff_image_eq_kernel _ _).1 h)
  · have hiso : is_iso ((CategoryTheory.Limits.imageSubobjectIso f).Hom ≫ imageToKernel' f g w) :=
      is_iso.comp_is_iso
    rw [imageSubobjectIso_imageToKernel'] at hiso 
    suffices is_iso (imageToKernel f g w) by haveI := this; infer_instance
    exact is_iso.of_is_iso_comp_right _ (kernel_subobject_iso g).Hom

theorem homology'_isZero_iff_imageToKernel'_isIso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) : IsZero (homology' f g w) ↔ IsIso (imageToKernel' f g w) :=
  ⟨fun h => (exact_iff_imageToKernel'_isIso _ _ _).1 (exact_of_homology'_isZero h), fun h =>
    Exact.homology'_isZero _ _ ((exact_iff_imageToKernel'_isIso _ _ w).2 h)⟩

end

