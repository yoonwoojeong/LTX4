import Mathlib.CategoryTheory.Limits.Shapes.Kernels

#align_import for_mathlib.kernel_comparison

open CategoryTheory

universe v

namespace CategoryTheory.Limits

variable {C D : Type _} [Category.{v} C] [Category.{v} D] [HasZeroMorphisms C] [HasZeroMorphisms D]

-- These two lemmas are no longer used.
@[simp, reassoc]
theorem lift_map_inv_kernelComparison {X Y Z : C} (f : Y ⟶ Z) [HasKernel f] (G : C ⥤ D)
    [G.PreservesZeroMorphisms] [HasKernel (G.map f)] [IsIso (kernelComparison f G)] {g : X ⟶ Y}
    (w : g ≫ f = 0) :
    kernel.lift (G.map f) (G.map g) (by simp only [← G.map_comp, w, functor.map_zero]) ≫
        CategoryTheory.inv (kernelComparison f G) =
      G.map (kernel.lift f g w) :=
  by simp [← cancel_mono (kernel_comparison f G)]

@[simp, reassoc]
theorem inv_cokernelComparison_desc_map {X Y Z : C} (f : X ⟶ Y) [HasCokernel f] (G : C ⥤ D)
    [G.PreservesZeroMorphisms] [HasCokernel (G.map f)] [IsIso (cokernelComparison f G)] {g : Y ⟶ Z}
    (w : f ≫ g = 0) :
    CategoryTheory.inv (cokernelComparison f G) ≫
        cokernel.desc (G.map f) (G.map g) (by simp only [← G.map_comp, w, functor.map_zero]) =
      G.map (cokernel.desc f g w) :=
  by simp [← cancel_epi (cokernel_comparison f G)]

end CategoryTheory.Limits

