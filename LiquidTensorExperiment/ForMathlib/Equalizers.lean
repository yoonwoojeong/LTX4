import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Generator
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.InjectiveResolution
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Preadditive.OfBiproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective

#align_import for_mathlib.equalizers

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)

/-- The fork given by the kernel of the difference of two maps -/
@[simps]
def forkOfKernel [Preadditive C] [HasKernel (f - g)] : Fork f g :=
  Fork.ofι (kernel.ι (f - g)) (by rw [← sub_eq_zero, ← preadditive.comp_sub, kernel.condition])

/-- In a preadditive category, an equalizer can be constructed as the kernel of the two maps -/
@[simps]
def forkOfKernelIsLimit [Preadditive C] [HasKernel (f - g)] : IsLimit (forkOfKernel f g) :=
  Fork.IsLimit.mk _
    (fun s => kernel.lift _ s.ι (by rw [preadditive.comp_sub, sub_eq_zero, fork.condition]))
    (fun s => by apply kernel.lift_ι) fun s m hm => by ext; simpa only [kernel.lift_ι] using hm

/-- The cofork given by the cokernel of the difference of two maps -/
@[simps]
def coforkOfCokernel [Preadditive C] [HasCokernel (f - g)] : Cofork f g :=
  Cofork.ofπ (cokernel.π (f - g))
    (by rw [← sub_eq_zero, ← preadditive.sub_comp, cokernel.condition])

/-- In a preadditive category, a coequalizer can be constructed as the cokernel of the two maps -/
@[simps]
def coforkOfCokernelIsColimit [Preadditive C] [HasCokernel (f - g)] :
    IsColimit (coforkOfCokernel f g) :=
  Cofork.IsColimit.mk _
    (fun s => cokernel.desc _ s.π (by rw [preadditive.sub_comp, sub_eq_zero, cofork.condition]))
    (fun s => by apply cokernel.π_desc) fun s m hm => by ext; simpa only [cokernel.π_desc] using hm

end CategoryTheory.Limits

