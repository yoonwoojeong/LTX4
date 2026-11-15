import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.Algebra.Homology.Homotopy
import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp

#align_import for_mathlib.homotopy_category_lemmas

open CategoryTheory

open CategoryTheory.Limits

namespace Homotopy

universe v u

variable {M : Type _} {c : ComplexShape M} (A : Type u) [Category.{v} A] [Abelian A]

variable (C₁ C₂ : HomologicalComplex A c) (f₁ f₂ : C₁ ⟶ C₂)

theorem kernel_ι_comp_comp_cokernel_π_of_homotopy (h : Homotopy f₁ f₂) (i : M) :
    kernel.ι (C₁.dFrom i) ≫ f₁.f i ≫ cokernel.π (C₂.dTo i) = kernel.ι _ ≫ f₂.f i ≫ cokernel.π _ :=
  by
  have := h.comm i
  apply_fun fun e => kernel.ι (C₁.dFrom i) ≫ e ≫ cokernel.π (C₂.dTo i) at this 
  simpa using this

def homotopyUnopFunctorRightOpMapUnopOfHomotopy (C₁ C₂ : HomologicalComplex Aᵒᵖ c) (f₁ f₂ : C₁ ⟶ C₂)
    (h : Homotopy f₁ f₂) :
    Homotopy (HomologicalComplex.unopFunctor.rightOp.map f₁).unop
      (HomologicalComplex.unopFunctor.rightOp.map f₂).unop
    where
  hom i j := (h.hom _ _).unop
  -- Porting note: Lean 3 used `let z := _; change _ = z; rw ← z.unop_op`
  zero i j hh := by
    dsimp only
    rw [h.zero _ _ hh]
    rfl
  comm := by
    intro i
    dsimp
    rw [h.comm i]
    simp only [unop_add, unop_comp, add_left_inj]
    rw [add_comm]; rfl

end Homotopy

