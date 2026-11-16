import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import LiquidTensorExperiment.ForMathlib.HomologicalComplexShift
import LiquidTensorExperiment.ForMathlib.MonoidalCategory
import LiquidTensorExperiment.ForMathlib.Int

#align_import for_mathlib.triangle_shift

noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

-- Porting note: the notations `α_`, `λ_`, `ρ_` are scoped in Lean 4.
open CategoryTheory.MonoidalCategory

universe v u

-- Move + generalize!
@[simp]
theorem CategoryTheory.Discrete.associator_def (a b c : Discrete ℤ) :
    α_ a b c = eqToIso (Discrete.ext _ _ <| add_assoc a.1 b.1 c.1) :=
  rfl

-- Move + generalize!
@[simp]
theorem CategoryTheory.Discrete.leftUnitor_def (a : Discrete ℤ) :
    λ_ a = eqToIso (Discrete.ext _ _ <| zero_add _) :=
  rfl

-- Move + generalize!
@[simp]
theorem CategoryTheory.Discrete.rightUnitor_def (a : Discrete ℤ) :
    ρ_ a = eqToIso (Discrete.ext _ _ <| add_zero _) :=
  rfl

/-! Porting note: mathlib4 (`Mathlib.CategoryTheory.Triangulated.TriangleShift`, which was upstreamed
from this very file) provides the shift on the category of triangles, i.e. `Triangle.shiftFunctor`,
`Triangle.shiftFunctorZero`, `Triangle.shiftFunctorAdd'` and the instance `HasShift (Triangle C) ℤ`.
LTE's own copies (`triangleShiftObj`, `triangleShiftMap`, `triangleShiftFunctor`, `Iso.ofComponents`,
`triangleShiftFunctorε`, `triangleShiftFunctorμ`, `mapTriangleShiftFunctor`, the `*_aux` lemmas and the
instance `Triangle.hasShift`) as well as the helper lemmas about `shiftAdd`/`shiftComm` (which no longer
exist in mathlib4: they are `shiftFunctorAdd`/`shiftFunctorComm`) are therefore removed, to avoid a second,
non-defeq `HasShift (Triangle C) ℤ` instance. `Triangle.hasShift` is kept as a (non-instance)
alias of the mathlib instance since it is referred to explicitly downstream. -/

namespace CategoryTheory.Triangulated

open CategoryTheory.Category CategoryTheory.Pretriangulated

variable (C : Type u) [Category.{v} C] [Preadditive C]

variable [HasShift C ℤ]

namespace Triangle

-- Porting note: alias of the mathlib instance (see the note above).
def hasShift [∀ i : ℤ, (shiftFunctor C i).Additive] : HasShift (Triangle C) ℤ :=
  inferInstance

variable {C}

variable [∀ i : ℤ, (shiftFunctor C i).Additive]

-- Porting note: in mathlib4 the sign is `i.negOnePow : ℤˣ`; the statement keeps LTE's `ℤ`-valued
-- `i.negOnePow'` (which is definitionally the coercion of mathlib's sign), so it is still `rfl`.
@[simp]
theorem shift_obj₁ (T : Triangle C) (i : ℤ) : T⟦i⟧.obj₁ = T.obj₁⟦i⟧ :=
  rfl

@[simp]
theorem shift_obj₂ (T : Triangle C) (i : ℤ) : T⟦i⟧.obj₂ = T.obj₂⟦i⟧ :=
  rfl

@[simp]
theorem shift_obj₃ (T : Triangle C) (i : ℤ) : T⟦i⟧.obj₃ = T.obj₃⟦i⟧ :=
  rfl

@[simp]
theorem shift_mor₁ (T : Triangle C) (i : ℤ) : T⟦i⟧.mor₁ = i.negOnePow' • T.mor₁⟦i⟧' :=
  rfl

@[simp]
theorem shift_mor₂ (T : Triangle C) (i : ℤ) : T⟦i⟧.mor₂ = i.negOnePow' • T.mor₂⟦i⟧' :=
  rfl

@[simp]
theorem shift_mor₃ (T : Triangle C) (i : ℤ) :
    T⟦i⟧.mor₃ = i.negOnePow' • T.mor₃⟦i⟧' ≫ (shiftFunctorComm C 1 i).hom.app T.obj₁ :=
  rfl

@[simp]
theorem shift_hom₁ {T₁ T₂ : Triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₁ = f.hom₁⟦i⟧' :=
  rfl

@[simp]
theorem shift_hom₂ {T₁ T₂ : Triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₂ = f.hom₂⟦i⟧' :=
  rfl

@[simp]
theorem shift_hom₃ {T₁ T₂ : Triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₃ = f.hom₃⟦i⟧' :=
  rfl

end Triangle

namespace Pretriangulated

/-! Porting note: `shiftComm_self` is `CategoryTheory.shiftFunctorComm_eq_refl` in mathlib4. -/

variable [HasZeroObject C] [∀ i : ℤ, (shiftFunctor C i).Additive] [Pretriangulated C]

theorem dist_triangle_iff_of_iso {T₁ T₂ : Triangle C} (e : T₁ ≅ T₂) :
    T₁ ∈ (distTriang C) ↔ T₂ ∈ (distTriang C) :=
  ⟨fun h => isomorphic_distinguished _ h _ e.symm, fun h => isomorphic_distinguished _ h _ e⟩

theorem dist_triangle_rot_iff (T : Triangle C) : T.rotate ∈ (distTriang C) ↔ T ∈ (distTriang C) :=
  by
  refine' ⟨fun h => _, fun h => CategoryTheory.Pretriangulated.rot_of_distTriang _ h⟩
  let e : T ≅ T.rotate.invRotate := (triangleRotation C).unitIso.app T
  rw [← dist_triangle_iff_of_iso _ e.symm]
  exact CategoryTheory.Pretriangulated.inv_rot_of_distTriang _ h

theorem shift_of_dist_triangle (T : Triangle C) (hT : T ∈ (distTriang C)) (i : ℤ) :
    T⟦i⟧ ∈ (distTriang C) :=
  by
  induction' i using Int.induction_on_iff with i
  · exact isomorphic_distinguished T hT _ ((CategoryTheory.shiftFunctorZero (Triangle C) ℤ).app T)
  · suffices T⟦(i + 1 : ℤ)⟧ ≅ T⟦(i : ℤ)⟧.rotate.rotate.rotate
      by
      rw [dist_triangle_iff_of_iso _ this]
      iterate 3 rw [dist_triangle_rot_iff]
    exact (CategoryTheory.shiftFunctorAdd (Triangle C) i 1).app T ≪≫
      ((rotateRotateRotateIso C).app (T⟦i⟧)).symm

end Pretriangulated

end CategoryTheory.Triangulated
