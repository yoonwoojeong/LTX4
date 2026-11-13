import LiquidTensorExperiment.ForMathlib.ShortComplexFunctorCategory

#align_import for_mathlib.short_complex_homological_complex

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ : Type _} [Category C₁] [Category C₂] [Category C₃] [HasZeroMorphisms C₃]
  [HasZeroObject C₃]

theorem isZero_of_comp (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (h : Limits.IsZero G) : Limits.IsZero (F ⋙ G) :=
  by
  rw [limits.is_zero.iff_id_eq_zero]
  ext
  apply limits.is_zero.eq_zero_of_src
  dsimp
  apply limits.is_zero.obj
  exact h

end Functor

end CategoryTheory

namespace HomologicalComplex

variable (C : Type _) [Category C] [HasZeroMorphisms C] {M : Type _} (c : ComplexShape M)

@[simps]
def prevFunctor (i : M) : HomologicalComplex C c ⥤ C :=
  HomologicalComplex.eval _ c (c.prev i)

@[simps]
def nextFunctor (i : M) : HomologicalComplex C c ⥤ C :=
  HomologicalComplex.eval _ c (c.next i)

def prevFunctorIsoEval (i j : M) (hij : c.Rel j i) :
    prevFunctor C c i ≅ HomologicalComplex.eval C c j :=
  NatIso.ofComponents (fun X => X.xPrevIso hij) fun X Y f => by dsimp;
    rw [← iso.eq_comp_inv, assoc, ← hom.prev_eq f hij]

def nextFunctorIsoEval (i j : M) (hij : c.Rel i j) :
    nextFunctor C c i ≅ HomologicalComplex.eval C c j :=
  NatIso.ofComponents (fun X => X.xNextIso hij) fun X Y f => by dsimp;
    rw [← iso.eq_comp_inv, assoc, ← hom.next_eq f hij]

end HomologicalComplex

namespace ShortComplex

variable (C : Type _) [Category C] [HasZeroMorphisms C] {M : Type _} (c : ComplexShape M)

def functorHomologicalComplexπ₁IsoPrevFunctor (i : M) :
    functorHomologicalComplex C c i ⋙ π₁ ≅ HomologicalComplex.prevFunctor C c i := by rfl

def functorHomologicalComplexπ₂IsoEval (i : M) :
    functorHomologicalComplex C c i ⋙ π₂ ≅ HomologicalComplex.eval C c i := by rfl

def functorHomologicalComplexπ₃IsoNextFunctor (i : M) :
    functorHomologicalComplex C c i ⋙ π₃ ≅ HomologicalComplex.nextFunctor C c i := by rfl

end ShortComplex

