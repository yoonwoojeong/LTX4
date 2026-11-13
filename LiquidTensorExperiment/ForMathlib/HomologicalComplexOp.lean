import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Homology.Additive

#align_import for_mathlib.homological_complex_op

noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type _} [Category C] [Preadditive C]

variable {ι : Type _} {c : ComplexShape ι}

@[simps]
protected def op (X : HomologicalComplex C c) : HomologicalComplex Cᵒᵖ c.symm
    where
  X i := op (X.pt i)
  d i j := (X.d j i).op
  shape' i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' := by intros; rw [← op_comp, X.d_comp_d, op_zero]

@[simps]
protected def unop (X : HomologicalComplex Cᵒᵖ c) : HomologicalComplex C c.symm
    where
  X i := unop (X.pt i)
  d i j := (X.d j i).unop
  shape' i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' := by intros; rw [← unop_comp, X.d_comp_d, unop_zero]

@[simps]
def opFunctor : (HomologicalComplex C c)ᵒᵖ ⥤ HomologicalComplex Cᵒᵖ c.symm
    where
  obj X := (unop X).op
  map X Y f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j hij => by simp only [op_d, ← op_comp, f.unop.comm] }

@[simps]
def unopFunctor : (HomologicalComplex Cᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex C c.symm
    where
  obj X := (unop X).unop
  map X Y f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j hij => by simp only [unop_d, ← unop_comp, f.unop.comm] }

instance opFunctor_additive : (@opFunctor C _ _ _ c).Additive where

instance unopFunctor_additive : (@unopFunctor C _ _ _ c).Additive where

end HomologicalComplex

