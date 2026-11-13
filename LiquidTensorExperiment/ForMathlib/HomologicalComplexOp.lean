import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Homology.Additive

#align_import for_mathlib.homological_complex_op

noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type _} [Category C] [Preadditive C]

variable {ι : Type _} {c : ComplexShape ι}

#print HomologicalComplex.op /-
@[simps]
protected def op (X : HomologicalComplex C c) : HomologicalComplex Cᵒᵖ c.symm
    where
  pt i := op (X.pt i)
  d i j := (X.d j i).op
  shape' i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' := by intros; rw [← op_comp, X.d_comp_d, op_zero]
-/

#print HomologicalComplex.unop /-
@[simps]
protected def unop (X : HomologicalComplex Cᵒᵖ c) : HomologicalComplex C c.symm
    where
  pt i := unop (X.pt i)
  d i j := (X.d j i).unop
  shape' i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' := by intros; rw [← unop_comp, X.d_comp_d, unop_zero]
-/

#print HomologicalComplex.opFunctor /-
@[simps]
def opFunctor : (HomologicalComplex C c)ᵒᵖ ⥤ HomologicalComplex Cᵒᵖ c.symm
    where
  obj X := (unop X).op
  map X Y f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j hij => by simp only [op_d, ← op_comp, f.unop.comm] }
-/

#print HomologicalComplex.unopFunctor /-
@[simps]
def unopFunctor : (HomologicalComplex Cᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex C c.symm
    where
  obj X := (unop X).unop
  map X Y f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j hij => by simp only [unop_d, ← unop_comp, f.unop.comm] }
-/

#print HomologicalComplex.opFunctor_additive /-
instance opFunctor_additive : (@opFunctor C _ _ _ c).Additive where
-/

#print HomologicalComplex.unopFunctor_additive /-
instance unopFunctor_additive : (@unopFunctor C _ _ _ c).Additive where
-/

end HomologicalComplex

