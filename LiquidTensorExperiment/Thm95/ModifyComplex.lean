import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import thm95.modify_complex

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {ι : Type} {V₁ V₂ : Type _} {c : ComplexShape ι}

variable [Category V₁] [Category V₂] [Preadditive V₁] [Preadditive V₂]

-- this is of course functorial in `C`, see below
@[simps]
def modify (C : HomologicalComplex V₁ c) (F : ι → V₁ ⥤ V₂) (α : ∀ i j, F i ⟶ F j)
    [∀ i, (F i).Additive] : HomologicalComplex V₂ c
    where
  X i := (F i).obj (C.pt i)
  d i j := (F i).map (C.d i j) ≫ (α i j).app _
  shape' i j h := by rw [C.shape _ _ h, CategoryTheory.Functor.map_zero, zero_comp]
  d_comp_d' i j k hij hjk := by
    simp only [NatTrans.naturality_assoc, ← Functor.map_comp_assoc, Category.assoc, C.d_comp_d,
      CategoryTheory.Functor.map_zero, zero_comp, comp_zero]

-- this is a generalization of `functor.map_homological_complex`
@[simps (config := { fullyApplied := false })]
def modifyFunctor (F : ι → V₁ ⥤ V₂) (α : ∀ i j, F i ⟶ F j) [∀ i, (F i).Additive] :
    HomologicalComplex V₁ c ⥤ HomologicalComplex V₂ c
    where
  obj C := C.modify F α
  map C₁ C₂ f :=
    { f := fun i => (F i).map (f.f i)
      comm' := by
        intro i j hij; dsimp
        rw [← Category.assoc, ← (F i).map_comp, f.comm, (F i).map_comp, Category.assoc,
          (α _ _).naturality, Category.assoc] }
  map_id := by intro X; dsimp at *; simp at *; rfl
  map_comp := by intro X Y Z f g; dsimp at *; simp at *; rfl

end HomologicalComplex

