import LiquidTensorExperiment.ForMathlib.HomotopyCategoryOp

#align_import for_mathlib.homotopy_category_functor_compatibilities

noncomputable section

open Opposite

namespace CategoryTheory

namespace Functor

def quotientOpMapHomologyNatIso {A B : Type _} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : Aᵒᵖ ⥤ B) {ι : Type _} (c : ComplexShape ι) [Functor.Additive F] (i : ι) :
    (HomotopyCategory.quotient A c).op ⋙
        HomotopyCategory.opFunctor ⋙
          Functor.mapHomotopyCategory c.symm F ⋙ HomotopyCategory.homology'Functor _ _ i ≅
      HomologicalComplex.opFunctor ⋙ F.mapHomologicalComplex c.symm ⋙ homology'Functor _ _ i :=
  by
  refine'
    _ ≪≫
      iso_whisker_left (HomologicalComplex.opFunctor ⋙ F.map_homological_complex c.symm)
          (HomotopyCategory.homology'Factors B c.symm i) ≪≫
        functor.associator _ _ _
  refine' functor.associator _ _ _ ≪≫ _ ≪≫ (functor.associator _ _ _).symm
  refine' iso_whisker_left _ _
  refine' (functor.associator _ _ _).symm ≪≫ _ ≪≫ functor.associator _ _ _
  refine' iso_whisker_right _ _
  exact (F.map_homotopy_category_comp c.symm).symm

def quotientOpMapHomologyIso {A B : Type _} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : Aᵒᵖ ⥤ B) {ι : Type _} {c : ComplexShape ι} [Functor.Additive F] (X : HomotopyCategory A c)
    (i : ι) :
    (HomotopyCategory.opFunctor ⋙
            Functor.mapHomotopyCategory c.symm F ⋙ HomotopyCategory.homology'Functor _ _ i).obj
        (op X) ≅
      (F.mapHomologicalComplex c.symm ⋙ homology'Functor _ _ i).obj X.as.op :=
  by
  have e : op X ≅ (HomotopyCategory.quotient A c).op.obj (op X.as) :=
    by
    dsimp
    apply iso.op
    apply eq_to_iso
    cases X
    rfl
  refine' _ ≪≫ (F.quotient_op_map_homology_nat_iso c i).app (op X.as) ≪≫ _
  ·
    exact
      (HomotopyCategory.opFunctor ⋙
            functor.map_homotopy_category c.symm F ⋙
              HomotopyCategory.homology'Functor B c.symm i).mapIso
        e
  · rfl

end Functor

end CategoryTheory

