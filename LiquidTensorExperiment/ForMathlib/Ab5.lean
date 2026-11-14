import LiquidTensorExperiment.ForMathlib.ExactFunctor
import LiquidTensorExperiment.ForMathlib.Ab4
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.FunctorCategory
import LiquidTensorExperiment.ForMathlib.HomologicalComplex2
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import LiquidTensorExperiment.ForMathlib.ShortComplexColimits

#align_import for_mathlib.ab5

namespace CategoryTheory

open CategoryTheory.Limits

universe v u

variable (A : Type u) [Category.{v} A] [Abelian A] [HasColimits A]

instance colim_additive (J : Type v) [SmallCategory J] :
    Functor.Additive (Limits.colim : (J ⥤ A) ⥤ A) :=
  ⟨⟩

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-
TODO: Change `AB5` from this definition to saying that `colim : (J ⥤ A) ⥤ A`
preserves finite limits and colimits whenever `J` is filtered.
-/
class AB5 : Prop where
  cond : ∀ (J : Type v) [SmallCategory J] [IsFiltered J], Functor.Exact (Limits.colim : (J ⥤ A) ⥤ A)

variable (J : Type v) [SmallCategory J] [IsFiltered J]

theorem AB5.colimExact [AB5 A] : Functor.Exact (Limits.colim : (J ⥤ A) ⥤ A) :=
  AB5.cond A J

variable [PreservesFiniteLimits (Limits.colim : (J ⥤ A) ⥤ A)]
  [PreservesFiniteColimits (Limits.colim : (J ⥤ A) ⥤ A)]

noncomputable def colimitHomologyFunctorIso {M : Type} (c : ComplexShape M) (i : M) :
    homology'Functor (J ⥤ A) c i ⋙ Limits.colim ≅
      Limits.colim.mapHomologicalComplex _ ⋙ homology'Functor _ _ i :=
  Functor.homology'FunctorIso _ _ _

noncomputable def evalFunctorColimitIso {M : Type} (c : ComplexShape M)
    (F : J ⥤ HomologicalComplex A c) :
    colimit F ≅ (Limits.colim.mapHomologicalComplex c).obj (HomologicalComplex.EvalFunctor.obj F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => preservesColimitIso (HomologicalComplex.eval A c i) _)
    (by
      intro i j hij
      rw [← Iso.eq_inv_comp]
      apply colimit.hom_ext
      intro k
      dsimp
      simp only [colimit.ι_map, CategoryTheory.whiskerLeft_app, ι_preserves_colimits_iso_inv_assoc,
        HomologicalComplex.eval_map, HomologicalComplex.Hom.comm_assoc]
      congr
      rw [CategoryTheory.preservesColimitIso, ←
        Limits.colimit.isoColimitCocone_ι_inv
          ⟨_, PreservesColimit.preserves (colimit.isColimit F)⟩]
      rfl)

noncomputable instance homologyFunctorPreservesFilteredColimit {M : Type} (c : ComplexShape M)
    (i : M) (F : J ⥤ HomologicalComplex A c) : PreservesColimit F (homology'Functor A c i) :=
  preservesColimitOfNatIso F (ShortComplex.homologyFunctorIso A c i).symm

noncomputable instance homologyFunctorPreservesFilteredColimits {M : Type} (c : ComplexShape M)
    (i : M)
    [∀ (J : Type v) [hJ : SmallCategory J] [@IsFiltered J hJ],
        preserves_finite_limits (Limits.colim : (J ⥤ A) ⥤ A)]
    [∀ (J : Type v) [hJ : SmallCategory J] [@IsFiltered J hJ],
        preserves_finite_colimits (Limits.colim : (J ⥤ A) ⥤ A)] :
    PreservesFilteredColimits (homology'Functor A c i : HomologicalComplex A c ⥤ A) := by
  constructor; intro J _ _; constructor

end CategoryTheory

