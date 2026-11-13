import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.Condensed.Exact
import LiquidTensorExperiment.ForMathlib.ExactFunctor

#align_import condensed.evaluation_homology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace Condensed

universe u

variable {X Y Z : Condensed.{u} Ab.{u + 1}} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  (S : Profinite.{u})

noncomputable section

instance evaluation_additive (S : Profinite.{u}) :
    Functor.Additive (Condensed.evaluation _ S : Condensed.{u} Ab.{u + 1} ⥤ _) :=
  ⟨fun X Y f g => rfl⟩

theorem evaluationExact (S : ExtrDisc.{u}) :
    Functor.Exact (Condensed.evaluation _ S.val : Condensed.{u} Ab.{u + 1} ⥤ _) :=
  by
  intro X Y Z f g h
  rw [Condensed.exact_iff_extrDisc] at h 
  apply h

abbrev homologyEvaluationIso (S : ExtrDisc.{u}) :
    (homology' f g w).val.obj (op S.val) ≅
      homology' (f.val.app (op S.val)) (g.val.app (op S.val))
        (by rw [← f.val.comp_app, ← Sheaf.hom.comp_val, w]; rfl) :=
  (Condensed.evaluation Ab.{u + 1} _).homology'Iso _ _ _ _

abbrev homologyFunctorEvaluationIso {M : Type _} (c : ComplexShape M) (i : M) (S : ExtrDisc.{u}) :
    homology'Functor (Condensed.{u} Ab.{u + 1}) c i ⋙ Condensed.evaluation _ S.val ≅
      (Condensed.evaluation _ S.val).mapHomologicalComplex _ ⋙ homology'Functor Ab.{u + 1} c i :=
  (Condensed.evaluation Ab.{u + 1} _).homology'FunctorIso _ _

end Condensed

