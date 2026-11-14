import LiquidTensorExperiment.Condensed.Exact

#align_import condensed.sheafification_homology

namespace Condensed

universe u

noncomputable abbrev homologyFunctorSheafificationIso {M : Type _} (c : ComplexShape M) (i : M) :
    homology'Functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) c i ⋙ presheafToCondensedAb ≅
      presheafToCondensedAb.mapHomologicalComplex _ ⋙ homology'Functor _ c i :=
  CategoryTheory.Functor.homology'FunctorIso _ _ _

end Condensed

