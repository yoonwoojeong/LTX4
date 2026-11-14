import LiquidTensorExperiment.ForMathlib.DerivedFunctor
import Mathlib.CategoryTheory.Abelian.LeftDerived

#align_import for_mathlib.derived_functor_zero

universe w v u

noncomputable section

namespace CategoryTheory.Abelian.Functor

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

open CategoryTheory.Functor.leftDerived

variable {C : Type u} {D : Type u} [Category.{w} C] [Category.{w} D] [EnoughProjectives C]

variable (F : C ⥤ D) {A₁ A₂ A₃ X : C} {f : A₁ ⟶ A₂} {g : A₂ ⟶ A₃}

variable [Abelian C] [Abelian D] [Additive F] [PreservesFiniteColimits F]

section Les

def δ₀ (A : ShortExactSequence C) :=
  δ F 0 A ≫ (leftDerivedZeroIsoSelf F).hom.app A.1

theorem seven_term_exactSeq (A : ShortExactSequence C) :
    ExactSeq D
      [(F.leftDerived 1).map A.f, (F.leftDerived 1).map A.g, δ₀ F A, F.map A.f, F.map A.g,
        (0 : F.obj A.3 ⟶ F.obj A.3)] :=
  by
  refine' ExactSeq.cons _ _ (exact_of_short_exact _ _ _) _ (ExactSeq.cons _ _ _ _ _)
  · refine'
      Preadditive.exact_of_iso_of_exact' ((F.left_derived 1).map A.g) (δ F 0 A) _ _ (iso.refl _)
        (iso.refl _) ((CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf F).app A.1) (by simp) _ _
    · dsimp [δ₀]; rw [Category.id_comp]
    · exact (CategoryTheory.exact_iff_exactSeq _ _).2 ((six_term_exact_seq F 0 A).extract 1 2)
  refine' ExactSeq.cons _ _ _ _ _
  · refine'
      Preadditive.exact_of_iso_of_exact' (δ F 0 A) ((F.left_derived 0).map A.f) _ _ (iso.refl _)
        ((CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf F).app A.1) ((CategoryTheory.Abelian.Functor.leftDerivedZeroIsoSelf F).app A.2) _
        (by simp) _
    · dsimp [δ₀]; rw [Category.id_comp]
    · exact (CategoryTheory.exact_iff_exactSeq _ _).2 ((six_term_exact_seq F 0 A).extract 2 2)
  apply ExactSeq.cons
  · exact CategoryTheory.Abelian.Functor.preserves_exact_of_PreservesFiniteColimits_of_epi _ A.exact'
  · rw [← CategoryTheory.exact_iff_exactSeq]
    exact ((Abelian.tfae_epi (F.obj A.3) (F.map A.g)).out 0 2).1 inferInstance

end Les

end CategoryTheory.Abelian.Functor

