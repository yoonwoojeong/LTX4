import Mathlib.CategoryTheory.Functor.LeftDerived

#align_import for_mathlib.projectives

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C]

variable [Preadditive C] [HasZeroObject C] [HasEqualizers C] [HasImages C]

structure IsProjectiveResolution (P : ChainComplex C ℕ) (Z : C)
    (π : P ⟶ (ChainComplex.single₀ C).obj Z) : Prop where
  Projective : ∀ n, Projective (P.pt n) := by infer_instance
  exact₀ : Exact (P.d 1 0) (π.f 0) := by infer_instance
  exact : ∀ n, Exact (P.d (n + 2) (n + 1)) (P.d (n + 1) n) := by infer_instance
  Epi : Epi (π.f 0) := by infer_instance

def IsProjectiveResolution.mkProjectiveResolution (P : ChainComplex C ℕ) (Z : C)
    (π : P ⟶ (ChainComplex.single₀ C).obj Z) (h : P.IsProjectiveResolution Z π) :
    ProjectiveResolution Z :=
  { h with
    complex := P
    π }

end ChainComplex

