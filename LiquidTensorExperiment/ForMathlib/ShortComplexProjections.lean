import LiquidTensorExperiment.ForMathlib.ShortComplex

#align_import for_mathlib.short_complex_projections

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe v

namespace ShortComplex

variable {C : Type _} [Category C] [HasZeroMorphisms C]

@[simps]
def π₁ : ShortComplex C ⥤ C where
  obj S := S.1.pt
  map S₁ S₂ f := f.τ₁

@[simps]
def π₂ : ShortComplex C ⥤ C where
  obj S := S.1.y
  map S₁ S₂ f := f.τ₂

@[simps]
def π₃ : ShortComplex C ⥤ C where
  obj S := S.1.z
  map S₁ S₂ f := f.τ₃

@[simps]
def φ₁₂ : (π₁ : ShortComplex C ⥤ C) ⟶ π₂
    where
  app S := S.1.f
  naturality S₁ S₂ f := (ComposableMorphisms.Hom.comm₁₂ f).symm

@[simps]
def φ₂₃ : (π₂ : ShortComplex C ⥤ C) ⟶ π₃
    where
  app S := S.1.g
  naturality S₁ S₂ f := (ComposableMorphisms.Hom.comm₂₃ f).symm

end ShortComplex

