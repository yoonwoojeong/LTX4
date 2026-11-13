import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Abelian.Homology

#align_import for_mathlib.ComposableMorphisms

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D]

namespace CategoryTheory

variable (C)

/- TODO : define the subcategory of complexes with 3 objects, and consider
functor to this category, etc. -/
structure ComposableMorphisms where
  {pt y z : C}
  f : X ⟶ Y
  g : Y ⟶ Z

instance [Inhabited C] : Inhabited (ComposableMorphisms C) :=
  ⟨⟨𝟙 default, 𝟙 default⟩⟩

variable {C}

namespace ComposableMorphisms

@[ext]
structure Hom (S₁ S₂ : ComposableMorphisms C) where
  τ₁ : S₁.pt ⟶ S₂.pt
  τ₂ : S₁.y ⟶ S₂.y
  τ₃ : S₁.z ⟶ S₂.z
  comm₁₂' : S₁.f ≫ τ₂ = τ₁ ≫ S₂.f
  comm₂₃' : S₁.g ≫ τ₃ = τ₂ ≫ S₂.g

namespace Hom

attribute [reassoc] comm₁₂

attribute [reassoc] comm₂₃

attribute [local simp] comm₁₂ comm₂₃

@[simps]
def id (S : ComposableMorphisms C) : Hom S S
    where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := 𝟙 _
  comm₁₂' := by simp
  comm₂₃' := by simp

instance (S : ComposableMorphisms C) : Inhabited (Hom S S) :=
  ⟨id S⟩

@[simps]
def comp {S₁ S₂ S₃ : ComposableMorphisms C} (φ : Hom S₁ S₂) (ψ : Hom S₂ S₃) : Hom S₁ S₃
    where
  τ₁ := φ.τ₁ ≫ ψ.τ₁
  τ₂ := φ.τ₂ ≫ ψ.τ₂
  τ₃ := φ.τ₃ ≫ ψ.τ₃
  comm₁₂' := by simp only [comm₁₂_assoc, comm₁₂, assoc]
  comm₂₃' := by simp only [comm₂₃_assoc, comm₂₃, assoc]

end Hom

instance : Category (ComposableMorphisms C)
    where
  Hom S₁ S₂ := Hom S₁ S₂
  id := Hom.id
  comp S₁ S₂ S₃ := Hom.comp

@[simp]
theorem id_τ₁ (S : ComposableMorphisms C) : Hom.τ₁ (𝟙 S) = 𝟙 _ :=
  rfl

@[simp]
theorem id_τ₂ (S : ComposableMorphisms C) : Hom.τ₂ (𝟙 S) = 𝟙 _ :=
  rfl

@[simp]
theorem id_τ₃ (S : ComposableMorphisms C) : Hom.τ₃ (𝟙 S) = 𝟙 _ :=
  rfl

@[simp]
theorem comp_τ₁ {S₁ S₂ S₃ : ComposableMorphisms C} (φ : S₁ ⟶ S₂) (ψ : S₂ ⟶ S₃) :
    (φ ≫ ψ).τ₁ = φ.τ₁ ≫ ψ.τ₁ :=
  rfl

@[simp]
theorem comp_τ₂ {S₁ S₂ S₃ : ComposableMorphisms C} (φ : S₁ ⟶ S₂) (ψ : S₂ ⟶ S₃) :
    (φ ≫ ψ).τ₂ = φ.τ₂ ≫ ψ.τ₂ :=
  rfl

@[simp]
theorem comp_τ₃ {S₁ S₂ S₃ : ComposableMorphisms C} (φ : S₁ ⟶ S₂) (ψ : S₂ ⟶ S₃) :
    (φ ≫ ψ).τ₃ = φ.τ₃ ≫ ψ.τ₃ :=
  rfl

def Zero (S : ComposableMorphisms C) [HasZeroMorphisms C] : Prop :=
  S.f ≫ S.g = 0

end ComposableMorphisms

namespace Functor

@[simps]
def mapComposableMorphisms (F : C ⥤ D) : ComposableMorphisms C ⥤ ComposableMorphisms D
    where
  obj S :=
    { f := F.map S.f
      g := F.map S.g }
  map S₁ S₂ φ :=
    { τ₁ := F.map φ.τ₁
      τ₂ := F.map φ.τ₂
      τ₃ := F.map φ.τ₃
      comm₁₂' := by dsimp; simp only [← F.map_comp, φ.comm₁₂]
      comm₂₃' := by dsimp; simp only [← F.map_comp, φ.comm₂₃] }

end Functor

namespace ComposableMorphisms

@[simps]
def applyFunctor (S : ComposableMorphisms C) (F : C ⥤ D) :=
  F.mapComposableMorphisms.obj S

end ComposableMorphisms

end CategoryTheory

