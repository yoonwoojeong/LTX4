import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sheafification

#align_import for_mathlib.sheaf

namespace CategoryTheory.Presheaf

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type w} [Category.{max v u} D]

theorem isSheaf_of_iso {F G : Cᵒᵖ ⥤ D} (η : F ≅ G) (hG : IsSheaf J G) : IsSheaf J F :=
  by
  intro T X S hS
  let e : F ⋙ coyoneda.obj (Opposite.op T) ≅ G ⋙ coyoneda.obj (Opposite.op T) :=
    CategoryTheory.isoWhiskerRight η _
  apply CategoryTheory.Presieve.isSheafFor_iso e.symm
  apply hG _ _ hS

variable [ConcreteCategory.{max v u} D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), Limits.HasMultiequalizer (S.index P)]

variable [Limits.PreservesLimits (forget D)]

variable [∀ X : C, Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [∀ X : C, Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

variable [ReflectsIsomorphisms (forget D)]

theorem CategoryTheory.GrothendieckTopology.isIso_sheafifyLift_of_isIso {F G : Cᵒᵖ ⥤ D} (η : F ⟶ G)
    (hG : IsSheaf J G) [h : IsIso η] : IsIso (J.sheafifyLift η hG) :=
  by
  have hF : IsSheaf J F := by apply is_sheaf_of_iso _ (as_iso η) hG
  constructor
  use inv η ≫ J.toSheafify _
  constructor
  · apply J.sheafify_hom_ext _ _
    · exact CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus J F
    simp only [← CategoryTheory.Category.assoc, J.to_sheafify_sheafify_lift, is_iso.hom_inv_id, category.id_comp,
      category.comp_id]
  · simp only [CategoryTheory.Category.assoc, J.to_sheafify_sheafify_lift, is_iso.inv_hom_id]

end CategoryTheory.Presheaf

namespace CategoryTheory

namespace Sheaf

variable {C : Type _} [Category C]

variable {J : GrothendieckTopology C}

variable {A : Type _} [Category A]

@[simp]
theorem Hom.id_val (X : Sheaf J A) : Sheaf.Hom.val (𝟙 X) = 𝟙 X.val :=
  rfl

theorem Hom.comp_val {X Y Z : Sheaf J A} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simps]
def Iso.mk (X Y : Sheaf J A) (e : X.val ≅ Y.val) : X ≅ Y :=
  ⟨⟨e.hom⟩, ⟨e.inv⟩, by ext1; simp, by ext1; simp⟩

end Sheaf

end CategoryTheory

