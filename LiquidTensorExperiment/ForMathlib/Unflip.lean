import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Products.Basic

#align_import for_mathlib.unflip

open CategoryTheory

namespace CategoryTheory

namespace NatTrans

@[simps]
def unflip {C D E : Type _} [Category C] [Category D] [Category E] {F G : C ⥤ D ⥤ E}
    (φ : F.flip ⟶ G.flip) : F ⟶ G
    where
  app c :=
    { app := fun d => (φ.app d).app c
      naturality := fun d₁ d₂ g => NatTrans.congr_app (φ.naturality g) c }
  naturality c₁ c₂ f := by
    ext d
    exact (φ.app d).naturality f

theorem unflip_id {C D E : Type _} [Category C] [Category D] [Category E] {F : C ⥤ D ⥤ E} :
    NatTrans.unflip (𝟙 F.flip) = 𝟙 F :=
  rfl

theorem unflip_comp {C D E : Type _} [Category C] [Category D] [Category E] {F G H : C ⥤ D ⥤ E}
    (φ₁ : F.flip ⟶ G.flip) (φ₂ : G.flip ⟶ H.flip) :
    NatTrans.unflip (φ₁ ≫ φ₂) = NatTrans.unflip φ₁ ≫ NatTrans.unflip φ₂ :=
  rfl

end NatTrans

namespace NatIso

def unflip {C D E : Type _} [Category C] [Category D] [Category E] {F G : C ⥤ D ⥤ E}
    (e : F.flip ≅ G.flip) : F ≅ G
    where
  hom := NatTrans.unflip e.hom
  inv := NatTrans.unflip e.inv
  hom_inv_id := by rw [← NatTrans.unflip_comp, e.hom_inv_id, NatTrans.unflip_id]
  inv_hom_id := by rw [← NatTrans.unflip_comp, e.inv_hom_id, NatTrans.unflip_id]

end NatIso

namespace Functor

def flipEvaluationCompWhiskeringRight (C : Type _) {D E : Type _} [Category C] [Category D]
    [Category E] (H : D ⥤ E) :
    (evaluation C D ⋙ (whiskeringRight (C ⥤ D) D E).obj H).flip ≅ (whiskeringRight C D E).obj H :=
  Iso.refl _

def whiskeringRightObjComp (C : Type _) {D₁ D₂ D₃ : Type _} [Category C] [Category D₁] [Category D₂]
    [Category D₃] (F₁₂ : D₁ ⥤ D₂) (F₂₃ : D₂ ⥤ D₃) :
    (whiskeringRight C _ _).obj (F₁₂ ⋙ F₂₃) ≅
      (whiskeringRight C _ _).obj F₁₂ ⋙ (whiskeringRight C _ _).obj F₂₃ :=
  Iso.refl _

end Functor

end CategoryTheory

