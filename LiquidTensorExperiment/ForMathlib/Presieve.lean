import Mathlib.CategoryTheory.Sites.Sheaf

#align_import for_mathlib.presieve

open CategoryTheory Opposite

universe w v u v' u'

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Presieve

theorem mem_ofArrows_iff {ι} {B Y} (X : ι → C) (f : ∀ i, X i ⟶ B) (g : Y ⟶ B) :
    ofArrows X f g ↔ ∃ (i : ι) (hi : Y = X i), g = eqToHom hi ≫ f i :=
  by
  constructor
  · rintro ⟨i⟩
    use i, rfl
    simp
  · rintro ⟨i, rfl, rfl⟩
    simp [ofArrows.mk i]

noncomputable section

def indexOfArrows {ι} {B Y} {X : ι → C} {f : ∀ i, X i ⟶ B} {g : Y ⟶ B} (h : ofArrows X f g) : ι :=
  ((mem_ofArrows_iff X f g).mp h).some

theorem eq_obj_ofArrows {ι} {B Y} {X : ι → C} {f : ∀ i, X i ⟶ B} {g : Y ⟶ B} (h : ofArrows X f g) :
    Y = X (indexOfArrows h) :=
  ((mem_ofArrows_iff X f g).mp h).choose_spec.some

@[simp]
theorem eq_hom_ofArrows {ι} {B Y} {X : ι → C} {f : ∀ i, X i ⟶ B} {g : Y ⟶ B} (h : ofArrows X f g) :
    eqToHom (eq_obj_ofArrows h) ≫ f _ = g :=
  ((mem_ofArrows_iff X f g).mp h).choose_spec.choose_spec.symm

def mkFamilyOfElementsOfArrows {ι} {B} (X : ι → C) (f : ∀ i, X i ⟶ B) (F : Cᵒᵖ ⥤ Type w)
    (x : ∀ i, F.obj (op (X i))) : (ofArrows X f).FamilyOfElements F := fun Y f hf =>
  F.map (eqToHom <| eq_obj_ofArrows hf).op (x <| indexOfArrows hf)

theorem mkFamilyOfElementsOfArrows_compatible {ι} {B} (X : ι → C) (f : ∀ i, X i ⟶ B)
    (F : Cᵒᵖ ⥤ Type w) (x : ∀ i, F.obj (op (X i)))
    (hx :
      ∀ (i j : ι) (Z) (g₁ : Z ⟶ X i) (g₂ : Z ⟶ X j),
        g₁ ≫ f _ = g₂ ≫ f _ → F.map g₁.op (x _) = F.map g₂.op (x _)) :
    (mkFamilyOfElementsOfArrows X f F x).Compatible :=
  by
  intro X Y Z g₁ g₂ f₁ f₂ h₁ h₂ h
  dsimp [CategoryTheory.Presieve.mkFamilyOfElementsOfArrows]
  specialize
    hx (CategoryTheory.Presieve.indexOfArrows h₁) (CategoryTheory.Presieve.indexOfArrows h₂) Z (g₁ ≫ eq_to_hom (CategoryTheory.Presieve.eq_obj_ofArrows h₁))
      (g₂ ≫ eq_to_hom (CategoryTheory.Presieve.eq_obj_ofArrows h₂)) (by simpa)
  convert hx using 1 <;> simp

theorem mkFamilyOfElementsOfArrows_eval {ι} {B} (X : ι → C) (f : ∀ i, X i ⟶ B) (F : Cᵒᵖ ⥤ Type w)
    (x : ∀ i, F.obj (op (X i)))
    (hx :
      ∀ (i j : ι) (Z) (g₁ : Z ⟶ X i) (g₂ : Z ⟶ X j),
        g₁ ≫ f _ = g₂ ≫ f _ → F.map g₁.op (x _) = F.map g₂.op (x _))
    (i : ι) : (mkFamilyOfElementsOfArrows X f F x) (f i) (Presieve.ofArrows.mk i) = x i :=
  by
  have : X i = X (CategoryTheory.Presieve.indexOfArrows (Presieve.ofArrows.mk i)) := by fapply CategoryTheory.Presieve.eq_obj_ofArrows
  rotate_left 2; exact f
  dsimp [CategoryTheory.Presieve.mkFamilyOfElementsOfArrows]
  specialize hx i (CategoryTheory.Presieve.indexOfArrows (Presieve.ofArrows.mk i))
  rotate_left 3; exact X; exact f
  specialize hx (X i) (𝟙 _) (eq_to_hom this) (by simp)
  simp at hx 
  simpa using hx.symm

end CategoryTheory.Presieve

