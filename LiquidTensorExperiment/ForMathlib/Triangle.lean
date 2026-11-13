import Mathlib.CategoryTheory.Triangulated.Rotate

#align_import for_mathlib.triangle

namespace CategoryTheory

namespace Triangulated

open CategoryTheory.Triangulated.TriangleMorphism

variable {C : Type _} [Category C] [HasShift C ℤ] {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂)

theorem triangle_morphism_isIso [IsIso f.hom₁] [IsIso f.hom₂] [IsIso f.hom₃] : IsIso f := by
  refine' ⟨⟨⟨inv f.hom₁, inv f.hom₂, inv f.hom₃, _, _, _⟩, _, _⟩⟩ <;> tidy

instance [IsIso f] : IsIso f.hom₁ := by
  refine' ⟨⟨(inv f).hom₁, _, _⟩⟩ <;>
    simpa only [← comp_hom₁, ← triangle_category_comp, is_iso.hom_inv_id, is_iso.inv_hom_id]

instance [IsIso f] : IsIso f.hom₂ := by
  refine' ⟨⟨(inv f).hom₂, _, _⟩⟩ <;>
    simpa only [← comp_hom₂, ← triangle_category_comp, is_iso.hom_inv_id, is_iso.inv_hom_id]

instance [IsIso f] : IsIso f.hom₃ := by
  refine' ⟨⟨(inv f).hom₃, _, _⟩⟩ <;>
    simpa only [← comp_hom₃, ← triangle_category_comp, is_iso.hom_inv_id, is_iso.inv_hom_id]

@[simp]
theorem inv_hom₁ [IsIso f] : (inv f).hom₁ = inv f.hom₁ := by ext; change (f ≫ inv f).hom₁ = _;
  rw [is_iso.hom_inv_id]; rfl

@[simp]
theorem inv_hom₂ [IsIso f] : (inv f).hom₂ = inv f.hom₂ := by ext; change (f ≫ inv f).hom₂ = _;
  rw [is_iso.hom_inv_id]; rfl

@[simp]
theorem inv_hom₃ [IsIso f] : (inv f).hom₃ = inv f.hom₃ := by ext; change (f ≫ inv f).hom₃ = _;
  rw [is_iso.hom_inv_id]; rfl

theorem triangle_morphism_isIso_iff : IsIso f ↔ IsIso f.hom₁ ∧ IsIso f.hom₂ ∧ IsIso f.hom₃ :=
  by
  constructor
  · intro; refine' ⟨_, _, _⟩ <;> exact inferInstance
  · rintro ⟨_, _, _⟩; exact triangle_morphism_is_iso f

@[simps]
def mkTriangleIso (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂) (e₃ : T₁.obj₃ ≅ T₂.obj₃)
    (comm₁ : T₁.mor₁ ≫ e₂.Hom = e₁.Hom ≫ T₂.mor₁) (comm₂ : T₁.mor₂ ≫ e₃.Hom = e₂.Hom ≫ T₂.mor₂)
    (comm₃ : T₁.mor₃ ≫ e₁.Hom⟦1⟧' = e₃.Hom ≫ T₂.mor₃) : T₁ ≅ T₂ :=
  ⟨⟨_, _, _, comm₁, comm₂, comm₃⟩,
    ⟨e₁.inv, e₂.inv, e₃.inv, by rw [e₂.comp_inv_eq]; simp [comm₁], by rw [e₃.comp_inv_eq];
      simp [comm₂], by rw [e₃.eq_inv_comp, ← category.assoc, ← comm₃]; simp [← functor.map_comp]⟩,
    by ext <;> simp, by ext <;> simp⟩

@[simps]
noncomputable def Triangle.nonnegInvRotate (T : triangle C) : triangle C :=
  triangle.mk _ (T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg _ _).Hom) T.mor₁
    (T.mor₂ ≫ (shiftNegShift _ _).inv)

@[simps]
def Triangle.nonnegRotate {C : Type _} [Category C] [HasShift C ℤ] (T : triangle C) : triangle C :=
  triangle.mk _ T.mor₂ T.mor₃ (T.mor₁⟦1⟧')

variable (C) [Preadditive C]

@[simps]
def neg₃Functor : triangle C ⥤ triangle C
    where
  obj T := triangle.mk C T.mor₁ T.mor₂ (-T.mor₃)
  map S T f :=
    { hom₁ := f.hom₁
      hom₂ := f.hom₂
      hom₃ := f.hom₃ }

@[simps]
def neg₃UnitIso : neg₃Functor C ⋙ neg₃Functor C ≅ 𝟭 _ :=
  by
  refine'
    nat_iso.of_components (fun X => ⟨⟨𝟙 _, 𝟙 _, 𝟙 _, _, _, _⟩, ⟨𝟙 _, 𝟙 _, 𝟙 _, _, _, _⟩, _, _⟩)
      fun X Y f => _
  any_goals ext
  all_goals
    dsimp
    simp only [category.comp_id, category.id_comp, CategoryTheory.Functor.map_id, neg_neg]

@[simps]
def neg₃Equiv : triangle C ≌ triangle C
    where
  Functor := neg₃Functor C
  inverse := neg₃Functor C
  unitIso := (neg₃UnitIso C).symm
  counitIso := neg₃UnitIso C

--move this (do we want this?)
instance {C : Type _} [Category C] [Preadditive C] {X Y : C} : Neg (X ≅ Y) :=
  ⟨fun e => ⟨-e.hom, -e.inv, by simp, by simp⟩⟩

@[simp]
theorem neg_iso_hom {C : Type _} [Category C] [Preadditive C] {X Y : C} {e : X ≅ Y} :
    (-e).hom = -e.hom :=
  rfl

@[simp]
theorem neg_iso_inv {C : Type _} [Category C] [Preadditive C] {X Y : C} {e : X ≅ Y} :
    (-e).inv = -e.inv :=
  rfl

--move this
@[simps]
def CategoryTheory.Equivalence.isoEquiv {C D : Type _} [Category C] [Category D] (e : C ≌ D) (X : C)
    (Y : D) : (e.functor.obj X ≅ Y) ≃ (X ≅ e.inverse.obj Y)
    where
  toFun f := e.unitIso.app X ≪≫ e.inverse.mapIso f
  invFun f := e.functor.mapIso f ≪≫ e.counitIso.app Y
  left_inv f := by
    ext; dsimp; simp only [CategoryTheory.Iso.inv_hom_id_app, category.assoc, functor.map_comp, e.fun_inv_map]
    rw [reassoc_of e.functor_unit_iso_comp]; dsimp; simp
  right_inv f := by ext; dsimp; simp

variable {C} (T : triangle C)

noncomputable def Triangle.nonnegInvRotateNeg₃ [(shiftFunctor C (1 : ℤ)).Additive] :
    (neg₃Functor C).obj T.nonnegInvRotate ≅ T.invRotate :=
  by
  fapply mk_triangle_iso
  exact -iso.refl _
  exact iso.refl _
  exact iso.refl _
  all_goals dsimp; simp

noncomputable def Triangle.nonnegInvRotateIso [(shiftFunctor C (1 : ℤ)).Additive] :
    T.nonnegInvRotate ≅ (neg₃Functor C).obj T.invRotate :=
  (neg₃Equiv C).isoEquiv _ _ T.nonnegInvRotateNeg₃

@[simps]
def neg₃Rotate : neg₃Functor C ⋙ rotate C ≅ rotate C ⋙ neg₃Functor C :=
  NatIso.ofComponents
    (fun X =>
      mkTriangleIso (Iso.refl _) (Iso.refl _) (-Iso.refl _) (by dsimp; simp) (by dsimp; simp)
        (by dsimp; simp))
    fun X Y f => by dsimp; ext <;> dsimp <;> simp

theorem Triangle.nonnegRotate_neg₃ : (neg₃Functor C).obj T.nonnegRotate = T.rotate :=
  rfl

def Triangle.nonnegRotateIso : T.nonnegRotate ≅ (neg₃Functor C).obj T.rotate :=
  (neg₃Equiv C).isoEquiv _ _ (Iso.refl _)

--
@[simps]
def Triangle.obj₁Functor : triangle C ⥤ C
    where
  obj T := T.obj₁
  map S T f := f.hom₁
  map_id' _ := rfl
  map_comp' A B C f g := rfl

@[simps]
def Triangle.obj₂Functor : triangle C ⥤ C
    where
  obj T := T.obj₂
  map S T f := f.hom₂
  map_id' _ := rfl
  map_comp' A B C f g := rfl

@[simps]
def Triangle.obj₃Functor : triangle C ⥤ C
    where
  obj T := T.obj₃
  map S T f := f.hom₃
  map_id' _ := rfl
  map_comp' A B C f g := rfl

end Triangulated

end CategoryTheory

