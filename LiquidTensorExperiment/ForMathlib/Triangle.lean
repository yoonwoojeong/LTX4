import Mathlib.CategoryTheory.Triangulated.Rotate

#align_import for_mathlib.triangle

namespace CategoryTheory

namespace Triangulated

-- Porting note: mathlib4's triangles live in `CategoryTheory.Pretriangulated`
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.TriangleMorphism

variable {C : Type _} [Category C] [HasShift C ℤ]

variable {T₁ T₂ : Triangle C} (f : T₁ ⟶ T₂)

theorem triangle_morphism_isIso [IsIso f.hom₁] [IsIso f.hom₂] [IsIso f.hom₃] : IsIso f :=
  -- Porting note: `tidy` replaced by the corresponding mathlib lemma
  Triangle.isIso_of_isIsos f ‹_› ‹_› ‹_›

instance [IsIso f] : IsIso f.hom₁ :=
  -- Porting note: proof rewritten using `congrArg`
  ⟨⟨(inv f).hom₁, congrArg TriangleMorphism.hom₁ (IsIso.hom_inv_id f),
    congrArg TriangleMorphism.hom₁ (IsIso.inv_hom_id f)⟩⟩

instance [IsIso f] : IsIso f.hom₂ :=
  ⟨⟨(inv f).hom₂, congrArg TriangleMorphism.hom₂ (IsIso.hom_inv_id f),
    congrArg TriangleMorphism.hom₂ (IsIso.inv_hom_id f)⟩⟩

instance [IsIso f] : IsIso f.hom₃ :=
  ⟨⟨(inv f).hom₃, congrArg TriangleMorphism.hom₃ (IsIso.hom_inv_id f),
    congrArg TriangleMorphism.hom₃ (IsIso.inv_hom_id f)⟩⟩

@[simp]
theorem inv_hom₁ [IsIso f] : (inv f).hom₁ = inv f.hom₁ :=
  -- Porting note: `ext` replaced by `IsIso.eq_inv_of_hom_inv_id`
  IsIso.eq_inv_of_hom_inv_id (congrArg TriangleMorphism.hom₁ (IsIso.hom_inv_id f))

@[simp]
theorem inv_hom₂ [IsIso f] : (inv f).hom₂ = inv f.hom₂ :=
  IsIso.eq_inv_of_hom_inv_id (congrArg TriangleMorphism.hom₂ (IsIso.hom_inv_id f))

@[simp]
theorem inv_hom₃ [IsIso f] : (inv f).hom₃ = inv f.hom₃ :=
  IsIso.eq_inv_of_hom_inv_id (congrArg TriangleMorphism.hom₃ (IsIso.hom_inv_id f))

theorem triangle_morphism_isIso_iff : IsIso f ↔ IsIso f.hom₁ ∧ IsIso f.hom₂ ∧ IsIso f.hom₃ := by
  constructor
  · intro h
    refine' ⟨_, _, _⟩ <;> exact inferInstance
  · rintro ⟨h₁, h₂, h₃⟩
    exact CategoryTheory.Triangulated.triangle_morphism_isIso f

@[simps]
def mkTriangleIso (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂) (e₃ : T₁.obj₃ ≅ T₂.obj₃)
    (comm₁ : T₁.mor₁ ≫ e₂.hom = e₁.hom ≫ T₂.mor₁) (comm₂ : T₁.mor₂ ≫ e₃.hom = e₂.hom ≫ T₂.mor₂)
    (comm₃ : T₁.mor₃ ≫ e₁.hom⟦1⟧' = e₃.hom ≫ T₂.mor₃) : T₁ ≅ T₂ :=
  ⟨⟨_, _, _, comm₁, comm₂, comm₃⟩,
    ⟨e₁.inv, e₂.inv, e₃.inv,
      by
        rw [e₂.comp_inv_eq]
        simp [comm₁],
      by
        rw [e₃.comp_inv_eq]
        simp [comm₂],
      by
        rw [e₃.eq_inv_comp, ← Category.assoc, ← comm₃]
        simp [← Functor.map_comp]⟩,
    by ext <;> simp, by ext <;> simp⟩

@[simps]
noncomputable def _root_.CategoryTheory.Pretriangulated.Triangle.nonnegInvRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftShiftNeg _ _).hom) T.mor₁
    (T.mor₂ ≫ (shiftNegShift _ _).inv)

@[simps]
def _root_.CategoryTheory.Pretriangulated.Triangle.nonnegRotate (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₂ T.mor₃ (T.mor₁⟦1⟧')

variable (C)

-- Porting note: split into two `variable` commands
variable [Preadditive C]

@[simps]
def neg₃Functor : Triangle C ⥤ Triangle C
    where
  obj T := Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)
  map f :=
    { hom₁ := f.hom₁
      hom₂ := f.hom₂
      hom₃ := f.hom₃ }

@[simps]
def neg₃UnitIso : neg₃Functor C ⋙ neg₃Functor C ≅ 𝟭 _ :=
  by
  refine'
    NatIso.ofComponents (fun X => ⟨⟨𝟙 _, 𝟙 _, 𝟙 _, _, _, _⟩, ⟨𝟙 _, 𝟙 _, 𝟙 _, _, _, _⟩, _, _⟩)
      fun f => _
  any_goals ext
  all_goals
    dsimp
    simp only [Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_id, neg_neg]

@[simps]
def neg₃Equiv : Triangle C ≌ Triangle C
    where
  functor := neg₃Functor C
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
def _root_.CategoryTheory.Equivalence.isoEquiv {C D : Type _} [Category C] [Category D] (e : C ≌ D) (X : C)
    (Y : D) : (e.functor.obj X ≅ Y) ≃ (X ≅ e.inverse.obj Y)
    where
  toFun f := e.unitIso.app X ≪≫ e.inverse.mapIso f
  invFun f := e.functor.mapIso f ≪≫ e.counitIso.app Y
  left_inv f := by
    ext; dsimp; simp only [CategoryTheory.Iso.inv_hom_id_app, Category.assoc, Functor.map_comp, e.fun_inv_map]
    rw [reassoc_of% e.functor_unitIso_comp]; dsimp; simp
  right_inv f := by ext; dsimp; simp

variable {C}

-- Porting note: split into two `variable` commands
variable (T : Triangle C)

noncomputable def _root_.CategoryTheory.Pretriangulated.Triangle.nonnegInvRotateNeg₃ [(shiftFunctor C (1 : ℤ)).Additive] :
    (neg₃Functor C).obj T.nonnegInvRotate ≅ T.invRotate :=
  by
  fapply CategoryTheory.Triangulated.mkTriangleIso
  exact -Iso.refl _
  exact Iso.refl _
  exact Iso.refl _
  all_goals dsimp; simp

noncomputable def _root_.CategoryTheory.Pretriangulated.Triangle.nonnegInvRotateIso [(shiftFunctor C (1 : ℤ)).Additive] :
    T.nonnegInvRotate ≅ (neg₃Functor C).obj T.invRotate :=
  (neg₃Equiv C).isoEquiv _ _ T.nonnegInvRotateNeg₃

@[simps]
def neg₃Rotate : neg₃Functor C ⋙ rotate C ≅ rotate C ⋙ neg₃Functor C :=
  NatIso.ofComponents
    (fun X =>
      mkTriangleIso (Iso.refl _) (Iso.refl _) (-Iso.refl _) (by dsimp; simp) (by dsimp; simp)
        (by dsimp; simp))
    fun f => by dsimp; ext <;> dsimp <;> simp

theorem _root_.CategoryTheory.Pretriangulated.Triangle.nonnegRotate_neg₃ : (neg₃Functor C).obj T.nonnegRotate = T.rotate :=
  rfl

def _root_.CategoryTheory.Pretriangulated.Triangle.nonnegRotateIso : T.nonnegRotate ≅ (neg₃Functor C).obj T.rotate :=
  (neg₃Equiv C).isoEquiv _ _ (Iso.refl _)

--
-- Porting note: the `[Preadditive C]` binder is written explicitly (Lean 3 included the section
-- variable `[preadditive C]` in these declarations)
@[simps]
def _root_.CategoryTheory.Pretriangulated.Triangle.obj₁Functor [Preadditive C] : Triangle C ⥤ C
    where
  obj T := T.obj₁
  map f := f.hom₁
  map_id _ := rfl
  map_comp f g := rfl

@[simps]
def _root_.CategoryTheory.Pretriangulated.Triangle.obj₂Functor [Preadditive C] : Triangle C ⥤ C
    where
  obj T := T.obj₂
  map f := f.hom₂
  map_id _ := rfl
  map_comp f g := rfl

@[simps]
def _root_.CategoryTheory.Pretriangulated.Triangle.obj₃Functor [Preadditive C] : Triangle C ⥤ C
    where
  obj T := T.obj₃
  map f := f.hom₃
  map_id _ := rfl
  map_comp f g := rfl

end Triangulated

end CategoryTheory

