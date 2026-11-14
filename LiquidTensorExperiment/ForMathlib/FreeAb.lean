import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup

#align_import for_mathlib.FreeAb

noncomputable section

universe v u

/-- Porting note: two-variable extensionality for additive maps out of free abelian groups.
Lean 3's recursive `ext f g` is replaced by this explicit lemma. -/
theorem freeAbelianGroup_ext₂ {α β γ : Type _} [AddCommGroup γ]
    (P Q : FreeAbelianGroup α →+ FreeAbelianGroup β →+ γ)
    (h : ∀ a b, P (FreeAbelianGroup.of a) (FreeAbelianGroup.of b) =
      Q (FreeAbelianGroup.of a) (FreeAbelianGroup.of b)) : P = Q := by
  apply FreeAbelianGroup.lift.ext
  intro a
  apply FreeAbelianGroup.lift.ext
  intro b
  exact h a b

namespace CategoryTheory

structure FreeAb (C : Type u) [Category.{v} C] where of ::
  as : C

namespace FreeAb

variable (C : Type u) [Category.{v} C]

instance : Quiver (FreeAb C) where Hom X Y := FreeAbelianGroup (X.as ⟶ Y.as)

-- Porting note: instance search does not unfold `X ⟶ Y` to `FreeAbelianGroup _`,
-- so the additive group structure on the hom-types is provided explicitly.
instance homAddCommGroup (X Y : FreeAb C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup (X.as ⟶ Y.as)))

variable {C}

protected def id (X : FreeAb C) : X ⟶ X :=
  FreeAbelianGroup.of (𝟙 X.as)

protected def comp {X Y Z : FreeAb C} : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z) :=
  FreeAbelianGroup.lift fun f : X.as ⟶ Y.as =>
    FreeAbelianGroup.lift fun g : Y.as ⟶ Z.as => FreeAbelianGroup.of (f ≫ g)

variable (C)

instance : CategoryStruct (FreeAb C) where
  id := FreeAb.id
  comp f g := FreeAb.comp f g

@[simp]
protected theorem comp_apply {X Y Z : FreeAb C} (f : X ⟶ Y) (g : Y ⟶ Z) : FreeAb.comp f g = f ≫ g :=
  rfl

-- Porting note: a helper lemma for the basis case of `map_comp` below; the `erw` is needed
-- because `simp` does not fire `FreeAbelianGroup.lift.of` on these hom-types.
protected theorem comp_of_of {X Y Z : FreeAb C} (a : X.as ⟶ Y.as) (b : Y.as ⟶ Z.as) :
    FreeAb.comp (X := X) (Y := Y) (Z := Z) (FreeAbelianGroup.of a) (FreeAbelianGroup.of b) =
      FreeAbelianGroup.of (a ≫ b) := by
  simp only [FreeAb.comp]
  erw [FreeAbelianGroup.lift.of, FreeAbelianGroup.lift.of]

instance : Category (FreeAb C)
    where
  id_comp := by
    intro X Y f
    show FreeAb.comp X.id f = AddMonoidHom.id _ f
    congr 1
    clear f
    apply FreeAbelianGroup.lift.ext
    intro f
    simp only [FreeAb.comp, FreeAb.id]
    -- Porting note: `simp` does not fire `FreeAbelianGroup.lift.of` on these hom-types
    -- (instance mismatch), so `erw` is used for the rewrites.
    erw [FreeAbelianGroup.lift.of, FreeAbelianGroup.lift.of, AddMonoidHom.id_apply]
    simp only [Category.id_comp]
  comp_id := by
    intro X Y f
    show FreeAb.comp f Y.id = AddMonoidHom.id _ f
    rw [← AddMonoidHom.flip_apply]
    congr 1
    clear f
    apply FreeAbelianGroup.lift.ext
    intro f
    simp only [FreeAb.comp, FreeAb.id]
    -- Porting note: `erw` is needed for `FreeAbelianGroup.lift.of`, see `id_comp` above.
    erw [AddMonoidHom.flip_apply, FreeAbelianGroup.lift.of, FreeAbelianGroup.lift.of,
      AddMonoidHom.id_apply, Category.comp_id]
  assoc := by
    intro W X Y Z f g h
    show FreeAb.comp.comp (FreeAb.comp f) g h = (FreeAb.comp f).comp (FreeAb.comp g) h
    congr 1
    rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.compHom_apply_apply, ←
      AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]
    congr 1
    conv_rhs =>
      rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.flip_apply, ← AddMonoidHom.comp_apply,
        ← AddMonoidHom.comp_apply]
    congr 1
    clear f g h
    apply FreeAbelianGroup.lift.ext
    intro f
    apply FreeAbelianGroup.lift.ext
    intro g
    apply FreeAbelianGroup.lift.ext
    intro h
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply, AddMonoidHom.flip_apply,
      FreeAb.comp]
    -- Porting note: `erw` is needed for `FreeAbelianGroup.lift.of`, see `id_comp` above.
    repeat' erw [FreeAbelianGroup.lift.of]
    simp only [Category.assoc]

instance : Preadditive (FreeAb C)
    where
  homGroup := by intros; infer_instance
  add_comp := by
    intros
    show FreeAb.comp (_ + _) _ = _
    simp only [map_add, AddMonoidHom.add_apply, FreeAb.comp_apply]
  comp_add := by
    intros
    show FreeAb.comp _ (_ + _) = _
    simp only [map_add, AddMonoidHom.add_apply, FreeAb.comp_apply]

def eval [Preadditive C] : FreeAb C ⥤ C
    where
  obj := FreeAb.as
  map f := FreeAbelianGroup.lift id f
  map_id X := by
    show FreeAbelianGroup.lift id (FreeAb.id X) = 𝟙 X.as
    simp only [FreeAb.id, FreeAbelianGroup.lift.of, id_eq]
  map_comp := by
    intro X Y Z f g
    have key := freeAbelianGroup_ext₂
      ((AddMonoidHom.compHom (FreeAbelianGroup.lift (id : (X.as ⟶ Z.as) → (X.as ⟶ Z.as)))).comp
        (FreeAb.comp (X := X) (Y := Y) (Z := Z)))
      ((AddMonoidHom.compHom' (FreeAbelianGroup.lift (id : (Y.as ⟶ Z.as) → (Y.as ⟶ Z.as)))).comp
        ((Preadditive.compHom (P := X.as) (Q := Y.as) (R := Z.as)).comp
          (FreeAbelianGroup.lift (id : (X.as ⟶ Y.as) → (X.as ⟶ Y.as)))))
      (by
        intro a b
        show FreeAbelianGroup.lift id (FreeAb.comp (FreeAbelianGroup.of a) (FreeAbelianGroup.of b)) =
          FreeAbelianGroup.lift id (FreeAbelianGroup.of a) ≫ FreeAbelianGroup.lift id (FreeAbelianGroup.of b)
        simp only [FreeAb.comp]
        -- Porting note: `erw` is needed for `FreeAbelianGroup.lift.of`, see `id_comp` above.
        repeat' erw [FreeAbelianGroup.lift.of]
        rfl)
    exact FunLike.congr_fun (FunLike.congr_fun key f) g

instance eval_additive [Preadditive C] : (eval C).Additive where
  map_add := by
    intros
    exact AddMonoidHom.map_add _ _ _

end FreeAb

namespace Functor

variable {C D : Type _} [Category C] [Category D]

def mapFreeAb (F : C ⥤ D) : FreeAb C ⥤ FreeAb D
    where
  obj X := FreeAb.of (F.obj X.as)
  map f := FreeAbelianGroup.map (fun g => F.map g) f
  map_id X := by
    show FreeAbelianGroup.map (fun g => F.map g) (FreeAbelianGroup.of (𝟙 X.as)) =
      FreeAbelianGroup.of (𝟙 (F.obj X.as))
    simp only [FreeAbelianGroup.map_of_apply, F.map_id]
  map_comp := by
    intro X Y Z f g
    have key := freeAbelianGroup_ext₂
      ((AddMonoidHom.compHom (FreeAbelianGroup.map (fun h => F.map h))).comp
        (FreeAb.comp (X := X) (Y := Y) (Z := Z)))
      ((AddMonoidHom.compHom' (FreeAbelianGroup.map (fun h => F.map h))).comp
        ((FreeAb.comp (X := FreeAb.of (F.obj X.as)) (Y := FreeAb.of (F.obj Y.as))
          (Z := FreeAb.of (F.obj Z.as))).comp (FreeAbelianGroup.map (fun h => F.map h))))
      (by
        intro a b
        -- Porting note: `erw` is needed for the `AddMonoidHom` unfoldings and the basis
        -- computation: `simp` does not fire these lemmas on the hom-types, see `id_comp`.
        repeat' erw [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply,
          AddMonoidHom.compHom'_apply_apply]
        erw [FreeAbelianGroup.map_of_apply, FreeAb.comp_of_of, FreeAbelianGroup.map_of_apply,
          F.map_comp])
    have h2 := FunLike.congr_fun (FunLike.congr_fun key f) g
    trace_state
    sorry

instance mapFreeAb_additive (F : C ⥤ D) : F.mapFreeAb.Additive where
  map_add := by
    intros
    exact AddMonoidHom.map_add _ _ _

end Functor

end CategoryTheory
