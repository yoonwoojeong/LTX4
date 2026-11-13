import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup

#align_import for_mathlib.FreeAb

noncomputable section

universe v u

namespace CategoryTheory

structure FreeAb (C : Type u) [Category.{v} C] where of ::
  as : C

namespace FreeAb

variable (C : Type u) [Category.{v} C]

instance : Quiver (FreeAb C) where Hom X Y := FreeAbelianGroup (X.as ⟶ Y.as)

variable {C}

protected def id (X : FreeAb C) : X ⟶ X :=
  FreeAbelianGroup.of (𝟙 X.as)

protected def comp {X Y Z : FreeAb C} : (X ⟶ Y) →+ (Y ⟶ Z) →+ (X ⟶ Z) :=
  FreeAbelianGroup.lift fun f : X.as ⟶ Y.as =>
    FreeAbelianGroup.lift fun g : Y.as ⟶ Z.as => FreeAbelianGroup.of (f ≫ g)

variable (C)

instance : CategoryStruct (FreeAb C) where
  id := FreeAb.id
  comp X Y Z f g := FreeAb.comp f g

@[simp]
protected theorem comp_apply {X Y Z : FreeAb C} (f : X ⟶ Y) (g : Y ⟶ Z) : FreeAb.comp f g = f ≫ g :=
  rfl

instance : Category (FreeAb C)
    where
  id_comp' X Y f := by
    show FreeAb.comp X.id f = AddMonoidHom.id _ f; congr 1; clear f; ext1 f
    simp only [AddMonoidHom.id_apply, FreeAb.comp, FreeAbelianGroup.lift.of, FreeAb.id,
      category.id_comp]
  comp_id' X Y f := by
    show FreeAb.comp f Y.id = AddMonoidHom.id _ f
    rw [← AddMonoidHom.flip_apply]; congr 1; clear f; ext1 f
    simp only [AddMonoidHom.id_apply, FreeAb.comp, FreeAbelianGroup.lift.of, FreeAb.id,
      category.comp_id, AddMonoidHom.flip_apply]
  assoc' W X Y Z f g h :=
    by
    show FreeAb.comp.comp (FreeAb.comp f) g h = (FreeAb.comp f).comp (FreeAb.comp g) h
    congr 1
    rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.compHom_apply_apply, ←
      AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]
    congr 1
    conv_rhs =>
      rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.flip_apply, ← AddMonoidHom.comp_apply,
        ← AddMonoidHom.comp_apply]
    congr 1
    clear f g h; ext f g h
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply, AddMonoidHom.flip_apply,
      FreeAb.comp, FreeAbelianGroup.lift.of, category.assoc]

instance : Preadditive (FreeAb C)
    where
  homGroup := by intros; infer_instance
  add_comp := by intros; show FreeAb.comp (_ + _) _ = _; simp only [map_add]; rfl
  comp_add := by intros; show FreeAb.comp _ (_ + _) = _; simp only [map_add]; rfl

def eval [Preadditive C] : FreeAb C ⥤ C
    where
  obj := FreeAb.as
  map X Y := FreeAbelianGroup.lift id
  map_id' X :=
    show FreeAbelianGroup.lift id X.id = 𝟙 X.as by simp only [FreeAb.id, FreeAbelianGroup.lift.of];
      rfl
  map_comp' X Y Z f g :=
    by
    show FreeAbelianGroup.lift id (FreeAb.comp f g) = preadditive.comp_hom _ _
    rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]; congr 1
    rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.comp_apply]
    conv_rhs =>
      rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.flip_apply, ← AddMonoidHom.comp_apply]
    congr 1; clear f g; ext f g
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply, AddMonoidHom.flip_apply,
      FreeAb.comp, FreeAbelianGroup.lift.of]
    rfl

instance eval_additive [Preadditive C] : (eval C).Additive
    where map_add' X Y f g := AddMonoidHom.map_add _ _ _

end FreeAb

namespace Functor

variable {C D : Type _} [Category C] [Category D]

def mapFreeAb (F : C ⥤ D) : FreeAb C ⥤ FreeAb D
    where
  obj X := FreeAb.of (F.obj X.as)
  map X Y := FreeAbelianGroup.map fun f => F.map f
  map_id' X := by erw [FreeAbelianGroup.map_of_apply, F.map_id]; rfl
  map_comp' X Y Z f g :=
    by
    rw [← FreeAb.comp_apply, ← FreeAb.comp_apply, ← AddMonoidHom.comp_apply, ←
      AddMonoidHom.comp_apply]
    congr 1
    rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.comp_apply]
    conv_rhs =>
      rw [← AddMonoidHom.compHom_apply_apply, ← AddMonoidHom.flip_apply, ← AddMonoidHom.comp_apply,
        ← AddMonoidHom.comp_apply]
    congr 1; clear f g; ext f g
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom_apply_apply, AddMonoidHom.flip_apply,
      FreeAb.comp, FreeAbelianGroup.lift.of, FreeAbelianGroup.map, ← F.map_comp]

instance mapFreeAb_additive (F : C ⥤ D) : F.mapFreeAb.Additive
    where map_add' X Y f g := AddMonoidHom.map_add _ _ _

end Functor

end CategoryTheory

