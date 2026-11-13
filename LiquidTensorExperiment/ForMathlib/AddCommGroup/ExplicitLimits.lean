import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory

#align_import for_mathlib.AddCommGroup.explicit_limits

universe u v

namespace Ab

open CategoryTheory

open CategoryTheory.Limits

variable {J : Type u} [CategoryTheory.SmallCategory J] (K : J ⥤ Ab.{max u v})

theorem comp_apply {A B C : Ab} (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) :=
  rfl

instance : AddCommGroup (K ⋙ CategoryTheory.forget _).sections
    where
  add u v :=
    ⟨u + v, fun i j f => by
      have u2 := u.2 f
      have v2 := v.2 f
      dsimp only [functor.comp_map, Pi.add_apply, forget_map_eq_coe, Subtype.val_eq_coe] at u2 v2 ⊢
      simp only [u2, v2, map_add]⟩
  add_assoc a b c := by ext; simp only [add_assoc, Subtype.coe_mk]
  zero :=
    ⟨0, fun i j f =>
      by
      dsimp only [CategoryTheory.Functor.comp_map, Pi.zero_apply, forget_map_eq_coe]
      rw [map_zero]⟩
  zero_add a := by ext; simp only [Subtype.coe_mk, zero_add]
  add_zero a := by ext; simp only [Subtype.coe_mk, add_zero]
  neg t :=
    ⟨-t, by
      intro i j f
      have t2 := t.2 f
      dsimp only [CategoryTheory.Functor.comp_map, Pi.neg_apply, forget_map_eq_coe, Subtype.val_eq_coe] at t2 ⊢
      simp only [map_neg, t2]⟩
  add_left_neg a := by ext; change -a.1 Pell.Solution₁.x + a.1 Pell.Solution₁.x = 0; simp only [add_left_neg]
  add_comm a b := by ext; change a.1 Pell.Solution₁.x + b.1 Pell.Solution₁.x = b.1 Pell.Solution₁.x + a.1 Pell.Solution₁.x; rw [add_comm]

def explicitLimitCone : Cone K
    where
  pt := AddCommGroupCat.of (K ⋙ CategoryTheory.forget _).sections
  π :=
    { app := fun j =>
        { toFun := fun t => t.1 j
          map_zero' := rfl
          map_add' := fun x y => rfl }
      naturality' := by
        intro i j f
        ext
        simpa using (x.2 f).symm }

def explicitLimitConeIsLimit : IsLimit (explicitLimitCone K)
    where
  lift S :=
    { toFun := fun t =>
        ⟨fun j => S.π.app j t, by
          intro i j f
          dsimp
          rw [← S.w f]
          rfl⟩
      map_zero' := by ext; dsimp; simpa
      map_add' := fun x y => by ext; dsimp; simpa }
  fac := by
    intro S j
    ext
    rfl
  uniq := by
    intro S m hm
    ext
    simpa [← hm]

noncomputable def barx : PreservesLimit K (forget Ab.{max u v}) :=
  PreservesLimitsOfShape.preservesLimit

noncomputable instance foo {K : J ⥤ Ab.{u}} : PreservesLimit K (forget Ab.{u}) :=
  barx.{u, u} K

theorem is_limit_ext {K : J ⥤ Ab.{u}} (C : LimitCone K) (x y : C.cone.pt)
    (h : ∀ j : J, C.cone.π.app j x = C.cone.π.app j y) : x = y :=
  Limits.Concrete.isLimit_ext K C.2 _ _ h

noncomputable instance forgetCreatesLimit (J : Type u) [SmallCategory J] (K : J ⥤ Ab.{max u v}) :
    CreatesLimit K (forget Ab) :=
  createsLimitOfReflectsIso fun C hC =>
    { liftedCone := explicitLimitCone _
      validLift := (Types.limitConeIsLimit _).uniqueUpToIso hC
      makesLimit := explicitLimitConeIsLimit _ }

-- Do we have this somewhere else?
noncomputable instance forgetCreatesLimits : CreatesLimits (forget Ab.{max u v}) := by constructor;
  intro J hJ; constructor; intro K; apply Ab.forgetCreatesLimit.{_, u} J K

-- Do we have this somewhere else?
noncomputable instance forgetCreatesLimits' : CreatesLimits (forget Ab.{u}) :=
  Ab.forgetCreatesLimits.{u, u}

end Ab

