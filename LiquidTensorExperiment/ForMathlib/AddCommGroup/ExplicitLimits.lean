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

-- Porting note: the instance is obtained from mathlib's `sectionsAddSubgroup` (Lean 4 cannot
-- elaborate the original structure instance on the coerced set `sections`).
-- Porting note: the instance is named so that its universes can be given explicitly below.
instance sectionsAddCommGroup : AddCommGroup (K ⋙ CategoryTheory.forget _).sections :=
  @AddSubgroup.toAddCommGroup (∀ j, K.obj j) _
    (AddGroupCat.sectionsAddSubgroup.{u, max u v}
      (K ⋙ forget₂ AddCommGroupCat.{max u v} AddGroupCat.{max u v}))

-- Porting note: explicit universes help Lean 4 unify `max u v`.
def explicitLimitCone : Cone.{u, max u v, u, max u v + 1} K where
  pt := @AddCommGroupCat.of _ (sectionsAddCommGroup.{u, v} K)
  π :=
    { app := fun j =>
        { toFun := fun t => t.1 j
          map_zero' := rfl
          map_add' := fun x y => rfl }
      naturality := by
        intro i j f
        ext x
        exact (x.2 f).symm }

def explicitLimitConeIsLimit : IsLimit (explicitLimitCone.{u, v} K) where
  lift S :=
    { toFun := fun t =>
        ⟨fun j => S.π.app j t, by
          intro i j f
          dsimp
          rw [← S.w f]
          rfl⟩
      map_zero' := by
        apply Subtype.ext
        funext j
        exact (S.π.app j).map_zero
      map_add' := fun x y => by
        apply Subtype.ext
        funext j
        exact (S.π.app j).map_add x y }
  fac := by
    intro S j
    ext
    rfl
  uniq := by
    intro S m hm
    ext x
    apply Subtype.ext
    funext j
    exact FunLike.congr_fun (hm j) x

noncomputable def barx : PreservesLimit K (forget Ab.{max u v}) :=
  -- Porting note: the instance is given explicitly to help Lean unify universe levels
  haveI := AddCommGroupCat.forgetPreservesLimitsOfSize.{u, v}
  PreservesLimitsOfShape.preservesLimit

noncomputable instance foo {K : J ⥤ Ab.{u}} : PreservesLimit K (forget Ab.{u}) :=
  barx.{u, u} K

theorem is_limit_ext {K : J ⥤ Ab.{u}} (C : LimitCone K) (x y : C.cone.pt)
    (h : ∀ j : J, C.cone.π.app j x = C.cone.π.app j y) : x = y :=
  Limits.Concrete.isLimit_ext K C.2 _ _ h

noncomputable instance forgetCreatesLimit (J : Type u) [SmallCategory J] (K : J ⥤ Ab.{max u v}) :
    CreatesLimit K (forget Ab) :=
  createsLimitOfReflectsIso fun C hC =>
    { liftedCone := explicitLimitCone.{u, v} K
      validLift := (Types.limitConeIsLimit.{u, max u v} _).uniqueUpToIso hC
      makesLimit := explicitLimitConeIsLimit.{u, v} K }

-- Do we have this somewhere else?
noncomputable instance forgetCreatesLimits : CreatesLimits (forget Ab.{max u v}) := by
  constructor
  intro J hJ
  constructor
  intro K
  apply Ab.forgetCreatesLimit.{_, u} J K

-- Do we have this somewhere else?
noncomputable instance forgetCreatesLimits' : CreatesLimits (forget Ab.{u}) :=
  Ab.forgetCreatesLimits.{u, u}

end Ab
