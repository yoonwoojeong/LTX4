import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import LiquidTensorExperiment.Condensed.Adjunctions

#align_import condensed.adjunctions_module

open CategoryTheory

open CategoryTheory.Limits

universe u

variable (A : Type (u + 1)) [Ring A]

abbrev CondensedMod :=
  Condensed.{u} (ModuleCat.{u + 1} A)

noncomputable section

instance forgetModulePreservesColimitsProetaleTopologyCover (X : Profinite.{u}) :
    Limits.PreservesColimitsOfShape (proetaleTopology.cover X)ᵒᵖ (forget (ModuleCat.{u + 1} A)) :=
  inferInstance

-- TODO: Move this. Also, do we have this somewhere already?
instance forget_moduleCat_reflectsIsomorphisms :
    ReflectsIsomorphisms (forget (ModuleCat.{u + 1} A)) :=
  by
  constructor
  intro M N f h
  rw [is_iso_iff_bijective] at *
  let e := LinearEquiv.ofBijective f h.1 h.2
  use e.symm
  constructor
  · ext t; change e.symm (e t) = t; rw [LinearEquiv.symm_apply_apply]
  · ext t; change e (e.symm t) = t; rw [LinearEquiv.apply_symm_apply]

-- (AT) I will fix this in mathlib asap...
instance : HasColimits (ModuleCat.{u + 1} A) :=
  ModuleCat.Colimits.hasColimits_moduleCat.{u + 1, u + 1}

instance abelianCondensedMod : Abelian (CondensedMod A) := by
  apply
    @CategoryTheory.Sheaf.abelian.{u + 2, u, u + 1} Profinite.{u} _ proetaleTopology
      (ModuleCat.{u + 1} A) _ _ _ _ _ _ _ _

def condensedModToCondensedSet : CondensedMod A ⥤ CondensedSet :=
  sheafCompose _ (forget _)

@[simps obj_val map]
def condensedSetToCondensedMod : CondensedSet ⥤ CondensedMod A :=
  Sheaf.composeAndSheafify _ (ModuleCat.free A)

@[simps unit_app counit_app]
def condensedModCondensedSetAdjunction :
    condensedSetToCondensedMod A ⊣ condensedModToCondensedSet A :=
  Sheaf.adjunction _ (ModuleCat.adj A)

@[simp]
theorem condensedModCondensedSetAdjunction_homEquiv_apply (X : CondensedSet) (Y : CondensedMod A)
    (e : (condensedSetToCondensedMod A).obj X ⟶ Y) :
    ((condensedModCondensedSetAdjunction A).homEquiv _ _ e).val =
      ((ModuleCat.adj A).whiskerRight _).homEquiv _ _ (proetaleTopology.toSheafify _ ≫ e.val) :=
  rfl

@[simp]
theorem condensedModCondensedSetAdjunction_homEquiv_symm_apply (X : CondensedSet)
    (Y : CondensedMod A) (e : X ⟶ (condensedModToCondensedSet A).obj Y) :
    (((condensedModCondensedSetAdjunction A).homEquiv _ _).symm e).val =
      proetaleTopology.sheafifyLift ((((ModuleCat.adj A).whiskerRight _).homEquiv _ _).symm e.val)
        Y.2 :=
  rfl

