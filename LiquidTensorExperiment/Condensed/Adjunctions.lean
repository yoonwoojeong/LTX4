import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import LiquidTensorExperiment.ForMathlib.SheafOfTypesSheafification
import LiquidTensorExperiment.ForMathlib.WhiskerAdjunction
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Exact
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Main
import LiquidTensorExperiment.ForMathlib.AddCommGroup
import LiquidTensorExperiment.Condensed.Basic

#align_import condensed.adjunctions

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

@[simps obj map]
def condensedSetToPresheaf : CondensedSet ⥤ Profiniteᵒᵖ ⥤ Type _ :=
  sheafToPresheaf _ _

@[simps obj_val map]
def presheafToCondensedSet : (Profiniteᵒᵖ ⥤ Type _) ⥤ CondensedSet :=
  presheafToSheaf _ _

def condensedSetPresheafAdjunction : presheafToCondensedSet ⊣ condensedSetToPresheaf :=
  sheafificationAdjunction proetaleTopology (Type (u + 1))

@[simp]
theorem condensedSetPresheafAdjunction_homEquiv_apply (X : Profiniteᵒᵖ ⥤ Type _) (Y : CondensedSet)
    (e : presheafToCondensedSet.obj X ⟶ Y) :
    condensedSetPresheafAdjunction.homEquiv _ _ e = proetaleTopology.toSheafify X ≫ e.val :=
  rfl

@[simp]
theorem condensedSetPresheafAdjunction_homEquiv_symm_apply (X : Profiniteᵒᵖ ⥤ Type _)
    (Y : CondensedSet) (e : X ⟶ condensedSetToPresheaf.obj Y) :
    ((condensedSetPresheafAdjunction.homEquiv _ _).symm e).val =
      proetaleTopology.sheafifyLift e Y.cond :=
  rfl

@[simp]
theorem condensedSetPresheafAdjunction_unit_app (X : Profiniteᵒᵖ ⥤ Type _) :
    condensedSetPresheafAdjunction.Unit.app X = proetaleTopology.toSheafify X :=
  rfl

@[simp]
theorem condensedSetPresheafAdjunction_counit_app (Y : CondensedSet) :
    (condensedSetPresheafAdjunction.counit.app Y).val =
      proetaleTopology.sheafifyLift (𝟙 _) Y.cond :=
  rfl

@[simps obj_val map]
def condensedAbToCondensedSet : Condensed Ab ⥤ CondensedSet :=
  sheafCompose _ (forget _)

@[simps obj_val map]
def condensedSetToCondensedAb : CondensedSet ⥤ Condensed Ab :=
  Sheaf.composeAndSheafify _ AddCommGroupCat.free

@[simps obj_val map]
def condensedSetToCondensedAb' : CondensedSet ⥤ Condensed Ab :=
  Sheaf.composeAndSheafify _ AddCommGroupCat.free'

@[simps hom_app_val inv_app_val]
def condensedSetToCondensedAbIso : condensedSetToCondensedAb ≅ condensedSetToCondensedAb' :=
  isoWhiskerLeft _ <| isoWhiskerRight (Functor.mapIso _ <| AddCommGroupCat.freeIsoFree') _

@[simps unit_app counit_app]
def condensedAbCondensedSetAdjunction : condensedSetToCondensedAb ⊣ condensedAbToCondensedSet :=
  Sheaf.adjunction _ AddCommGroupCat.adj

@[simps unit_app counit_app]
def condensedAbCondensedSetAdjunction' : condensedSetToCondensedAb' ⊣ condensedAbToCondensedSet :=
  Sheaf.adjunction _ AddCommGroupCat.adj'

@[simp]
theorem condensedAbCondensedSetAdjunction_homEquiv_apply (X : CondensedSet) (Y : Condensed Ab)
    (e : condensedSetToCondensedAb.obj X ⟶ Y) :
    (condensedAbCondensedSetAdjunction.homEquiv _ _ e).val =
      (AddCommGroupCat.adj.whiskerRight _).homEquiv _ _ (proetaleTopology.toSheafify _ ≫ e.val) :=
  rfl

@[simp]
theorem condensedAbCondensedSetAdjunction_homEquiv_symm_apply (X : CondensedSet) (Y : Condensed Ab)
    (e : X ⟶ condensedAbToCondensedSet.obj Y) :
    ((condensedAbCondensedSetAdjunction.homEquiv _ _).symm e).val =
      proetaleTopology.sheafifyLift (((AddCommGroupCat.adj.whiskerRight _).homEquiv _ _).symm e.val)
        Y.2 :=
  rfl

@[simp]
theorem condensedAbCondensedSetAdjunction'_homEquiv_apply (X : CondensedSet) (Y : Condensed Ab)
    (e : condensedSetToCondensedAb'.obj X ⟶ Y) :
    (condensedAbCondensedSetAdjunction'.homEquiv _ _ e).val =
      (AddCommGroupCat.adj'.whiskerRight _).homEquiv _ _ (proetaleTopology.toSheafify _ ≫ e.val) :=
  rfl

@[simp]
theorem condensedAbCondensedSetAdjunction'_homEquiv_symm_apply (X : CondensedSet) (Y : Condensed Ab)
    (e : X ⟶ condensedAbToCondensedSet.obj Y) :
    ((condensedAbCondensedSetAdjunction'.homEquiv _ _).symm e).val =
      proetaleTopology.sheafifyLift
        (((AddCommGroupCat.adj'.whiskerRight _).homEquiv _ _).symm e.val) Y.2 :=
  rfl

def presheafToCondensedAb : (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) ⥤ Condensed.{u} Ab.{u + 1} :=
  presheafToSheaf _ _

def condensedAbToPresheaf : Condensed.{u} Ab.{u + 1} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  sheafToPresheaf _ _

def condensedAbPresheafAdjunction : presheafToCondensedAb.{u} ⊣ condensedAbToPresheaf.{u} :=
  sheafificationAdjunction _ _

instance presheafToCondensedAbPreservesColimits : PreservesColimits presheafToCondensedAb.{u} :=
  condensedAbPresheafAdjunction.leftAdjointPreservesColimits

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

instance : Functor.Additive presheafToCondensedAb.{u} := by
  apply CategoryTheory.Sheaf.presheafToSheaf_additive.{u + 2, u, u + 1}

instance : Functor.Additive condensedAbToPresheaf :=
  ⟨⟩

instance : PreservesColimits presheafToCondensedAb :=
  condensedAbPresheafAdjunction.leftAdjointPreservesColimits

instance : PreservesFiniteLimits presheafToCondensedAb :=
  CategoryTheory.presheafToSheaf.Limits.preservesFiniteLimits.{u + 2, u, u + 1}

