import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective
import Mathlib.CategoryTheory.Filtered.Basic
import LiquidTensorExperiment.LocallyConstant.Analysis
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels

#align_import locally_constant.SemiNormedGroup

/-!

# The functor of locally constant maps

The functor sending a seminormed group `V` and a profinite type `S` to the seminormed group
of locally constant maps from `S` to `V` (with the sup norm).

## Main definition

- `LocallyConstant : SemiNormedGroup ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroup` : the functor.

-/


noncomputable section

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.proofs -/
set_option pp.proofs true

namespace SemiNormedGroupCat

open Opposite LocallyConstant

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

/-- The bifunctor of locally constant maps from profinite spaces to seminormed groups.
    The effects on homs of groups or space are defined in terms of push-forward
    (ie. post-composition) and pull-back (ie. pre-composition) of locally constant maps
    respectively. -/
@[simps]
def locallyConstant : SemiNormedGroupCat ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroupCat
    where
  obj V :=
    { obj := fun S => SemiNormedGroupCat.of <| LocallyConstant (unop S : Profinite) V
      map := fun S₁ S₂ f => comapHom f.unop f.unop.continuous
      map_id := fun S => comapHom_id
      map_comp := fun S₁ S₂ S₃ f g => (comapHom_comp _ _ _ _).symm }
  map V W f :=
    { app := fun S => mapHom f
      naturality := fun S₁ S₂ g => by
        dsimp; ext
        simp only [map_hom_apply, LocallyConstant.comapHom_apply, CategoryTheory.coe_comp, Function.comp_apply,
          map_apply, coe_comap, g.unop.continuous] }
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

@[simp]
theorem locallyConstant_map_apply (M : SemiNormedGroupCat) (X Y : Profinite) (f : X ⟶ Y)
    (g : (locallyConstant.obj M).obj (op Y)) (x : X) :
    ((locallyConstant.obj M).map f.op g).toFun x = g.toFun (f x) :=
  by
  dsimp [LocallyConstant, comap]
  split_ifs
  · rfl
  all_goals exfalso; apply h; continuity

theorem locallyConstant_obj_map_normNoninc (V : SemiNormedGroupCat) (X Y : Profiniteᵒᵖ)
    (φ : X ⟶ Y) : ((locallyConstant.obj V).map φ).NormNoninc :=
  comapHom_normNoninc _ _

open CategoryTheory

universe u

-- TODO: Fix the statement below using bounded colimits.
--@[nolint unused_arguments]
--instance {M : SemiNormedGroup.{u}} {J : Type u} [small_category J] [is_filtered J] :
--  limits.preserves_colimits_of_shape J (LocallyConstant.obj M) := by admit
end SemiNormedGroupCat

#lint

