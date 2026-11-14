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
-- Porting note: `open CategoryTheory` moved up from below, as the `⥤` notation is needed here.
open CategoryTheory

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
      -- Porting note: Lean 4 `Prefunctor.map` takes its source and target implicitly.
      map := fun f => comapHom f.unop f.unop.continuous
      map_id := fun S => comapHom_id
      map_comp := fun f g =>
        (comapHom_comp ⇑g.unop ⇑f.unop g.unop.continuous f.unop.continuous).symm }
  -- Porting note: Lean 4 `Functor.map` takes its source and target implicitly.
  map f :=
    { app := fun S => mapHom f
      naturality := fun S₁ S₂ g => by
        dsimp; ext s
        simp only [SemiNormedGroupCat.coe_comp, NormedAddGroupHom.coe_comp, Function.comp_apply]
        -- Porting note: `ext` does not see through the bundled carrier, and `simp` lemmas do not
        -- match it, so the pointwise computation is given by explicit terms.
        refine LocallyConstant.ext fun t => ?_
        exact (congrArg (⇑f) (LocallyConstant.coe_comap_apply (⇑g.unop) s
          (ContinuousMap.continuous g.unop) t)).trans
          (LocallyConstant.coe_comap_apply (⇑g.unop) (LocallyConstant.map (⇑f) s)
            (ContinuousMap.continuous g.unop) t).symm }
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

@[simp]
theorem locallyConstant_map_apply (M : SemiNormedGroupCat) (X Y : Profinite) (f : X ⟶ Y)
    (g : (locallyConstant.obj M).obj (op Y)) (x : X) :
    -- Porting note: `.toFun` is not accessible by dot notation on the bundled carrier.
    (LocallyConstant.toFun ((locallyConstant.obj M).map f.op g)) x = LocallyConstant.toFun g (f x) :=
  by
  dsimp [LocallyConstant, comap]
  -- Porting note: the Lean 3 `split_ifs` is replaced by the explicit `coe_comap_apply`, since the
  -- `comap` definition is a `dite` on continuity that does not reduce definitionally.
  exact LocallyConstant.coe_comap_apply (⇑f) g (ContinuousMap.continuous f) x

theorem locallyConstant_obj_map_normNoninc (V : SemiNormedGroupCat) (X Y : Profiniteᵒᵖ)
    (φ : X ⟶ Y) : ((locallyConstant.obj V).map φ).NormNoninc :=
  comapHom_normNoninc φ.unop φ.unop.continuous

universe u

-- TODO: Fix the statement below using bounded colimits.
--@[nolint unused_arguments]
--instance {M : SemiNormedGroup.{u}} {J : Type u} [small_category J] [is_filtered J] :
--  limits.preserves_colimits_of_shape J (LocallyConstant.obj M) := by admit
end SemiNormedGroupCat

-- Porting note: the Lean 3 `#lint` command is omitted; its Lean 4 output is not part of the port.

