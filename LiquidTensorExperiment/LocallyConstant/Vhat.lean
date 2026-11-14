import LiquidTensorExperiment.LocallyConstant.SemiNormedGroup
import LiquidTensorExperiment.NormedGroup.NormedWithAut
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Completion

#align_import locally_constant.Vhat

/-!

# Completions of normed groups

This file contains an API for completions for seminormed groups equipped with
an automorphism which scales norms by a constant factor `r`.

## Main definitions

- `normed_with_aut_Completion` : if `V` is equipped with an automorphism changing norms
  by a factor `r` then the completion also has such an automorphism.
- `LCC : SemiNormedGroup ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroup` :
  `LCC V S` is the seminormed group completion of the locally constant functions from `S` to `V`.

## TODO

Pull off the stuff about completions and put it into `normed_add_comm_group/SemiNormedGroup`?
Then `system_of_complexes.basic` would not have to import this file.

-/


noncomputable section

open scoped NNReal

universe u

namespace SemiNormedGroupCat

-- Porting note: `Completion` is no longer opened: in Lean 4 it would resolve to
-- `UniformSpace.Completion` instead of the functor `SemiNormedGroupCat.completion`.
open UniformSpace Opposite CategoryTheory

-- Porting note: the uniform space structure on `LocallyConstant S V` is not found by instance
-- search through the bundled carrier in the statement of `lCC_obj_map`, so the local instances
-- used in `locallyConstant` are brought in scope here as well.
attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

instance normedWithAutCompletion (V : SemiNormedGroupCat.{u}) (r : ℝ≥0) [NormedWithAut r V] :
    NormedWithAut r (completion.obj V)
    where
  t := completion.mapIso NormedWithAut.t
  norm_t := by
    -- Porting note: the Lean 3 proof used `AbstractCompletion.funext`, which does not unify
    -- through the bundled carrier here; use density of the image of `V` instead.
    have huc : UniformContinuous
        (⇑(id NormedWithAut.t.hom : NormedAddGroupHom V V)) :=
      NormedAddGroupHom.uniformContinuous (V₁ := V) (V₂ := V) NormedWithAut.t.hom
    intro v
    refine' UniformSpace.Completion.induction_on v (isClosed_eq _ _) _
    · exact Continuous.norm (UniformSpace.Completion.continuous_map (f := ⇑(id NormedWithAut.t.hom : NormedAddGroupHom V V)))
    · exact continuous_const.mul (continuous_norm (E := UniformSpace.Completion V))
    intro a
    calc
      _ = _ := congr_arg norm (UniformSpace.Completion.map_coe huc _)
      _ = _ := ?_
    erw [UniformSpace.Completion.norm_coe, NormedWithAut.norm_t, UniformSpace.Completion.norm_coe]

@[simp]
theorem completion_t_inv_eq (V : SemiNormedGroupCat.{u}) (r : ℝ≥0) [NormedWithAut r V] :
    (NormedWithAut.t.hom : completion.obj V ⟶ _) = completion.map NormedWithAut.t.hom :=
  rfl

theorem t_hom_incl {V : SemiNormedGroupCat} {r : ℝ≥0} [NormedWithAut r V] :
    (completion.incl : V ⟶ _) ≫ NormedWithAut.t.hom = NormedWithAut.t.hom ≫ completion.incl :=
  by
  ext x
  simp only [completion.incl_apply, CategoryTheory.comp_apply, completion_t_inv_eq]
  have huc : UniformContinuous
      (⇑(id NormedWithAut.t.hom : NormedAddGroupHom V V)) :=
    NormedAddGroupHom.uniformContinuous (V₁ := V) (V₂ := V) NormedWithAut.t.hom
  change UniformSpace.Completion.map (⇑(id NormedWithAut.t.hom : NormedAddGroupHom V V)) _ = _
  exact UniformSpace.Completion.map_coe huc x

theorem t_hom_eq {V : SemiNormedGroupCat} {r : ℝ≥0} [NormedWithAut r V] :
    NormedWithAut.t.hom = completion.lift ((NormedWithAut.t.hom : V ⟶ V) ≫ completion.incl) :=
  completion.lift_unique _ _ t_hom_incl

/-- `LCC` (Locally Constant Completion) is the bifunctor
that sends a seminormed group `V` and a profinite space `S` to `V-hat(S)`.
Here `V-hat(S)` is the completion (for the sup norm) of the locally constant functions `S → V`. -/
def lCC : SemiNormedGroupCat ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroupCat :=
  curry.obj (uncurry.obj locallyConstant ⋙ completion)

theorem lCC_obj_map' (V : SemiNormedGroupCat) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) :
    (lCC.obj V).map f = completion.map ((locallyConstant.obj V).map f) :=
  by
  delta lCC
  simp only [curry_obj_obj_map, locallyConstant_obj_map, Functor.comp_map, uncurry_obj_map,
    NatTrans.id_app, Functor.map_comp, Functor.map_id, CategoryTheory.Functor.map_id]
  erw [← Functor.map_comp, Category.id_comp]

theorem lCC_obj_map (V : SemiNormedGroupCat) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X)
    (v : (lCC.obj V).obj Y) :
    (lCC.obj V).map f v = UniformSpace.Completion.map (LocallyConstant.comap f.unop) v := by
  rw [lCC_obj_map']
  rfl

theorem lCC_obj_map_normNoninc (V : SemiNormedGroupCat) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) :
    ((lCC.obj V).map f).NormNoninc := by
  rw [lCC_obj_map']
  exact completion.map_normNoninc <| locallyConstant_obj_map_normNoninc _ _ _ _

variable (S : Type _) [TopologicalSpace S] [CompactSpace S]

@[simps]
instance normedWithAutLocallyConstant (V : SemiNormedGroupCat) (S : Profiniteᵒᵖ) (r : ℝ≥0)
    [NormedWithAut r V] [hr : Fact (0 < r)] : NormedWithAut r ((locallyConstant.obj V).obj S)
    where
  t := (locallyConstant.mapIso NormedWithAut.t).app S
  norm_t := by
    rw [← op_unop S]
    rintro (f : LocallyConstant (unop S : Profinite) V)
    show sSup _ = (r : ℝ) * sSup _
    dsimp
    -- Porting note: `simp only [NormedWithAut.norm_t]` does not see through `mapHom`; the
    -- pointwise statement is given explicitly (it holds by `rfl` on the underlying function).
    have key : ∀ x, ‖(LocallyConstant.mapHom (NormedWithAut.t.hom : V ⟶ V) f) x‖ =
        (r : ℝ) * ‖f x‖ := fun x => NormedWithAut.norm_t (f x)
    refine' Eq.trans _ (Real.sSup_hMul r _ hr.out)
    congr 1
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨‖f x‖, ⟨x, rfl⟩, (key x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, key x⟩

instance normedWithAutLCC (V : SemiNormedGroupCat) (S : Profiniteᵒᵖ) (r : ℝ≥0) [NormedWithAut r V]
    [hr : Fact (0 < r)] : NormedWithAut r ((lCC.obj V).obj S) :=
  show NormedWithAut r (completion.obj <| (locallyConstant.obj V).obj S) by infer_instance

end SemiNormedGroupCat

-- Porting note: the Lean 3 `#lint` command is omitted; its Lean 4 output is not part of the port.

