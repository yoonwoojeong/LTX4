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

open UniformSpace _Root_.Opposite _Root_.CategoryTheory Completion

instance normedWithAutCompletion (V : SemiNormedGroupCat.{u}) (r : ℝ≥0) [NormedWithAut r V] :
    NormedWithAut r (completion.obj V)
    where
  t := completion.mapIso NormedWithAut.t
  norm_t := by
    rw [← Function.funext_iff]
    refine' AbstractCompletion.funext Completion.cPkg _ _ _
    · apply continuous_norm.comp _; exact Completion.continuous_map
    · exact (continuous_const.mul continuous_norm : _)
    intro v
    calc
      _ = _ := congr_arg norm (Completion.map_coe _ _)
      _ = _ := _
    · exact NormedAddGroupHom.uniformContinuous _
    · erw [Completion.norm_coe, NormedWithAut.norm_t, Completion.norm_coe]

@[simp]
theorem completion_t_inv_eq (V : SemiNormedGroupCat.{u}) (r : ℝ≥0) [NormedWithAut r V] :
    (NormedWithAut.t.hom : completion.obj V ⟶ _) = Completion.map NormedWithAut.t.hom :=
  rfl

theorem t_hom_incl {V : SemiNormedGroupCat} {r : ℝ≥0} [NormedWithAut r V] :
    (incl : V ⟶ _) ≫ NormedWithAut.t.hom = NormedWithAut.t.hom ≫ incl :=
  by
  ext x
  simp only [incl_apply, CategoryTheory.comp_apply, Completion_T_inv_eq]
  change Completion.map normed_with_aut.T.hom _ = _
  rw [Completion.map_coe]
  exact NormedAddGroupHom.uniformContinuous _

theorem t_hom_eq {V : SemiNormedGroupCat} {r : ℝ≥0} [NormedWithAut r V] :
    NormedWithAut.t.hom = completion.lift ((NormedWithAut.t.hom : V ⟶ V) ≫ incl) :=
  lift_unique _ _ t_hom_incl

/-- `LCC` (Locally Constant Completion) is the bifunctor
that sends a seminormed group `V` and a profinite space `S` to `V-hat(S)`.
Here `V-hat(S)` is the completion (for the sup norm) of the locally constant functions `S → V`. -/
def lCC : SemiNormedGroupCat ⥤ Profiniteᵒᵖ ⥤ SemiNormedGroupCat :=
  curry.obj (uncurry.obj locallyConstant ⋙ completion)

theorem lCC_obj_map' (V : SemiNormedGroupCat) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) :
    (lCC.obj V).map f = Completion.map ((locallyConstant.obj V).map f) :=
  by
  delta LCC
  simp only [curry_obj_obj_map, LocallyConstant_obj_map, Functor.comp_map, uncurry_obj_map,
    NatTrans.id_app, Functor.map_comp, Functor.map_id, CategoryTheory.Functor.map_id]
  erw [← Functor.map_comp, Category.id_comp]

theorem lCC_obj_map (V : SemiNormedGroupCat) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X)
    (v : (lCC.obj V).obj Y) :
    (lCC.obj V).map f v = Completion.map (LocallyConstant.comap f.unop) v := by rw [LCC_obj_map'];
  rfl

theorem lCC_obj_map_normNoninc (V : SemiNormedGroupCat) {X Y : Profiniteᵒᵖ} (f : Y ⟶ X) :
    ((lCC.obj V).map f).NormNoninc := by
  rw [LCC_obj_map']
  exact completion.map_normNoninc <| LocallyConstant_obj_map_norm_noninc _ _ _ _

variable (S : Type _) [TopologicalSpace S] [CompactSpace S]

@[simps]
instance normedWithAutLocallyConstant (V : SemiNormedGroupCat) (S : Profiniteᵒᵖ) (r : ℝ≥0)
    [NormedWithAut r V] [hr : Fact (0 < r)] : NormedWithAut r ((locallyConstant.obj V).obj S)
    where
  t := (locallyConstant.mapIso NormedWithAut.t).app S
  norm_t := by
    rw [← op_unop S]
    rintro (f : LocallyConstant (unop S : Profinite) V)
    show Sup _ = ↑r * Sup _
    dsimp
    simp only [NormedWithAut.norm_t]
    convert Real.sSup_hMul r _ hr.out
    ext
    simp only [exists_prop, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]

instance normedWithAutLCC (V : SemiNormedGroupCat) (S : Profiniteᵒᵖ) (r : ℝ≥0) [NormedWithAut r V]
    [hr : Fact (0 < r)] : NormedWithAut r ((lCC.obj V).obj S) :=
  show NormedWithAut r (completion.obj <| (locallyConstant.obj V).obj S) by infer_instance

end SemiNormedGroupCat

#lint

