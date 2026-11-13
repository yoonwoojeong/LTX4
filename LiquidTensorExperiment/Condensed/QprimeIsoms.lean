import LiquidTensorExperiment.BreenDeligne.Eval2
import LiquidTensorExperiment.Condensed.Tensor
import LiquidTensorExperiment.Condensed.EvaluationHomology
import LiquidTensorExperiment.Condensed.SheafificationHomology
import LiquidTensorExperiment.ForMathlib.AddCommGroup
import LiquidTensorExperiment.ForMathlib.MapToSheafIsIso
import LiquidTensorExperiment.Condensed.IsIsoIffExtrdisc
import LiquidTensorExperiment.Condensed.Ab5
import LiquidTensorExperiment.Condensed.Ab4
import LiquidTensorExperiment.ForMathlib.Endomorphisms.Ab4
import LiquidTensorExperiment.ForMathlib.HomologyExact
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup2
import LiquidTensorExperiment.ForMathlib.EmbedPreservesColimits

#align_import condensed.Qprime_isoms

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits BreenDeligne Opposite

open BoundedHomotopyCategory

abbrev freeCond' :=
  condensedAbToCondensedSet ⋙ condensedSetToCondensedAb

namespace Condensed

variable (BD : Package)

abbrev freeFunc : (Profiniteᵒᵖ ⥤ Ab) ⥤ Profiniteᵒᵖ ⥤ Ab :=
  (whiskeringRight _ _ _).obj (forget _ ⋙ AddCommGroupCat.free)

namespace EvalFreeCond'Iso

def componentZero (M : Condensed.{u} Ab.{u + 1}) :
    ((BD.eval' freeCond').obj M).pt (Int.ofNat 0) ≅
      ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).pt
        (Int.ofNat 0) :=
  presheafToCondensedAb.mapIso
    (by
      refine' functor.associator _ _ _ ≪≫ _
      refine' iso_whisker_right _ _
      refine' Condensed_Ab_to_presheaf.map_biproduct _)

def componentPos (M : Condensed.{u} Ab.{u + 1}) (i : ℕ) :
    ((BD.eval' freeCond').obj M).pt (Int.ofNat (i + 1)) ≅
      ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).pt
        (Int.ofNat (i + 1)) :=
  IsZero.iso (isZero_zero _) (Functor.map_isZero _ <| isZero_zero _)

def componentNeg (M : Condensed.{u} Ab.{u + 1}) (i : ℕ) :
    ((BD.eval' freeCond').obj M).pt -[i+1] ≅
      ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).pt
        -[i+1] :=
  presheafToCondensedAb.mapIso
    (by
      refine' functor.associator _ _ _ ≪≫ _
      refine' iso_whisker_right _ _
      refine' Condensed_Ab_to_presheaf.map_biproduct _)

end EvalFreeCond'Iso

open scoped BigOperators

open CategoryTheory.Preadditive

theorem eval_freeCond'_iso_component_aux₀ (M : Condensed.{u} Ab.{u + 1}) :
    (EvalFreeCond'Iso.componentNeg BD M 0).hom ≫
        ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).d
          -[0+1] (Int.ofNat 0) =
      ((BD.eval' freeCond').obj M).d -[0+1] (Int.ofNat 0) ≫
        (EvalFreeCond'Iso.componentZero BD M).hom :=
  by
  dsimp [eval_freeCond'_iso.component_neg, eval_freeCond'_iso.component_zero, package.eval',
    HomologicalComplex.embed, HomologicalComplex.Embed.obj]
  erw [HomologicalComplex.Embed.d_some_some]
  erw [HomologicalComplex.Embed.d_some_some]
  dsimp [data.eval_functor', universal_map.eval_Pow]
  simp_rw [FreeAbelianGroup.lift_eq_sum]
  simp only [nat_trans.app_sum, nat_trans.app_zsmul]
  --dsimp,
  rw [functor.map_sum, sum_comp, comp_sum]
  refine' Finset.sum_congr rfl _; rintro x -
  rw [functor.map_zsmul, zsmul_comp, comp_zsmul]
  refine' congr_arg₂ _ rfl _
  dsimp
  rw [← presheaf_to_Condensed_Ab.map_comp]
  erw [← presheaf_to_Condensed_Ab.map_comp]
  congr 1
  ext t : 2; dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator]
  simp only [category.id_comp, category.comp_id]
  simp only [← functor.map_comp]
  congr 1; simp only [← nat_trans.comp_app]; congr 1
  apply biproduct.hom_ext; intro j
  simp only [category.assoc, biproduct.matrix_π, biproduct.lift_π]
  dsimp only [functor.map_bicone]
  rw [biproduct.lift_desc]
  erw [← Condensed_Ab_to_presheaf.map_comp, biproduct.matrix_π]
  simp_rw [comp_zsmul, category.comp_id, ← functor.map_zsmul, ← functor.map_sum]
  congr 1
  apply biproduct.hom_ext'; intro k
  rw [biproduct.ι_desc, comp_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  · simp
  · rintro b - hb; dsimp; rw [comp_zsmul]; rw [biproduct.ι_π]
    rw [dif_neg hb.symm, zsmul_zero]

theorem eval_freeCond'_iso_component_aux_i (M : Condensed.{u} Ab.{u + 1}) (i : ℕ) :
    (EvalFreeCond'Iso.componentNeg BD M (i + 1)).hom ≫
        ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).d
          -[i + 1+1] -[i+1] =
      ((BD.eval' freeCond').obj M).d -[i + 1+1] -[i+1] ≫
        (EvalFreeCond'Iso.componentNeg BD M i).hom :=
  by
  dsimp [eval_freeCond'_iso.component_neg, eval_freeCond'_iso.component_zero, package.eval',
    HomologicalComplex.embed, HomologicalComplex.Embed.obj]
  erw [HomologicalComplex.Embed.d_some_some]
  erw [HomologicalComplex.Embed.d_some_some]
  dsimp [data.eval_functor', universal_map.eval_Pow]
  simp_rw [FreeAbelianGroup.lift_eq_sum]
  simp only [nat_trans.app_sum, nat_trans.app_zsmul]
  --dsimp,
  rw [functor.map_sum, sum_comp, comp_sum]
  refine' Finset.sum_congr rfl _; rintro x -
  rw [functor.map_zsmul, zsmul_comp, comp_zsmul]
  refine' congr_arg₂ _ rfl _
  dsimp
  rw [← presheaf_to_Condensed_Ab.map_comp]
  erw [← presheaf_to_Condensed_Ab.map_comp]
  congr 1
  ext t : 2; dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator]
  simp only [category.id_comp, category.comp_id]
  simp only [← functor.map_comp]
  congr 1; simp only [← nat_trans.comp_app]; congr 1
  apply biproduct.hom_ext; intro j
  simp only [category.assoc, biproduct.matrix_π, biproduct.lift_π]
  dsimp only [functor.map_bicone]
  rw [biproduct.lift_desc]
  erw [← Condensed_Ab_to_presheaf.map_comp, biproduct.matrix_π]
  simp_rw [comp_zsmul, category.comp_id, ← functor.map_zsmul, ← functor.map_sum]
  congr 1
  apply biproduct.hom_ext'; intro k
  rw [biproduct.ι_desc, comp_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
  · simp
  · rintro b - hb; dsimp; rw [comp_zsmul]; rw [biproduct.ι_π]
    rw [dif_neg hb.symm, zsmul_zero]

def evalFreeCond'IsoComponent (M : Condensed.{u} Ab.{u + 1}) :
    (BD.eval' freeCond').obj M ≅
      (presheafToCondensedAb.mapHomologicalComplex _).obj
        ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      match i with
      | Int.ofNat 0 => EvalFreeCond'Iso.componentZero _ _
      | Int.ofNat (i + 1) => EvalFreeCond'Iso.componentPos _ _ _
      | -[i+1] => EvalFreeCond'Iso.componentNeg _ _ _)
    (by
      rintro ((_ | i) | (_ | i)) ((_ | j) | (_ | j)) ⟨rfl⟩
      · apply is_zero.eq_of_tgt
        apply functor.map_is_zero
        apply is_zero_zero
      · apply is_zero.eq_of_tgt
        apply functor.map_is_zero
        apply is_zero_zero
      · apply eval_freeCond'_iso_component_aux₀
      · apply eval_freeCond'_iso_component_aux_i
      · apply eval_freeCond'_iso_component_aux_i)

theorem evalFreeCond'IsoComponent_hom_zero (M : Condensed.{u} Ab.{u + 1}) :
    (evalFreeCond'IsoComponent BD M).hom.f 0 =
      by
      refine' presheaf_to_Condensed_Ab.map _
      refine' _ ≫ (functor.associator _ _ _).hom
      refine' whisker_right _ _
      refine' whisker_right _ _
      refine' (Condensed_Ab_to_presheaf.map_biproduct _).hom :=
  rfl

theorem evalFreeCond'IsoComponent_hom_neg (M : Condensed.{u} Ab.{u + 1}) (i : ℕ) :
    (evalFreeCond'IsoComponent BD M).hom.f -[i+1] =
      by
      refine' presheaf_to_Condensed_Ab.map _
      refine' _ ≫ (functor.associator _ _ _).hom
      refine' whisker_right _ _
      refine' whisker_right _ _
      refine' (Condensed_Ab_to_presheaf.map_biproduct _).hom :=
  rfl

namespace EvalFreeAbIso

def componentZero (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) :
    ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
            ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).pt
        (Int.ofNat 0) ≅
      ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj (M.val.obj (op S.val))).pt
        (Int.ofNat 0) :=
  by
  refine' AddCommGroup.free.map_iso _
  refine' (CategoryTheory.forget _).mapIso _
  refine' ((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).mapBiproduct _

def componentPos (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) (i : ℕ) :
    ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
            ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).pt
        (Int.ofNat (i + 1)) ≅
      ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj (M.val.obj (op S.val))).pt
        (Int.ofNat (i + 1)) :=
  IsZero.iso (Functor.map_isZero _ <| isZero_zero _) (isZero_zero _)

def componentNeg (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) (i : ℕ) :
    ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
            ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).pt
        -[i+1] ≅
      ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj (M.val.obj (op S.val))).pt
        -[i+1] :=
  by
  refine' AddCommGroup.free.map_iso _
  refine' (CategoryTheory.forget _).mapIso _
  refine' ((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).mapBiproduct _

end EvalFreeAbIso

attribute [-simp] forget_map_eq_coe

theorem eval_freeAb_iso_component_aux₀ (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) :
    (EvalFreeAbIso.componentNeg BD M S 0).hom ≫
        ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj (M.val.obj (op S.val))).d
          -[0+1] (Int.ofNat 0) =
      ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                      (op S.val)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
              ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).d
          -[0+1] (Int.ofNat 0) ≫
        (EvalFreeAbIso.componentZero BD M S).hom :=
  by
  dsimp only [eval_freeAb_iso.component_neg, eval_freeAb_iso.component_zero, functor.map_iso,
    package.eval', data.eval_functor', functor.map_homological_complex, CategoryTheory.evaluation,
    functor.comp_obj, HomologicalComplex.embed, HomologicalComplex.Embed.obj]
  erw [HomologicalComplex.Embed.d_some_some]
  erw [HomologicalComplex.Embed.d_some_some]
  dsimp only [data.eval_functor, data.eval_functor', functor.comp_obj, functor.flip,
    HomologicalComplex.functorEval, HomologicalComplex.FunctorEval.obj, CategoryTheory.evaluation,
    functor.map_homological_complex, universal_map.eval_Pow_functor, universal_map.eval_Pow,
    functor.map_biproduct]
  simp only [FreeAbelianGroup.lift_eq_sum, sum_comp, comp_sum, nat_trans.app_sum]
  apply Finset.sum_congr rfl; rintro x -
  simp only [nat_trans.app_zsmul]
  dsimp [functor.map_bicone]
  simp only [zsmul_comp, comp_zsmul, ← functor.map_comp]; congr 3
  apply biproduct.hom_ext; intro j
  simp only [category.assoc, biproduct.lift_π, biproduct.matrix_π, biproduct.lift_desc]
  erw [biproduct.lift_π]
  rw [← nat_trans.comp_app, biproduct.matrix_π]
  simp_rw [← nat_trans.id_app, ← nat_trans.app_zsmul, ← nat_trans.comp_app, ← nat_trans.app_sum]
  congr 1
  apply biproduct.hom_ext'; intro k; simp only [comp_sum, biproduct.ι_desc]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _), biproduct.ι_π_assoc, dif_pos rfl]
  · simpa
  · rintro b - hb; rw [biproduct.ι_π_assoc, dif_neg hb.symm, zero_comp]

theorem eval_freeAb_iso_component_aux (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) (i : ℕ) :
    (EvalFreeAbIso.componentNeg BD M S (i + 1)).hom ≫
        ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj (M.val.obj (op S.val))).d
          -[i + 1+1] -[i+1] =
      ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                      (op S.val)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
              ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))).d
          -[i + 1+1] -[i+1] ≫
        (EvalFreeAbIso.componentNeg BD M S i).hom :=
  by
  dsimp only [eval_freeAb_iso.component_neg, eval_freeAb_iso.component_zero, functor.map_iso,
    package.eval', data.eval_functor', functor.map_homological_complex, CategoryTheory.evaluation,
    functor.comp_obj, HomologicalComplex.embed, HomologicalComplex.Embed.obj]
  erw [HomologicalComplex.Embed.d_some_some]
  erw [HomologicalComplex.Embed.d_some_some]
  dsimp only [data.eval_functor, data.eval_functor', functor.comp_obj, functor.flip,
    HomologicalComplex.functorEval, HomologicalComplex.FunctorEval.obj, CategoryTheory.evaluation,
    functor.map_homological_complex, universal_map.eval_Pow_functor, universal_map.eval_Pow,
    functor.map_biproduct]
  simp only [FreeAbelianGroup.lift_eq_sum, sum_comp, comp_sum, nat_trans.app_sum]
  apply Finset.sum_congr rfl; rintro x -
  simp only [nat_trans.app_zsmul]
  dsimp [functor.map_bicone]
  simp only [zsmul_comp, comp_zsmul, ← functor.map_comp]; congr 3
  apply biproduct.hom_ext; intro j
  simp only [category.assoc, biproduct.lift_π, biproduct.matrix_π, biproduct.lift_desc]
  erw [biproduct.lift_π]
  rw [← nat_trans.comp_app, biproduct.matrix_π]
  simp_rw [← nat_trans.id_app, ← nat_trans.app_zsmul, ← nat_trans.comp_app, ← nat_trans.app_sum]
  congr 1
  apply biproduct.hom_ext'; intro k; simp only [comp_sum, biproduct.ι_desc]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _), biproduct.ι_π_assoc, dif_pos rfl]
  · simpa
  · rintro b - hb; rw [biproduct.ι_π_assoc, dif_neg hb.symm, zero_comp]

def evalFreeAbIsoComponent (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) :
    (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
        ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) ≅
      (BD.eval' <| CategoryTheory.forget _ ⋙ AddCommGroupCat.free).obj (M.val.obj (op S.val)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      match i with
      | Int.ofNat 0 => EvalFreeAbIso.componentZero _ _ _
      | Int.ofNat (i + 1) => EvalFreeAbIso.componentPos _ _ _ _
      | -[i+1] => EvalFreeAbIso.componentNeg _ _ _ _)
    (by
      rintro ((_ | i) | (_ | i)) ((_ | j) | (_ | j)) ⟨rfl⟩
      · apply is_zero.eq_of_tgt
        apply is_zero_zero
      · apply is_zero.eq_of_tgt
        apply is_zero_zero
      · apply eval_freeAb_iso_component_aux₀
      · apply eval_freeAb_iso_component_aux
      · apply eval_freeAb_iso_component_aux)

@[simp]
theorem evalFreeAbIsoComponent_zero (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) :
    (evalFreeAbIsoComponent BD M S).hom.f 0 = (EvalFreeAbIso.componentZero BD M S).hom :=
  rfl

@[simp]
theorem evalFreeAbIsoComponent_neg (M : Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) (i : ℕ) :
    (evalFreeAbIsoComponent BD M S).hom.f -[i+1] = (EvalFreeAbIso.componentNeg BD M S i).hom :=
  rfl

theorem eval_freeCond'_iso_aux_zero (X Y : Condensed Ab) (f : X ⟶ Y) :
    ((BD.eval' freeCond').map f ≫ (evalFreeCond'IsoComponent BD Y).hom).f (Int.ofNat 0) =
      ((evalFreeCond'IsoComponent BD X).hom ≫
            (condensedAbToPresheaf ⋙
                  BD.eval' freeFunc ⋙
                    presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).map
              f).f
        (Int.ofNat 0) :=
  by
  dsimp only [HomologicalComplex.Hom.isoOfComponents, HomologicalComplex.comp_f, package.eval',
    data.eval_functor', data.eval_functor, functor.comp_map, Int.ofNat_zero,
    HomologicalComplex.embed_nat_obj_down_up_zero_f, HomologicalComplex.comp_f,
    functor.map_homological_complex_map_f, functor.comp_obj, functor.flip,
    HomologicalComplex.functorEval, universal_map.eval_Pow_functor, functor.map_homological_complex]
  rw [eval_freeCond'_iso_component_hom_zero]
  rw [eval_freeCond'_iso_component_hom_zero]
  dsimp
  rw [← presheaf_to_Condensed_Ab.map_comp]
  erw [← presheaf_to_Condensed_Ab.map_comp]
  congr 1
  -- we got rid of the sheafification :)
  ext t : 2
  dsimp
  simp only [category.id_comp, category.comp_id, ← functor.map_comp]
  congr 2
  simp_rw [← nat_trans.comp_app]; congr 1
  dsimp [functor.map_bicone]
  apply biproduct.hom_ext; intro j
  simp only [category.assoc, biproduct.map_π, biproduct.lift_π_assoc, biproduct.lift_π]
  erw [← Condensed_Ab_to_presheaf.map_comp, ← Condensed_Ab_to_presheaf.map_comp, biproduct.map_π]

theorem evalFreeAbIsoComponent_naturality (M : Condensed.{u} Ab.{u + 1}) (S T : ExtrDisc.{u})
    (f : S ⟶ T) :
    (evalFreeAbIsoComponent BD M T).hom ≫
        (BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map
          (M.val.map (extrDiscToProfinite.map f).op) =
      (NatTrans.mapHomologicalComplex ((CategoryTheory.evaluation Profiniteᵒᵖ Ab).map f.val.op)
              (ComplexShape.up ℤ)).app
          ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) ≫
        (evalFreeAbIsoComponent BD M S).hom :=
  by
  ext ((_ | i) | i) : 2
  · change
      AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
          AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) =
        AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
          AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _)
    simp only [← functor.map_comp]; congr 2
    apply biproduct.hom_ext; rintro ⟨j⟩
    dsimp [functor.map_bicone]
    simp only [category.assoc]
    erw [biproduct.lift_π]
    erw [biproduct.map_π]
    erw [biproduct.lift_π_assoc]
    simp only [nat_trans.naturality]
    rfl
  · apply is_zero.eq_of_tgt
    apply is_zero_zero
  · change
      AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
          AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) =
        AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
          AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _)
    simp only [← functor.map_comp]; congr 2
    apply biproduct.hom_ext; rintro ⟨j⟩
    dsimp [functor.map_bicone]
    simp only [category.assoc]
    erw [biproduct.lift_π]
    erw [biproduct.map_π]
    erw [biproduct.lift_π_assoc]
    simp only [nat_trans.naturality]
    rfl

theorem eval_freeCond'_iso_aux_neg (X Y : Condensed Ab) (f : X ⟶ Y) (i : ℕ) :
    ((BD.eval' freeCond').map f ≫ (evalFreeCond'IsoComponent BD Y).hom).f -[i+1] =
      ((evalFreeCond'IsoComponent BD X).hom ≫
            (condensedAbToPresheaf ⋙
                  BD.eval' freeFunc ⋙
                    presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).map
              f).f
        -[i+1] :=
  by
  dsimp only [HomologicalComplex.Hom.isoOfComponents, HomologicalComplex.comp_f, package.eval',
    data.eval_functor', data.eval_functor, functor.comp_map, Int.ofNat_zero,
    HomologicalComplex.embed_nat_obj_down_up_zero_f, HomologicalComplex.comp_f,
    functor.map_homological_complex_map_f, functor.comp_obj, functor.flip,
    HomologicalComplex.functorEval, universal_map.eval_Pow_functor, functor.map_homological_complex]
  rw [eval_freeCond'_iso_component_hom_neg]
  rw [eval_freeCond'_iso_component_hom_neg]
  dsimp
  rw [← presheaf_to_Condensed_Ab.map_comp]
  erw [← presheaf_to_Condensed_Ab.map_comp]
  congr 1
  -- we got rid of the sheafification :)
  ext t : 2
  dsimp
  simp only [category.id_comp, category.comp_id, ← functor.map_comp]
  congr 2
  simp_rw [← nat_trans.comp_app]; congr 1
  dsimp [functor.map_bicone]
  apply biproduct.hom_ext; intro j
  simp only [category.assoc, biproduct.map_π, biproduct.lift_π_assoc, biproduct.lift_π]
  erw [← Condensed_Ab_to_presheaf.map_comp, ← Condensed_Ab_to_presheaf.map_comp, biproduct.map_π]

def evalFreeCond'Iso :
    BD.eval' freeCond' ≅
      condensedAbToPresheaf ⋙ BD.eval' freeFunc ⋙ presheafToCondensedAb.mapHomologicalComplex _ :=
  NatIso.ofComponents (fun M => evalFreeCond'IsoComponent _ _)
    (by
      intro X Y f
      ext ((_ | i) | i) : 2
      · apply eval_freeCond'_iso_aux_zero
      · apply is_zero.eq_of_src; apply is_zero_zero
      · apply eval_freeCond'_iso_aux_neg)

def evalFreeAbIso (S : ExtrDisc.{u}) :
    condensedAbToPresheaf ⋙
        BD.eval' freeFunc ⋙
          ((CategoryTheory.evaluation _ _).obj (op S.val)).mapHomologicalComplex _ ≅
      evaluation _ S.val ⋙ BD.eval' (CategoryTheory.forget _ ⋙ AddCommGroupCat.free) :=
  NatIso.ofComponents (fun M => evalFreeAbIsoComponent _ _ _)
    (by
      intro X Y f
      ext ((_ | i) | i) : 2
      · change
          AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
              AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) =
            AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
              AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _)
        simp only [← functor.map_comp]; congr 2
        apply biproduct.hom_ext; intro j
        dsimp [functor.map_bicone]
        simp only [category.assoc, biproduct.map_π, biproduct.lift_π]
        erw [biproduct.lift_π_assoc]
        erw [biproduct.lift_π]
        simp_rw [← nat_trans.comp_app, biproduct.map_π]
        rfl
      · apply is_zero.eq_of_tgt; apply is_zero_zero
      · change
          AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
              AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) =
            AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _) ≫
              AddCommGroup.free.map ((CategoryTheory.forget Ab.{u + 1}).map _)
        simp only [← functor.map_comp]; congr 2
        apply biproduct.hom_ext; intro j
        dsimp [functor.map_bicone]
        simp only [category.assoc, biproduct.map_π, biproduct.lift_π]
        erw [biproduct.lift_π_assoc]
        erw [biproduct.lift_π]
        simp_rw [← nat_trans.comp_app, biproduct.map_π]
        rfl)

-- Move this.
def point {A : Type u} (a : A) : PUnit.{u + 1} ⟶ A := fun _ => a

def tensorToUnsheafifiedHomologyComponentApplied (M : Condensed.{u} Ab.{u + 1}) (i : ℤ)
    (S : ExtrDisc.{u}) (m : M.val.obj (op S.val)) :
    ((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                (AddCommGroupCat.free.obj PUnit)).val.as.homology'
        i ⟶
      (HomologicalComplex.homology' ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) i).obj
        (op S.val) :=
  (HomotopyCategory.homology'Functor _ _ _).map
      ((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map
        ((AddCommGroupCat.adj.homEquiv _ _).symm (point m))) ≫
    (homology'Functor _ _ _).map (evalFreeAbIsoComponent _ _ _).inv ≫
      (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op S.val)).homology'FunctorIso _
              _).inv.app
        _

open CategoryTheory.Preadditive

def tensorToUnsheafifiedHomologyComponent (M : Condensed.{u} Ab.{u + 1}) (i : ℤ)
    (S : ExtrDisc.{u}) :
    M.val.obj (op S.val) ⟶
      AddCommGroupCat.of
        (((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                    (AddCommGroupCat.free.obj PUnit)).val.as.homology'
            i ⟶
          (HomologicalComplex.homology' ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M))
                i).obj
            (op S.val)) :=
  AddMonoidHom.mk' (fun m => tensorToUnsheafifiedHomologyComponentApplied _ _ _ _ m)
    (by
      intro x y; rcases i with ((_ | i) | i)
      · erw [← add_comp, ← functor.map_add, ← functor.map_add]; apply congr_arg₂ _ _ rfl; congr 2
        dsimp only [AddCommGroupCat.adj, adjunction.mk_of_hom_equiv_hom_equiv]
        ext ⟨⟩; simp only [Equiv.symm_symm, AddMonoidHom.add_apply, FreeAbelianGroup.lift.of]
        rfl
      · apply is_zero.eq_of_src
        apply is_zero.homology_is_zero; apply is_zero_zero
      · erw [← add_comp, ← functor.map_add, ← functor.map_add]; apply congr_arg₂ _ _ rfl; congr 2
        dsimp only [AddCommGroupCat.adj, adjunction.mk_of_hom_equiv_hom_equiv]
        ext ⟨⟩; simp only [Equiv.symm_symm, AddMonoidHom.add_apply, FreeAbelianGroup.lift.of]
        rfl)

theorem tensor_to_unsheafified_homology'_natural (M : Condensed.{u} Ab.{u + 1}) (i : ℤ)
    (S T : ExtrDiscᵒᵖ) (f : S ⟶ T)
    (x :
      ((extrSheafExtrSheafProdEquiv Ab).Functor.obj
              ((condensedExtrSheafEquiv Ab).inverse.obj M)).val.obj
        S) :
    (tensorToUnsheafifiedHomologyComponentApplied BD M i (unop T)) ((M.val.map f.unop.val.op) x) =
      (tensorToUnsheafifiedHomologyComponentApplied BD M i (unop S)) x ≫
        (HomologicalComplex.homology' ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) i).map
          f.unop.val.op :=
  by
  dsimp only [tensor_to_unsheafified_homology_component_applied]
  rw [← nat_iso.app_inv, ← category.assoc, iso.comp_inv_eq]
  simp only [category.assoc]
  have :=
    functor.naturality_homology_functor_iso
      ((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).map (ExtrDisc_to_Profinite.op.map f))
      (ComplexShape.up ℤ) i
  apply_fun fun e => e.app ((BD.eval' freeFunc).obj (Condensed_Ab_to_presheaf.obj M)) at this 
  dsimp [-homology'Functor_map] at this ; simp only [category.id_comp, category.comp_id] at this 
  erw [this]; rw [← nat_iso.app_inv, ← nat_iso.app_hom, iso.inv_hom_id_assoc]
  clear this
  rw [← functor.map_iso_inv, ← category.assoc, iso.comp_inv_eq, category.assoc, category.assoc]
  dsimp [-homology'Functor_map]; simp only [← functor.map_comp]
  rw [← eval_freeAb_iso_component_naturality, iso.inv_hom_id_assoc]
  have :
    (AddCommGroup.adj.hom_equiv PUnit (M.val.obj (op (unop T).val))).symm
        (point ((M.val.map f.unop.val.op) x)) =
      (AddCommGroup.adj.hom_equiv PUnit (M.val.obj (op (unop S).val))).symm (point x) ≫
        M.val.map (ExtrDisc_to_Profinite.map f.unop).op :=
    by
    ext ⟨⟩
    dsimp only [AddCommGroupCat.adj, adjunction.mk_of_hom_equiv_hom_equiv, Equiv.symm,
      Equiv.toFun_as_coe]
    simp only [comp_apply]
    erw [FreeAbelianGroup.lift.of]
    erw [FreeAbelianGroup.lift.of]
    rfl
  rw [this, functor.map_comp]
  erw [functor.map_comp]
  rfl

def tensorToUnsheafifiedHomology (M : Condensed.{u} Ab.{u + 1}) (i : ℤ) :
    (((condensedExtrSheafEquiv Ab).inverse.obj M).tensor
          (((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                    (AddCommGroupCat.free.obj PUnit)).val.as.homology'
            i)).val ⟶
      extrDiscToProfinite.op ⋙
        HomologicalComplex.homology' ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) i
    where
  app S := AddCommGroupCat.tensorUncurry <| tensorToUnsheafifiedHomologyComponent _ _ _ _
  naturality' S T f := by
    apply AddCommGroupCat.tensor_ext; intro x y
    dsimp only [ExtrSheaf.tensor, ExtrSheafProd.tensor, extrSheafExtrSheafProdEquiv,
      ExtrSheafProd.tensorPresheaf_map, AddCommGroupCat.mapTensor, AddCommGroupCat.tensorUncurry]
    erw [comp_apply, comp_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
      TensorProduct.lift.tmul]
    dsimp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.comp_apply, AddMonoidHom.coe_mk,
      functor.comp_map, condensedExtrSheafEquiv_inverse_val, extrDiscToProfinite_map,
      functor.op_map, tensor_to_unsheafified_homology_component, AddMonoidHom.mk'_apply]
    erw [id_apply, ← comp_apply]; congr 1
    apply tensor_to_unsheafified_homology_natural

def plainEvalComparisonComponent (i : ℤ) (A : AddCommGroupCat.{u + 1}) :
    A ⟶
      AddCommGroupCat.of
        ((HomotopyCategory.homology'Functor _ _ i).obj
            ((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                (AddCommGroupCat.free.obj PUnit)).val ⟶
          (HomotopyCategory.homology'Functor _ _ i).obj
            ((BD.eval (CategoryTheory.forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj A).val) :=
  AddMonoidHom.mk'
    (fun a =>
      (HomotopyCategory.homology'Functor _ _ _).map <|
        (BD.eval _).map <| (AddCommGroupCat.adj.homEquiv _ _).symm (point a))
    (by
      intro x y; rw [← functor.map_add, ← functor.map_add]; congr 2
      dsimp only [AddCommGroupCat.adj, adjunction.mk_of_hom_equiv_hom_equiv]
      ext ⟨⟩; simp only [Equiv.symm_symm, AddMonoidHom.add_apply, FreeAbelianGroup.lift.of]
      rfl)

theorem plain_eval_comparison_natural (i : ℤ) (A B : AddCommGroupCat.{u + 1}) (f : A ⟶ B) (x) :
    (plainEvalComparisonComponent BD i B) (f x) =
      (plainEvalComparisonComponent BD i A) x ≫
        (HomotopyCategory.homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i).map
          ((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map f) :=
  by
  dsimp only [plain_eval_comparison_component, AddMonoidHom.mk'_apply, functor.comp_map]
  rw [← functor.map_comp]; congr 1
  erw [← (BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map_comp]; congr 1
  dsimp only [AddCommGroupCat.adj, adjunction.mk_of_hom_equiv_hom_equiv, Equiv.symm,
    Equiv.coe_fn_mk, Equiv.toFun_as_coe]
  ext ⟨⟩
  simp only [FreeAbelianGroup.lift.of, comp_apply]
  rfl

theorem plain_eval_comparison_natural' (i : ℤ) (A B : AddCommGroupCat.{u + 1}) (f : A ⟶ B) :
    (AddCommGroupCat.tensorFunctor.flip.obj
              (HomologicalComplex.homology'
                ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                  (AddCommGroupCat.free.obj PUnit))
                i)).map
          f ≫
        AddCommGroupCat.tensorUncurry (plainEvalComparisonComponent BD i B) =
      AddCommGroupCat.tensorUncurry (plainEvalComparisonComponent BD i A) ≫
        (BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free) ⋙
              homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i).map
          f :=
  by
  apply AddCommGroupCat.tensor_ext; intro x y
  rw [comp_apply, comp_apply]
  dsimp only [functor.flip_obj_map, AddCommGroupCat.tensorFunctor_map_app]
  delta AddCommGroupCat.tensorUncurry AddCommGroupCat.mapTensor
  dsimp only [LinearMap.toAddMonoidHom_coe]
  rw [TensorProduct.map_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  dsimp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.comp_apply, AddMonoidHom.coe_mk]
  rw [plain_eval_comparison_natural]
  rfl

def plainEvalComparison (i : ℤ) :
    AddCommGroupCat.tensorFunctor.flip.obj
        (((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
              (AddCommGroupCat.free.obj PUnit)).homology'
          i) ⟶
      BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free) ⋙ homology'Functor _ _ i
    where
  app A := AddCommGroupCat.tensorUncurry <| plainEvalComparisonComponent _ _ _
  naturality' A B f := by apply plain_eval_comparison_natural'

attribute [-simp] homology'Functor_map

theorem tensorToUnsheafifiedHomology_app_eq (M : Condensed.{u} Ab.{u + 1}) (i : ℤ)
    (S : ExtrDisc.{u}) :
    (tensorToUnsheafifiedHomology BD M i).app (op S) =
      (plainEvalComparison BD i).app (M.val.obj (op S.val)) ≫
        (homology'Functor _ _ _).map (evalFreeAbIsoComponent _ _ _).inv ≫
          (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                      (op S.val)).homology'FunctorIso
                  _ _).inv.app
            _ :=
  by
  rw [← nat_iso.app_inv, ← category.assoc, iso.eq_comp_inv, ← functor.map_iso_inv, iso.eq_comp_inv,
    category.assoc, functor.map_iso_hom, nat_iso.app_hom]
  apply_fun AddCommGroupCat.tensorCurryEquiv _ _ _
  swap; apply AddEquiv.injective
  dsimp [plain_eval_comparison, tensor_to_unsheafified_homology]
  rw [AddCommGroupCat.tensorCurry_uncurry]
  rw [AddCommGroupCat.tensorCurry_uncurry_comp]
  ext x y
  dsimp [plain_eval_comparison_component, tensor_to_unsheafified_homology_component]
  simp only [comp_apply]
  dsimp [preadditive_yoneda]
  simp only [comp_apply]
  dsimp [tensor_to_unsheafified_homology_component_applied]
  simp only [← comp_apply, category.assoc]
  dsimp only [← nat_iso.app_inv, ← nat_iso.app_hom]
  simp only [iso.inv_hom_id_assoc]
  congr 2
  simp only [← category.assoc]
  congr 1
  simp only [category.assoc, iso.inv_hom_id, category.comp_id, ← functor.map_iso_hom, ←
    functor.map_iso_inv]

def tensorToHomologyAux (M : Condensed.{u} Ab.{u + 1}) (i : ℤ) :
    ((condensedExtrSheafEquiv Ab).inverse.obj M).tensor
        (((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                  (AddCommGroupCat.free.obj PUnit)).val.as.homology'
          i) ⟶
      (presheafToSheaf ExtrDisc.proetaleTopology Ab).obj
        (extrDiscToProfinite.op ⋙
          HomologicalComplex.homology' ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) i) :=
  Sheaf.Hom.mk <| tensorToUnsheafifiedHomology _ _ _ ≫ GrothendieckTopology.toSheafify _ _

def tensorToHomology (M : Condensed.{u} Ab.{u + 1}) (i : ℤ) :
    (tensor M <|
        ((BD.eval <| CategoryTheory.forget AddCommGroupCat ⋙ AddCommGroupCat.free).obj
                  (AddCommGroupCat.free.obj PUnit)).val.as.homology'
          i) ⟶
      ((BD.eval freeCond').obj M).val.as.homology' i :=
  (condensedExtrSheafEquiv Ab).Functor.map
      (tensorToHomologyAux _ _ _ ≫ extrDiscSheafificationIso.hom.app _) ≫
    ((condensedExtrSheafEquiv _).counitIso.app _).hom ≫
      (homologyFunctorSheafificationIso _ _).hom.app _ ≫
        (homology'Functor _ _ _).map (evalFreeCond'IsoComponent _ _).inv

instance preservesFilteredColimitsTensorFlip (A) :
    PreservesFilteredColimits (AddCommGroupCat.tensorFunctor.flip.obj A) :=
  inferInstance

instance preservesFilteredColimitsTensorFlipEval' (i : ℤ) :
    PreservesFilteredColimits
      (AddCommGroupCat.tensorFunctor.flip.obj
        (HomologicalComplex.homology'
          ((BD.eval' (forget AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free)).obj
            (AddCommGroupCat.free.obj PUnit))
          i)) :=
  Condensed.preservesFilteredColimitsTensorFlip _

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

instance additive_tensor_flip (A : AddCommGroupCat.{u}) :
    Functor.Additive (AddCommGroupCat.tensorFunctor.flip.obj A)
    where map_add' X Y f g := by
    dsimp [AddCommGroupCat.mapTensor]; ext x
    dsimp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.add_apply]
    rw [← LinearMap.add_apply]
    congr 1; apply TensorProduct.ext'; intro x y
    apply TensorProduct.add_tmul

instance additive_tensor_flip_eval' (i : ℤ) :
    Functor.Additive
      (AddCommGroupCat.tensorFunctor.flip.obj
        (HomologicalComplex.homology'
          ((BD.eval' (forget AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free)).obj
            (AddCommGroupCat.free.obj PUnit))
          i)) :=
  Condensed.additive_tensor_flip _

-- move me
instance AddCommGroup.freePreservesLimits : PreservesColimits AddCommGroupCat.free :=
  AddCommGroupCat.adj.leftAdjointPreservesColimits

instance preservesFilteredColimitsEval'ForgetFree :
    PreservesFilteredColimits.{u + 1, u + 2, u + 2}
      (BD.eval'
        (forget.{u + 2, u + 1, u + 1} AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free.{u + 1})) :=
  by
  apply (config := { instances := false })
    Limits.compPreservesFilteredColimits.{u + 1, u + 2, _, u + 2}
  · apply (config := { instances := false }) data.eval_functor_preserves_filtered_colimits
    apply Limits.compPreservesFilteredColimits.{u + 1, u + 2, _, u + 2}
  · constructor
    intro J
    intro
    intro
    infer_instance

instance preservesFilteredColimitsHomology (i : ℤ) :
    PreservesFilteredColimits.{u + 1, u + 2, u + 2}
      (homology'Functor.{u + 1, u + 2, 0} AddCommGroupCat.{u + 1} (ComplexShape.up.{0} ℤ) i) :=
  ⟨fun J => by
    intro
    intro
    constructor
    intro K
    infer_instance⟩

instance preservesFilteredColimitsEval'ForgetFreeHomology (i : ℤ) :
    PreservesFilteredColimits
      (BD.eval' (forget AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free) ⋙
        homology'Functor AddCommGroupCat.{u + 1} (ComplexShape.up ℤ) i) :=
  Limits.compPreservesFilteredColimits.{u + 1, u + 2, _, u + 2}
    (BD.eval' (forget AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free))
    (homology'Functor AddCommGroupCat.{u + 1} (ComplexShape.up ℤ) i)

instance BoundedHomotopyCategory.forget_additive (𝓐 : Type _) [Category 𝓐] [Abelian 𝓐] :
    (BoundedHomotopyCategory.forget 𝓐).Additive where map_add' X Y f g := rfl

instance additive_eval'_forget_free (i : ℤ) :
    Functor.Additive
      (BD.eval' (forget AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free) ⋙
        homology'Functor AddCommGroupCat.{u + 1} (ComplexShape.up ℤ) i) :=
  by
  show
    functor.additive
      ((BD.eval (forget AddCommGroupCat.{u + 1} ⋙ AddCommGroupCat.free) ⋙
          BoundedHomotopyCategory.forget _) ⋙
        HomotopyCategory.homology'Functor _ _ i)
  exact
    functor.comp.additive
      (package.eval BD (forget AddCommGroupCat ⋙ AddCommGroupCat.free) ⋙ forget AddCommGroupCat)
      (HomotopyCategory.homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i)

theorem coeff_unit_smul (x : FreeAbelianGroup.{u} PUnit) :
    FreeAbelianGroup.coeff PUnit.unit x • FreeAbelianGroup.of.{u} PUnit.unit = x :=
  by
  refine' FreeAbelianGroup.induction_on'' x _ _ _ <;> clear x
  · simp only [map_zero, zero_smul]
  · rintro n hn ⟨⟩; simp only [map_zsmul, FreeAbelianGroup.coeff_of_self, smul_assoc, one_smul]
  · rintro x n hn ⟨⟩ hx IH1 IH2; simp only [map_add, add_smul, IH1, IH2]

theorem AddCommGroup.adj_homEquiv_pUnit (a) :
    (AddCommGroupCat.adj.{u + 1}.homEquiv PUnit.{u + 2}
            (AddCommGroupCat.free.{u + 1}.obj PUnit.{u + 2})).symm
        (point.{u + 1} a) =
      FreeAbelianGroup.coeff PUnit.unit a • 𝟙 _ :=
  by
  dsimp only [AddCommGroupCat.adj, adjunction.mk_of_hom_equiv_hom_equiv, Equiv.symm,
    Equiv.coe_fn_mk, Equiv.toFun_as_coe]
  ext ⟨⟩
  rw [FreeAbelianGroup.lift.of, AddMonoidHom.smul_apply, id_apply, coeff_star_smul]
  rfl

theorem HomologyFunctor.map_id_bo_ho_ca {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]
    (X : BoundedHomotopyCategory 𝓐) (i : ℤ) :
    (HomotopyCategory.homology'Functor _ (ComplexShape.up ℤ) i).map (𝟙 X : _) =
      𝟙 ((HomotopyCategory.homology'Functor _ (ComplexShape.up ℤ) i).obj X.val) :=
  CategoryTheory.Functor.map_id _ _

theorem plain_eval_comparison_isIso_aux (A : AddCommGroupCat) :
    IsIso
      (AddCommGroupCat.tensorUncurry <|
        (AddMonoidHom.mk' fun a : AddCommGroupCat.free.obj PUnit =>
            (FreeAbelianGroup.coeff PUnit.unit) a • 𝟙 A) <|
          by intros <;> simp only [map_add, add_smul]) :=
  by
  constructor
  refine' ⟨AddMonoidHom.mk' (fun a => FreeAbelianGroup.of PUnit.unit ⊗ₜ a) _, _, _⟩
  · intros; rw [TensorProduct.tmul_add]
  · apply AddCommGroupCat.tensor_ext; intro x y
    erw [comp_apply, id_apply]
    dsimp only [AddCommGroupCat.tensorUncurry, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe]
    rw [TensorProduct.lift.tmul]
    dsimp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.comp_apply, AddMonoidHom.coe_mk,
      AddMonoidHom.mk'_apply, AddMonoidHom.smul_apply]
    rw [← TensorProduct.smul_tmul, id_apply, coeff_star_smul]
  · ext a; rw [id_apply, comp_apply]
    dsimp only [AddCommGroupCat.tensorUncurry, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe]
    rw [TensorProduct.lift.tmul]
    dsimp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.comp_apply, AddMonoidHom.coe_mk,
      AddMonoidHom.mk'_apply, AddMonoidHom.smul_apply]
    rw [FreeAbelianGroup.coeff_of_self, one_smul]; rfl

instance (i : ℤ) :
    IsIso ((plainEvalComparison BD i).app (AddCommGroupCat.free.obj (PUnit : Type (u + 1)))) :=
  by
  dsimp only [plain_eval_comparison, plain_eval_comparison_component]
  simp only [AddCommGroup.adj_hom_equiv_punit, functor.map_smul, CategoryTheory.Functor.map_id,
    homology_functor.map_id_bo_ho_ca]
  apply plain_eval_comparison_is_iso_aux

theorem AddCommGroup.free_pUnit_isTensorUnit :
    (AddCommGroupCat.free.{u + 1}.obj PUnit.{u + 2}).IsTensorUnit :=
  by
  constructor; intro B; swap; exact FreeAbelianGroup.of PUnit.unit
  constructor; · intro f g h; ext ⟨⟩; exact h
  intro b; refine' ⟨FreeAbelianGroup.lift (point b), _⟩
  dsimp only; rw [FreeAbelianGroup.lift.of]; rfl

instance isIso_map_tensorToHomologyAux_comp (M : Condensed.{u} Ab.{u + 1}) (i : ℤ)
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (M.val.obj (op S.val))] :
    IsIso (tensorToHomologyAux BD M i) :=
  by
  suffices ∀ X : ExtrDisc, is_iso ((tensor_to_unsheafified_homology BD M i).app (op X))
    by
    skip
    apply
      Sheaf.is_iso_of_eval _ (tensor_to_homology_aux BD M i) (tensor_to_unsheafified_homology _ _ _)
        rfl
  intro S
  rw [tensor_to_unsheafified_homology_app_eq]
  suffices is_iso ((plain_eval_comparison BD i).app (M.val.obj (op S.val))) by skip;
    apply is_iso.comp_is_iso
  apply
    AddCommGroupCat.isIso_of_preserves_of_isTensorUnit.{u + 1, u + 2} _ _
      (plain_eval_comparison BD i) (AddCommGroup.free.obj PUnit)
  apply AddCommGroup.free_punit_is_tensor_unit

instance isIso_tensorToHomology (M : Condensed.{u} Ab.{u + 1}) (i : ℤ)
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (M.val.obj (op S.val))] :
    IsIso (tensorToHomology BD M i) :=
  by
  dsimp only [tensor_to_homology]
  apply is_iso.comp_is_iso

def homologyBdEval (M : Condensed.{u} Ab.{u + 1})
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (M.val.obj (op S.val))] (i : ℤ) :
    ((BD.eval freeCond').obj M).val.as.homology' i ≅
      tensor M <|
        ((BD.eval <| CategoryTheory.forget AddCommGroupCat ⋙ AddCommGroupCat.free).obj
                  (AddCommGroupCat.free.obj PUnit)).val.as.homology'
          i :=
  (asIso (tensorToHomology BD M i)).symm

section

variable (M N : Condensed.{u} Ab.{u + 1}) (f : M ⟶ N)

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes false

@[simp]
theorem embed_f_0 {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {X Y : ChainComplex 𝓐 ℕ} (f : X ⟶ Y) :
    ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).map f).f 0 = f.f 0 :=
  rfl

@[simp]
theorem embed_f_neg {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {X Y : ChainComplex 𝓐 ℕ} (f : X ⟶ Y)
    (n : ℕ) :
    ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).map f).f -[n+1] = f.f (n + 1) :=
  rfl

theorem eval_freeCond'_iso_componentZero_natural :
    (EvalFreeCond'Iso.componentZero BD M).inv ≫ ((BD.eval' freeCond').map f).f 0 =
      ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f))).f
          0 ≫
        (EvalFreeCond'Iso.componentZero BD N).inv :=
  by
  dsimp only [eval_freeCond'_iso.component_zero, package.eval', functor.map_iso_trans,
    iso.trans_inv, functor.map_iso_inv, iso_whisker_right_inv,
    functor.map_homological_complex_map_f, functor.comp_map, functor.comp_obj, functor.flip_obj_map,
    HomologicalComplex.functorEval, embed_f_0, data.eval_functor, data.eval_functor'_obj_X_map]
  simp only [functor.map_biproduct, category.assoc]
  simp only [biproduct.unique_up_to_iso_inv, functor.map_comp, condensedAbToCondensedSet_map,
    condensedSetToCondensedAb_map, whisker_right_twice, category.assoc, whiskering_right_obj_map]
  dsimp only [presheafToCondensedAb]
  simp only [← functor.map_comp]; congr 1
  ext t : 2; dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator]
  simp only [category.id_comp, category.comp_id]
  simp only [← functor.map_comp]; congr 1
  simp only [← nat_trans.comp_app]; congr 1
  apply biproduct.hom_ext'; intro j
  simp only [category.assoc, biproduct.ι_desc_assoc, biproduct.ι_desc, biproduct.ι_map_assoc]
  dsimp only [functor.map_bicone, condensedAbToPresheaf, ← Sheaf_to_presheaf_map]
  simp only [← functor.map_comp]; congr 1
  erw [biproduct.ι_map]

theorem eval_freeCond'_iso_componentNeg_natural (n : ℕ) :
    (EvalFreeCond'Iso.componentNeg BD M n).inv ≫ ((BD.eval' freeCond').map f).f -[n+1] =
      ((presheafToCondensedAb.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f))).f
          -[n+1] ≫
        (EvalFreeCond'Iso.componentNeg BD N n).inv :=
  by
  dsimp only [eval_freeCond'_iso.component_neg, package.eval', functor.map_iso_trans, iso.trans_inv,
    functor.map_iso_inv, iso_whisker_right_inv, functor.map_homological_complex_map_f,
    functor.comp_map, functor.comp_obj, functor.flip_obj_map, HomologicalComplex.functorEval,
    embed_f_neg, data.eval_functor, data.eval_functor'_obj_X_map]
  simp only [functor.map_biproduct, category.assoc]
  simp only [biproduct.unique_up_to_iso_inv, functor.map_comp, condensedAbToCondensedSet_map,
    condensedSetToCondensedAb_map, whisker_right_twice, category.assoc, whiskering_right_obj_map]
  dsimp only [presheafToCondensedAb]
  simp only [← functor.map_comp]; congr 1
  ext t : 2; dsimp only [nat_trans.comp_app, whisker_right_app, functor.associator]
  simp only [category.id_comp, category.comp_id]
  simp only [← functor.map_comp]; congr 1
  simp only [← nat_trans.comp_app]; congr 1
  apply biproduct.hom_ext'; intro j
  simp only [category.assoc, biproduct.ι_desc_assoc, biproduct.ι_desc, biproduct.ι_map_assoc]
  dsimp only [functor.map_bicone, condensedAbToPresheaf, ← Sheaf_to_presheaf_map]
  simp only [← functor.map_comp]; congr 1
  erw [biproduct.ι_map]

theorem evalFreeCond'IsoComponent_natural :
    (evalFreeCond'IsoComponent.{u} BD M).inv ≫ (BD.eval' freeCond'.{u}).map f =
      (presheafToCondensedAb.{u}.mapHomologicalComplex (ComplexShape.up.{0} ℤ)).map
          ((BD.eval' freeFunc.{u, u + 1}).map (condensedAbToPresheaf.{u}.map f)) ≫
        (evalFreeCond'IsoComponent.{u} BD N).inv :=
  by
  ext ((_ | n) | n) : 2
  · apply eval_freeCond'_iso_component_zero_natural
  · apply is_zero.eq_of_tgt; exact is_zero_zero _
  · apply eval_freeCond'_iso_component_neg_natural

end

end Condensed

