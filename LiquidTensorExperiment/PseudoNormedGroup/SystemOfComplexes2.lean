import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp
import LiquidTensorExperiment.ForMathlib.SplitExact
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import LiquidTensorExperiment.PseudoNormedGroup.FP2
import LiquidTensorExperiment.PseudoNormedGroup.SystemOfComplexes
import LiquidTensorExperiment.SystemOfComplexes.Rescale
import LiquidTensorExperiment.Prop92.Prop92

#align_import pseudo_normed_group.system_of_complexes2

noncomputable section

open scoped NNReal

universe u v

open CategoryTheory BreenDeligne

variable (r r' : ℝ≥0)

variable (BD : BreenDeligne.Data)

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (V : SemiNormedGroupCat.{v})

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

def auxSystem (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ c)]
    [∀ n : ℕ, Fact (Monotone (Function.swap κ n))] : SystemOfComplexes :=
  (fPsystem r' BD M κ).op ⋙
    (((cLC.{v, u} V).rightOp.mapFreeAb ⋙ FreeAb.eval _).mapHomologicalComplex _).op ⋙
      HomologicalComplex.unopFunctor

namespace auxSystem

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r' ≤ 1)]

open SystemOfComplexes Opposite

variable (κ₁ κ₂ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ₁ c)] [∀ c, BD.Suitable (κ₂ c)]

def tinv [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)] :
    auxSystem r' BD M V κ₂ ⟶ auxSystem r' BD M V κ₁ :=
  whiskerRight (NatTrans.op <| fPsystem.tinv r' BD M κ₁ κ₂)
    ((((cLC.{v, u} V).rightOp.mapFreeAb ⋙ FreeAb.eval _).mapHomologicalComplex _).op ⋙
      HomologicalComplex.unopFunctor)

theorem tinv_eq [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)]
    (c : ℝ≥0ᵒᵖ) (n : ℕ) :
    ((tinv r' BD M V κ₁ κ₂).app c).f n = ((cLCFP.tinv V r' _ _ (BD.pt n)).app (op M) : _) :=
  by
  dsimp only [Tinv, cLCFP.tinv, FPsystem.Tinv, FP2.Tinv, HomologicalComplex.comp_f, auxSystem,
    functor.comp_map, HomologicalComplex.unopFunctor, HomologicalComplex.unop_d, functor.op_obj,
    functor.map_homological_complex_obj_d, unop_op, cLC, functor.op_map, Quiver.Hom.unop_op,
    functor.map_homological_complex_map_f, functor.map_FreeAb, FreeAb.eval,
    FreeAbelianGroup.map_of_apply, FPsystem, FP2.res_app, FreeAb.of_functor, functor.right_op_map,
    whisker_right_app, nat_trans.op_app]
  erw [FreeAbelianGroup.lift.of]
  rfl

def tInv [NormedWithAut r V] (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ c)]
    [∀ n : ℕ, Fact (Monotone (Function.swap κ n))] : auxSystem r' BD M V κ ⟶ auxSystem r' BD M V κ
    where
  app c :=
    { f := fun i =>
        NormedAddGroupHom.completion <|
          (SemiNormedGroupCat.locallyConstant.map <| NormedWithAut.t.inv).app _
      comm' := by
        rintro i j (rfl : i + 1 = j)
        dsimp only [auxSystem, functor.comp_obj, HomologicalComplex.unopFunctor,
          HomologicalComplex.unop_d, functor.op_obj, functor.map_homological_complex_obj_d, unop_op]
        erw [← SemiNormedGroupCat.completion_map, ← SemiNormedGroupCat.completion_map,
          ChainComplex.of_d]
        dsimp only [FPsystem.d, universal_map.eval_FP2, universal_map.eval_CLCFP,
          universal_map.eval_LCFP, cLC]
        simp only [nat_trans.app_sum, functor.map_sum, preadditive.comp_sum, preadditive.sum_comp,
          CategoryTheory.unop_sum, nat_trans.app_zsmul, functor.map_zsmul, preadditive.comp_zsmul,
          preadditive.zsmul_comp, CategoryTheory.unop_zsmul]
        refine' Finset.sum_congr rfl _
        rintro ⟨g, hg⟩ -
        dsimp only [basic_universal_map.eval_FP2, basic_universal_map.eval_LCFP, whisker_right_app,
          nat_trans.op_app, unop_op, FreeAb.of_functor, FreeAbelianGroup.map_of_apply,
          functor.right_op_map, lC, functor.comp_map, functor.map_FreeAb, FreeAb.eval]
        rw [FreeAbelianGroup.lift.of, _root_.id, Quiver.Hom.unop_op, ←
          SemiNormedGroup.Completion.map_comp, ← SemiNormedGroup.Completion.map_comp,
          nat_trans.naturality] }
  naturality' c₁ c₂ h := by
    ext n : 2
    dsimp only [HomologicalComplex.comp_f, auxSystem, functor.comp_map,
      HomologicalComplex.unopFunctor, HomologicalComplex.unop_d, functor.op_obj,
      functor.map_homological_complex_obj_d, unop_op, cLC, functor.op_map, Quiver.Hom.unop_op,
      functor.map_homological_complex_map_f, functor.map_FreeAb, FreeAb.eval,
      FreeAbelianGroup.map_of_apply, FPsystem, FP2.res_app, FreeAb.of_functor, functor.right_op_map]
    rw [← SemiNormedGroupCat.completion_map, ← SemiNormedGroupCat.completion_map,
      FreeAbelianGroup.lift.of, _root_.id, Quiver.Hom.unop_op, ←
      SemiNormedGroup.Completion.map_comp, ← SemiNormedGroup.Completion.map_comp,
      nat_trans.naturality]
    rfl

variable [NormedWithAut r V]

theorem tInv_eq (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ c)]
    [∀ n : ℕ, Fact (Monotone (Function.swap κ n))] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
    ((tInv r r' BD M V κ).app c).f n = ((cLCFP.tInv r V r' _ (BD.pt n)).app (op M) : _) :=
  by
  dsimp only [T_inv, cLCFP.tInv, FPsystem, ChainComplex.of_x, FPsystem.X, HomologicalComplex.comp_f,
    auxSystem, functor.comp_map, HomologicalComplex.unopFunctor, HomologicalComplex.unop_d,
    functor.op_obj, functor.map_homological_complex_obj_d, functor.map_homological_complex_map_f,
    functor.map_FreeAb, unop_op, cLC, functor.op_map, functor.op_obj, Quiver.Hom.unop_op,
    FreeAb.eval, FreeAbelianGroup.map_of_apply, FPsystem, FP2.res_app, FreeAb.of_functor,
    functor.right_op_map, whisker_right_app, nat_trans.op_app, whisker_left_app]
  rfl

def res [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ κ₂ c n)] :
    auxSystem r' BD M V κ₂ ⟶ auxSystem r' BD M V κ₁ :=
  whiskerRight (NatTrans.op <| fPsystem.res r' BD M κ₁ κ₂)
    ((((cLC.{v, u} V).rightOp.mapFreeAb ⋙ FreeAb.eval _).mapHomologicalComplex _).op ⋙
      HomologicalComplex.unopFunctor)

theorem res_eq [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)]
    [∀ c n, Fact (κ₁ c n ≤ κ₂ c n)] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
    ((res r' BD M V κ₁ κ₂).app c).f n = ((cLCFP.res V r' _ _ (BD.pt n)).app (op M) : _) :=
  by
  dsimp only [res, cLCFP.res, FPsystem.res, FP2.res, HomologicalComplex.comp_f, auxSystem,
    functor.comp_map, HomologicalComplex.unopFunctor, HomologicalComplex.unop_d, functor.op_obj,
    functor.map_homological_complex_obj_d, unop_op, cLC, functor.op_map, Quiver.Hom.unop_op,
    functor.map_homological_complex_map_f, functor.map_FreeAb, FreeAb.eval,
    FreeAbelianGroup.map_of_apply, FPsystem, FP2.res_app, FreeAb.of_functor, functor.right_op_map,
    whisker_right_app, nat_trans.op_app]
  rw [FreeAbelianGroup.lift.of]
  rfl

def tinv2 [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)]
    [∀ c n, Fact (κ₁ c n ≤ κ₂ c n)] : auxSystem r' BD M V κ₂ ⟶ auxSystem r' BD M V κ₁ :=
  tinv r' BD M V κ₁ κ₂ - tInv r r' BD M V κ₂ ≫ res r' BD M V κ₁ κ₂

theorem tinv2_eq [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)]
    [∀ c n, Fact (κ₁ c n ≤ κ₂ c n)] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
    ((tinv2 r r' BD M V κ₁ κ₂).app c).f n =
      ((cLCFP.tinv V r' _ _ (BD.pt n)).app (op M) : _) -
        ((cLCFP.tInv r V r' _ (BD.pt n)).app (op M) : _) ≫
          ((cLCFP.res V r' _ _ (BD.pt n)).app (op M) : _) :=
  by
  rw [Tinv2, nat_trans.app_sub, HomologicalComplex.sub_f_apply, Tinv_eq, nat_trans.comp_app,
    HomologicalComplex.comp_f, T_inv_eq, res_eq]

theorem auxSystem_d_eq (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ c)]
    [∀ n : ℕ, Fact (Monotone (Function.swap κ n))] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Arrow.mk (((auxSystem r' BD M V κ).obj c).d i (i + 1)) =
      Arrow.mk
        ((UniversalMap.evalCLCFP V r' (κ (unop c) i) (κ (unop c) (i + 1)) (BD.d (i + 1) i) : _).app
          (op M)) :=
  by
  dsimp [auxSystem, FPsystem]
  rw [ChainComplex.of_d]
  dsimp [FreeAb.eval, functor.map_FreeAb, functor.right_op_map, FPsystem.d, universal_map.eval_FP2,
    universal_map.eval_CLCFP, universal_map.eval_LCFP]
  simp only [nat_trans.app_sum, map_sum, ← normedAddGroupHomCompletionHom_apply,
    CategoryTheory.unop_sum]
  congr 1
  refine' Finset.sum_congr rfl _
  rintro ⟨g, hg⟩ -
  simp only [nat_trans.app_zsmul, map_zsmul, CategoryTheory.unop_zsmul]
  dsimp only [basic_universal_map.eval_FP2, basic_universal_map.eval_LCFP, whisker_right_app,
    nat_trans.op_app, unop_op, FreeAb.of_functor, FreeAbelianGroup.map_of_apply]
  rw [FreeAbelianGroup.lift.of]
  rfl

section

variable (κ : ℕ → ℝ≥0) [BD.Suitable κ]

instance hMul_left_mono (n : ℕ) :
    Fact (Monotone (Function.swap (fun (c : ℝ≥0) (n : ℕ) => c * κ n) n)) :=
  ⟨fun c₁ c₂ h => mul_le_mul' h le_rfl⟩

def inclF (c : ℝ≥0ᵒᵖ) (n : ℕ) :
    ((BD.Complex κ r V r' (unop c)).obj (op M)).pt n ⟶
      ((auxSystem r' BD M V fun c n => c * κ n).obj c).pt n :=
  by
  dsimp [BreenDeligne.Data.complex, BreenDeligne.Data.complex₂, BreenDeligne.Data.complex₂X,
    cLCTinv, auxSystem, FPsystem, FPsystem.X, functor.map_FreeAb, FreeAb.eval]
  exact (SemiNormedGroupCat.equalizer.ι _ _ : _)

theorem incl_comm (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    inclF.{u, v} r r' BD M V κ c i ≫
        ((auxSystem.{u, v} r' BD M V fun c n => c * κ n).obj c).d i (i + 1) =
      ((BD.Complex κ r V r' (unop c)).obj (op.{u + 2} M)).d i (i + 1) ≫
        inclF.{u, v} r r' BD M V κ c (i + 1) :=
  by
  dsimp [auxSystem]
  erw [ChainComplex.of_d, BreenDeligne.Data.complex_obj_d]
  dsimp [BreenDeligne.Data.complex, BreenDeligne.Data.complex₂, BreenDeligne.Data.complex₂X,
    cLCTinv, FPsystem, FPsystem.X, functor.map_FreeAb, FreeAb.eval, universal_map.eval_CLCFPTinv,
    universal_map.eval_CLCFPTinv₂, SemiNormedGroupCat.equalizer.mapNat, incl_f]
  delta id; dsimp only; symm
  convert SemiNormedGroupCat.equalizer.map_comp_ι _ _ _ _ using 2
  apply arrow.mk_injective
  rw [← aux_system_d_eq r' BD M V fun c n => c * κ n]
  dsimp [auxSystem]
  erw [ChainComplex.of_d]
  rfl

def incl : (BD.system κ r V r').obj (op M) ⟶ auxSystem r' BD M V fun c n => c * κ n
    where
  app c :=
    { f := inclF r r' BD M V κ c
      comm' := by rintro i j (rfl : i + 1 = j); apply incl_comm }
  naturality' c₁ c₂ h := by
    ext n : 2
    dsimp [auxSystem]
    dsimp [BreenDeligne.Data.complex, BreenDeligne.Data.complex₂, BreenDeligne.Data.complex₂X,
      cLCTinv, FPsystem, FPsystem.X, functor.map_FreeAb, FreeAb.eval, FreeAb.of_functor,
      universal_map.eval_CLCFPTinv, universal_map.eval_CLCFPTinv₂,
      SemiNormedGroupCat.equalizer.mapNat, incl_f, cLCFPTinv₂.res, cLCTinv.mapNat, cLCTinv.map]
    delta id
    erw [FreeAbelianGroup.lift.of]
    convert SemiNormedGroupCat.equalizer.map_comp_ι _ _ _ _ using 1

def incl' :=
  whiskerRight (incl r r' BD M V κ) (Functor.mapHomologicalComplex (forget₂ _ Ab.{max u v}) _)

end

def tinv2' [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)]
    [∀ c n, Fact (κ₁ c n ≤ κ₂ c n)] :=
  whiskerRight (tinv2 r r' BD M V κ₁ κ₂) (Functor.mapHomologicalComplex (forget₂ _ Ab.{max u v}) _)

theorem SemiNormedGroupCat.equalizer.ι_injective {V W : SemiNormedGroupCat} (f g : V ⟶ W) :
    Function.Injective (SemiNormedGroupCat.equalizer.ι f g) :=
  Subtype.val_injective

theorem SemiNormedGroupCat.equalizer.forget₂_ι {V W : SemiNormedGroupCat} (f g : V ⟶ W) :
    (forget₂ _ Ab).map (SemiNormedGroupCat.equalizer.ι f g) =
      AddSubgroup.subtype (AddMonoidHom.ker ((forget₂ _ Ab).map (f - g))) :=
  rfl

instance hMul_left_mono' (κ : ℕ → ℝ≥0) (n : ℕ) :
    Fact (Monotone (Function.swap (fun (c : ℝ≥0) (n : ℕ) => r' * (c * κ n)) n)) :=
  ⟨fun c₁ c₂ h => mul_le_mul' le_rfl <| mul_le_mul' h le_rfl⟩

theorem neg_surjective {A B : Ab} (f : A ⟶ B) (hf : Function.Surjective f) :
    Function.Surjective (-f) := by intro y; obtain ⟨x, rfl⟩ := hf y; use-x;
  simp only [Pi.neg_apply, map_neg, neg_neg]

theorem shortExact [Fact (r < 1)] (κ : ℕ → ℝ≥0) [BD.Suitable κ]
    [∀ c n, Fact (κ₁ c n ≤ r' * (c * κ n))] (c : ℝ≥0ᵒᵖ) (n : ℕ) :
    ShortExact (((incl' r r' BD M V κ).app c).f n)
      (((tinv2' r r' BD M V (fun c n => r' * (c * κ n)) fun c n => c * κ n).app c).f n) :=
  by
  apply (config := { instances := false }) @short_exact.mk
  · rw [AddCommGroupCat.mono_iff_injective]
    dsimp [incl', incl, incl_f, BreenDeligne.Data.complex, BreenDeligne.Data.complex₂,
      BreenDeligne.Data.complex₂X]
    exact SemiNormedGroupCat.equalizer.ι_injective _ _
  · rw [Tinv2', whisker_right_app, functor.map_homological_complex_map_f, Tinv2_eq, ←
      nat_trans.comp_app, ← cLCFP.res_comp_tInv, nat_trans.comp_app, ← neg_sub, functor.map_neg,
      functor.map_sub, CategoryTheory.Functor.map_comp, AddCommGroupCat.epi_iff_surjective]
    apply neg_surjective
    have := cLCFP.tInvSubTinv_surjective r r' V (unop c * κ n) (BD.X n) (op M)
    rw [cLCFP.tInvSubTinv, nat_trans.app_sub, nat_trans.comp_app] at this 
    exact this
  · rw [AddCommGroupCat.exact_iff]
    dsimp [incl', incl, incl_f, Tinv2', BreenDeligne.Data.complex, BreenDeligne.Data.complex₂,
      BreenDeligne.Data.complex₂X]
    rw [SemiNormedGroupCat.equalizer.forget₂_ι, AddSubgroup.subtype_range, Tinv2_eq, ←
      nat_trans.comp_app, ← cLCFP.res_comp_tInv]
    rfl

end auxSystem

