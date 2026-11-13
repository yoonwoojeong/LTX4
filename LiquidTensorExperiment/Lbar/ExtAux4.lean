import LiquidTensorExperiment.Lbar.ExtAux3
import LiquidTensorExperiment.Lbar.Iota

#align_import Lbar.ext_aux4

noncomputable section

universe v u u'

open Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

open scoped NNReal ZeroObject

variable (r r' : ℝ≥0)

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r < 1)] [Fact (r' < 1)]

open BoundedHomotopyCategory

variable {r'}

variable (BD : BreenDeligne.Package)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.data.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.data.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

section Preps

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem HomotopyCategory.colimitCofanBdd {A : Type u} [Category.{v} A] [Abelian A]
    [HasCoproducts.{v} A] {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X] :
    HomotopyCategory.IsBoundedAbove (HomotopyCategory.colimitCofan fun a : α => (X a).val).pt :=
  by
  obtain ⟨n, hn⟩ := HomotopyCategory.IsUniformlyBoundedAbove.cond (val ∘ X)
  use n; intro i hi
  dsimp [HomotopyCategory.colimitCofan]
  let e : (∐ fun a : α => (X a).val.as).pt i ≅ ∐ fun a : α => (X a).val.as.pt i :=
    HomotopyCategory.coproductIso _ _
  refine' is_zero_of_iso_of_zero _ e.symm
  apply CategoryTheory.isZero_colimit
  rintro ⟨j⟩
  apply hn j _ hi

def tinv2IsoOfBicartesianAux1 (i : ℤ) :
    Commsq.{u + 2, u + 1}
      (shiftSubId.{u + 1}
        ((qprimeFP.{u} r' BD.data κ₂ M).op ⋙
          (ext.{u + 1, u + 2} i).flip.obj
            ((single.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1}) 0).obj V.toCond))
        ι hι)
      (piExtIsoExtSigma.{u} BD κ₂ M V (fun k : ULift.{u + 1, 0} ℕ => ι k) i).hom
      (piExtIsoExtSigma.{u} BD κ₂ M V (fun k : ULift.{u + 1, 0} ℕ => ι k) i).hom
      (((ext.{u + 1, u + 2} i).map
            (ofHom.{u + 1, u + 2}
                (qprimeFP.shiftSubId.{u, u + 2, u + 1} ι hι
                  (qprimeFPInt.{u} r' BD.data κ₂ M))).op).app
        ((single.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1}) 0).obj
          (Condensed.ofTopAb.{u} ↥V))) :=
  by
  apply Commsq.ofEq
  dsimp only [shiftSubId, qprimeFP.shiftSubId]
  simp only [sub_comp, comp_sub, HomologicalComplex.ofHom_sub, CategoryTheory.op_sub,
    functor.map_sub, op_id, CategoryTheory.Functor.map_id, ofHom_id, nat_trans.app_sub,
    nat_trans.id_app, category.comp_id, category.id_comp]
  apply congr_arg₂ _ _ rfl
  rw [← iso.eq_comp_inv]
  dsimp only [piExtIsoExtSigma, iso.trans_hom, iso.trans_inv, iso.symm_hom, iso.symm_inv,
    functor.map_iso_hom, iso.op_hom, op_comp, functor.flip_obj_map, functor.map_iso_inv]
  simp only [category.assoc, ← nat_trans.comp_app_assoc, ← functor.map_comp_assoc, ←
    functor.map_comp, iso.op_inv, ← op_comp]
  rw [cofanPointIsoColimit_conj_eq_desc]
  rw [iso.eq_inv_comp]
  have :=
    extCoproductIso_naturality_shift _ (fun k : ULift ℕ => (qprimeFP r' BD.data κ₂ M).obj (ι k))
      (fun k =>
        (qprimeFP r' BD.data κ₂ M).map (hom_of_le <| hι <| by exact_mod_cast k.down.le_succ))
      i ((single (Condensed Ab) 0).obj V.to_Cond)
  exact this.symm
  · apply HomotopyCategory.colimitCofanBdd

@[reassoc]
theorem extCoproductIso_π (A : Type u) [Category.{v} A] [Abelian A] [EnoughProjectives A]
    [HasCoproducts.{v} A] [AB4 A] (X : ULift.{v} ℕ → BoundedHomotopyCategory A) [UniformlyBounded X]
    (i : ℤ) (Y) (k) :
    (extCoproductIso X i Y).hom ≫ Pi.π _ k = ((ext i).map <| Quiver.Hom.op <| Sigma.ι _ _).app Y :=
  by
  dsimp only [Ext_coproduct_iso, iso.trans_hom, pi_iso, preadditive_yoneda_coproduct_iso,
    as_iso_hom, preadditive_yoneda_coproduct_to_product]
  simp only [category.assoc, limit.lift_π, limit.lift_π_assoc, fan.mk_π_app]
  dsimp only [Ext_iso, iso.symm_hom, functor.map_iso_hom, functor.map_iso_inv]
  simp only [← functor.map_comp, iso.op_hom, iso.op_inv, ← op_comp]
  dsimp only [Ext, Ext0, functor.comp_map, whiskering_left_obj_map, whisker_left_app,
    functor.flip_map_app, replacement_iso]
  congr 2
  simp only [category.assoc, iso.inv_comp_eq, Quiver.Hom.unop_op, unop_op, op_unop]
  apply lift_unique
  simp only [category.assoc, iso.inv_comp_eq, Quiver.Hom.unop_op, unop_op, op_unop]
  erw [lift_lifts]
  simp only [uniform_π, colimit.ι_desc, cofan.mk_ι_app, lift_lifts_assoc]
  rfl

theorem Tinv2_iso_of_bicartesian_aux_2 [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (j)
    {e :
      (HomotopyCategory.colimitCofan.{u + 1, u + 2} fun a : ULift.{u + 1, 0} ℕ =>
            ((fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ₂ M).obj (ι k))
                a).val).pt.IsBoundedAbove} :
    ((cofan.{u + 1, u + 2} fun k : ULift.{u + 1, 0} ℕ =>
                  (qprimeFP.{u} r' BD.data κ₂ M).obj (ι k)).ι.app
            j ≫
          ofHom.{u + 1, u + 2}
            (sigmaMap.{u, u + 2, u + 1} ι (qprimeFPInt.tinv.{u} BD.data κ₂ κ M))) ≫
        (cofanPointIsoColimit.{u} fun k : ULift.{u + 1, 0} ℕ =>
            (qprimeFP.{u} r' BD.data κ M).obj (ι k)).hom =
      (qprimeFP.tinv _ _ _ _).app _ ≫
        Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ M).obj (ι k)) j.1 :=
  by
  rw [← iso.eq_comp_inv];
  simp only [category.assoc, cofanPointIsoColimit, colimit.comp_cocone_point_unique_up_to_iso_inv]
  dsimp only [BoundedHomotopyCategory.cofan, cofan.mk_ι_app, of_hom, HomotopyCategory.colimitCofan,
    qprimeFP.tinv, whisker_right_app, ChainComplex.toBoundedHomotopyCategory, functor.comp_map]
  erw [←
    (HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
        (ComplexShape.up.{0} ℤ)).map_comp]
  erw [←
    (HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
        (ComplexShape.up.{0} ℤ)).map_comp]
  congr 1
  dsimp only [sigmaMap]
  erw [colimit.ι_desc]
  rfl

theorem Tinv2_iso_of_bicartesian_aux_3 [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (j)
    {e :
      (HomotopyCategory.colimitCofan.{u + 1, u + 2} fun a : ULift.{u + 1, 0} ℕ =>
            ((fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ₂ M).obj (ι k))
                a).val).pt.IsBoundedAbove} :
    (cofan.{u + 1, u + 2} fun k : ULift.{u + 1, 0} ℕ =>
                (qprimeFP.{u} r' BD.data κ₂ M).obj (ι k)).ι.app
          j ≫
        ofHom.{u + 1, u + 2} (sigmaMap.{u, u + 2, u + 1} ι (qprimeFPInt.ι.{u} BD.data κ₂ κ M)) ≫
          (cofanPointIsoColimit.{u} fun k : ULift.{u + 1, 0} ℕ =>
              (qprimeFP.{u} r' BD.data κ M).obj (ι k)).hom =
      (qprimeFP.ι _ κ₂ κ M).app _ ≫
        Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ M).obj (ι k)) j.1 :=
  by
  simp only [← category.assoc]; rw [← iso.eq_comp_inv]
  simp only [category.assoc, cofanPointIsoColimit, colimit.comp_cocone_point_unique_up_to_iso_inv]
  dsimp only [BoundedHomotopyCategory.cofan, cofan.mk_ι_app, of_hom, HomotopyCategory.colimitCofan,
    qprimeFP.ι, whisker_right_app, ChainComplex.toBoundedHomotopyCategory, functor.comp_map]
  erw [←
    (HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
        (ComplexShape.up.{0} ℤ)).map_comp]
  erw [←
    (HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
        (ComplexShape.up.{0} ℤ)).map_comp]
  congr 1
  dsimp only [sigmaMap]
  erw [colimit.ι_desc]
  rfl

theorem tinv2_iso_of_bicartesian_aux [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (i : ℤ)
    (H1 : (shiftSubId.commsq (ExtQprime.tinv2 r r' BD.data κ κ₂ M V i) ι hι).Bicartesian) :
    (extTinv2Commsq (ofHom (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.tinv BD.data κ₂ κ M)))
        (ofHom (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.ι BD.data κ₂ κ M)))
        (ofHom (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.tinv BD.data κ₂ κ M)))
        (ofHom (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.ι BD.data κ₂ κ M)))
        (ofHom (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ₂ M)))
        (ofHom (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ M)))
        (auux <| commsqShiftSubIdTinv _ _ _ _ _ _) (auux <| commsqShiftSubIdι _ _ _ _ _ _)
        ((single _ 0).map
          (Condensed.ofTopAbMap (NormedAddGroupHom.toAddMonoidHom (NormedWithAut.t.inv : V ⟶ V))
            (NormedAddGroupHom.continuous _)))
        i).Bicartesian :=
  by
  have h1 := _; have h2 := _; have h3 := _
  refine'
    Commsq.Bicartesian.of_iso (piExtIsoExtSigma _ _ _ _ _ _) (piExtIsoExtSigma _ _ _ _ _ _)
      (piExtIsoExtSigma _ _ _ _ _ _) (piExtIsoExtSigma _ _ _ _ _ _) h1 h2 h2 h3 H1
  apply tinv2IsoOfBicartesianAux1
  · clear h1; apply Commsq.ofEq; rw [← iso.eq_comp_inv]
    apply limit.hom_ext; rintro ⟨j⟩; rw [lim_map_π]
    dsimp [piExtIsoExtSigma]
    simp only [category.assoc]
    have :=
      extCoproductIso_π _ (fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ₂ M).obj (ι k)) i
        ((single.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1}) 0).obj V.to_Cond) j
    rw [this, ← nat_trans.comp_app, ← functor.map_comp, ← op_comp]
    clear this
    erw [colimit.ι_desc]
    dsimp [extTinv2, ExtQprime.tinv2]
    simp only [sub_comp, comp_sub]
    refine' congr_arg₂ _ _ _
    · simp only [← nat_trans.comp_app, ← functor.map_comp, ← op_comp]
      rw [Tinv2_iso_of_bicartesian_aux_2]
      swap
      · apply HomotopyCategory.colimitCofanBdd
      simp only [functor.map_comp, op_comp, nat_trans.comp_app, category.assoc]
      have :=
        extCoproductIso_π _ (fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ M).obj (ι k))
          i ((single.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1}) 0).obj V.to_Cond) j
      rw [← iso.eq_inv_comp] at this 
      rw [← reassoc_of this]; rfl
    · simp only [category.assoc, nat_trans.naturality, ← nat_trans.comp_app_assoc, ←
        functor.map_comp_assoc, ← functor.map_comp, ← nat_trans.comp_app, ← op_comp]
      rw [Tinv2_iso_of_bicartesian_aux_3]
      simp only [functor.map_comp, op_comp, nat_trans.comp_app, category.assoc]
      have :=
        extCoproductIso_π _ (fun k : ULift.{u + 1, 0} ℕ => (qprimeFP.{u} r' BD.data κ M).obj (ι k))
          i ((single.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1}) 0).obj V.to_Cond) j
      rw [← iso.eq_inv_comp] at this 
      rw [← reassoc_of this]
      rfl
      · apply HomotopyCategory.colimitCofanBdd
  apply tinv2IsoOfBicartesianAux1

theorem tinv2_iso_of_bicartesian [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (hκ : Lbar.SufficientlyIncreasing κ ι)
    (hκ₂ : Lbar.SufficientlyIncreasing κ₂ ι) (i : ℤ)
    (H1 : (shiftSubId.commsq (ExtQprime.tinv2 r r' BD.data κ κ₂ M V i) ι hι).Bicartesian)
    (H2 : (shiftSubId.commsq (ExtQprime.tinv2 r r' BD.data κ κ₂ M V (i + 1)) ι hι).Bicartesian) :
    IsIso
      (((ext (i + 1)).map ((BD.eval freeCond'.{u}).map M.tinvCond).op).app
          ((single (Condensed Ab) 0).obj V.toCond) -
        ((ext (i + 1)).obj ((BD.eval freeCond').op.obj (op M.toCondensed))).map
          ((single (Condensed Ab) 0).map
            (Condensed.ofTopAbMap (NormedAddGroupHom.toAddMonoidHom NormedWithAut.t.inv)
              (NormedAddGroupHom.continuous _)))) :=
  by
  let Vc := (single (Condensed Ab) 0).obj V.to_Cond
  have SES₁ := qprimeFP.shortExact BD κ₂ M ι hι hκ₂
  have SES₂ := qprimeFP.shortExact BD κ M ι hι hκ
  have :=
    ext_iso_of_bicartesian_of_bicartesian SES₁ SES₂ (sigmaMap _ (qprimeFPInt.tinv BD.data _ _ M))
      (sigmaMap _ (qprimeFPInt.tinv BD.data _ _ M)) (CategoryTheory.Functor.map _ M.Tinv_cond)
      (sigmaMap _ (qprimeFPInt.ι BD.data _ _ M)) (sigmaMap _ (qprimeFPInt.ι BD.data _ _ M))
      (commsqShiftSubIdTinv BD.data _ _ M ι hι) (commsqSigmaProjTinv BD _ _ M ι)
      (commsqShiftSubIdι BD.data _ _ M ι hι) (commsqSigmaProjι BD _ _ M ι) Vc
      ((single _ _).map <|
        Condensed.ofTopAbMap (NormedAddGroupHom.toAddMonoidHom normed_with_aut.T.inv)
          (NormedAddGroupHom.continuous _))
      _ (tinv2_iso_of_bicartesian_aux _ _ _ _ _ _ _ _ _ H1)
      (tinv2_iso_of_bicartesian_aux _ _ _ _ _ _ _ _ _ H2)
  delta extTinv2 at this 
  simpa only [op_id, CategoryTheory.Functor.map_id, category.id_comp, nat_trans.id_app]

theorem tinv2_iso_of_bicartesian' [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)]
    (H :
      ∀ i,
        ∃ (ι : _) (hι : _),
          Lbar.SufficientlyIncreasing κ ι ∧
            Lbar.SufficientlyIncreasing κ₂ ι ∧
              (shiftSubId.commsq (ExtQprime.tinv2 r r' BD.data κ κ₂ M V i) ι hι).Bicartesian ∧
                (shiftSubId.commsq (ExtQprime.tinv2 r r' BD.data κ κ₂ M V (i + 1)) ι
                    hι).Bicartesian)
    (i : ℤ) :
    IsIso
      (((ext i).map ((BD.eval freeCond'.{u}).map M.tinvCond).op).app
          ((single (Condensed Ab) 0).obj V.toCond) -
        ((ext i).obj ((BD.eval freeCond').op.obj (op M.toCondensed))).map
          ((single (Condensed Ab) 0).map
            (Condensed.ofTopAbMap (NormedAddGroupHom.toAddMonoidHom NormedWithAut.t.inv)
              (NormedAddGroupHom.continuous _)))) :=
  by
  obtain ⟨i, rfl⟩ : ∃ k, k + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
  obtain ⟨ι, hι, hκ, hκ₂, H1, H2⟩ := H i
  apply tinv2_iso_of_bicartesian _ _ _ _ _ _ ι hι hκ hκ₂ i H1 H2

end Preps

