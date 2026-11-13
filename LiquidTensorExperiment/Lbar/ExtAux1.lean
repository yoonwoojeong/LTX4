import LiquidTensorExperiment.Lbar.ExtPreamble

#align_import Lbar.ext_aux1

noncomputable section

universe u v

open Opposite CategoryTheory CategoryTheory.Limits

open scoped NNReal ZeroObject

variable (r r' : ℝ≥0)

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r < 1)] [Fact (r' < 1)]

open BoundedHomotopyCategory

variable (BD : BreenDeligne.Data)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

def extQprimeIsoAuxSystemObjAux' (X : Profinite.{u}) :
    Ab.ulift.{u + 1}.obj
        ((forget₂ SemiNormedGroupCat Ab).obj
          (SemiNormedGroupCat.completion.obj
            ((SemiNormedGroupCat.locallyConstant.obj V).obj (op X)))) ≅
      (forget₂ SemiNormedGroupCat.{u + 1} Ab.{u + 1}).obj
        (SemiNormedGroupCat.completion.obj
          ((SemiNormedGroupCat.locallyConstant.obj (SemiNormedGroupCat.ulift.{u + 1}.obj V)).obj
            (op X))) :=
  by
  refine' AddEquiv.toAddCommGroupCatIso _
  refine' add_equiv.ulift.trans _
  refine' AddEquiv.mk _ _ _ _ _
  · refine' NormedAddGroupHom.completion _
    refine' LocallyConstant.mapHom _
    refine' { add_equiv.ulift.symm with bound' := ⟨1, fun v => _⟩ }
    rw [one_mul]; exact le_rfl
  · refine' UniformSpace.Completion.map _
    refine' LocallyConstant.mapHom _
    refine' { AddEquiv.ulift with bound' := ⟨1, fun v => _⟩ }
    rw [one_mul]; exact le_rfl
  · erw [Function.leftInverse_iff_comp, UniformSpace.Completion.map_comp]
    · have : ULift.down.{u + 1} ∘ ULift.up.{u + 1} = (id : V → V) := rfl
      erw [LocallyConstant.map_comp, this, LocallyConstant.map_id, UniformSpace.Completion.map_id]
    · apply NormedAddGroupHom.uniformContinuous
    · apply NormedAddGroupHom.uniformContinuous
  · erw [Function.rightInverse_iff_comp, UniformSpace.Completion.map_comp]
    · have : ULift.up.{u + 1, u} ∘ ULift.down.{u + 1} = @id (ULift V) := by ext v; rfl
      erw [LocallyConstant.map_comp, this, LocallyConstant.map_id, UniformSpace.Completion.map_id]
    · apply NormedAddGroupHom.uniformContinuous
    · apply NormedAddGroupHom.uniformContinuous
  · intro x y; apply map_add

attribute [simps] Equiv.ulift AddEquiv.ulift

theorem SemiNormedGroupCat.forget₂_ab_map {V W : SemiNormedGroupCat} (f : V ⟶ W) :
    (forget₂ SemiNormedGroupCat Ab).map f = f.toAddMonoidHom :=
  rfl

theorem SemiNormedGroupCat.forget₂_ab_obj (V : SemiNormedGroupCat) :
    (forget₂ SemiNormedGroupCat Ab).obj V = AddCommGroupCat.of V :=
  rfl

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

--jmc: is this helpful??
@[reassoc]
theorem extQprimeIsoAuxSystemObjAux'_natural (X Y : Profinite.{u}) (f : X ⟶ Y) :
    (extQprimeIsoAuxSystemObjAux' V Y).hom ≫
        (forget₂ _ _).map
          (SemiNormedGroupCat.completion.map
            ((SemiNormedGroupCat.locallyConstant.obj _).map f.op)) =
      Ab.ulift.map
          ((forget₂ _ _).map
            (SemiNormedGroupCat.completion.map
              ((SemiNormedGroupCat.locallyConstant.obj _).map f.op))) ≫
        (extQprimeIsoAuxSystemObjAux' V X).hom :=
  by
  ext1 ⟨φ⟩; simp only [comp_apply]
  dsimp only [extQprimeIsoAuxSystemObjAux', AddEquiv.toAddCommGroupCatIso, AddEquiv.trans_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_mk, Ab.ulift_map_apply,
    SemiNormedGroupCat.forget₂_ab_map, SemiNormedGroupCat.forget₂_ab_obj, AddCommGroupCat.coe_of]
  apply UniformSpace.Completion.induction_on φ <;> clear φ
  · refine' @isClosed_eq _ _ _ _ (id _) _ _ _ _
    · dsimp [SemiNormedGroupCat.completion_obj, SemiNormedGroupCat.locallyConstant_obj_obj]
      infer_instance
    · apply uniform_space.completion.continuous_map.comp UniformSpace.Completion.continuous_map
    · apply uniform_space.completion.continuous_map.comp
      dsimp only [Ab.ulift, AddMonoidHom.coe_mk, AddEquiv.uLift_apply, Equiv.toFun_as_coe,
        Equiv.ulift_apply]
      apply UniformSpace.Completion.continuous_map
  · intro φ
    dsimp only [Ab.ulift, AddMonoidHom.coe_mk, AddEquiv.uLift_apply, Equiv.toFun_as_coe,
      Equiv.ulift_apply, SemiNormedGroupCat.locallyConstant_obj_map,
      SemiNormedGroupCat.completion_map]
    erw [NormedAddGroupHom.completion_coe, NormedAddGroupHom.completion_coe,
      NormedAddGroupHom.completion_coe, NormedAddGroupHom.completion_coe]
    congr 1
    dsimp only [LocallyConstant.comapHom_apply, LocallyConstant.mapHom_apply]
    erw [LocallyConstant.comap_map]
    exact f.continuous

open CategoryTheory.Preadditive

theorem freeAb_naturality_helper {C 𝓐 : Type _} [Category C] [Category 𝓐] [Preadditive 𝓐]
    (F G : FreeAb C ⥤ 𝓐) [F.Additive] [G.Additive] (η : ∀ X : FreeAb C, F.obj X ⟶ G.obj X)
    (hη :
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
        F.map ((FreeAb.ofFunctor _).map f) ≫ η _ = η _ ≫ G.map ((FreeAb.ofFunctor _).map f))
    {X Y : FreeAb C} (f : X ⟶ Y) : F.map f ≫ η Y = η X ≫ G.map f :=
  by
  change right_comp _ (η Y) (F.map_add_hom f) = left_comp _ (η X) (G.map_add_hom f)
  rw [← AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply]; congr 1; clear f
  ext1 f; cases X; cases Y; exact hη f

theorem ExtQprime_iso_aux_system_obj_aux_aux (X Y : Profinite.{u}) (f : X ⟶ Y) :
    (lCCIsoCondOfTopAb.{u} V).inv.app (op.{u + 2} Y) ≫
        (forget₂.{u + 1, u + 1, u, u, u} SemiNormedGroupCat.{u} Ab.{u}).map
          (SemiNormedGroupCat.completion.{u}.map
            ((SemiNormedGroupCat.locallyConstant.{u, u}.obj V).map f.op)) =
      (Condensed.OfTopAb.presheaf _).map f.op ≫ (lCCIsoCondOfTopAb V).inv.app (op X) :=
  by
  simp only [← nat_iso.app_inv, iso.inv_comp_eq]
  simp only [← category.assoc, iso.eq_comp_inv]
  ext1 t; dsimp [forget₂, has_forget₂.forget₂, lCCIsoCondOfTopAb, lCCIsoCondOfTopAbAddEquiv] at t ⊢
  simp only [comp_apply, NormedAddGroupHom.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.coe_mk]
  dsimp only [Condensed.OfTopAb.presheaf, AddMonoidHom.mk'_apply]
  ext x
  simp only [ContinuousMap.comp_apply]
  apply UniformSpace.Completion.induction_on t <;> clear t
  · refine' isClosed_eq _ _
    · have h1 : Continuous fun q : C(X, V) => q x := ContinuousMap.continuous_eval_const.{u, u} x
      have h2 :
        Continuous
          (UniformSpace.Completion.extension.{u, u} LocallyConstant.toContinuousMap.{u, u}) :=
        UniformSpace.Completion.continuous_extension
      have h3 := (LocallyConstant.comapHom.{u, u, u} f f.continuous).Completion.Continuous
      refine' (h1.comp h2).comp h3
      infer_instance
    · let t := _; change Continuous t
      have ht : t = _ ∘ UniformSpace.Completion.extension LocallyConstant.toContinuousMap.{u, u}
      rotate_left 2
      · intro q; exact q (f x)
      · rfl
      rw [ht]; clear ht t
      apply Continuous.comp
      exact ContinuousMap.continuous_eval_const.{u, u} (f x)
      exact UniformSpace.Completion.continuous_extension.{u, u}
  · intro a
    simp only [NormedAddGroupHom.completion_coe, LocallyConstant.comapHom_apply, Quiver.Hom.unop_op]
    erw [UniformSpace.Completion.extension_coe]
    erw [UniformSpace.Completion.extension_coe]
    unfold LocallyConstant.comap
    classical
    erw [dif_pos]
    rfl
    exact f.continuous
    exact LocallyConstant.toContinuousMap_uniformContinuous.{u} Y ↥V
    exact LocallyConstant.toContinuousMap_uniformContinuous.{u} X ↥V

def extQprimeIsoAuxSystemObjAux :
    ((cLC (SemiNormedGroupCat.ulift.{u + 1}.obj V)).rightOp.mapFreeAb ⋙
          FreeAb.eval SemiNormedGroupCatᵒᵖ) ⋙
        (forget₂ SemiNormedGroupCat Ab).op ≅
      (freeCond.mapFreeAb ⋙ FreeAb.eval (Condensed.{u} Ab.{u + 1})) ⋙
        (preadditiveYoneda.obj V.toCond).rightOp :=
  by
  refine' nat_iso.of_components _ _
  · intro X
    dsimp only [functor.comp_obj, functor.right_op, functor.op_obj, FreeAb.eval, functor.map_FreeAb]
    refine' iso.op _
    refine' preadditiveYonedaObjObjCondensedSetToCondensedAb _ _ ≪≫ _
    let e := (Condensed_Ab_to_presheaf.map_iso (condensedLCCIsoOfTopAb V)).app (op X.as)
    refine' e.symm ≪≫ extQprimeIsoAuxSystemObjAux' V X.as
  · intro X Y f
    apply freeAb_naturality_helper; clear f X Y; intro X Y f
    dsimp only [id.def, iso.trans_hom, iso.op_hom, op_comp, iso.symm_hom, functor.map_iso_inv,
      functor.comp_map, functor.right_op_map, functor.op_map, iso.app_inv, FreeAb.eval,
      functor.map_FreeAb, FreeAb.of_functor]
    simp only [category.assoc, ← op_comp]; congr 1
    simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift.of, id.def,
      functor.right_op_map, Quiver.Hom.unop_op]
    erw [← preadditiveYonedaObjObjCondensedSetToCondensedAb_natural'_assoc]
    congr 1
    dsimp [condensedLCCIsoOfTopAb]
    erw [extQprimeIsoAuxSystemObjAux'_natural]
    simp only [← category.assoc]; congr 1
    rw [← Ab.ulift.map_comp]
    rw [ExtQprime_iso_aux_system_obj_aux_aux]
    ext; rfl

/-- Hom(X,A) -/
def homComplexInt (X : HomologicalComplex (Condensed.{u} Ab.{u + 1}) (ComplexShape.up ℤ))
    (A : Condensed.{u} Ab.{u + 1}) : HomologicalComplex Ab.{u + 1} (ComplexShape.up ℤ).symm :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex _).obj X.op

def homComplexNat (X : HomologicalComplex (Condensed.{u} Ab.{u + 1}) (ComplexShape.down ℕ))
    (A : Condensed.{u} Ab.{u + 1}) : HomologicalComplex Ab.{u + 1} (ComplexShape.down ℕ).symm :=
  ((preadditiveYoneda.obj A).mapHomologicalComplex _).obj X.op

def embedHomComplexNatIso (X : HomologicalComplex (Condensed.{u} Ab.{u + 1}) (ComplexShape.down ℕ))
    (A : Condensed.{u} Ab.{u + 1}) :
    homComplexInt ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj X) A ≅
      (HomologicalComplex.embed ComplexShape.Embedding.natUpIntDown).obj (homComplexNat X A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      match i with
      | Int.ofNat 0 => Iso.refl _
      | Int.ofNat (i + 1) => IsZero.iso (Functor.map_isZero _ (isZero_zero _).op) (isZero_zero _)
      | -[i+1] => Iso.refl _)
    (by
      rintro i (j | (_ | j)) (rfl : _ = _)
      · apply is_zero.eq_of_src
        refine' functor.map_is_zero _ _
        dsimp; apply is_zero.op; exact is_zero_zero _
      · refine' (category.id_comp _).trans (category.comp_id _).symm
      · refine' (category.id_comp _).trans (category.comp_id _).symm)

/-
lemma embed_hom_complex_nat_iso_homology_iso (X : homological_complex (Condensed.{u} Ab.{u+1})
  (complex_shape.down ℕ)) (A : Condensed.{u} Ab.{u+1}) (n : ℕ) :
  (homology_functor _ _ (-(n : ℤ))).map (embed_hom_complex_nat_iso X A).hom ≫
  (homological_complex.homology_embed_nat_iso _
    complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff
    n (-(n : ℤ)) (by { cases n; refl })).app _
  = _
-/
/-
-- OLD construction of ExtQprime_iso_aux_system_obj
begin
  refine (homology_functor _ _ (-n:ℤ)).map_iso _ ≪≫ _,
  { let C := ((preadditive_yoneda.obj V.to_Cond).right_op.map_homological_complex _).obj
      (((QprimeFP_nat r' BD κ M).obj c)),
    exact ((homological_complex.embed complex_shape.embedding.nat_up_int_down).obj C.unop), },
  { refine _ ≪≫ embed_unop.app (op (((preadditive_yoneda_obj V.to_Cond ⋙ forget₂ _ _).right_op.map_homological_complex
      (complex_shape.down ℕ)).obj ((QprimeFP_nat r' BD κ M).obj c))),
    dsimp,
    refine (homological_complex.unop_functor.right_op.map_iso _).unop,
    symmetry, refine (map_homological_complex_embed _).app _, },
  refine (homological_complex.homology_embed_nat_iso _
    complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff
    n (-n) (by { cases n; refl })).app _ ≪≫ (homology_functor _ _ _).map_iso _,
  refine hom_complex_QprimeFP_nat_iso_aux_system r' BD κ M V c
end
-/
def homComplexQprimeFPNatIsoAuxSystem (c : ℝ≥0) :
    homComplexNat.{u} ((qprimeFPNat.{u} r' BD κ M).obj c) V.toCond ≅
      (auxSystem.{u, u + 1} r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V) κ).toAb.obj
        (op.{1} c) :=
  by
  refine' _ ≪≫ forget₂_unop.app _
  let φ :
    op
        (((preadditive_yoneda.obj V.to_Cond).rightOp.mapHomologicalComplex
              (ComplexShape.down ℕ)).obj
          ((qprimeFPNat r' BD κ M).obj c)) ≅
      _ :=
    _
  refine' homological_complex.unop_functor.map_iso φ
  refine'
    ((CategoryTheory.NatIso.mapHomologicalComplex (extQprimeIsoAuxSystemObjAux V) _).app
        ((BreenDeligne.fPsystem r' BD _ κ).obj c)).op

def extQprimeIsoAuxSystemObj (c : ℝ≥0) (n : ℕ) :
    ((ext n).obj (op <| (qprimeFP r' BD κ M).obj c)).obj ((single _ 0).obj V.toCond) ≅
      ((auxSystem r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1}.obj V) κ).toAbH n).obj (op c) :=
  extComputeWithAcyclic _ _ (ExtQprime_iso_aux_system_aux r' BD κ M V c) _ ≪≫
    by
    refine' (homology'Functor _ _ (-n : ℤ)).mapIso (embedHomComplexNatIso _ _) ≪≫ _
    refine'
      (HomologicalComplex.homologyEmbedNatIso _ ComplexShape.Embedding.natUpIntDown n (-n)
              (by cases n <;> rfl)).app
          _ ≪≫
        (homology'Functor _ _ _).mapIso _
    refine' homComplexQprimeFPNatIsoAuxSystem r' BD κ M V c

attribute [reassoc] extComputeWithAcyclic_naturality

def cofanPointIsoColimit {α : Type (u + 1)}
    (X : α → BoundedHomotopyCategory (Condensed.{u} Ab.{u + 1}))
    [BoundedHomotopyCategory.UniformlyBounded X] : (BoundedHomotopyCategory.cofan X).pt ≅ ∐ X :=
  (BoundedHomotopyCategory.isColimitCofan X).coconePointUniqueUpToIso (colimit.isColimit _)

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

instance sigmaQprimeIntBoundedAbove :
    ((HomotopyCategory.quotient (Condensed Ab) (ComplexShape.up ℤ)).obj
        (∐ fun k : ULift ℕ => (qprimeFPInt r' BD κ M).obj (ι k))).IsBoundedAbove :=
  by
  refine' ⟨⟨1, _⟩⟩
  intro a ha
  refine' is_zero.of_iso _ (HomotopyCategory.coproductIso _ _)
  apply CategoryTheory.isZero_colimit
  intro
  exact ChainComplex.boundedByOne _ _ ha

def coproductShift (A : Type u) [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]
    (X : ULift.{v} ℕ → BoundedHomotopyCategory A) [UniformlyBounded X]
    (e : X ⟶ fun i => X (ULift.up <| ULift.down i + 1)) : ∐ X ⟶ ∐ X :=
  by
  apply sigma.desc
  intro i
  refine' _ ≫ sigma.ι _ (ULift.up <| ULift.down i + 1)
  refine' e _

@[reassoc]
theorem extCoproductIso_naturality_shift (A : Type u) [Category.{v} A] [Abelian A]
    [EnoughProjectives A] [HasCoproducts.{v} A] [AB4 A]
    (X : ULift.{v} ℕ → BoundedHomotopyCategory A) [UniformlyBounded X]
    (e : X ⟶ fun i => X (ULift.up <| ULift.down i + 1)) (i : ℤ) (Y) :
    ((ext i).map (coproductShift _ X e).op).app Y ≫ (extCoproductIso X _ _).hom =
      (extCoproductIso _ _ _).hom ≫
        Pi.lift fun j => Pi.π _ (ULift.up (ULift.down j + 1)) ≫ ((ext i).map (e _).op).app Y :=
  by
  dsimp only [Ext_coproduct_iso, Ext, Ext0, Ext_iso, functor.comp_map, whiskering_left,
    whisker_left, iso.trans_hom, functor.map_iso, preadditive_yoneda_coproduct_iso, functor.flip,
    pi_iso, as_iso, preadditive_yoneda_coproduct_to_product]
  simp only [category.assoc]
  simp only [Quiver.Hom.unop_op, iso.op_hom, replacement_iso_hom, iso.op_inv, replacement_iso_inv,
    iso.symm_mk]
  apply limit.hom_ext
  intro j
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc]
  simp only [← functor.map_comp, ← op_comp]
  congr 2
  simp only [category.assoc]
  apply lift_ext (∐ X).π; swap; infer_instance
  dsimp [Quiver.Hom.unop_op]
  simp only [category.assoc, lift_lifts, lift_lifts_assoc]
  dsimp [uniform_π, coproductShift]
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc, lift_lifts_assoc]

