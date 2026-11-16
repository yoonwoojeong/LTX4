import LiquidTensorExperiment.Lbar.ExtAux1

#align_import Lbar.ext_aux2

noncomputable section

universe v u u'

open Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

open scoped NNReal ZeroObject

variable (r r' : ℝ≥0)

variable [Fact (0 < r)] [Fact (r < r')] [Fact (r < 1)]

section

open BoundedHomotopyCategory

variable (BD : BreenDeligne.Data)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (V : SemiNormedGroupCat.{u})

theorem qprimeFP_map (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) :
    (qprimeFP r' BD κ M).map h = of'Hom ((qprimeFPInt r' BD κ _).map h) :=
  rfl

instance aaahrg (X : Profinite) : SeminormedAddCommGroup (LocallyConstant X V) :=
  LocallyConstant.seminormedAddCommGroup

def vTInv (r : ℝ≥0) (V : SemiNormedGroupCat.{u}) [NormedWithAut r V] : V ⟶ V :=
  NormedWithAut.t.{u}.inv

variable [Fact (0 < r')] [Fact (r' < 1)]

section

variable [CompleteSpace V] [SeparatedSpace V]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem final_boss_aux₁ (X : Profinite) (x) :
    (lCCIsoCondOfTopAbAddEquiv.{u} X V).symm x = (lCCIsoCondOfTopAbEquiv X V).symm x :=
  rfl

theorem final_boss_aux₂ [NormedWithAut r V] (X : Profinite) (x : LocallyConstant X V) :
    (LocallyConstant.mapHom.{u, u, u} (vTInv r V)).Completion
        (UniformSpace.Completion.cPkg.{u}.coe x) =
      UniformSpace.Completion.map (LocallyConstant.mapHom (vTInv r V)) x :=
  rfl

-- should this be a global instance earlier in mathlib?
attribute [local instance] AbstractCompletion.uniformStruct

theorem final_boss_aux₃ [NormedWithAut r V] (X : Profinite) :
    Continuous.{u, u} fun x : C(X, V) =>
      (LocallyConstant.mapHom.{u, u, u} NormedWithAut.t.{u}.inv).Completion
        ((UniformSpace.Completion.cPkg.{u}.compareEquiv (LocallyConstant.pkg.{u} X ↥V)).symm x) :=
  by
  dsimp [AbstractCompletion.compareEquiv]
  refine' (NormedAddGroupHom.continuous _).comp _
  refine' ((LocallyConstant.pkg X V).uniformContinuous_compare _).continuous

example {β : Type _} [UniformSpace β] (a : AbstractCompletion β) : UniformSpace a.Space := by
  infer_instance

theorem final_boss_aux₄ [NormedWithAut r V] (X : Profinite) :
    @Continuous.{u, u} _ _ _ UniformSpace.Completion.cPkg.uniformStruct.toTopologicalSpace
      fun x : C(X, V) =>
      (LocallyConstant.pkg X V).compare UniformSpace.Completion.cPkg.{u}
        { toFun := vTInv r V ∘ x.toFun
          continuous_toFun := NormedWithAut.t.inv.continuous.comp x.2 } :=
  by
  let e : C(X, V) → C(X, V) := fun e => ⟨vTInv r V ∘ e, (vTInv r V).continuous.comp e.2⟩
  have he : Continuous e :=
    ContinuousMap.continuous_comp (⟨vTInv r V, (vTInv r V).continuous⟩ : C(V, V))
  refine' Continuous.comp _ he
  refine' ((LocallyConstant.pkg X V).uniformContinuous_compare _).continuous

theorem final_boss [NormedWithAut r V] (X : Profinite)
    (x : (Condensed.OfTopAb.presheaf V).obj (op X)) :
    (LocallyConstant.mapHom (vTInv r V)).Completion ((lCCIsoCondOfTopAbAddEquiv X V).symm x) =
      (lCCIsoCondOfTopAbAddEquiv X V).symm
        { toFun := NormedWithAut.t.inv ∘ x.1
          continuous_toFun := NormedWithAut.t.inv.continuous.comp x.2 } :=
  by
  rw [final_boss_aux₁]
  rw [final_boss_aux₁]
  dsimp only [vTInv]
  dsimp only [lCCIsoCondOfTopAbEquiv]
  change C(X, V) at x 
  apply AbstractCompletion.induction_on (LocallyConstant.pkg.{u} X ↥V) x
  · apply isClosed_eq
    · apply final_boss_aux₃
    · apply final_boss_aux₄
  clear x
  intro x
  change
    (LocallyConstant.mapHom.{u, u, u} NormedWithAut.t.{u}.inv).Completion
        ((LocallyConstant.pkg.{u} X ↥V).compare UniformSpace.Completion.cPkg.{u}
          ((LocallyConstant.pkg.{u} X ↥V).coe x)) =
      _
  --dsimp [abstract_completion.compare_equiv],
  rw [AbstractCompletion.compare_coe]
  erw [final_boss_aux₂]
  erw [UniformSpace.Completion.map_coe]
  let q : C(X, V) :=
    { toFun := NormedWithAut.t.{u}.inv ∘ ((LocallyConstant.pkg.{u} X ↥V).coe x).toFun
      continuous_toFun := _ }
  swap
  · apply Continuous.comp
    apply NormedAddGroupHom.continuous
    refine' ((LocallyConstant.pkg.{u} X ↥V).coe x).2
  have hq :
    q = (LocallyConstant.pkg X V).coe ((LocallyConstant.mapHom.{u, u, u} (vTInv.{u} r V)) x) := by
    ext; rfl
  change _ = ((LocallyConstant.pkg.{u} X ↥V).compare UniformSpace.Completion.cPkg) q
  rw [hq]
  rw [AbstractCompletion.compare_coe]
  rfl
  apply NormedAddGroupHom.uniformContinuous

end

@[reassoc]
theorem massive_aux₁ (X Y : Profinite.{u}) (f : X ⟶ Y) :
    (preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).map (freeCond.{u}.map f).op ≫
        (preadditiveYonedaObjObjCondensedSetToCondensedAb.{u} V.toCond X).hom =
      (preadditiveYonedaObjObjCondensedSetToCondensedAb.{u} V.toCond Y).hom ≫
        V.toCond.val.map f.op :=
  by
  erw [preadditiveYonedaObjObjCondensedSetToCondensedAb_natural']
  rfl

theorem AddEquiv.mk_symm {A B : Type _} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (g : B →+ A)
    (h1 h2 h3) :
    (AddEquiv.mk f g h1 h2 h3).symm =
      AddEquiv.mk g f h2 h1 (by intro x y; apply h1.injective; rw [h3, h2, h2, h2]) :=
  rfl

theorem AddEquiv.mk_symm_apply {A B : Type _} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (g : B →+ A) (h1 h2 h3) (x : B) : (AddEquiv.mk f g h1 h2 h3).symm x = g x :=
  rfl

theorem LocallyConstant.comapHom_mapHom {X Y V W : Type _} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [SeminormedAddCommGroup V] [SeminormedAddCommGroup W]
    (f : X → Y) (hf : Continuous f) (g : NormedAddGroupHom V W) (φ : LocallyConstant Y V) :
    LocallyConstant.comapHom f hf (LocallyConstant.mapHom g φ) =
      (LocallyConstant.mapHom g ∘ LocallyConstant.comapHom f hf) φ :=
  by
  dsimp only [LocallyConstant.comapHom_apply, LocallyConstant.mapHom_apply, Function.comp]
  rw [LocallyConstant.comap_map]
  exact hf

instance (X : Profinite) : UniformSpace.{u} (LocallyConstant.{u, u} X V) :=
  @PseudoMetricSpace.toUniformSpace.{u}
    (@LocallyConstant.{u, u}
      (@coeSort.{u + 2, u + 2} Profinite.{u} (Type u) Profinite.hasCoeToSort.{u} X)
      (@coeSort.{u + 2, u + 2} SemiNormedGroupCat.{u} (Type u) SemiNormedGroupCat.hasCoeToSort.{u}
        V)
      (TopCat.topologicalSpace.{u} X.toCompHaus.toTop))
    (@SeminormedAddCommGroup.toPseudoMetricSpace.{u}
      (@LocallyConstant.{u, u}
        (@coeSort.{u + 2, u + 2} Profinite.{u} (Type u) Profinite.hasCoeToSort.{u} X)
        (@coeSort.{u + 2, u + 2} SemiNormedGroupCat.{u} (Type u) SemiNormedGroupCat.hasCoeToSort.{u}
          V)
        (TopCat.topologicalSpace.{u} X.toCompHaus.toTop))
      LocallyConstant.seminormedAddCommGroup)

instance (X : Profinite) : TopologicalSpace ↥(V.toCond.val.obj (op X)) :=
  @ULift.topologicalSpace _ ContinuousMap.compactOpen.{u, u}

variable [CompleteSpace V] [SeparatedSpace V]

theorem toCond_val_map_apply (X Y : Profinite.{u}) (f : X ⟶ Y) (x) :
    V.toCond.val.map f.op x = ⟨ContinuousMap.compRightContinuousMap V f x.down⟩ :=
  rfl

theorem toCond_val_map (X Y : Profinite.{u}) (f : X ⟶ Y) :
    ⇑(V.toCond.val.map f.op) =
      (fun x => ⟨ContinuousMap.compRightContinuousMap V f x.down⟩ :
        ↥(V.toCond.val.obj (op Y)) → ↥(V.toCond.val.obj (op X))) :=
  by ext x; rw [toCond_val_map_apply]

theorem massive_aux₂ (X Y : Profinite.{u}) (f : X ⟶ Y) (x : V.toCond.val.obj (op.{u + 2} Y)) :
    UniformSpace.Completion.map.{u, u} (LocallyConstant.comapHom.{u, u, u} f f.continuous)
        ((LocallyConstant.pkg.{u} Y ↥V).compare UniformSpace.Completion.cPkg.{u} x.down) =
      ((LocallyConstant.pkg.{u} X ↥V).compare UniformSpace.Completion.cPkg.{u})
        ((V.toCond.val.map f.op) x).down :=
  by
  cases x
  apply AbstractCompletion.induction_on (LocallyConstant.pkg.{u} Y V) x
  · apply isClosed_eq
    · apply uniform_space.completion.continuous_map.comp
      apply (AbstractCompletion.uniformContinuous_compare _ _).continuous
    · apply (AbstractCompletion.uniformContinuous_compare _ _).continuous.comp
      let φ : C(Y, V) → C(X, V) := _; change Continuous φ
      let ψ := V.to_Cond.val.map f.op; have hψ : φ = ULift.down ∘ ψ ∘ ULift.up := rfl
      rw [hψ]; clear hψ
      refine' continuous_induced_dom.comp _
      refine' Continuous.comp _ continuous_uLift_up
      rw [toCond_val_map]
      refine' Continuous.comp _ _; · exact continuous_uLift_up
      dsimp only [Condensed.ofTopAb, Condensed.OfTopAb.presheaf]
      exact
        (map_continuous (ContinuousMap.compRightContinuousMap (↥V) f)).comp continuous_induced_dom
  · intro φ
    dsimp only
    simp only [AbstractCompletion.compare_coe, toCond_val_map_apply, UniformSpace.Completion.map]
    rw [AbstractCompletion.map_coe]
    swap
    · let this.1 : SeminormedAddCommGroup (LocallyConstant (↥X.to_CompHaus.toTop) ↥V) :=
        LocallyConstant.seminormedAddCommGroup
      let this.1 : SeminormedAddCommGroup (LocallyConstant (↥Y.to_CompHaus.toTop) ↥V) :=
        LocallyConstant.seminormedAddCommGroup
      exact NormedAddGroupHom.uniformContinuous _
    have :
      (ContinuousMap.compRightContinuousMap (↥V) f) ((LocallyConstant.pkg Y V).coe φ) =
        (LocallyConstant.pkg X V).coe _ :=
      _
    rw [this, AbstractCompletion.compare_coe]
    ext1
    erw [LocallyConstant.coe_comap]
    rfl
    exact f.continuous

theorem massive_aux (X Y : Profinite.{u}) (f : X ⟶ Y) :
    (preadditiveYonedaObjObjCondensedSetToCondensedAb.{u} V.toCond Y).hom ≫
        Ab.ulift.{u + 1, u}.map ((lCCIsoCondOfTopAb.{u} V).inv.app (op.{u + 2} Y)) ≫
          (extQprimeIsoAuxSystemObjAux'.{u} V Y).hom ≫
            (forget₂.{u + 2, u + 2, u + 1, u + 1, u + 1} SemiNormedGroupCat.{u + 1} Ab.{u + 1}).map
              ((FreeAb.eval.{u + 1, u + 2} SemiNormedGroupCat.{u + 1}ᵒᵖ).map
                  ((cLC.{u + 1, u}
                            (SemiNormedGroupCat.ulift.{u + 1, u}.obj V)).rightOp.mapFreeAb.map
                    ((FreeAb.ofFunctor.{u + 1, u} Profinite.{u}).map f))).unop =
      (preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).map
          ((FreeAb.eval.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})).map
              (freeCond.{u}.mapFreeAb.map ((FreeAb.ofFunctor.{u + 1, u} Profinite.{u}).map f))).op ≫
        (preadditiveYonedaObjObjCondensedSetToCondensedAb.{u} V.toCond X).hom ≫
          Ab.ulift.{u + 1, u}.map ((lCCIsoCondOfTopAb.{u} V).inv.app (op.{u + 2} X)) ≫
            (extQprimeIsoAuxSystemObjAux'.{u} V X).hom :=
  by
  dsimp only [Functor.mapFreeAb, FreeAb.ofFunctor, FreeAb.eval]
  simp only [FreeAbelianGroup.map_of_apply, FreeAbelianGroup.lift.of, id]
  dsimp only [Functor.rightOp_map, Quiver.Hom.op_unop, Quiver.Hom.unop_op]
  rw [massive_aux₁_assoc]; congr 1
  ext1 x; simp only [comp_apply]
  dsimp only [extQprimeIsoAuxSystemObjAux', lCCIsoCondOfTopAb, lCCIsoCondOfTopAbAddEquiv,
    lCCIsoCondOfTopAbEquiv, cLC, lC, Functor.comp_map, Condensed.ofTopAb]
  simp only [AddEquiv.to_fun_eq_coe, NormedAddGroupHom.completion_coe_to_fun,
    AddEquiv.to_AddCommGroup_iso_hom, AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
    AddEquiv.uLift_apply, Equiv.toFun_as_coe, Equiv.uLift_apply_2, Ab.uLift_map_apply_down,
    AddEquiv.coe_mk, NatIso.ofComponents_inv_app, AddEquiv.toAddCommGroupCatIso, AddEquiv.mk_symm,
    SemiNormedGroupCat.forget₂_ab_map, NormedAddGroupHom.coe_toAddMonoidHom]
  let F :=
    SemiNormedGroupCat.completion.{u + 1}.map
      ((SemiNormedGroupCat.locallyConstant.{u + 1, u}.obj
            (SemiNormedGroupCat.ulift.{u + 1, u}.obj V)).map
        f.op)
  let g := _
  let Z := _
  change F ((UniformSpace.Completion.map g) Z) = _
  change (F ∘ UniformSpace.Completion.map g) Z = _
  erw [UniformSpace.Completion.map_comp]
  rotate_left
  · apply NormedAddGroupHom.uniformContinuous
  · apply NormedAddGroupHom.uniformContinuous
  conv_lhs =>
    dsimp only [Function.comp, NormedAddGroupHom.coe_toAddMonoidHom, g,
      SemiNormedGroupCat.locallyConstant_obj_map]
  simp only [LocallyConstant.comapHom_mapHom]
  letI : UniformSpace.{u} (LocallyConstant.{u, u} (↥(unop.{u + 2} (op.{u + 2} X))) ↥V) := _
  erw [← UniformSpace.Completion.map_comp]
  rotate_left
  · apply NormedAddGroupHom.uniformContinuous
  · apply NormedAddGroupHom.uniformContinuous
  dsimp only [Function.comp, Z, Quiver.Hom.unop_op]
  congr 1; clear Z g F
  exact massive_aux₂ V X Y f x

theorem massive (X Y : FreeAb Profinite.{u}) (f : X ⟶ Y) :
    (((preadditiveYonedaObjObjCondensedSetToCondensedAb.{u} V.toCond Y.as).hom ≫
            (condensedAbToPresheaf.{u}.map (condensedLCCIsoOfTopAb.{u} V).inv).app
                (op.{u + 2} Y.as) ≫
              (extQprimeIsoAuxSystemObjAux'.{u} V Y.as).hom) ≫
          𝟙 _) ≫
        (forget₂.{u + 2, u + 2, u + 1, u + 1, u + 1} SemiNormedGroupCat.{u + 1} Ab.{u + 1}).map
          (((cLC.{u + 1, u} (SemiNormedGroupCat.ulift.{u + 1, u}.obj V)).rightOp.mapFreeAb ⋙
                  FreeAb.eval.{u + 1, u + 2} SemiNormedGroupCat.{u + 1}ᵒᵖ).map
              f).unop =
      (preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).map
          ((freeCond.{u}.mapFreeAb ⋙
                  FreeAb.eval.{u + 1, u + 2} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})).map
              f).op ≫
        ((preadditiveYonedaObjObjCondensedSetToCondensedAb.{u} V.toCond X.as).hom ≫
            (condensedAbToPresheaf.{u}.map (condensedLCCIsoOfTopAb.{u} V).inv).app
                (op.{u + 2} X.as) ≫
              (extQprimeIsoAuxSystemObjAux'.{u} V X.as).hom) ≫
          𝟙 _ :=
  by
  simp only [condensedAbToPresheaf_map, Category.assoc, Category.comp_id, Functor.comp_map]
  dsimp only [condensedLCCIsoOfTopAb, Sheaf.Iso.mk_inv_val, CategoryTheory.isoWhiskerRight_inv,
    CategoryTheory.whiskerRight_app]
  apply FreeAbelianGroup.induction_on f <;> clear f
  · simp only [Functor.map_zero, unop_zero, comp_zero, op_zero, zero_comp]
  · apply massive_aux
  · intro f hf
    simp only [Functor.map_neg, unop_neg, op_neg, comp_neg, neg_comp, hf]
  · intro f g hf hg
    simp only [Functor.map_add, unop_add, op_add, comp_add, add_comp, hf, hg]

theorem homComplexQprimeFPNatIsoAuxSystem_naturality_in_c (c₁ c₂) (h : c₁ ⟶ c₂) :
    (homComplexQprimeFPNatIsoAuxSystem r' BD κ M V c₂).hom ≫ CategoryTheory.Functor.map _ h.op =
      CategoryTheory.Functor.map _
          (by
            refine' homological_complex.op_functor.map (Quiver.Hom.op _)
            refine' CategoryTheory.Functor.map _ h) ≫
        (homComplexQprimeFPNatIsoAuxSystem r' BD κ M V c₁).hom :=
  by
  ext n : 2
  have aux : ∀ n : ℕ, Monotone.{0, 0} (Function.swap.{1, 1, 1} κ n) := by intro n; exact Fact.out _
  haveI : Fact (κ c₁ n ≤ κ c₂ n) := ⟨aux n h.le⟩
  have :=
    massive V (BreenDeligne.FPsystem.x.{u} r' BD ⟨M⟩ κ c₁ n)
      (BreenDeligne.FPsystem.x.{u} r' BD ⟨M⟩ κ c₂ n) ((BreenDeligne.fP2.res.{u} r' _ _ _).app ⟨M⟩)
  exact this

theorem homComplexQprimeFPNatIsoAuxSystem_naturality_in_κ (c : ℝ≥0)
    [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ κ c n)] :
    (homComplexQprimeFPNatIsoAuxSystem r' BD κ M V c).hom ≫
        (whiskerRight (auxSystem.res _ _ _ _ _ _) _).app _ =
      by
        refine' CategoryTheory.Functor.map _ _
        refine' homological_complex.op_functor.map (Quiver.Hom.op _)
        refine' (qprimeFPNat.ι BD κ₂ κ M).app _ ≫
        (homComplexQprimeFPNatIsoAuxSystem r' BD κ₂ M V c).hom :=
  by
  ext n : 2
  have :=
    massive V (BreenDeligne.FPsystem.x.{u} r' BD ⟨M⟩ κ₂ c n)
      (BreenDeligne.FPsystem.x.{u} r' BD ⟨M⟩ κ c n) ((BreenDeligne.fP2.res.{u} r' _ _ _).app ⟨M⟩)
  exact this

theorem homComplexQprimeFPNatIsoAuxSystem_naturality_in_tinv (c : ℝ≥0)
    [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ r' * κ c n)] :
    (homComplexQprimeFPNatIsoAuxSystem r' BD κ M V c).hom ≫
        (whiskerRight (auxSystem.tinv _ _ _ _ _ _) _).app _ =
      by
        refine' CategoryTheory.Functor.map _ _
        refine' homological_complex.op_functor.map (Quiver.Hom.op _)
        refine' (qprimeFPNat.tinv BD κ₂ κ M).app _ ≫
        (homComplexQprimeFPNatIsoAuxSystem r' BD κ₂ M V c).hom :=
  by
  ext n : 2
  have :=
    massive V (BreenDeligne.FPsystem.x.{u} r' BD ⟨M⟩ κ₂ c n)
      (BreenDeligne.FPsystem.x.{u} r' BD ⟨M⟩ κ c n)
      (((BreenDeligne.fPsystem.tinv.{u} r' BD ⟨M⟩ κ₂ κ).app c).f n)
  exact this

def toCondTInv (r : ℝ≥0) (V : SemiNormedGroupCat.{u}) [NormedWithAut r V] : V.toCond ⟶ V.toCond :=
  Condensed.ofTopAbMap.{u} (NormedAddGroupHom.toAddMonoidHom.{u, u} NormedWithAut.t.{u}.inv)
    (NormedAddGroupHom.continuous _)

theorem UniformSpace.Completion.map_comp' {α β γ : Type _} [UniformSpace α] [UniformSpace β]
    [UniformSpace γ] {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f)
    (x) :
    UniformSpace.Completion.map g (UniformSpace.Completion.map f x) =
      UniformSpace.Completion.map (g ∘ f) x :=
  by rw [← UniformSpace.Completion.map_comp hg hf]

theorem hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_T_inv_aux_helper (r : ℝ≥0)
    (V : SemiNormedGroupCat.{u}) [NormedWithAut r V] [CompleteSpace V] [SeparatedSpace V]
    (X : Profinite.{u}) :
    (extQprimeIsoAuxSystemObjAux' V X).hom ≫
        CategoryTheory.Functor.map _
          (SemiNormedGroupCat.completion.map
            (NatTrans.app
              (SemiNormedGroupCat.locallyConstant.map (CategoryTheory.Functor.map _ <| vTInv _ _))
              _)) =
      Ab.ulift.map
          (CategoryTheory.Functor.map _ <|
            CategoryTheory.Functor.map _ <|
              NatTrans.app (SemiNormedGroupCat.locallyConstant.map <| vTInv _ _) _) ≫
        (extQprimeIsoAuxSystemObjAux' V X).hom :=
  by
  ext1 ⟨f⟩
  simp only [comp_apply]
  dsimp only [extQprimeIsoAuxSystemObjAux', AddEquiv.toAddCommGroupCatIso,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply]
  simp only [AddEquiv.to_fun_eq_coe, SemiNormedGroupCat.locallyConstant_map_app,
    SemiNormedGroupCat.completion_map, NormedAddGroupHom.completion_coe_to_fun,
    AddEquiv.uLift_apply, Equiv.toFun_as_coe, Equiv.uLift_apply_2, AddEquiv.coe_mk,
    Ab.uLift_map_apply_down, SemiNormedGroupCat.forget₂_ab_map,
    NormedAddGroupHom.coe_toAddMonoidHom]
  rw [UniformSpace.Completion.map_comp']
  rotate_left
  · apply NormedAddGroupHom.uniformContinuous
  · apply NormedAddGroupHom.uniformContinuous
  rw [UniformSpace.Completion.map_comp']
  rotate_left
  · apply NormedAddGroupHom.uniformContinuous
  · apply NormedAddGroupHom.uniformContinuous
  rfl

theorem another_aux_lemma [NormedWithAut r V] (X : Profinite) :
    ((preadditiveYonedaObjObjCondensedSetToCondensedAb V.toCond X).hom ≫
        (condensedAbToPresheaf.mapIso (condensedLCCIsoOfTopAb V)).inv.app (op X) ≫
          by
          refine' NatTrans.app _ _
          refine' Condensed_Ab_to_presheaf.map _
          refine' Sheaf.Hom.mk _
          dsimp [condensedLCC]
          refine' whisker_right _ _
          refine' whisker_right _ _
          refine' SemiNormedGroup.LCC.map _
          exact vTInv r V) =
      (preadditiveYoneda.map (toCondTInv r V)).app _ ≫
        (preadditiveYonedaObjObjCondensedSetToCondensedAb V.toCond X).hom ≫
          (condensedAbToPresheaf.mapIso (condensedLCCIsoOfTopAb V)).inv.app _ :=
  by
  have := preadditiveYonedaObjObjCondensedSetToCondensedAb_natural (toCondTInv r V) X
  erw [← reassoc_of this]
  congr 1
  dsimp only [condensedAbToPresheaf, Functor.mapIso_inv, NatIso.app_inv, Sheaf_to_presheaf_map,
    id, CategoryTheory.whiskerRight_app, SemiNormedGroupCat.lCC, curry, uncurry, CategoryTheory.curryObj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← NatTrans.comp_app]
  rw [← Sheaf.Hom.comp_val]
  -- how to make those commute?
  ext ⟨x⟩
  dsimp only [condensedLCCIsoOfTopAb, Sheaf.Iso.mk, CategoryTheory.isoWhiskerRight, toCondTInv, Ab.ulift]
  simp only [comp_apply]
  dsimp [Condensed.ofTopAbMap]
  simp only [comp_apply]
  dsimp [lCCIsoCondOfTopAb, forget₂, HasForget₂.forget₂]
  apply final_boss

theorem hom_complex_QprimeFP_nat_iso_auxSystem_naturality_in_tInv_aux (c : ℝ≥0) [NormedWithAut r V]
    (n : ℕ) (t) :
    ((forget₂.{u + 2, u + 2, u + 1, u + 1, u + 1} SemiNormedGroupCat.{u + 1} Ab.{u + 1}).map
          (((auxSystem.tInv.{u, u + 1} r r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V)
                    κ).app
                (op.{1} c)).f
            n))
        (((extQprimeIsoAuxSystemObjAux.{u} V).hom.app
              (((BreenDeligne.fPsystem.{u} r' BD ⟨M⟩ κ).obj c).pt n)).unop
          t) =
      ((extQprimeIsoAuxSystemObjAux.{u} V).hom.app
            (((BreenDeligne.fPsystem.{u} r' BD ⟨M⟩ κ).obj c).pt n)).unop
        (t ≫ toCondTInv.{u} r V) :=
  by
  /-
    Note: This should reduce to some calcuation with the sheafification adjunction,
    as well as something about completion/ulift compatibiity.
    If we can reduce this to such statements, we will be in pretty good shape.
    -/
  /- This code block is pretty slow.
    dsimp [ExtQprime_iso_aux_system_obj_aux, ExtQprime_iso_aux_system_obj_aux'],
    simp only [comp_apply],
    dsimp [forget₂, has_forget₂.forget₂, aux_system.T_inv,
      Condensed_LCC_iso_of_top_ab, LCC_iso_Cond_of_top_ab],
    rw nat_iso.of_components_inv_app,
    dsimp only [unop_op],
    -/
  dsimp only [forget₂, HasForget₂.forget₂, extQprimeIsoAuxSystemObjAux,
    NatIso.ofComponents_hom_app, id, Iso.op, Iso.trans_hom, iso.symm, NatIso.app_inv,
    auxSystem.tInv, Quiver.Hom.op_unop, Quiver.Hom.unop_op, HomologicalComplex.unop]
  simp only [comp_apply]
  let X : Profinite := (((BreenDeligne.fPsystem r' BD ⟨M⟩ κ).obj c).pt n).as
  have := preadditiveYonedaObjObjCondensedSetToCondensedAb_natural (toCondTInv r V) X
  apply_fun fun e => e t at this 
  erw [this]; clear this
  simp only [comp_apply]
  dsimp only [SemiNormedGroupCat.locallyConstant]
  have := hom_complex_QprimeFP_nat_iso_aux_system_naturality_in_T_inv_aux_helper r V X
  let s :=
    ((Condensed_Ab_to_presheaf.map_iso (condensedLCCIsoOfTopAb V)).inv.app (op X))
      ((preadditiveYonedaObjObjCondensedSetToCondensedAb V.to_Cond X).hom t)
  apply_fun fun e => e s at this 
  erw [this]; clear this
  simp only [comp_apply]
  congr 1; dsimp only [s]
  simp only [← comp_apply]
  congr 1
  simp only [Category.assoc]
  erw [← another_aux_lemma r V X]
  congr 2
  ext1 ⟨x⟩; dsimp only [Ab.ulift, condensedAbToPresheaf, CategoryTheory.whiskerRight_app, Sheaf_to_presheaf]
  ext1
  dsimp
  congr 2
  dsimp only [SemiNormedGroupCat.lCC, curry, CategoryTheory.curryObj, Functor.comp_map, uncurry]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem homComplexQprimeFPNatIsoAuxSystem_naturality_in_tInv (c : ℝ≥0) [NormedWithAut r V] :
    (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ M V c).hom ≫
        ((forget₂.{u + 2, u + 2, u + 1, u + 1, u + 1} SemiNormedGroupCat.{u + 1}
                  Ab.{u + 1}).mapHomologicalComplex
              (ComplexShape.up.{0} ℕ)).map
          (NatTrans.app
            (auxSystem.tInv.{u, u + 1} r r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V) κ)
            _) =
      by
        let e := preadditive_yoneda.map (toCondTInv r V)
        let e' := NatTrans.mapHomologicalComplex e (ComplexShape.down ℕ).symm
        let Q := ((qprimeFPNat r' BD κ M).obj c).op
        exact e'.app Q ≫ (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ M V c).hom :=
  by
  ext n : 2; ext1 t
  dsimp [homComplexQprimeFPNatIsoAuxSystem]
  simp only [comp_apply]
  dsimp [NatIso.mapHomologicalComplex, forget₂Unop]
  erw [id_apply]; erw [id_apply]
  erw [Functor.mapHomologicalComplex_map_f]
  apply hom_complex_QprimeFP_nat_iso_auxSystem_naturality_in_tInv_aux

namespace ExtQprimeIsoAuxSystemObjNaturalitySetup

/-
lemma aux₁ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) :
homological_complex.unop_functor.{u+2 u+1 0}.map
    (((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
         forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
           AddCommGroup.{u+1}).right_op.map_homological_complex
        (complex_shape.up.{0} ℤ)).map
       ((homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_down_int_up).map
          ((QprimeFP_nat.{u} r' BD κ M).map h))).op ≫
  homological_complex.unop_functor.{u+2 u+1 0}.map
      ((map_homological_complex_embed.{u+2 u+2 u+1 u+1}
          (preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
             forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
               AddCommGroup.{u+1}).right_op).inv.app
         ((QprimeFP_nat.{u} r' BD κ M).obj c₁)).op ≫
    embed_unop.{u+2 u+1}.hom.app
      (op.{u+3}
         (((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
              forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
                Ab.{u+1}).right_op.map_homological_complex
             (complex_shape.down.{0} ℕ)).obj
            ((QprimeFP_nat.{u} r' BD κ M).obj c₁))) =
  begin
    dsimp,
    let e := (QprimeFP_nat r' BD κ M).map h,
    let e₁ := ((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
      forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
      Ab.{u+1}).right_op.map_homological_complex
      (complex_shape.down.{0} ℕ)).map e,
    let e₂ := homological_complex.unop_functor.map e₁.op,
    refine _ ≫
      (homological_complex.embed.{0 0 u+2 u+1} complex_shape.embedding.nat_up_int_down).map
      e₂,
    refine homological_complex.unop_functor.{u+2 u+1 0}.map
    ((map_homological_complex_embed.{u+2 u+2 u+1 u+1}
        (preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
           forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
             AddCommGroup.{u+1}).right_op).inv.app
       ((QprimeFP_nat.{u} r' BD κ M).obj c₂)).op ≫
    embed_unop.{u+2 u+1}.hom.app
    (op.{u+3}
       (((preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
            forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
              Ab.{u+1}).right_op.map_homological_complex
           (complex_shape.down.{0} ℕ)).obj
          ((QprimeFP_nat.{u} r' BD κ M).obj c₂)))
  end := admit

def F : ℝ≥0 ⥤
  (homological_complex.{u+1 u+2 0} AddCommGroup.{u+1} (complex_shape.down.{0} ℕ).symm)ᵒᵖ :=
QprimeFP_nat.{u} r' BD κ M ⋙
  (preadditive_yoneda_obj.{u+1 u+2} V.to_Cond ⋙
     forget₂.{u+2 u+2 u+1 u+1 u+1} (Module.{u+1 u+1} (End.{u+1 u+2} V.to_Cond))
       AddCommGroup.{u+1}).right_op.map_homological_complex
    (complex_shape.down.{0} ℕ) ⋙ homological_complex.unop_functor.right_op

@[reassoc]
lemma naturality_helper {c₁ c₂ : ℝ≥0} (h : c₁ ⟶ c₂) (n : ℕ) (w1 w2) :
  (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1} complex_shape.embedding.nat_up_int_down
   nat_up_int_down_c_iff n (-↑n) w1).hom.app
    (((preadditive_yoneda.{u+1 u+2}.obj
    V.to_Cond).right_op.map_homological_complex (complex_shape.down.{0} ℕ)).obj
     ((QprimeFP_nat.{u} r' BD κ M).obj c₂)).unop ≫
     (homology_functor _ _ _).map
     (homological_complex.map_unop _ _ $
     category_theory.functor.map _ $ category_theory.functor.map _ h) =
  category_theory.functor.map _
  (homological_complex.map_unop _ _ $
    category_theory.functor.map _ $ category_theory.functor.map _ h) ≫
    (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1} complex_shape.embedding.nat_up_int_down
  nat_up_int_down_c_iff n (-↑n) w2).hom.app
    (((preadditive_yoneda.{u+1 u+2}.obj
    V.to_Cond).right_op.map_homological_complex (complex_shape.down.{0} ℕ)).obj
    ((QprimeFP_nat.{u} r' BD κ M).obj c₁)).unop :=
admit
-/
theorem aux₁ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
    (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ M V c₂).hom ≫
        (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          ((auxSystem.{u, u + 1} r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V) κ).toAb.map
            h.op) =
      (homology'Functor _ _ _).map
          (CategoryTheory.Functor.map _
            (HomologicalComplex.opFunctor.map ((qprimeFPNat r' BD κ M).map h).op)) ≫
        (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ M V c₁).hom :=
  by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  erw [← homComplexQprimeFPNatIsoAuxSystem_naturality_in_c]

theorem aux₂ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
    (HomologicalComplex.homologyEmbedNatIso.{0, 0, u + 2, u + 1} Ab.{u + 1}
                ComplexShape.Embedding.natUpIntDown n (-↑n) (by cases n <;> rfl)).hom.app
          (homComplexNat.{u} ((qprimeFPNat.{u} r' BD κ M).obj c₂) V.toCond) ≫
        (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          (((preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).mapHomologicalComplex
                (ComplexShape.down.{0} ℕ).symm).map
            (HomologicalComplex.opFunctor.{u + 2, u + 1, 0}.map
              ((qprimeFPNat.{u} r' BD κ M).map h).op)) =
      (HomologicalComplex.embed.{0, 0, u + 2, u + 1} ComplexShape.Embedding.natUpIntDown ⋙
              homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.down.{0} ℤ) (-↑n)).map
          (CategoryTheory.Functor.map _
            (HomologicalComplex.opFunctor.map ((qprimeFPNat r' BD κ M).map h).op)) ≫
        (HomologicalComplex.homologyEmbedNatIso.{0, 0, u + 2, u + 1} Ab.{u + 1}
                ComplexShape.Embedding.natUpIntDown n (-↑n) (by cases n <;> rfl)).hom.app
          (homComplexNat.{u} ((qprimeFPNat.{u} r' BD κ M).obj c₁) V.toCond) :=
  by erw [NatTrans.naturality]

theorem aux₃ (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
    (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℤ).symm (-↑n)).map
          (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ M).obj c₂) V.toCond).hom ≫
        (HomologicalComplex.embed.{0, 0, u + 2, u + 1} ComplexShape.Embedding.natUpIntDown ⋙
              homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.down.{0} ℤ) (-↑n)).map
          (((preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).mapHomologicalComplex
                (ComplexShape.down.{0} ℕ).symm).map
            (HomologicalComplex.opFunctor.{u + 2, u + 1, 0}.map
              ((qprimeFPNat.{u} r' BD κ M).map h).op)) =
      ((homology'Functor.{u + 1, u + 2, 0} AddCommGroupCat.{u + 1} (ComplexShape.up.{0} ℤ).symm
                  (-↑n)).op.map
            (HomologicalComplex.unopFunctor.{u + 2, u + 1, 0}.rightOp.map
              (((preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).rightOp.mapHomologicalComplex
                    (ComplexShape.up.{0} ℤ)).map
                ((qprimeFPInt.{u} r' BD κ M).map h)))).unop ≫
        (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℤ).symm (-↑n)).map
          (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ M).obj c₁) V.toCond).hom :=
  by
  dsimp only [Functor.op_map, Functor.comp_map]
  erw [← Functor.map_comp]
  erw [← Functor.map_comp]
  congr 1
  ext ((_ | k) | k) : 2
  · refine' (Category.id_comp _).trans (Category.comp_id _).symm
  · apply IsZero.eq_of_tgt
    exact is_zero_zero _
  · refine' (Category.id_comp _).trans (Category.comp_id _).symm

/-
lemma naturality_helper {c₂ : ℝ≥0} (n : ℕ) :
  (homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℤ).symm (-↑n)).map
  (embed_hom_complex_nat_iso.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₂) V.to_Cond).hom ≫
  (homological_complex.homology_embed_nat_iso.{0 0 u+2 u+1} Ab.{u+1}
  complex_shape.embedding.nat_up_int_down nat_up_int_down_c_iff n (-↑n) (by { cases n; refl})).hom.app
  (hom_complex_nat.{u} ((QprimeFP_nat.{u} r' BD κ M).obj c₂) V.to_Cond) =
  _
-/
end ExtQprimeIsoAuxSystemObjNaturalitySetup

theorem QprimeFP_acyclic (c) (k i : ℤ) (hi : 0 < i) :
    IsZero (((ext' i).obj (op (((qprimeFPInt.{u} r' BD κ M).obj c).pt k))).obj V.toCond) :=
  by
  rcases k with ((_ | k) | k)
  · apply free_acyclic; exact hi
  · rw [← Functor.flip_obj_obj]; refine' Functor.map_isZero _ _; refine' (is_zero_zero _).op
  · apply free_acyclic; exact hi

theorem extQprimeIsoAuxSystemObj_natrality (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (n : ℕ) :
    (extQprimeIsoAuxSystemObj r' BD κ M V c₂ n).hom ≫
        (homology'Functor _ _ _).map ((SystemOfComplexes.toAb _).map h.op) =
      ((ext n).map ((qprimeFP r' BD κ _).map h).op).app _ ≫
        (extQprimeIsoAuxSystemObj r' BD κ M V c₁ n).hom :=
  by
  dsimp only [extQprimeIsoAuxSystemObj, Iso.trans_hom, id, Functor.mapIso_hom]
  haveI :
    ((HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ)).obj
        ((qprimeFPInt.{u} r' BD κ M).obj c₁)).IsBoundedAbove :=
    ChainComplex.isBoundedAbove _
  haveI :
    ((HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ)).obj
        ((qprimeFPInt.{u} r' BD κ M).obj c₂)).IsBoundedAbove :=
    ChainComplex.isBoundedAbove _
  have :=
    extComputeWithAcyclic_naturality ((qprimeFPInt.{u} r' BD κ M).obj c₁)
      ((qprimeFPInt.{u} r' BD κ M).obj c₂) V.to_Cond _ _ ((qprimeFPInt.{u} r' BD κ M).map h) n
  rotate_left
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  dsimp only [Functor.comp_map] at this 
  erw [reassoc_of this]; clear this
  simp only [Category.assoc, NatIso.app_hom]
  congr 1
  rw [ExtQprimeIsoAuxSystemObjNaturalitySetup.aux₁ r' BD κ M V c₁ c₂ h n]
  simp only [← Category.assoc]; congr 1
  simp only [Category.assoc]
  rw [ExtQprimeIsoAuxSystemObjNaturalitySetup.aux₂ r' BD κ M V c₁ c₂ h n]
  simp only [← Category.assoc]; congr 1
  exact ExtQprimeIsoAuxSystemObjNaturalitySetup.aux₃ r' BD κ M V c₁ c₂ h n

--- OLD PROOF FROM HERE
--have := ExtQprime_iso_aux_system_obj_naturality_setup.naturality_helper r' BD κ
--  M V h n _ _,
--simp only [category.assoc, functor.map_comp],
--slice_rhs 3 4
--{ erw ← this },
/-
  dsimp only [QprimeFP_int],
  congr' 1,
  dsimp only [nat_iso.app_hom],
  simp only [functor.map_comp, functor.comp_map, nat_trans.naturality,
    nat_trans.naturality_assoc],
  dsimp only [functor.op_map, quiver.hom.unop_op, functor.right_op_map],
  simp only [← functor.map_comp, ← functor.map_comp_assoc, category.assoc],
  dsimp [-homology_functor_map],
  rw ExtQprime_iso_aux_system_obj_naturality_setup.aux₁,
  dsimp [-homology_functor_map],
  simp only [functor.map_comp, functor.map_comp_assoc,
    category.assoc, nat_trans.naturality_assoc],
  congr' 2,
  dsimp [-homology_functor_map],
  dsimp only [← functor.comp_map, ← functor.comp_obj],
  --erw nat_trans.naturality_assoc,
  --refine congr_arg2 _ _ (congr_arg2 _ rfl _),

  --congr' 1,
  --refl,
  admit

  -/
def extQprimeIsoAuxSystem (n : ℕ) :
    (qprimeFP r' BD κ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) ≅
      auxSystem r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1}.obj V) κ ⋙
        (forget₂ _ Ab).mapHomologicalComplex _ ⋙ homology'Functor _ _ n :=
  NatIso.ofComponents (fun c => extQprimeIsoAuxSystemObj r' BD κ M V (unop c) n)
    (by
      intro c₁ c₂ h
      dsimp [-homology'Functor_map]
      rw [← extQprimeIsoAuxSystemObj_natrality]
      rfl)

/-- The `Tinv` map induced by `M` -/
def ExtQprime.tinv [∀ c n, Fact (κ₂ c n ≤ κ c n)] [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (n : ℤ) :
    (qprimeFP r' BD κ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) ⟶
      (qprimeFP r' BD κ₂ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) :=
  whiskerRight (NatTrans.op <| qprimeFP.tinv BD _ _ M) _

/-- The `T_inv` map induced by `V` -/
def ExtQprime.tInv [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (n : ℤ) :
    (qprimeFP r' BD κ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) ⟶
      (qprimeFP r' BD κ₂ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) :=
  whiskerRight (NatTrans.op <| qprimeFP.ι BD _ _ M) _ ≫
    whiskerLeft _
      ((ext n).flip.map <|
        (single _ _).map <|
          Condensed.ofTopAbMap NormedWithAut.t.inv.toAddMonoidHom (NormedAddGroupHom.continuous _))

def ExtQprime.tinv2 [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (n : ℤ) :
    (qprimeFP r' BD κ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) ⟶
      (qprimeFP r' BD κ₂ M).op ⋙ (ext n).flip.obj ((single _ 0).obj V.toCond) :=
  ExtQprime.tinv r' BD κ κ₂ M V n - ExtQprime.tInv r r' BD κ κ₂ M V n

namespace ExtQprimeIsoAuxSystemCommTinvSetup

variable (c : ℝ≥0ᵒᵖ) (n : ℕ) [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ r' * κ c n)]

theorem aux₁ :
    (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ M V (unop.{1} c)).hom ≫
        ((forget₂.{u + 2, u + 2, u + 1, u + 1, u + 1} SemiNormedGroupCat.{u + 1}
                    Ab.{u + 1}).mapHomologicalComplex
                (ComplexShape.up.{0} ℕ) ⋙
              homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          ((auxSystem.tinv.{u, u + 1} r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V) κ₂
                κ).app
            c) =
      (homology'Functor _ _ _).map
          (CategoryTheory.Functor.map _
            (HomologicalComplex.opFunctor.map
              (Quiver.Hom.op <| (qprimeFPNat.tinv BD κ₂ κ M).app _))) ≫
        (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℕ) n).map
          (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ₂ M V (unop.{1} c)).hom :=
  by
  simp only [← Functor.map_comp, Functor.comp_map]; congr 1
  apply homComplexQprimeFPNatIsoAuxSystem_naturality_in_tinv

theorem aux₂ :
    (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℤ).symm (-↑n)).map
          (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ M).obj (unop.{1} c)) V.toCond).hom ≫
        (HomologicalComplex.embed.{0, 0, u + 2, u + 1} ComplexShape.Embedding.natUpIntDown ⋙
              homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.down.{0} ℤ) (-↑n)).map
          (((preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).mapHomologicalComplex
                (ComplexShape.down.{0} ℕ).symm).map
            (HomologicalComplex.opFunctor.{u + 2, u + 1, 0}.map
              ((qprimeFPNat.tinv.{u} BD κ₂ κ M).app (unop.{1} c)).op)) =
      (((preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).rightOp.mapHomologicalComplex
                  (ComplexShape.up.{0} ℤ) ⋙
                HomologicalComplex.unopFunctor.{u + 2, u + 1, 0}.rightOp ⋙
                  (homology'Functor.{u + 1, u + 2, 0} AddCommGroupCat.{u + 1}
                      (ComplexShape.up.{0} ℤ).symm (-↑n)).op).map
            ((qprimeFPInt.tinv.{u} BD κ₂ κ M).app (unop.{1} c))).unop ≫
        (homology'Functor.{u + 1, u + 2, 0} Ab.{u + 1} (ComplexShape.up.{0} ℤ).symm (-↑n)).map
          (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ₂ M).obj (unop.{1} c))
              V.toCond).hom :=
  by
  dsimp only [Functor.op_map, Functor.comp_map]
  erw [← Functor.map_comp]
  erw [← Functor.map_comp]
  congr 1
  ext ((_ | k) | k) : 2
  · refine' (Category.id_comp _).trans (Category.comp_id _).symm
  · apply IsZero.eq_of_tgt
    exact is_zero_zero _
  · refine' (Category.id_comp _).trans (Category.comp_id _).symm

end ExtQprimeIsoAuxSystemCommTinvSetup

theorem extQprimeIsoAuxSystem_comm_tinv [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
    (extQprimeIsoAuxSystem r' BD κ M V n).hom ≫
        whiskerRight (auxSystem.tinv.{u} r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1}.obj V) κ₂ κ)
          ((forget₂ _ _).mapHomologicalComplex _ ⋙
            homology'Functor Ab.{u + 1} (ComplexShape.up ℕ) n) =
      ExtQprime.tinv r' BD κ κ₂ M V n ≫ (extQprimeIsoAuxSystem r' BD κ₂ M V n).hom :=
  by
  ext c : 2
  dsimp only [extQprimeIsoAuxSystemObj, extQprimeIsoAuxSystem, Iso.trans_hom, id,
    Functor.mapIso_hom, NatIso.ofComponents_hom_app, NatTrans.comp_app]
  haveI :
    ((HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ)).obj
        ((qprimeFPInt.{u} r' BD κ M).obj (unop.{1} c))).IsBoundedAbove :=
    ChainComplex.isBoundedAbove _
  haveI :
    ((HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ)).obj
        ((qprimeFPInt.{u} r' BD κ₂ M).obj (unop.{1} c))).IsBoundedAbove :=
    ChainComplex.isBoundedAbove _
  have :=
    extComputeWithAcyclic_naturality ((qprimeFPInt.{u} r' BD κ₂ M).obj c.unop)
      ((qprimeFPInt.{u} r' BD κ M).obj c.unop) V.to_Cond _ _ ((qprimeFPInt.tinv BD κ₂ κ M).app _) n
  rotate_left
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  erw [reassoc_of this]; clear this; simp only [Category.assoc]; congr 1
  dsimp only [CategoryTheory.whiskerRight_app]
  rw [ExtQprimeIsoAuxSystemCommTinvSetup.aux₁ r' BD κ κ₂ M V c n]
  simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
  erw [← NatTrans.naturality]
  simp only [← Category.assoc]; congr 1
  exact ExtQprimeIsoAuxSystemCommTinvSetup.aux₂ r' BD κ κ₂ M V c n

-- lemma ExtQprime_iso_aux_system_comm_T_inv [normed_with_aut r V] (n : ℕ) (c : ℝ≥0ᵒᵖ) :
--   (ExtQprime_iso_aux_system_obj.{u} r' BD κ₂ M V (unop.{1} c) n).hom ≫
--     ((forget₂.{u+2 u+2 u+1 u+1 u+1} SemiNormedGroup.{u+1} Ab.{u+1}).map_homological_complex (complex_shape.up.{0} ℕ) ⋙
--    homology_functor.{u+1 u+2 0} Ab.{u+1} (complex_shape.up.{0} ℕ) n).map
--   ((aux_system.res.{u u+1} r' BD ⟨M⟩ (SemiNormedGroup.ulift.{u+1 u}.obj V) κ₂ κ).app c) =
--   ((Ext.{u+1 u+2} ↑n).flip.map
--       ((single.{u+1 u+2} (Condensed.{u u+1 u+2} Ab.{u+1}) 0).map
--           (Condensed.of_top_ab_map.{u} (normed_add_group_hom.to_add_monoid_hom.{u u} normed_with_aut.T.{u}.inv) _))).app
--       ((QprimeFP.{u} r' BD κ₂ M).op.obj c) ≫
--     (ExtQprime_iso_aux_system_obj.{u} r' BD κ₂ M V (unop.{1} c) n).hom :=
-- by admit
def HomologicalComplex.mapUnop {A M : Type _} [Category A] [Abelian A] {c : ComplexShape M}
    (C₁ C₂ : HomologicalComplex Aᵒᵖ c) (f : C₁ ⟶ C₂) : C₂.unop ⟶ C₁.unop :=
  HomologicalComplex.unopFunctor.map f.op

namespace ExtQprimeIsoAuxSystemCommSetup

variable [NormedWithAut r V] [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ κ c n)]

def homComplexMapTInv (c : ℝ≥0ᵒᵖ) :
    homComplexNat.{u} ((qprimeFPNat.{u} r' BD κ M).obj (unop.{1} c)) V.toCond ⟶
      homComplexNat.{u} ((qprimeFPNat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.toCond :=
  by
    refine' NatTrans.app _ _
    refine' NatTrans.mapHomologicalComplex _ _
    refine' preadditive_yoneda.map _
    refine'
      Condensed.ofTopAbMap.{u} (NormedAddGroupHom.toAddMonoidHom.{u, u} NormedWithAut.t.{u}.inv)
        (NormedAddGroupHom.continuous _) ≫
    CategoryTheory.Functor.map _
      (HomologicalComplex.opFunctor.map (Quiver.Hom.op <| (qprimeFPNat.ι BD κ₂ κ M).app _))

theorem embed_homComplexNat_iso₀ (c : ℝ≥0ᵒᵖ) :
    (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.toCond).hom.f
        (Int.ofNat 0) =
      𝟙 _ :=
  rfl

theorem embedHomComplexNatIso_neg (n : ℕ) (c : ℝ≥0ᵒᵖ) :
    (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.toCond).hom.f
        -[n+1] =
      𝟙 _ :=
  rfl

theorem AddEquiv.toAddCommGroupCatIso_apply (A B : AddCommGroupCat.{u}) (e : A ≃+ B) (a : A) :
    e.toAddCommGroupCatIso.hom a = e a :=
  rfl

theorem preadditiveYonedaObjObjCondensedSetToCondensedAb_apply (M) (X) (t) :
    (preadditiveYonedaObjObjCondensedSetToCondensedAb M X).hom t =
      yoneda'Equiv _ _ (condensedAbCondensedSetAdjunction.homEquiv X.toCondensed M t).val :=
  rfl

theorem aux₁ (c : ℝ≥0ᵒᵖ) :
    (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ M V (unop.{1} c)).hom ≫
        ((forget₂.{u + 2, u + 2, u + 1, u + 1, u + 1} SemiNormedGroupCat.{u + 1}
                  Ab.{u + 1}).mapHomologicalComplex
              (ComplexShape.up.{0} ℕ)).map
          ((auxSystem.tInv.{u, u + 1} r r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V) κ).app
              c ≫
            (auxSystem.res.{u, u + 1} r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1, u}.obj V) κ₂
                  κ).app
              c) =
      homComplexMapTInv _ _ _ _ _ _ _ _ ≫
        (homComplexQprimeFPNatIsoAuxSystem.{u} r' BD κ₂ M V (unop.{1} c)).hom :=
  by
  --simp only [← category_theory.functor.map_comp, functor.comp_map], congr' 1,
  dsimp only [hom_complex_map_T_inv];
  simp only [Category.assoc]
  rw [← homComplexQprimeFPNatIsoAuxSystem_naturality_in_κ r' BD κ κ₂ M V c.unop]
  simp only [Functor.map_comp, ← Category.assoc]; congr 1
  apply homComplexQprimeFPNatIsoAuxSystem_naturality_in_tInv

/- -- IGNORE THIS
  ext k t : 3,
  dsimp [hom_complex_nat] at t,
  dsimp only [hom_complex_QprimeFP_nat_iso_aux_system, aux_system.T_inv,
    aux_system.res, hom_complex_nat, functor.map_iso, iso.trans_hom,
    homological_complex.unop_functor, homological_complex.comp_f,
    nat_iso.map_homological_complex, nat_iso.app_hom, iso.op_hom, quiver.hom.unop_op,
    nat_trans.map_homological_complex_app_f, ExtQprime_iso_aux_system_obj_aux,
    nat_iso.of_components_hom_app, id, iso.symm_hom, nat_iso.app_inv,
    whisker_right_app, nat_trans.op, functor.comp_map],
  simp only [category_theory.functor.map_comp],
  dsimp only [homological_complex.comp_f, functor.map_homological_complex, functor.op_obj,
    functor.unop, forget₂_unop, nat_iso.of_components_hom_app,
    homological_complex.hom.iso_of_components, iso.refl],
  simp only [category.assoc, category.id_comp],
  erw category.id_comp,
  dsimp only [functor.op, quiver.hom.unop_op],
  erw category.comp_id,
  repeat { rw [comp_apply] },
  -/
-- UUUUGGGHHH
theorem aux₂ (c : ℝ≥0ᵒᵖ) :
    ((((preadditiveYoneda.{u + 1, u + 2}.obj
                          (Condensed.ofTopAb.{u} ↥V)).rightOp.mapHomologicalComplex
                    (ComplexShape.up.{0} ℤ)).obj
                ((qprimeFPInt.{u} r' BD κ M).obj (unop.{1} c))).map_unop
            (((preadditiveYoneda.{u + 1, u + 2}.obj
                        (Condensed.ofTopAb.{u} ↥V)).rightOp.mapHomologicalComplex
                  (ComplexShape.up.{0} ℤ)).obj
              ((qprimeFPInt.{u} r' BD κ M).obj (unop.{1} c)))
            ((NatTrans.mapHomologicalComplex.{u + 1, u + 2, 0, u + 2, u + 1}
                  (NatTrans.rightOp.{u + 1, u + 1, u + 2, u + 2}
                    (preadditiveYoneda.{u + 1, u + 2}.map
                      (Condensed.ofTopAbMap.{u}
                        (NormedAddGroupHom.toAddMonoidHom.{u, u} NormedWithAut.t.{u}.inv)
                        (NormedAddGroupHom.continuous _))))
                  (ComplexShape.up.{0} ℤ)).app
              ((qprimeFPInt.{u} r' BD κ M).obj (unop.{1} c))) ≫
          (HomologicalComplex.unopFunctor.{u + 2, u + 1, 0}.rightOp.map
              (((preadditiveYoneda.{u + 1, u + 2}.obj V.toCond).rightOp.mapHomologicalComplex
                    (ComplexShape.up.{0} ℤ)).map
                ((qprimeFPInt.ι.{u} BD κ₂ κ M).app (unop.{1} c)))).unop) ≫
        (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ₂ M).obj (unop.{1} c)) V.toCond).hom =
      (embedHomComplexNatIso.{u} ((qprimeFPNat.{u} r' BD κ M).obj (unop.{1} c)) V.toCond).hom ≫
        CategoryTheory.Functor.map _ (homComplexMapTInv _ _ _ _ _ _ _ _) :=
  by
  ext ((_ | k) | k) : 2
  · dsimp only [Functor.Comp]
    simp only [Functor.rightOp_map, Quiver.Hom.unop_op, Category.assoc, HomologicalComplex.comp_f,
      HomologicalComplex.unopFunctor_map_f, Functor.mapHomologicalComplex_map_f]
    rw [embed_hom_complex_nat_iso₀]
    rw [embed_hom_complex_nat_iso₀]
    ext; rfl
  · apply IsZero.eq_of_tgt
    exact is_zero_zero _
  · dsimp only [Functor.Comp]
    simp only [Functor.rightOp_map, Quiver.Hom.unop_op, Category.assoc, HomologicalComplex.comp_f,
      HomologicalComplex.unopFunctor_map_f, Functor.mapHomologicalComplex_map_f]
    rw [ExtQprimeIsoAuxSystemCommSetup.embedHomComplexNatIso_neg]
    rw [ExtQprimeIsoAuxSystemCommSetup.embedHomComplexNatIso_neg]
    ext; rfl

end ExtQprimeIsoAuxSystemCommSetup

section NaturalitySndVar

variable {A : Type _} [Category A] [Abelian A] [EnoughProjectives A] (X : CochainComplex A ℤ)
  [((HomotopyCategory.quotient A (ComplexShape.up.{0} ℤ)).obj X).IsBoundedAbove] {B₁ B₂ : A}
  (f : B₁ ⟶ B₂)

-- (h₁) (h₂) (i)
@[reassoc]
theorem extComputeWithAcyclicAux₁_naturality_snd_var (i) (e : (0 : ℤ) - i = -i) :
    ((extComputeWithAcyclicAux₁ X B₁ i).hom ≫
        by
        refine' NatTrans.app _ _
        refine' preadditive_yoneda.map _
        refine' CategoryTheory.Functor.map _ f) =
      CategoryTheory.Functor.map _ (CategoryTheory.Functor.map _ f) ≫
        (extComputeWithAcyclicAux₁ X B₂ i).hom :=
  by
  ext t
  simp only [comp_apply]
  dsimp [extComputeWithAcyclicAux₁, Ext]
  simp only [Category.assoc]
  generalize_proofs h1 h2
  let φ₁ j := (single _ j).obj B₁
  let φ₂ j := (single _ j).obj B₂
  change t ≫ _ ≫ eq_to_hom (congr_arg φ₁ e) ≫ _ = _ ≫ _ ≫ _ ≫ eq_to_hom (congr_arg φ₂ e)
  induction e
  dsimp; simp only [Category.id_comp, Category.comp_id]
  erw [← NatTrans.naturality]
  rfl

@[reassoc]
theorem extComputeWithAcyclicAux₂_naturality_snd_var (i) :
    (extComputeWithAcyclicAux₂ X B₁ i).hom ≫
        (homology'Functor _ _ _).map
          (by
            refine' NatTrans.app _ _
            refine' NatTrans.mapHomologicalComplex _ _
            exact preadditive_yoneda.map f) =
      NatTrans.app (preadditiveYoneda.map <| CategoryTheory.Functor.map _ f) _ ≫
        (extComputeWithAcyclicAux₂ X B₂ i).hom :=
  by
  dsimp only [extComputeWithAcyclicAux₂, unop_op]
  have := BoundedHomotopyCategory.homSingleIso_naturality_snd_var_good (of' X).replace (-i) f
  erw [← this]

theorem extComputeWithAcyclicAux₃_naturality_snd_var (i) :
    (homology'Functor _ _ _).map
          (by
            refine' HomologicalComplex.mapUnop _ _ _
            refine' NatTrans.app _ _
            refine' NatTrans.mapHomologicalComplex _ _
            refine' NatTrans.rightOp _
            exact preadditive_yoneda.map f) ≫
        extComputeWithAcyclicAux₃ X B₂ i =
      extComputeWithAcyclicAux₃ X B₁ i ≫
        (homology'Functor _ _ _).map
          (by
            refine' NatTrans.app _ _
            refine' NatTrans.mapHomologicalComplex _ _
            exact preadditive_yoneda.map f) :=
  by
  dsimp only [extComputeWithAcyclicAux₃]
  erw [←
    (homology'Functor.{u_2, u_2 + 1, 0} AddCommGroupCat.{u_2} (ComplexShape.up.{0} ℤ).symm
        (-i)).map_comp]
  erw [←
    (homology'Functor.{u_2, u_2 + 1, 0} AddCommGroupCat.{u_2} (ComplexShape.up.{0} ℤ).symm
        (-i)).map_comp]
  congr 1
  ext t x
  dsimp [extComputeWithAcyclicHomB]
  simp only [comp_apply]
  dsimp [NatTrans.mapHomologicalComplex, Functor.rightOp, HomologicalComplex.mapUnop]
  simp only [Category.assoc]

theorem extComputeWithAcyclic_naturality_snd_var (h₁) (h₂) (i) :
    (extComputeWithAcyclic X B₁ h₁ i).hom ≫
        (homology'Functor _ _ _).map
          (by
            refine' HomologicalComplex.mapUnop _ _ _
            refine' NatTrans.app _ _
            refine' NatTrans.mapHomologicalComplex _ _
            exact (preadditive_yoneda.map f).rightOp) =
      CategoryTheory.Functor.map _ (CategoryTheory.Functor.map _ f) ≫
        (extComputeWithAcyclic X B₂ h₂ i).hom :=
  by
  dsimp [extComputeWithAcyclic, -homology'Functor_map]
  simp only [Category.assoc]
  rw [← extComputeWithAcyclicAux₁_naturality_snd_var_assoc]
  rw [← extComputeWithAcyclicAux₂_naturality_snd_var_assoc]
  simp only [Category.assoc]; congr 2
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq]
  apply extComputeWithAcyclicAux₃_naturality_snd_var
  simp

end NaturalitySndVar

theorem extQprimeIsoAuxSystem_comm [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
    (extQprimeIsoAuxSystem r' BD κ M V n).hom ≫
        whiskerRight (auxSystem.tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1}.obj V) κ₂ κ)
          ((forget₂ _ _).mapHomologicalComplex _ ⋙
            homology'Functor Ab.{u + 1} (ComplexShape.up ℕ) n) =
      ExtQprime.tinv2 r r' BD κ κ₂ M V n ≫ (extQprimeIsoAuxSystem r' BD κ₂ M V n).hom :=
  by
  ext c : 2; dsimp only [auxSystem.tinv2, ExtQprime.tinv2, NatTrans.comp_app, CategoryTheory.whiskerRight_app]
  simp only [sub_comp, NatTrans.app_sub, Functor.map_sub, comp_sub]
  refine' congr_arg₂ _ _ _
  · rw [← NatTrans.comp_app, ← extQprimeIsoAuxSystem_comm_tinv]; rfl
  dsimp only [extQprimeIsoAuxSystemObj, extQprimeIsoAuxSystem, Iso.trans_hom, id,
    Functor.mapIso_hom, NatIso.ofComponents_hom_app, NatTrans.comp_app]
  haveI :
    ((HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ)).obj
        ((qprimeFPInt.{u} r' BD κ M).obj (unop.{1} c))).IsBoundedAbove :=
    ChainComplex.isBoundedAbove _
  haveI :
    ((HomotopyCategory.quotient.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ)).obj
        ((qprimeFPInt.{u} r' BD κ₂ M).obj (unop.{1} c))).IsBoundedAbove :=
    ChainComplex.isBoundedAbove _
  have :=
    extComputeWithAcyclic_naturality ((qprimeFPInt.{u} r' BD κ₂ M).obj c.unop)
      ((qprimeFPInt.{u} r' BD κ M).obj c.unop) V.to_Cond _ _ ((qprimeFPInt.ι BD κ₂ κ M).app _) n
  rotate_left
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  simp only [Category.assoc];
  dsimp only [ExtQprime.tInv, NatTrans.comp_app, CategoryTheory.whiskerRight_app, CategoryTheory.whiskerLeft_app, Functor.flip]
  let η :=
    (ext.{u + 1, u + 2} ↑n).map
      ((NatTrans.op.{0, u + 1, 0, u + 2} (qprimeFP.ι.{u} BD κ₂ κ M)).app c)
  slice_rhs 1 2 => erw [← η.naturality]
  slice_rhs 2 3 => erw [this]
  simp only [Category.assoc]; clear this η
  let t : Condensed.ofTopAb V ⟶ _ :=
    Condensed.ofTopAbMap.{u} (NormedAddGroupHom.toAddMonoidHom.{u, u} NormedWithAut.t.{u}.inv)
      (NormedAddGroupHom.continuous _)
  have := extComputeWithAcyclic_naturality_snd_var ((qprimeFPInt r' BD κ M).obj c.unop) t _ _ n
  rotate_left
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  · intro k i hi; apply QprimeFP_acyclic; exact hi
  erw [← reassoc_of this]; clear this; congr 1
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp, Functor.op_map, Quiver.Hom.unop_op]
  slice_rhs 1 2 => rw [← CategoryTheory.Functor.map_comp]
  slice_lhs 4 5 => rw [← CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, ← Functor.map_comp_assoc]
  rw [ExtQprimeIsoAuxSystemCommSetup.aux₁ r r' BD κ κ₂ M V c]
  slice_lhs 2 4 => simp only [CategoryTheory.Functor.map_comp]
  simp only [← Category.assoc]; congr 1
  rw [ExtQprimeIsoAuxSystemCommSetup.aux₂ r r' BD κ κ₂ M V c]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  congr 1
  rw [NatIso.app_hom, ← NatTrans.naturality]
  congr 1

-- have := Ext_compute_with_acyclic_naturality, <-- we need naturality in the other variable?!
--simp only [category.assoc],
--erw reassoc_of this,
--clear this, simp only [category.assoc], congr' 1,
/-
  rw [nat_trans.comp_app, functor.map_comp, ExtQprime.T_inv,
    nat_trans.comp_app, whisker_right_app, whisker_left_app, category.assoc],
  dsimp only [ExtQprime_iso_aux_system, nat_iso.of_components_hom_app, aux_system,
    aux_system.res, functor.comp_map],
  -/
theorem extQprimeIsoAuxSystem_comm' [NormedWithAut r V] [∀ c n, Fact (κ₂ c n ≤ κ c n)]
    [∀ c n, Fact (κ₂ c n ≤ r' * κ c n)] (n : ℕ) :
    whiskerRight (auxSystem.tinv2.{u} r r' BD ⟨M⟩ (SemiNormedGroupCat.ulift.{u + 1}.obj V) κ₂ κ)
          ((forget₂ _ _).mapHomologicalComplex _ ⋙
            homology'Functor Ab.{u + 1} (ComplexShape.up ℕ) n) ≫
        (extQprimeIsoAuxSystem r' BD κ₂ M V n).inv =
      (extQprimeIsoAuxSystem r' BD κ M V n).inv ≫ ExtQprime.tinv2 r r' BD κ κ₂ M V n :=
  by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  apply extQprimeIsoAuxSystem_comm

end

section

def CategoryTheory.Functor.mapCommsq {C D : Type _} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) {X Y Z W : C} {f₁ : X ⟶ Y} {g₁ : X ⟶ Z} {g₂ : Y ⟶ W} {f₂ : Z ⟶ W}
    (sq : Commsq f₁ g₁ g₂ f₂) : Commsq (F.map f₁) (F.map g₁) (F.map g₂) (F.map f₂) :=
  Commsq.ofEq <| by rw [← F.map_comp, sq.w, F.map_comp]

end

section

variable {r'}

variable (BD : BreenDeligne.Package)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.data.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.data.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

open BoundedHomotopyCategory

-- move me
instance eval'IsBoundedAbove :
    ((HomotopyCategory.quotient (Condensed Ab) (ComplexShape.up ℤ)).obj
        ((BD.eval' freeCond').obj M.toCondensed)).IsBoundedAbove :=
  by delta BreenDeligne.Package.eval'; refine' ⟨⟨1, _⟩⟩; apply ChainComplex.boundedByOne

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

def extTinv2 {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]
    {A B V : BoundedHomotopyCategory 𝓐} (Tinv : A ⟶ B) (ι : A ⟶ B) (T_inv : V ⟶ V) (i : ℤ) :
    ((ext i).obj (op B)).obj V ⟶ ((ext i).obj (op A)).obj V :=
  ((ext i).map Tinv.op).app V - ((ext i).map ι.op).app V ≫ ((ext i).obj _).map T_inv

open CategoryTheory.Preadditive

def extTinv2Commsq {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]
    {A₁ B₁ A₂ B₂ V : BoundedHomotopyCategory 𝓐} (Tinv₁ : A₁ ⟶ B₁) (ι₁ : A₁ ⟶ B₁) (Tinv₂ : A₂ ⟶ B₂)
    (ι₂ : A₂ ⟶ B₂) (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (sqT : f ≫ Tinv₂ = Tinv₁ ≫ g) (sqι : f ≫ ι₂ = ι₁ ≫ g)
    (T_inv : V ⟶ V) (i : ℤ) :
    Commsq (((ext i).map g.op).app V) (extTinv2 Tinv₂ ι₂ T_inv i) (extTinv2 Tinv₁ ι₁ T_inv i)
      (((ext i).map f.op).app V) :=
  Commsq.ofEq
    (by
      delta extTinv2
      simp only [comp_sub, sub_comp, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp, sqT, ←
        NatTrans.naturality, ← NatTrans.naturality_assoc, Category.assoc, sqι])

open CategoryTheory.Preadditive

theorem auux {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]
    {A₁ B₁ A₂ B₂ : CochainComplex 𝓐 ℤ}
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj A₁).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj B₁).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj A₂).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj B₂).IsBoundedAbove] {f₁ : A₁ ⟶ B₁}
    {f₂ : A₂ ⟶ B₂} {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂} (sq1 : Commsq f₁ α β f₂) :
    ofHom f₁ ≫ ofHom β = ofHom α ≫ ofHom f₂ :=
  by
  have := sq1.w
  apply_fun fun f => (HomotopyCategory.quotient _ _).map f at this 
  simp only [Functor.map_comp] at this 
  exact this

@[simp]
theorem ofHom_id {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]
    {A : CochainComplex 𝓐 ℤ}
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj A).IsBoundedAbove] :
    ofHom (𝟙 A) = 𝟙 _ := by delta of_hom; rw [CategoryTheory.Functor.map_id]; rfl

theorem ext_iso_of_bicartesian_of_bicartesian {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]
    [EnoughProjectives 𝓐] {A₁ B₁ C A₂ B₂ : CochainComplex 𝓐 ℤ}
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj A₁).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj B₁).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj C).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj A₂).IsBoundedAbove]
    [((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj B₂).IsBoundedAbove] {f₁ : A₁ ⟶ B₁}
    {g₁ : B₁ ⟶ C} (w₁ : ∀ n, ShortExact (f₁.f n) (g₁.f n)) {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C}
    (w₂ : ∀ n, ShortExact (f₂.f n) (g₂.f n)) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (γ : C ⟶ C) (ιA : A₁ ⟶ A₂)
    (ιB : B₁ ⟶ B₂) (sq1 : Commsq f₁ α β f₂) (sq2 : Commsq g₁ β γ g₂) (sq1' : Commsq f₁ ιA ιB f₂)
    (sq2' : Commsq g₁ ιB (𝟙 _) g₂) (V : BoundedHomotopyCategory 𝓐) (T_inv : V ⟶ V) (i : ℤ)
    (H1 :
      (extTinv2Commsq (ofHom α) (ofHom ιA) (ofHom β) (ofHom ιB) (ofHom f₁) (ofHom f₂) (auux sq1)
          (auux sq1') T_inv i).Bicartesian)
    (H2 :
      (extTinv2Commsq (ofHom α) (ofHom ιA) (ofHom β) (ofHom ιB) (ofHom f₁) (ofHom f₂) (auux sq1)
          (auux sq1') T_inv (i + 1)).Bicartesian) :
    IsIso (extTinv2 (ofHom γ) (𝟙 _) T_inv (i + 1)) :=
  by
  have LES₁ :=
    ((Ext_five_term_exact_seq' _ _ i V w₁).drop 2).pair.cons
      (Ext_five_term_exact_seq' _ _ (i + 1) V w₁)
  replace LES₁ := (((Ext_five_term_exact_seq' _ _ i V w₁).drop 1).pair.cons LES₁).extract 0 4
  have LES₂ :=
    (((Ext_five_term_exact_seq' _ _ i V w₂).drop 2).pair.cons
          (Ext_five_term_exact_seq' _ _ (i + 1) V w₂)).extract
      0 4
  replace LES₂ := (((Ext_five_term_exact_seq' _ _ i V w₂).drop 1).pair.cons LES₂).extract 0 4
  refine' iso_of_bicartesian_of_bicartesian LES₂ LES₁ _ _ _ _ H1 H2
  · apply Commsq.ofEq; delta extTinv2; clear LES₁ LES₂
    rw [sub_comp, comp_sub, ← Functor.flip_obj_map, ← Functor.flip_obj_map]
    rw [← Ext_δ_natural i V _ _ _ _ α β γ sq1.w sq2.w w₁ w₂]
    congr 1
    rw [← NatTrans.naturality, ← Functor.flip_obj_map, Category.assoc,
      Ext_δ_natural i V _ _ _ _ ιA ιB (𝟙 _) sq1'.w sq2'.w w₁ w₂]
    simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, ofHom_id,
      Category.comp_id]
    erw [Category.id_comp]
    symm
    apply Ext_δ_natural'
  · apply extTinv2Commsq
    · exact auux sq2
    · exact auux sq2'

end

