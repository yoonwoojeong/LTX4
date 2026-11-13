import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.Condensed.FilteredColimits
import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.ForMathlib.PowFunctor
import LiquidTensorExperiment.ForMathlib.NatTrans

#align_import condensed.filtered_colimits_commute_with_finite_limits

open CategoryTheory

open CategoryTheory.Limits

namespace CondensedSet

universe u

variable {J K : Type (u + 1)} [SmallCategory J] [SmallCategory K] [FinCategory K]
  (F : K ⥤ J ⥤ CondensedSet.{u})

noncomputable def colimToLim : colimit (limit F) ⟶ limit (colimit F.flip) :=
  colimit.desc (limit F)
    ⟨limit (colimit F.flip),
      { app := fun j =>
          limit.lift (colimit F.flip)
            ⟨(limit F).obj j,
              { app := fun k => (limit.π F k).app j ≫ (colimit.ι F.flip j).app k
                naturality := fun X Y f =>
                  by
                  erw [Functor.const_obj_map, Category.id_comp, Category.assoc]
                  rw [← NatTrans.naturality, ← Category.assoc]
                  simp only [Functor.flip_obj_map, ← NatTrans.comp_app, limit.w] }⟩
        naturality := fun X Y f =>
          by
          erw [Functor.const_obj_map, Category.comp_id]
          apply limit.hom_ext; intro k
          simp only [Category.assoc, limit.lift_π, NatTrans.naturality_assoc]
          simp only [← Functor.flip_map_app, ← NatTrans.comp_app, colimit.w] }⟩

noncomputable instance preservesFilteredColimits :
    PreservesFilteredColimits condensedSetToPresheaf.{u} :=
  by
  constructor; intro J _ _; constructor; intro F
  apply CategoryTheory.Limits.preservesColimitOfPreservesColimitCocone (filteredCoconeIsColimit F)
  let e : CondensedSet_to_presheaf.map_cocone (filteredCocone F) ≅ colimit.cocone _ :=
    Cocones.ext (iso.refl _) _
  swap
  · intro j; dsimp; simpa
  apply IsColimit.ofIsoColimit _ e.symm
  exact colimit.isColimit _

instance fullCondesensedSetToPresheaf : Full condensedSetToPresheaf :=
  show Full (sheafToPresheaf _ _) by infer_instance

instance faithful_CondesensedSet_to_presheaf : Faithful condensedSetToPresheaf :=
  show Faithful (sheafToPresheaf _ _) by infer_instance

noncomputable instance preservesLimitsCondesensedSetToPresheaf :
    PreservesLimits condensedSetToPresheaf :=
  Adjunction.rightAdjointPreservesLimits condensedSetPresheafAdjunction

section

noncomputable section

-- set_option pp.universes true
def CategoryTheory.Functor.mapLimit {C D J : Type _} [Category C] [Category D] [SmallCategory J]
    (G : C ⥤ D) (F : J ⥤ C) [HasLimit F] [HasLimit (F ⋙ G)] [PreservesLimit F G] :
    G.obj (limit F) ≅ limit (F ⋙ G) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfPreserves G (limit.isLimit _)) (limit.isLimit _)

@[simp, reassoc]
theorem CategoryTheory.Functor.mapLimit_hom_π {J C D : Type _} [SmallCategory J] [Category C]
    [Category D] (G : C ⥤ D) (F : J ⥤ C) [HasLimit F] [HasLimit (F ⋙ G)] [PreservesLimit F G]
    (j : J) : (G.mapLimit F).hom ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  simp only [CategoryTheory.Functor.mapLimit, Functor.mapCone_π_app,
    limit.conePointUniqueUpToIso_hom_comp, limit.cone_π]

def CategoryTheory.Functor.mapColimit {J C D : Type _} [SmallCategory J] [Category C] [Category D]
    (G : C ⥤ D) (F : J ⥤ C) [HasColimit F] [HasColimit (F ⋙ G)] [PreservesColimit F G] :
    G.obj (colimit F) ≅ colimit (F ⋙ G) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfPreserves G (colimit.isColimit _))
    (colimit.isColimit _)

@[simp, reassoc]
theorem CategoryTheory.Functor.ι_mapColimit_inv {J C D : Type _} [SmallCategory J] [Category C]
    [Category D] (G : C ⥤ D) (F : J ⥤ C) [HasColimit F] [HasColimit (F ⋙ G)] [PreservesColimit F G]
    (j : J) : colimit.ι (F ⋙ G) j ≫ (G.mapColimit F).inv = G.map (colimit.ι F j) := by
  simp only [CategoryTheory.Functor.mapColimit, Functor.mapCocone_ι_app,
    colimit.comp_coconePointUniqueUpToIso_inv, colimit.cocone_ι]

def limitCompIso {J K C D : Type _} [SmallCategory J] [SmallCategory K] [Category C] [Category D]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] (F : J ⥤ K ⥤ C) (G : C ⥤ D) [HasLimit F]
    [H : ∀ k, HasLimit (F.flip.obj k)] [∀ k, PreservesLimit (F.flip.obj k) G]
    [∀ k, PreservesLimit F ((CategoryTheory.evaluation K C).obj k)] :
    limit F ⋙ G ≅ F.flip ⋙ (whiskeringRight _ _ _).obj G ⋙ limUnder :=
  by
  refine' NatIso.ofComponents _ _
  · intro k
    refine' G.map_iso _ ≪≫ G.map_limit _
    letI : has_limit (F ⋙ (CategoryTheory.evaluation K C).obj k) := H k
    refine' ((CategoryTheory.evaluation _ _).obj k).mapLimit _ ≪≫ _
    refine' limits.lim.map_iso _
    exact iso.refl _
  · intro k₁ k₂ f
    ext j
    dsimp
    simp only [Functor.map_comp, CategoryTheory.Functor.mapLimit_hom_π, Category.assoc, lim_map_π,
      CategoryTheory.whiskerRight_app, Functor.flip_map_app, CategoryTheory.Functor.mapLimit_hom_π_assoc]
    simp only [← Functor.map_comp, Category.assoc]; congr 1
    simp only [lim_map_π, lim_map_π_assoc, CategoryTheory.Functor.mapLimit_hom_π_assoc,
      CategoryTheory.Functor.mapLimit_hom_π]
    erw [← evaluation_map_app K C, ← Category.assoc, ← NatTrans.naturality]
    erw [NatTrans.id_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
    rfl

def colimitCompIso {J K C D : Type _} [SmallCategory J] [SmallCategory K] [Category C] [Category D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] (F : J ⥤ K ⥤ C) (G : C ⥤ D) [HasColimit F]
    [H : ∀ k, HasColimit (F.flip.obj k)] [∀ k, PreservesColimit (F.flip.obj k) G]
    [∀ k, PreservesColimit F ((CategoryTheory.evaluation K C).obj k)] :
    colimit F ⋙ G ≅ F.flip ⋙ (whiskeringRight _ _ _).obj G ⋙ colim :=
  by
  refine' NatIso.ofComponents _ _
  · intro k
    refine' G.map_iso _ ≪≫ G.map_colimit _
    letI : has_colimit (F ⋙ (CategoryTheory.evaluation K C).obj k) := H k
    refine' ((CategoryTheory.evaluation _ _).obj k).mapColimit _ ≪≫ _
    refine' colim.map_iso _
    exact iso.refl _
  · intro k₁ k₂ f
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
    ext j
    dsimp
    simp only [Category.assoc, CategoryTheory.Functor.ι_mapColimit_inv_assoc, colimit.ι_map_assoc,
      CategoryTheory.whiskerRight_app, Functor.flip_map_app]
    simp only [← Functor.map_comp, Category.assoc]; congr 1
    simp only [colimit.ι_map_assoc, CategoryTheory.Functor.ι_mapColimit_inv_assoc,
      CategoryTheory.Functor.ι_mapColimit_inv]
    rw [← evaluation_map_app K C, NatTrans.naturality]
    erw [NatTrans.id_app, NatTrans.id_app, Category.id_comp, Category.id_comp]
    rfl

variable [IsFiltered J]

def isIsoColimToLimComponentE₁ (S : Profinite.{u}ᵒᵖ) :
    (colimit (limit F)).val.obj S ≅
      colimit
        (curry.obj
            (CategoryTheory.Prod.swap J K ⋙
              uncurry.{u + 1, u + 1}.obj F ⋙
                condensedSetToPresheaf.{u} ⋙
                  (CategoryTheory.evaluation.{u, u + 1, u + 1, u + 2} Profinite.{u}ᵒᵖ
                        (Type (u + 1))).obj
                    S) ⋙
          limUnder) :=
  by
  let VS :=
    condensedSetToPresheaf.{u} ⋙
      (CategoryTheory.evaluation.{u, u + 1, u + 1, u + 2} Profinite.{u}ᵒᵖ (Type (u + 1))).obj S
  refine' VS.map_colimit (limit F) ≪≫ _
  refine' colim.map_iso _
  refine' CondensedSet.limitCompIso _ _ ≪≫ _
  refine' (Functor.associator _ _ _).symm ≪≫ _
  refine' ((whiskering_right _ _ _).obj limUnder).mapIso _
  refine' NatIso.ofComponents _ _
  · intro k; refine' NatIso.ofComponents (fun j => iso.refl _) _
    intro i j f; dsimp
    simp only [Category.id_comp, Category.comp_id, (F.obj j).map_id, NatTrans.id_app,
      Sheaf.Hom.id_val]
  · intro k l f; ext j : 2; dsimp
    simp only [Category.id_comp, Category.comp_id, F.map_id, NatTrans.id_app, Sheaf.Hom.id_val]

def isIsoColimToLimComponentE₂ (S : Profinite.{u}ᵒᵖ) :
    (limit (colimit F.flip)).val.obj S ≅
      limit
        (curry.obj
            (uncurry.{u + 1, u + 1}.obj F ⋙
              condensedSetToPresheaf.{u} ⋙
                (CategoryTheory.evaluation.{u, u + 1, u + 1, u + 2} Profinite.{u}ᵒᵖ
                      (Type (u + 1))).obj
                  S) ⋙
          colim) :=
  by
  let VS :=
    condensedSetToPresheaf.{u} ⋙
      (CategoryTheory.evaluation.{u, u + 1, u + 1, u + 2} Profinite.{u}ᵒᵖ (Type (u + 1))).obj S
  refine' VS.map_limit (colimit F.flip) ≪≫ _
  refine' limits.lim.map_iso _
  refine' CondensedSet.colimitCompIso _ _ ≪≫ _
  refine' (Functor.associator _ _ _).symm ≪≫ _
  refine' ((whiskering_right _ _ _).obj colim).mapIso _
  refine' NatIso.ofComponents _ _
  · intro k; refine' NatIso.ofComponents (fun j => iso.refl _) _
    intro i j f; dsimp
    simp only [Category.id_comp, Category.comp_id, F.map_id, NatTrans.id_app, Sheaf.Hom.id_val]
  · intro k l f; ext j : 2; dsimp
    simp only [Category.id_comp, Category.comp_id, (F.obj l).map_id, NatTrans.id_app,
      Sheaf.Hom.id_val]

attribute [local reassoc] Sheaf.Hom.comp_val

theorem isIso_colimToLim_component (S : Profinite.{u}ᵒᵖ) : IsIso ((colimToLim F).val.app S) :=
  by
  /-
    The forgetful functor to presheaves preserves filtered colimits and all limits,
    while the same holds for evaluation, hence this morphism should be isomorphic to
    `colimit_limit_to_limit_colimit` which is an isomorphism.
    -/
  suffices
    (CondensedSet.colimToLim F).val.app S =
      (is_iso_colim_to_lim_component_e₁ F S).hom ≫
        CategoryTheory.Limits.colimitLimitToLimitColimit _ ≫ (is_iso_colim_to_lim_component_e₂ F S).inv
    by rw [this, CategoryTheory.Limits.isIso_iff_isIso_comp_left, CategoryTheory.Limits.isIso_iff_isIso_comp_right]; infer_instance
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv, Category.assoc]
  ext j k : 2
  dsimp [CategoryTheory.Limits.colimitLimitToLimitColimit, is_iso_colim_to_lim_component_e₁,
    is_iso_colim_to_lim_component_e₂]
  simp only [Category.assoc, limit.lift_π, colimit.ι_desc, colimit.ι_map_assoc,
    CategoryTheory.Functor.ι_mapColimit_inv_assoc, CategoryTheory.Functor.mapLimit_hom_π_assoc,
    lim_map_π, NatTrans.comp_app, CategoryTheory.whiskerRight_app, Category.id_comp, Functor.associator_hom_app,
    Functor.associator_inv_app, CondensedSet.limitCompIso, CondensedSet.colimitCompIso, Iso.trans_hom, Iso.trans_inv,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.comp_map, condensedSetToPresheaf_map, evaluation_obj_map]
  simp only [← Functor.mapIso_hom, ← Functor.mapIso_inv, Iso.inv_comp_eq]
  simp only [← Category.assoc, ← Iso.eq_comp_inv]
  simp only [Category.assoc, Functor.mapIso_hom, Functor.mapIso_inv, colimit.ι_map_assoc,
    CategoryTheory.Limits.lim_map, lim_map_π_assoc, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app]
  conv_rhs =>
    erw [CategoryTheory.Functor.ι_mapColimit_inv, CategoryTheory.Functor.mapLimit_hom_π_assoc,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.id_comp]
  simp only [← NatTrans.comp_app, ← Sheaf.Hom.comp_val, condensedSetToPresheaf_map,
    evaluation_obj_map, Functor.comp_map, ← CategoryTheory.NatTrans.comp_app_assoc, ←
    CategoryTheory.Sheaf.Hom.comp_val_assoc]
  simp only [CondensedSet.colimToLim, colimit.ι_desc_assoc, limit.lift_π_assoc, Category.assoc]
  congr 2
  simp only [← CategoryTheory.Limits.lim_map, ← Functor.mapIso_hom, ← Functor.mapIso_inv, Iso.inv_comp_eq]
  simp only [← Category.assoc, ← Iso.eq_comp_inv]
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc, CategoryTheory.Limits.lim_map,
    lim_map_π_assoc, colimit.ι_map_assoc, CategoryTheory.Functor.ι_mapColimit_inv,
    CategoryTheory.Functor.mapLimit_hom_π_assoc, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
    NatTrans.id_app]
  rfl

end

def prodEvalIso (α : Type (u + 1)) (X : α → J ⥤ CondensedSet.{u}) (j) :
    (∏ X).obj j ≅ ∏ fun i => (X i).obj j :=
  preservesLimitIso ((CategoryTheory.evaluation _ _).obj j) _ ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso fun i => Iso.refl _)

def isColimitPowFunctorMapCoconeAux (α : Type (u + 1)) [Fintype α] (F : J ⥤ CondensedSet)
    (S : Cocone (F ⋙ powFunctor CondensedSet α)) : Cocone (∏ fun i : α => F)
    where
  pt := S.pt
  ι :=
    { app := fun j => by
        refine' (CondensedSet.prodEvalIso _ _ _).hom ≫ _
        refine' S.ι.app j
      naturality := by
        intro i j f; dsimp [CondensedSet.prodEvalIso]; simp only [Category.comp_id, Category.assoc]
        rw [← S.w f]
        simp only [← Category.assoc]; congr 1; simp only [Category.assoc]; dsimp
        apply limit.hom_ext; intro k
        dsimp [pow_functor];
        simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π, Discrete.natIso_hom_app,
          preserves_limits_iso_hom_π_assoc, evaluation_obj_map, NatTrans.naturality_assoc,
          lim_map_π, Discrete.natTrans_app, HasLimit.isoOfNatIso_hom_π_assoc]
        dsimp [Discrete.functor]; simp }

variable [IsFiltered J]

theorem isIso_colimToLim : IsIso (colimToLim F) :=
  by
  suffices is_iso (CondensedSet_to_presheaf.map (CondensedSet.colimToLim F)) by skip;
    apply CategoryTheory.isIso_of_fully_faithful condensedSetToPresheaf
  apply (config := { instances := false }) NatIso.isIso_of_isIso_app
  intro S
  apply CondensedSet.isIso_colimToLim_component

noncomputable def colimitLimitIsoLimitColimit : colimit (limit F) ≅ limit (colimit F.flip) :=
  @asIso _ _ _ _ (colimToLim F) (isIso_colimToLim _)

open scoped Classical

noncomputable def colimitPowIso (α : Type (u + 1)) [Fintype α] (F : J ⥤ CondensedSet.{u}) :
    colimit (∏ fun i : α => F) ≅ ∏ fun i : α => colimit F :=
  colimitLimitIsoLimitColimit (Discrete.functor fun i : α => F) ≪≫
    HasLimit.isoOfNatIso
      (Discrete.natIso fun i =>
        by
        refine' CategoryTheory.preservesColimitIso ((CategoryTheory.evaluation _ _).obj i) _ ≪≫ _
        refine' HasColimit.isoOfNatIso _
        refine' NatIso.ofComponents (fun j => iso.refl _) _
        intro j k f; dsimp
        simp only [Category.comp_id, Category.id_comp]; rfl)

def isColimitPowFunctorMapCocone (α : Type (u + 1)) [Fintype α] (F : J ⥤ CondensedSet) :
    IsColimit ((powFunctor CondensedSet α).mapCocone (colimit.cocone F))
    where
  desc S :=
    (colimitPowIso α F).inv ≫
      colimit.desc (∏ fun i : α => F) (isColimitPowFunctorMapCoconeAux α F S)
  fac := by
    intro S j; dsimp; simp only [← Category.assoc]; let t := _; change t ≫ _ = _
    have ht : t = (CondensedSet.prodEvalIso _ _ _).inv ≫ colimit.ι _ j :=
      by
      rw [Iso.eq_inv_comp]
      dsimp [t]; rw [← Category.assoc, Iso.comp_inv_eq];
      dsimp [CondensedSet.prodEvalIso, CondensedSet.colimitPowIso, pow_functor, CondensedSet.colimitLimitIsoLimitColimit,
        CondensedSet.colimToLim]
      simp only [Category.assoc, colimit.ι_desc_assoc, HasLimit.lift_isoOfNatIso_hom]
      apply limit.hom_ext; intro k
      simp only [Category.assoc, lim_map_π, Discrete.natTrans_app,
        HasLimit.isoOfNatIso_hom_π_assoc, Discrete.natIso_hom_app,
        preserves_limits_iso_hom_π_assoc, evaluation_obj_map, limit.lift_π, Cones.postcompose_obj_π,
        NatTrans.comp_app, Iso.trans_hom]
      dsimp; simp only [Category.id_comp]
      erw [(CategoryTheory.Limits.isColimitOfPreserves ((CategoryTheory.evaluation (discrete α) CondensedSet).obj k)
            _).fac_assoc]
      erw [colimit.ι_desc]; rfl
    rw [ht, Category.assoc, colimit.ι_desc]
    dsimp [CondensedSet.isColimitPowFunctorMapCoconeAux]; simp
  uniq := by
    intro S m hm; rw [Iso.eq_inv_comp]; apply colimit.hom_ext; intro j
    dsimp [CondensedSet.colimitPowIso]; simp only [Category.assoc, colimit.ι_desc]
    erw [colimit.ι_desc_assoc]; dsimp [CondensedSet.isColimitPowFunctorMapCoconeAux]
    simp_rw [← hm, ← Category.assoc]; congr 1; apply limit.hom_ext; intro k
    dsimp [pow_functor, CondensedSet.prodEvalIso]
    simp only [HasLimit.lift_isoOfNatIso_hom, limit.lift_π, Cones.postcompose_obj_π,
      NatTrans.comp_app, Discrete.natIso_hom_app, Iso.trans_hom, Category.assoc, lim_map_π,
      Discrete.natTrans_app, HasLimit.isoOfNatIso_hom_π_assoc,
      preserves_limits_iso_hom_π_assoc, evaluation_obj_map]
    erw [(CategoryTheory.Limits.isColimitOfPreserves ((CategoryTheory.evaluation (discrete α) CondensedSet).obj k)
          _).fac_assoc]
    erw [colimit.ι_desc]
    dsimp; simp

-- Filtered colimits commute with finite products in condensed sets
noncomputable instance powFunctorPreservesFilteredColimits (α : Type (u + 1)) [Fintype α] :
    PreservesFilteredColimits (powFunctor CondensedSet.{u} α) :=
  by
  constructor; intro J _ _; constructor; intro F
  apply CategoryTheory.Limits.preservesColimitOfPreservesColimitCocone (colimit.isColimit F)
  apply CondensedSet.isColimitPowFunctorMapCocone

end CondensedSet

