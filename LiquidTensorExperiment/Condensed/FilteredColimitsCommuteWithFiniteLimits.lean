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
                naturality' := fun X Y f =>
                  by
                  erw [functor.const_obj_map, category.id_comp, category.assoc]
                  rw [← nat_trans.naturality, ← category.assoc]
                  simp only [functor.flip_obj_map, ← nat_trans.comp_app, limit.w] }⟩
        naturality' := fun X Y f =>
          by
          erw [functor.const_obj_map, category.comp_id]
          apply limit.hom_ext; intro k
          simp only [category.assoc, limit.lift_π, nat_trans.naturality_assoc]
          simp only [← functor.flip_map_app, ← nat_trans.comp_app, colimit.w] }⟩

noncomputable instance preservesFilteredColimits :
    PreservesFilteredColimits condensedSetToPresheaf.{u} :=
  by
  constructor; intro J _ _; constructor; intro F
  apply preserves_colimit_of_preserves_colimit_cocone (filteredCoconeIsColimit F)
  let e : CondensedSet_to_presheaf.map_cocone (filteredCocone F) ≅ colimit.cocone _ :=
    cocones.ext (iso.refl _) _
  swap
  · intro j; dsimp; simpa
  apply is_colimit.of_iso_colimit _ e.symm
  exact colimit.is_colimit _

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
    (j : J) : (G.mapLimit F).Hom ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) := by
  simp only [CategoryTheory.Functor.mapLimit, functor.map_cone_π_app,
    limit.cone_point_unique_up_to_iso_hom_comp, limit.cone_π]

def CategoryTheory.Functor.mapColimit {J C D : Type _} [SmallCategory J] [Category C] [Category D]
    (G : C ⥤ D) (F : J ⥤ C) [HasColimit F] [HasColimit (F ⋙ G)] [PreservesColimit F G] :
    G.obj (colimit F) ≅ colimit (F ⋙ G) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfPreserves G (colimit.isColimit _))
    (colimit.isColimit _)

@[simp, reassoc]
theorem CategoryTheory.Functor.ι_mapColimit_inv {J C D : Type _} [SmallCategory J] [Category C]
    [Category D] (G : C ⥤ D) (F : J ⥤ C) [HasColimit F] [HasColimit (F ⋙ G)] [PreservesColimit F G]
    (j : J) : colimit.ι (F ⋙ G) j ≫ (G.mapColimit F).inv = G.map (colimit.ι F j) := by
  simp only [CategoryTheory.Functor.mapColimit, functor.map_cocone_ι_app,
    colimit.comp_cocone_point_unique_up_to_iso_inv, colimit.cocone_ι]

def limitCompIso {J K C D : Type _} [SmallCategory J] [SmallCategory K] [Category C] [Category D]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] (F : J ⥤ K ⥤ C) (G : C ⥤ D) [HasLimit F]
    [H : ∀ k, HasLimit (F.flip.obj k)] [∀ k, PreservesLimit (F.flip.obj k) G]
    [∀ k, PreservesLimit F ((CategoryTheory.evaluation K C).obj k)] :
    limit F ⋙ G ≅ F.flip ⋙ (whiskeringRight _ _ _).obj G ⋙ limUnder :=
  by
  refine' nat_iso.of_components _ _
  · intro k
    refine' G.map_iso _ ≪≫ G.map_limit _
    letI : has_limit (F ⋙ (CategoryTheory.evaluation K C).obj k) := H k
    refine' ((CategoryTheory.evaluation _ _).obj k).mapLimit _ ≪≫ _
    refine' limits.lim.map_iso _
    exact iso.refl _
  · intro k₁ k₂ f
    ext j
    dsimp
    simp only [functor.map_comp, CategoryTheory.Functor.mapLimit_hom_π, category.assoc, lim_map_π,
      whisker_right_app, functor.flip_map_app, CategoryTheory.Functor.mapLimit_hom_π_assoc]
    simp only [← functor.map_comp, category.assoc]; congr 1
    simp only [lim_map_π, lim_map_π_assoc, CategoryTheory.Functor.mapLimit_hom_π_assoc,
      CategoryTheory.Functor.mapLimit_hom_π]
    erw [← evaluation_map_app K C, ← category.assoc, ← nat_trans.naturality]
    erw [nat_trans.id_app, nat_trans.id_app, category.comp_id, category.id_comp]
    rfl

def colimitCompIso {J K C D : Type _} [SmallCategory J] [SmallCategory K] [Category C] [Category D]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] (F : J ⥤ K ⥤ C) (G : C ⥤ D) [HasColimit F]
    [H : ∀ k, HasColimit (F.flip.obj k)] [∀ k, PreservesColimit (F.flip.obj k) G]
    [∀ k, PreservesColimit F ((CategoryTheory.evaluation K C).obj k)] :
    colimit F ⋙ G ≅ F.flip ⋙ (whiskeringRight _ _ _).obj G ⋙ colim :=
  by
  refine' nat_iso.of_components _ _
  · intro k
    refine' G.map_iso _ ≪≫ G.map_colimit _
    letI : has_colimit (F ⋙ (CategoryTheory.evaluation K C).obj k) := H k
    refine' ((CategoryTheory.evaluation _ _).obj k).mapColimit _ ≪≫ _
    refine' colim.map_iso _
    exact iso.refl _
  · intro k₁ k₂ f
    rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv]
    ext j
    dsimp
    simp only [category.assoc, CategoryTheory.Functor.ι_mapColimit_inv_assoc, colimit.ι_map_assoc,
      whisker_right_app, functor.flip_map_app]
    simp only [← functor.map_comp, category.assoc]; congr 1
    simp only [colimit.ι_map_assoc, CategoryTheory.Functor.ι_mapColimit_inv_assoc,
      CategoryTheory.Functor.ι_mapColimit_inv]
    rw [← evaluation_map_app K C, nat_trans.naturality]
    erw [nat_trans.id_app, nat_trans.id_app, category.id_comp, category.id_comp]
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
  refine' limit_comp_iso _ _ ≪≫ _
  refine' (functor.associator _ _ _).symm ≪≫ _
  refine' ((whiskering_right _ _ _).obj limUnder).mapIso _
  refine' nat_iso.of_components _ _
  · intro k; refine' nat_iso.of_components (fun j => iso.refl _) _
    intro i j f; dsimp
    simp only [category.id_comp, category.comp_id, (F.obj j).map_id, nat_trans.id_app,
      Sheaf.hom.id_val]
  · intro k l f; ext j : 2; dsimp
    simp only [category.id_comp, category.comp_id, F.map_id, nat_trans.id_app, Sheaf.hom.id_val]

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
  refine' colimit_comp_iso _ _ ≪≫ _
  refine' (functor.associator _ _ _).symm ≪≫ _
  refine' ((whiskering_right _ _ _).obj colim).mapIso _
  refine' nat_iso.of_components _ _
  · intro k; refine' nat_iso.of_components (fun j => iso.refl _) _
    intro i j f; dsimp
    simp only [category.id_comp, category.comp_id, F.map_id, nat_trans.id_app, Sheaf.hom.id_val]
  · intro k l f; ext j : 2; dsimp
    simp only [category.id_comp, category.comp_id, (F.obj l).map_id, nat_trans.id_app,
      Sheaf.hom.id_val]

attribute [local reassoc] Sheaf.hom.comp_val

theorem isIso_colimToLim_component (S : Profinite.{u}ᵒᵖ) : IsIso ((colimToLim F).val.app S) :=
  by
  /-
    The forgetful functor to presheaves preserves filtered colimits and all limits,
    while the same holds for evaluation, hence this morphism should be isomorphic to
    `colimit_limit_to_limit_colimit` which is an isomorphism.
    -/
  suffices
    (colim_to_lim F).val.app S =
      (is_iso_colim_to_lim_component_e₁ F S).Hom ≫
        colimit_limit_to_limit_colimit _ ≫ (is_iso_colim_to_lim_component_e₂ F S).inv
    by rw [this, is_iso_iff_is_iso_comp_left, is_iso_iff_is_iso_comp_right]; infer_instance
  rw [← iso.inv_comp_eq, iso.eq_comp_inv, category.assoc]
  ext j k : 2
  dsimp [colimit_limit_to_limit_colimit, is_iso_colim_to_lim_component_e₁,
    is_iso_colim_to_lim_component_e₂]
  simp only [category.assoc, limit.lift_π, colimit.ι_desc, colimit.ι_map_assoc,
    CategoryTheory.Functor.ι_mapColimit_inv_assoc, CategoryTheory.Functor.mapLimit_hom_π_assoc,
    lim_map_π, nat_trans.comp_app, whisker_right_app, category.id_comp, functor.associator_hom_app,
    functor.associator_inv_app, limit_comp_iso, colimit_comp_iso, iso.trans_hom, iso.trans_inv,
    nat_iso.of_components_hom_app, nat_iso.of_components_inv_app, functor.map_iso_hom,
    functor.map_iso_inv, functor.comp_map, condensedSetToPresheaf_map, evaluation_obj_map]
  simp only [← functor.map_iso_hom, ← functor.map_iso_inv, iso.inv_comp_eq]
  simp only [← category.assoc, ← iso.eq_comp_inv]
  simp only [category.assoc, functor.map_iso_hom, functor.map_iso_inv, colimit.ι_map_assoc,
    lim_map_eq_lim_map, lim_map_π_assoc, nat_iso.of_components_hom_app,
    nat_iso.of_components_inv_app]
  conv_rhs =>
    erw [CategoryTheory.Functor.ι_mapColimit_inv, CategoryTheory.Functor.mapLimit_hom_π_assoc,
      iso.refl_hom, iso.refl_inv, category.id_comp, category.id_comp]
  simp only [← nat_trans.comp_app, ← Sheaf.hom.comp_val, condensedSetToPresheaf_map,
    evaluation_obj_map, functor.comp_map, ← CategoryTheory.NatTrans.comp_app_assoc, ←
    CategoryTheory.Sheaf.Hom.comp_val_assoc]
  simp only [colim_to_lim, colimit.ι_desc_assoc, limit.lift_π_assoc, category.assoc]
  congr 2
  simp only [← lim_map_eq_lim_map, ← functor.map_iso_hom, ← functor.map_iso_inv, iso.inv_comp_eq]
  simp only [← category.assoc, ← iso.eq_comp_inv]
  simp only [functor.map_iso_hom, functor.map_iso_inv, category.assoc, lim_map_eq_lim_map,
    lim_map_π_assoc, colimit.ι_map_assoc, CategoryTheory.Functor.ι_mapColimit_inv,
    CategoryTheory.Functor.mapLimit_hom_π_assoc, iso.refl_hom, iso.refl_inv, category.id_comp,
    nat_trans.id_app]
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
        refine' (prod_eval_iso _ _ _).Hom ≫ _
        refine' S.ι.app j
      naturality' := by
        intro i j f; dsimp [prod_eval_iso]; simp only [category.comp_id, category.assoc]
        rw [← S.w f]
        simp only [← category.assoc]; congr 1; simp only [category.assoc]; dsimp
        apply limit.hom_ext; intro k
        dsimp [pow_functor];
        simp only [category.assoc, has_limit.iso_of_nat_iso_hom_π, discrete.nat_iso_hom_app,
          preserves_limits_iso_hom_π_assoc, evaluation_obj_map, nat_trans.naturality_assoc,
          lim_map_π, discrete.nat_trans_app, has_limit.iso_of_nat_iso_hom_π_assoc]
        dsimp [discrete.functor]; simp }

variable [IsFiltered J]

theorem isIso_colimToLim : IsIso (colimToLim F) :=
  by
  suffices is_iso (CondensedSet_to_presheaf.map (colim_to_lim F)) by skip;
    apply is_iso_of_fully_faithful condensedSetToPresheaf
  apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
  intro S
  apply is_iso_colim_to_lim_component

noncomputable def colimitLimitIsoLimitColimit : colimit (limit F) ≅ limit (colimit F.flip) :=
  @asIso _ _ _ _ (colimToLim F) (isIso_colimToLim _)

open scoped Classical

noncomputable def colimitPowIso (α : Type (u + 1)) [Fintype α] (F : J ⥤ CondensedSet.{u}) :
    colimit (∏ fun i : α => F) ≅ ∏ fun i : α => colimit F :=
  colimitLimitIsoLimitColimit (Discrete.functor fun i : α => F) ≪≫
    HasLimit.isoOfNatIso
      (Discrete.natIso fun i =>
        by
        refine' preserves_colimit_iso ((CategoryTheory.evaluation _ _).obj i) _ ≪≫ _
        refine' has_colimit.iso_of_nat_iso _
        refine' nat_iso.of_components (fun j => iso.refl _) _
        intro j k f; dsimp
        simp only [category.comp_id, category.id_comp]; rfl)

def isColimitPowFunctorMapCocone (α : Type (u + 1)) [Fintype α] (F : J ⥤ CondensedSet) :
    IsColimit ((powFunctor CondensedSet α).mapCocone (colimit.cocone F))
    where
  desc S :=
    (colimitPowIso α F).inv ≫
      colimit.desc (∏ fun i : α => F) (isColimitPowFunctorMapCoconeAux α F S)
  fac := by
    intro S j; dsimp; simp only [← category.assoc]; let t := _; change t ≫ _ = _
    have ht : t = (prod_eval_iso _ _ _).inv ≫ colimit.ι _ j :=
      by
      rw [iso.eq_inv_comp]
      dsimp [t]; rw [← category.assoc, iso.comp_inv_eq];
      dsimp [prod_eval_iso, colimit_pow_iso, pow_functor, colimit_limit_iso_limit_colimit,
        colim_to_lim]
      simp only [category.assoc, colimit.ι_desc_assoc, has_limit.lift_iso_of_nat_iso_hom]
      apply limit.hom_ext; intro k
      simp only [category.assoc, lim_map_π, discrete.nat_trans_app,
        has_limit.iso_of_nat_iso_hom_π_assoc, discrete.nat_iso_hom_app,
        preserves_limits_iso_hom_π_assoc, evaluation_obj_map, limit.lift_π, cones.postcompose_obj_π,
        nat_trans.comp_app, iso.trans_hom]
      dsimp; simp only [category.id_comp]
      erw [(is_colimit_of_preserves ((CategoryTheory.evaluation (discrete α) CondensedSet).obj k)
            _).fac_assoc]
      erw [colimit.ι_desc]; rfl
    rw [ht, category.assoc, colimit.ι_desc]
    dsimp [is_colimit_pow_functor_map_cocone_aux]; simp
  uniq := by
    intro S m hm; rw [iso.eq_inv_comp]; apply colimit.hom_ext; intro j
    dsimp [colimit_pow_iso]; simp only [category.assoc, colimit.ι_desc]
    erw [colimit.ι_desc_assoc]; dsimp [is_colimit_pow_functor_map_cocone_aux]
    simp_rw [← hm, ← category.assoc]; congr 1; apply limit.hom_ext; intro k
    dsimp [pow_functor, prod_eval_iso]
    simp only [has_limit.lift_iso_of_nat_iso_hom, limit.lift_π, cones.postcompose_obj_π,
      nat_trans.comp_app, discrete.nat_iso_hom_app, iso.trans_hom, category.assoc, lim_map_π,
      discrete.nat_trans_app, has_limit.iso_of_nat_iso_hom_π_assoc,
      preserves_limits_iso_hom_π_assoc, evaluation_obj_map]
    erw [(is_colimit_of_preserves ((CategoryTheory.evaluation (discrete α) CondensedSet).obj k)
          _).fac_assoc]
    erw [colimit.ι_desc]
    dsimp; simp

-- Filtered colimits commute with finite products in condensed sets
noncomputable instance powFunctorPreservesFilteredColimits (α : Type (u + 1)) [Fintype α] :
    PreservesFilteredColimits (powFunctor CondensedSet.{u} α) :=
  by
  constructor; intro J _ _; constructor; intro F
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit F)
  apply is_colimit_pow_functor_map_cocone

end CondensedSet

