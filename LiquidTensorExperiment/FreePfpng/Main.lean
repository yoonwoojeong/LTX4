import LiquidTensorExperiment.FreePfpng.Epi
import LiquidTensorExperiment.FreePfpng.Mono

#align_import free_pfpng.main

noncomputable section

open scoped Classical BigOperators

open CategoryTheory

open Opposite

open CategoryTheory.GrothendieckTopology

universe u

theorem Condensed.isZero_of_isZero_obj (A : Condensed.{u} Ab.{u + 1})
    (hA : ∀ S : Profinite.{u}, Limits.IsZero (A.val.obj (Opposite.op S))) : Limits.IsZero A :=
  { unique_to := fun Y =>
      Nonempty.intro
        { default := 0
          uniq := fun a => by
            ext t : 3
            apply (hA t.unop).eq_of_src }
    unique_from := fun Y =>
      Nonempty.intro
        { default := 0
          uniq := fun a => by
            ext t : 3
            apply (hA t.unop).eq_of_tgt } }

theorem Profinite.freePfpng_eq_zero_of_empty (S : Profinite.{u}) [IsEmpty S] (a : S.FreePfpng) :
    a = 0 :=
  by
  let E : Limits.Cone (S.fintype_diagram ⋙ freePfpngFunctor) :=
    ProFiltPseuNormGrp₁.boundedCone ⟨Ab.explicitLimitCone.{u, u} _, Ab.explicitLimitConeIsLimit _⟩
  let hE : Limits.IsLimit E := ProFiltPseuNormGrp₁.boundedConeIsLimit _
  let ee : S.free_pfpng ≅ E.X := (Limits.limit.isLimit _).conePointUniqueUpToIso hE
  apply_fun ee.hom; swap
  · intro x y h; apply_fun ee.inv at h ; simpa using h
  rw [ee.hom.map_zero]; ext T t
  obtain ⟨s⟩ := t
  apply IsEmpty.elim _ (s : S); assumption

theorem Profinite.isZero_of_empty (S : Profinite.{u}) [IsEmpty S] :
    Limits.IsZero S.condensedFreePfpng :=
  by
  apply Condensed.isZero_of_isZero_obj
  intro T
  dsimp [Profinite.condensedFreePfpng]
  dsimp [CompHausFiltPseuNormGrp.Presheaf]
  apply is_zero_Ab
  rintro ⟨⟨f, hf⟩⟩; ext t; change f t = 0
  apply Profinite.freePfpng_eq_zero_of_empty

theorem CategoryTheory.Abelian.isIso_of_mono_of_isZero {A : Type _} [Category A] [Abelian A]
    {X Y : A} (f : X ⟶ Y) [Mono f] (hY : Limits.IsZero Y) : IsIso f :=
  by
  use 0; simp; constructor
  rw [← cancel_mono f]
  apply hY.eq_of_tgt
  apply hY.eq_of_tgt

instance Profinite.epi_free'ToCondensedFreePfpng_of_empty (S : Profinite.{u}) [IsEmpty S] :
    Epi S.free'ToCondensedFreePfpng :=
  by
  suffices is_iso S.free'_to_condensed_free_pfpng by skip; infer_instance
  apply CategoryTheory.Abelian.isIso_of_mono_of_isZero
  apply Profinite.isZero_of_empty

-- Do a case split on `[nonempty S]` here.
instance Profinite.epi_free'ToCondensedFreePfpng (S : Profinite.{u}) :
    Epi S.free'ToCondensedFreePfpng :=
  by
  by_cases hS : Nonempty S; · skip; infer_instance
  simp only [not_nonempty_iff] at hS 
  skip; infer_instance

instance Profinite.isIso_free'ToCondensedFreePfpng (S : Profinite.{u}) :
    IsIso S.free'ToCondensedFreePfpng :=
  isIso_of_mono_of_epi _

def Profinite.freeToPfpng (S : Profinite.{u}) :
    condensedSetToCondensedAb.obj S.toCondensed ⟶ S.condensedFreePfpng :=
  (condensedAbCondensedSetAdjunction.homEquiv _ _).symm S.toCondensedFreePfpng

attribute [simps hom_app] AddCommGroupCat.freeIsoFree'

instance Profinite.isIso_freeToPfpng (S : Profinite.{u}) : IsIso S.freeToPfpng :=
  by
  suffices
    S.free_to_pfpng =
      (CondensedSet_to_Condensed_Ab_iso.app S.to_Condensed).hom ≫ S.free'_to_condensed_free_pfpng
    by rw [this]; infer_instance
  rw [Iso.app_hom]
  delta Profinite.free'ToCondensedFreePfpng Profinite.free'Lift Profinite.freeToPfpng
    condensedSetToCondensedAbIso Sheaf.adjunction condensedAbCondensedSetAdjunction
    condensedAbCondensedSetAdjunction'
  ext T : 4
  dsimp only [Adjunction.mkOfHomEquiv_homEquiv, Functor.mapIso_hom, Quiver.Hom.forgetAb,
    Sheaf.Hom.comp_val, condensedAbToCondensedSet_map, Sheaf.composeEquiv_symm_apply_val,
    presheaf_to_Sheaf_map_val, NatTrans.comp_app, CategoryTheory.isoWhiskerLeft_hom, CategoryTheory.isoWhiskerRight_hom,
    CategoryTheory.whiskerLeft_app, CategoryTheory.whiskerRight_app]
  rw [← NatTrans.comp_app, CategoryTheory.GrothendieckTopology.sheafifyMap_sheafifyLift]
  congr 4; clear T
  ext T : 2
  dsimp only [CategoryTheory.whiskeringRight_map_app_app, CategoryTheory.whiskeringRight_obj_map, NatTrans.comp_app,
    Adjunction.whiskerRight, Adjunction.mkOfUnitCounit_homEquiv_symm_apply, CategoryTheory.whiskerLeft_app,
    CategoryTheory.whiskerRight_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
  rw [← NatTrans.naturality_assoc]
  congr 1
  dsimp only [AddCommGroupCat.adj, AddCommGroupCat.adj', Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.ofNatIsoLeft, Adjunction.mkOfHomEquiv_counit_app, Equiv.invFun_as_coe,
    Equiv.symm_trans_apply, Iso.symm_hom, Adjunction.equivHomsetLeftOfNatIso_symm_apply]
  simp only [Equiv.symm_symm]
  erw [← Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app, Category.id_comp]

theorem freePfpng_profinite_natural_map_aux (S T : Profinite.{u}) (f : S ⟶ T) :
    f ≫ T.toFreePfpng =
      S.toFreePfpng ≫
        (ProFiltPseuNormGrp₁.level.obj 1).map ((Profinite.extend freePfpngFunctor).map f) :=
  by
  apply
    (Limits.isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj 1)
        (Limits.limit.isLimit _)).hom_ext
  intro W;
  dsimp [Profinite.toFreePfpng, Profinite.freePfpngLevelIso,
    Limits.IsLimit.conePointUniqueUpToIso, Limits.IsLimit.map]
  simp only [Category.assoc]
  erw [(Limits.isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj 1)
        (Limits.limit.isLimit (T.fintype_diagram ⋙ freePfpngFunctor))).fac]
  erw [Limits.limit.lift_π]
  swap; infer_instance
  simp only [← Functor.map_comp, Limits.limit.lift_π]
  dsimp [Profinite.changeCone]
  simp only [Functor.map_comp]
  erw [(Limits.isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj 1)
        (Limits.limit.isLimit (S.fintype_diagram ⋙ freePfpngFunctor))).fac_assoc]
  erw [Limits.limit.lift_π_assoc]
  ext;
  dsimp [Profinite.asLimitCone, FintypeCat.freePfpngUnit, FreePfpng.map, ProFiltPseuNormGrp₁.level]
  rcases x with ⟨x⟩
  simp only [Finset.filter_congr_decidable]
  erw [Finset.sum_filter, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.filter_congr_decidable, Finset.sum_const, Nat.smul_one_eq_coe,
    Finset.sum_const_zero, add_zero]
  rw [Finset.filter_filter]
  split_ifs
  · symm; norm_cast; rw [Finset.card_eq_one]
    use(W.comap f.2).proj a
    rw [Finset.eq_singleton_iff_nonempty_unique_mem]
    constructor
    · rw [Finset.filter_nonempty_iff]
      use(W.comap f.2).proj a
      refine' ⟨Finset.mem_univ _, h, rfl⟩
    · rintro ⟨q⟩ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff] at hq 
      erw [hq.2]
  · symm; norm_cast
    simp only [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    rintro ⟨q⟩ -; push_neg; intro hh
    rw [← hh] at h 
    erw [discrete_quotient.map_proj_apply] at h 
    contrapose! h
    let e : W.comap f.2 → W := DiscreteQuotient.map (le_refl _)
    apply_fun e at h ; exact h

def freePfpngProfiniteNaturalMap :
    profiniteToCondensed ⋙ condensedSetToCondensedAb ⟶
      Profinite.extend freePfpngFunctor ⋙
        pFPNG₁ToCHFPNG₁ₑₗ ⋙ cHFPNG₁ToCHFPNGₑₗ ⋙ CompHausFiltPseuNormGrp.toCondensed
    where
  app X := X.freeToPfpng
  naturality S T f :=
    by
    -- we should be able to precompose with the natural map `S.to_Condensed ⟶ S.free'`
    -- how do we do that?
    -- Answer: use `adjunction.hom_equiv`.
    dsimp only [Functor.comp_map]
    dsimp only [Profinite.freeToPfpng]
    apply_fun Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _
    simp only [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit, Functor.map_comp]
    simp only [NatTrans.naturality, Category.assoc, NatTrans.naturality_assoc]
    dsimp only [Profinite.condensedFreePfpng]
    have := Condensed_Ab_CondensedSet_adjunction.unit.naturality (Profinite_to_Condensed.map f)
    dsimp only [Functor.comp_map] at this 
    slice_lhs 1 2 => rw [← this]; clear this
    dsimp only [Functor.id_map]; simp only [Category.assoc]
    have := Condensed_Ab_CondensedSet_adjunction.unit.naturality S.to_condensed_free_pfpng
    dsimp only [Functor.comp_map] at this 
    slice_rhs 1 2 => erw [← this]; clear this
    dsimp only [Functor.id_map]; simp only [Category.assoc]
    have := Condensed_Ab_CondensedSet_adjunction.right_triangle_components
    slice_rhs 2 3 => erw [this]; clear this
    erw [Category.id_comp]
    slice_lhs 2 3 => erw [← NatTrans.naturality]
    simp only [Functor.id_map, Category.assoc]
    have := Condensed_Ab_CondensedSet_adjunction.right_triangle_components
    slice_lhs 3 4 => rw [this]; clear this
    erw [Category.comp_id]
    ext W ⟨t⟩ : 7; change W.unop ⟶ S at t 
    dsimp [Profinite.toCondensedFreePfpng, CompHausFiltPseuNormGrp.levelCondensedDiagramCocone,
      Ab.ulift, Profinite.toFreePfpngLevel]
    erw [← comp_apply]
    erw [← comp_apply]
    erw [← comp_apply]
    rw [freePfpng_profinite_natural_map_aux _ _ f]; rfl

instance freePfpngProfiniteNaturalMap_isIso : IsIso freePfpngProfiniteNaturalMap :=
  by
  apply (config := { instances := false }) NatIso.isIso_of_isIso_app
  intro X
  apply X.is_iso_free_to_pfpng

def freePfpngProfiniteIsoAux :
    condensify (freePfpngFunctor ⋙ pFPNG₁ToCHFPNG₁ₑₗ) ≅
      ((Profinite.extend freePfpngFunctor ⋙ pFPNG₁ToCHFPNG₁ₑₗ) ⋙ cHFPNG₁ToCHFPNGₑₗ) ⋙
        CompHausFiltPseuNormGrp.toCondensed :=
  isoWhiskerRight
    (isoWhiskerRight (Profinite.extendCommutes freePfpngFunctor pFPNG₁ToCHFPNG₁ₑₗ).symm
      cHFPNG₁ToCHFPNGₑₗ)
    CompHausFiltPseuNormGrp.toCondensed

/-- Prop 2.1 of Analytic.pdf -/
def freePfpngProfiniteIso :
    condensify (freePfpngFunctor ⋙ pFPNG₁ToCHFPNG₁ₑₗ) ≅
      profiniteToCondensed ⋙ condensedSetToCondensedAb :=
  freePfpngProfiniteIsoAux ≪≫ (asIso freePfpngProfiniteNaturalMap).symm

