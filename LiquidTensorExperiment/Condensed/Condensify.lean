import LiquidTensorExperiment.PseudoNormedGroup.Category.StrictProFiltPseuNormGrpWithTinv
import LiquidTensorExperiment.LaurentMeasures.Functor
import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.Condensed.Rescale
import LiquidTensorExperiment.Condensed.Exact
import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import condensed.condensify

noncomputable section

universe u

open scoped NNReal

open CategoryTheory

variable {C D : Type _} [Category C] [Category D] (r' : ℝ≥0) [Fact (0 < r')]

abbrev CategoryTheory.NatTrans.conjBy {F G : C ⥤ D} (α : F ≅ G) (β : G ⟶ G) : F ⟶ F :=
  α.Hom ≫ β ≫ α.inv

open CategoryTheory

open ProFiltPseuNormGrpWithTinv₁ CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp

variable {r'}

/-- Given a functor `F` from `Fintype` to `CompHausFiltPseuNormGrp₁`, we can obtain
a functor `Profinite ⥤ CompHausFiltPseuNormGrp₁` by expressing any profinite
set as a limit of finite sets and taking a limit in the target category.
We then compose with the functor to condensed abelian groups, and the result is
called `condensify F`.
-/
def condensify (F : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
    Profinite.{u} ⥤ Condensed.{u} Ab.{u + 1} :=
  (Profinite.extend.{u} F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) ⋙ toCondensed.{u}

variable {F G H : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}

variable (α β : F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ.{u})

variable (c cα cβ cαβ : ℝ≥0) [Fact (0 < c)] [Fact (0 < cα)] [Fact (0 < cβ)] [Fact (0 < cαβ)]

/-- Given functors `F G : Fintype ⥤ CompHausFiltPseuNormGrp₁` and a
natural transformation `η` between the induced functors `Fintype ⥤ CompHausFiltPseuNormGrp`
(obtained by composing with `CHFPNG₁_to_CHFPNGₑₗ`), such that the components of `η` are bounded
by a *single* `c : ℝ≥0`, this is the morphism between the associated condensed abelian groups.
-/
def condensifyNonstrict (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) (c : ℝ≥0)
    [Fact (0 < c)] (h : ∀ X, (α.app X).BoundBy c) : condensify F ⟶ condensify G :=
  whiskerRight (nonstrictExtend.{u} α c h) toCondensed

theorem condensifyNonstrict_id (c : ℝ≥0) [Fact (0 < c)]
    (h : ∀ X, (NatTrans.app (𝟙 (F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u})) X).BoundBy c) :
    condensifyNonstrict (𝟙 _) c h = 𝟙 _ := by
  simp only [condensifyNonstrict, nonstrictExtend_id, whisker_right_id']; rfl

theorem condensifyNonstrict_comp (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ)
    (β : G ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ H ⋙ cHFPNG₁ToCHFPNGₑₗ) (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, (β.app X).BoundBy cβ) (hαβ : ∀ X, ((α ≫ β).app X).BoundBy cαβ) :
    condensifyNonstrict (α ≫ β) cαβ hαβ =
      condensifyNonstrict α cα hα ≫ condensifyNonstrict β cβ hβ :=
  by
  simp only [condensifyNonstrict, whisker_right_comp]
  rw [nonstrictExtend_comp cα cβ cαβ _ _ _ _, whisker_right_comp]

def condensifyMap (α : F ⟶ G) : condensify F ⟶ condensify G :=
  condensifyNonstrict (whiskerRight α _) 1 fun X =>
    (ComphausFilteredPseudoNormedGroupHom.mkOfStrictStrict _ _).boundByOne

theorem condensifyMap_id (F : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
    condensifyMap (𝟙 F) = 𝟙 (condensify F) :=
  condensifyNonstrict_id _ _

theorem condensifyMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    condensifyMap (α ≫ β) = condensifyMap α ≫ condensifyMap β :=
  by
  dsimp only [condensifyMap]
  simp only [whisker_right_comp]
  apply condensifyNonstrict_comp

def condensifyDef (F : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}) :
    condensify F ≅ Profinite.extend.{u} F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⋙ toCondensed.{u} :=
  Iso.refl _

/-- Given a family `F` of profinitely filtered normed groups with `T⁻¹`,
  indexed by a category (and such that all the morphisms in the family are strict),
  `Tinv_nat_trans` is the associated (possibly non-strict) morphism from the
  corresponding family of `CompHaus`ly filtered pseudo-normed groups coming from `T⁻¹`.
  -/
def tinvNatTrans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
    (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r') ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶
      (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r') ⋙ cHFPNG₁ToCHFPNGₑₗ
    where
  app X := ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv
  naturality' X Y f := by ext x; exact ((F.map f).map_tinv x).symm

/-- The endomorphism `T⁻¹ - 2` of a strict family of profinitely-filtered
pseudo-normed groups with `T⁻¹`, considered as a possibly non-strict
endomorphism of the associated `CompHaus`ly filtered pseudo-normed groups. -/
def tinv2NatTrans (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
    (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r') ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶
      (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r') ⋙ cHFPNG₁ToCHFPNGₑₗ :=
  tinvNatTrans F - 2 • 𝟙 _

theorem tinvBoundBy (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
    ((tinvNatTrans F).app X).BoundBy r'⁻¹ :=
  ProfinitelyFilteredPseudoNormedGroupWithTinv.tinvBoundBy

theorem twoidBoundBy (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
    ComphausFilteredPseudoNormedGroupHom.BoundBy
      ((2 • 𝟙 ((F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r') ⋙ cHFPNG₁ToCHFPNGₑₗ)).app X) 2 :=
  by
  simp only [nat_trans.app_nsmul, nat_trans.id_app]
  refine' ((ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ 1 _).nsmul 2).Mono _ _
  norm_num

theorem tinv2BoundBy (F : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') (X : C) :
    ((tinv2NatTrans F).app X).BoundBy (r'⁻¹ + 2) :=
  (tinvBoundBy F X).sub (twoidBoundBy F X)

@[reassoc]
theorem tinvNatTrans_comp {F G : C ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'} (α : F ⟶ G) :
    tinvNatTrans F ≫
        @whiskerRight _ _ _ _ _ _ F G α (pFPNGT₁ToCHFPNG₁ₑₗ r' ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) =
      @whiskerRight _ _ _ _ _ _ F G α (pFPNGT₁ToCHFPNG₁ₑₗ r' ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) ≫
        tinvNatTrans G :=
  by ext X x; exact (α.app X).map_tinv x

-- move me
instance fact_inv_pos : Fact (0 < r'⁻¹) :=
  ⟨nnreal.inv_pos.2 <| Fact.out _⟩

--set_option pp.universes true
/-- Given a functor from `Fintype` to `ProFiltPseuNormGrpWithTinv₁`, the `T⁻¹` action
is a nonstrict morphism which is natural (see `Tinv_nat_trans`) and thus
induces a morphism on the associated condensed abelian groups.
-/
def condensifyTinv (F : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
    condensify.{u} (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r') ⟶ condensify.{u} (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r') :=
  condensifyNonstrict (tinvNatTrans _) r'⁻¹ (tinvBoundBy _)

/-- A variant of `condensify_Tinv` with a different bound, given by `r'⁻¹ + 2`.
-/
def condensifyTinv2 (F : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
    condensify.{u} (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r') ⟶ condensify.{u} (F ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r') :=
  condensifyNonstrict (tinv2NatTrans _) (r'⁻¹ + 2) (tinv2BoundBy _)

theorem condensifyMap_comp_Tinv {F G : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}
    (α : F ⟶ G) :
    condensifyMap (whiskerRight α (pFPNGT₁ToCHFPNG₁ₑₗ r')) ≫ condensifyTinv G =
      condensifyTinv F ≫ condensifyMap (whiskerRight α (pFPNGT₁ToCHFPNG₁ₑₗ r')) :=
  by
  delta condensifyMap condensifyTinv
  rw [← condensifyNonstrict_comp 1 r'⁻¹ r'⁻¹, ← condensifyNonstrict_comp r'⁻¹ 1 r'⁻¹]
  swap;
  · intro X
    rw [nat_trans.comp_app]
    rw [← one_mul r'⁻¹]
    apply ComphausFilteredPseudoNormedGroupHom.BoundBy.comp (tinvBoundBy F X)
    simp only [whisker_right_twice, whisker_right_app, functor.comp_map, cHFPNG₁ToCHFPNGₑₗ_map]
    apply StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.boundByOne
  swap;
  · intro X
    rw [nat_trans.comp_app]
    rw [← mul_one r'⁻¹]
    refine' ComphausFilteredPseudoNormedGroupHom.BoundBy.comp _ (tinvBoundBy G X)
    simp only [whisker_right_twice, whisker_right_app, functor.comp_map, cHFPNG₁ToCHFPNGₑₗ_map]
    apply StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.boundByOne
  · simp only [whisker_right_twice, tinvNatTrans_comp]

section

theorem condensifyNonstrict_map_add (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, (β.app X).BoundBy cβ) (hαβ : ∀ X, ((α + β).app X).BoundBy cαβ) :
    condensifyNonstrict (α + β) cαβ hαβ =
      condensifyNonstrict α cα hα + condensifyNonstrict β cβ hβ :=
  by
  delta condensifyNonstrict
  rw [nonstrictExtend_map_add _ _ cα cβ cαβ hα hβ]
  rfl

theorem condensifyNonstrict_map_neg (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, ((-α).app X).BoundBy cβ) :
    condensifyNonstrict (-α) cβ hβ = -condensifyNonstrict α cα hα :=
  by
  delta condensifyNonstrict
  rw [nonstrictExtend_map_neg _ _ cβ hα]
  rfl

theorem condensifyNonstrict_map_sub (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, (β.app X).BoundBy cβ) (hαβ : ∀ X, ((α - β).app X).BoundBy cαβ) :
    condensifyNonstrict (α - β) cαβ hαβ =
      condensifyNonstrict α cα hα - condensifyNonstrict β cβ hβ :=
  by
  delta condensifyNonstrict
  rw [nonstrictExtend_map_sub _ _ cα cβ cαβ hα hβ]
  rfl

theorem condensifyNonstrict_map_nsmul (n : ℕ) (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, ((n • α).app X).BoundBy cβ) :
    condensifyNonstrict (n • α) cβ hβ = n • condensifyNonstrict α cα hα :=
  by
  delta condensifyNonstrict
  rw [nonstrictExtend_map_nsmul _ _ cβ n hα]
  clear hβ
  induction' n with n ih
  · rw [zero_smul, zero_smul]; rfl
  · rw [succ_nsmul, succ_nsmul, ← ih]; rfl

-- lemma nonstrict_extend_Tinv (F : Fintype.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
--   nonstrict_extend (Tinv_nat_trans F) r'⁻¹ (Tinv_bound_by _) =
--     nat_trans.conj_by (iso_whisker_right
--       (Profinite.extend_commutes F (PFPNG₁_to_CHFPNG₁ₑₗ.{u} r')).symm enlarging_functor.{u})
--         (Tinv_nat_trans (Profinite.extend F)) :=
-- begin
--   refine nonstrict_extend_ext' _ _ r'⁻¹ (nonstrict_extend_bound_by _ _ _) _ _,
--   { admit },
--   { rw [nonstrict_extend_whisker_left],
--     simp only [whisker_left_comp, ← iso_whisker_left_hom, ← iso_whisker_left_inv,
--       ← iso.inv_comp_eq, iso.eq_comp_inv, category.assoc],
--     admit }
-- end
theorem condensifyNonstrict_Tinv (F : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
    condensifyNonstrict (tinvNatTrans F) r'⁻¹ (tinvBoundBy _) = condensifyTinv F :=
  rfl

theorem condensifyNonstrict_whiskerRight_enlarging (α : F ⟶ G) :
    (condensifyNonstrict (whiskerRight α _) 1 fun X =>
        (ComphausFilteredPseudoNormedGroupHom.mkOfStrictStrict _ _).boundByOne) =
      condensifyMap α :=
  rfl

end

open PseudoNormedGroup (filtration)

theorem exact_of_iso_comp_exact {V : Type u} [Category V] [Limits.HasImages V]
    [Limits.HasZeroMorphisms V] [Limits.HasEqualizers V] {A B C D : V} (f : A ⟶ B) {g : B ⟶ C}
    {h : C ⟶ D} (hf : IsIso f) (hgh : Exact g h) : Exact (f ≫ g) h := by rwa [exact_iso_comp]

theorem condensifyNonstrict_exact (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ.{u})
    (β : G ⟶ H) (c : ℝ≥0) [Fact (0 < c)] (h : ∀ X, (α.app X).BoundBy c) (cα cβ : ℝ≥0 → ℝ≥0)
    (hcα : id ≤ cα) (hcβ : id ≤ cβ) (H1 : ∀ S, Function.Injective (α.app S))
    (H2a : ∀ S, α.app S ≫ (whiskerRight β _).app S = 0)
    (H2b :
      ∀ S c',
        β.app S ⁻¹' {0} ∩ filtration (G.obj S) c' ⊆ α.app S '' filtration (F.obj S) (cα c' * c⁻¹))
    (H3b : ∀ S c', filtration (H.obj S) c' ⊆ β.app S '' filtration (G.obj S) (cβ c'))
    (X : Profinite.{u}) :
    ShortExact ((condensifyNonstrict α c h).app X) ((condensifyMap β).app X) :=
  by
  apply (config := { instances := false }) short_exact.mk
  · simp only [condensifyNonstrict, nonstrictExtend, whisker_right_comp]
    repeat' apply (config := { instances := false }) mono_comp <;> try infer_instance
    apply Condensed.mono_toCondensed_map
    apply strongly_exact_extend_zero_left
    intro S
    apply (config := { instances := false }) strongly_exact_of_mono
    rw [AddCommGroupCat.mono_iff_injective]
    exact H1 S
  · dsimp only [condensifyMap, condensifyNonstrict]
    rw [nonstrictExtend_whiskerRight_enlarging]
    apply Condensed.epi_toCondensed_map _ cβ
    apply strongly_exact_extend_zero_right
    intro S
    apply strongly_exact_of_epi _ _ _ hcβ (H3b S)
  · dsimp only [condensifyMap, condensifyNonstrict]
    rw [nonstrictExtend_whiskerRight_enlarging]
    simp only [nonstrictExtend, whisker_right_comp, nat_trans.comp_app, category.assoc]
    repeat' apply exact_of_iso_comp_exact <;> [infer_instance; skip]
    apply Condensed.exact_of_stronglyExact _ _ cα
    apply strongly_exact.extend
    intro S
    refine' ⟨_, _, hcα⟩
    · ext x; specialize H2a S; apply_fun fun φ => φ.toFun at H2a ; exact congr_fun H2a x
    · intro c' y hy
      obtain ⟨x, hx, rfl⟩ := H2b S c' hy
      refine' ⟨@Rescale.of c _ x, hx, rfl⟩

theorem condensify_exact (α : F ⟶ G) (β : G ⟶ H) (cα cβ : ℝ≥0 → ℝ≥0) (hcα : id ≤ cα) (hcβ : id ≤ cβ)
    (H1 : ∀ S, Function.Injective (α.app S)) (H2a : ∀ S, α.app S ≫ β.app S = 0)
    (H2b : ∀ S c, β.app S ⁻¹' {0} ∩ filtration (G.obj S) c ⊆ α.app S '' filtration (F.obj S) (cα c))
    (H3b : ∀ S c, filtration (H.obj S) c ⊆ β.app S '' filtration (G.obj S) (cβ c))
    (X : Profinite.{u}) : ShortExact ((condensifyMap α).app X) ((condensifyMap β).app X) :=
  by
  refine' condensifyNonstrict_exact _ _ 1 _ cα cβ hcα hcβ H1 _ _ H3b _
  · intro S; simp only [whisker_right_app, ← functor.map_comp, H2a]; rfl
  · intro S c' x H; obtain ⟨x, hx, rfl⟩ := H2b S c' H
    refine' ⟨x, PseudoNormedGroup.filtration_mono _ hx, rfl⟩
    simp only [inv_one, mul_one]

-- move me
attribute [simps] Ab.ulift

theorem condensifyTinv2_eq (F : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r') :
    condensifyTinv2 F = condensifyTinv F - 2 • 𝟙 _ :=
  by
  delta condensifyTinv2 tinv2NatTrans
  rw [condensifyNonstrict_map_sub _ _ r'⁻¹ 2 (r'⁻¹ + 2) (tinvBoundBy _) (twoidBoundBy _),
    condensifyNonstrict_map_nsmul _ 1 2, condensifyNonstrict_Tinv]
  swap
  · intro; exact ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ 1 _
  rw [← condensifyMap_id, ← condensifyNonstrict_whiskerRight_enlarging]
  rfl

open CategoryTheory.Preadditive

theorem condensifyMap_comp_Tinv2 {F G : FintypeCat.{u} ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r'}
    (α : F ⟶ G) :
    condensifyMap (whiskerRight α (pFPNGT₁ToCHFPNG₁ₑₗ r')) ≫ condensifyTinv2 G =
      condensifyTinv2 F ≫ condensifyMap (whiskerRight α (pFPNGT₁ToCHFPNG₁ₑₗ r')) :=
  by
  simp only [condensifyTinv2_eq, comp_sub, sub_comp, comp_nsmul, nsmul_comp,
    condensifyMap_comp_Tinv, category.id_comp, category.comp_id]

