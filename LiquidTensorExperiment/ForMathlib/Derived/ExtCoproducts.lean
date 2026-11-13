import LiquidTensorExperiment.ForMathlib.Derived.BoundedHomotopyCategory
import LiquidTensorExperiment.ForMathlib.IsQuasiIsoSigma
import LiquidTensorExperiment.ForMathlib.CoprodOp
import LiquidTensorExperiment.ForMathlib.Derived.Example

#align_import for_mathlib.derived.ext_coproducts

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]

open scoped ZeroObject

namespace BoundedHomotopyCategory

noncomputable def cofan {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X] :
    Cofan X :=
  Cofan.mk
    { val := (HomotopyCategory.colimitCofan fun a : α => (X a).val).pt
      bdd := by
        obtain ⟨n, hn⟩ := HomotopyCategory.IsUniformlyBoundedAbove.cond (val ∘ X)
        use n; intro i hi
        dsimp [HomotopyCategory.colimitCofan]
        let e : (∐ fun a : α => (X a).val.as).pt i ≅ ∐ fun a : α => (X a).val.as.pt i :=
          HomotopyCategory.coproductIso _ _
        refine' is_zero_of_iso_of_zero _ e.symm
        apply CategoryTheory.isZero_colimit
        intro j
        refine' hn j.as _ hi }
    fun a => (HomotopyCategory.colimitCofan fun a : α => (X a).val).ι.app ⟨a⟩

noncomputable def isColimitCofan {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] : IsColimit (cofan X)
    where
  desc S := (HomotopyCategory.isColimitCofan fun a : α => (X a).val).desc ((forget A).mapCocone S)
  fac := by
    intro S j
    erw [(HomotopyCategory.isColimitCofan fun a : α => (X a).val).fac ((forget A).mapCocone S) j]
    rfl
  uniq := by
    intro S m hm
    apply (HomotopyCategory.isColimitCofan fun a : α => (X a).val).hom_ext
    intro j
    specialize hm j
    erw [hm]
    erw [(HomotopyCategory.isColimitCofan fun a : α => (X a).val).fac]
    rfl

instance hasCoproduct_of_uniform_bound {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] : HasCoproduct X :=
  by
  constructor; apply Nonempty.intro
  refine' ⟨cofan X, is_colimit_cofan X⟩

instance isKProjectiveSigma {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X]
    [∀ a, HomotopyCategory.IsKProjective (X a).val] :
    HomotopyCategory.IsKProjective (sigmaObj X).val :=
  by
  let e : sigma_obj X ≅ (cofan X).pt :=
    (colimit.is_colimit _).coconePointUniqueUpToIso (is_colimit_cofan X)
  let ee := (forget A).mapIso e
  suffices HomotopyCategory.IsKProjective ((forget A).obj (cofan X).pt) by skip;
    apply HomotopyCategory.isKProjectiveOfIso _ _ ee.symm
  dsimp [forget, cofan]
  infer_instance

noncomputable instance forgetPreservesCoproduct {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] : PreservesColimit (Discrete.functor X) (forget A) :=
  by
  apply preserves_colimit_of_preserves_colimit_cocone (is_colimit_cofan X)
  let E : (forget A).mapCocone (cofan X) ≅ HomotopyCategory.colimitCofan (val ∘ X) :=
    cocones.ext (iso.refl _) _
  rotate_left
  · intro a; dsimp [forget, cofan]; simpa only [category.comp_id]
  apply is_colimit.of_iso_colimit _ E.symm
  apply HomotopyCategory.isColimitCofan

theorem isQuasiIsoSigma [AB4 A] {α : Type v} (X P : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] [UniformlyBounded P] (π : ∀ a, P a ⟶ X a)
    [∀ a, HomotopyCategory.IsQuasiIso (π a)] :
    HomotopyCategory.IsQuasiIso
      (Sigma.desc fun a : α => π a ≫ Sigma.ι X a : sigmaObj P ⟶ sigmaObj X) :=
  by
  let t := sigma.desc fun a : α => π a ≫ sigma.ι X a
  change HomotopyCategory.IsQuasiIso ((forget A).map t)
  let eP : (forget A).obj (∐ P) ≅ ∐ fun a => (forget A).obj (P a) :=
    preserves_colimit_iso (forget A) _
  let eX : (forget A).obj (∐ X) ≅ ∐ fun a => (forget A).obj (X a) :=
    preserves_colimit_iso (forget A) _
  let s : (∐ fun a => (forget A).obj (P a)) ⟶ ∐ fun a => (forget A).obj (X a) :=
    sigma.desc fun a : α => π a ≫ sigma.ι (val ∘ X) a
  suffices (forget A).map t = eP.hom ≫ s ≫ eX.inv
    by
    rw [this]
    apply HomotopyCategory.isQuasiIsoComp
  apply (is_colimit_of_preserves (forget A) (colimit.is_colimit _)).hom_ext
  swap; infer_instance
  intro a
  dsimp [t, s, eP, eX, preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso]
  rw [← (forget A).map_comp, colimit.ι_desc]
  slice_rhs 0 1 =>
    erw [(is_colimit_of_preserves (forget A) (colimit.is_colimit (discrete.functor P))).fac]
  erw [colimit.ι_desc]
  dsimp; simp only [category.assoc]; erw [colimit.ι_desc]
  dsimp; simp only [functor.map_comp]; rfl

variable [EnoughProjectives A]

noncomputable def uniformπ {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X] :
    sigmaObj (replaceUniformly X) ⟶ sigmaObj X :=
  Sigma.desc fun a => πUniformly _ _ ≫ Sigma.ι _ a

instance isQuasiIsoSigmaMapπUniformly [AB4 A] {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] : HomotopyCategory.IsQuasiIso (uniformπ X) :=
  isQuasiIsoSigma _ _ _

open Opposite

noncomputable def extCoproductIso [AB4 A] {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] (i : ℤ) (Y) :
    ((ext i).obj (op (sigmaObj X))).obj Y ≅ piObj fun a : α => ((ext i).obj (op (X a))).obj Y :=
  extIso i _ _ _ (uniformπ X) ≪≫
    CategoryTheory.preadditiveYonedaCoproductIso (replaceUniformly X) (Y⟦i⟧) ≪≫
      CategoryTheory.piIso _ _ fun a => (extIso i _ _ _ (πUniformly X a)).symm

theorem ι_ext_coprodut_iso [AB4 A] {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] (i : ℤ) (Y) (j) :
    (extCoproductIso X i Y).inv ≫ ((ext i).map (Sigma.ι X j : X j ⟶ ∐ X).op).app Y = Pi.π _ _ :=
  by
  rw [iso.inv_comp_eq]
  dsimp [Ext_coproduct_iso, pi_iso]
  simp only [category.assoc, limit.lift_π, fan.mk_π_app]
  simp only [← category.assoc]; rw [iso.eq_comp_inv]
  dsimp [Ext, Ext_iso]
  --ext t, simp only [comp_apply],
  dsimp [preadditive_yoneda_coproduct_iso, preadditive_yoneda_coproduct_to_product]
  simp only [category.assoc, limit.lift_π]
  ext t; simp only [comp_apply]; dsimp
  simp only [← category.assoc]; congr 1
  apply lift_ext (∐ X).π; swap; infer_instance
  dsimp [uniform_π]
  simp

theorem ι_ext_coproduct_iso' [AB4 A] {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] (i : ℤ) (Y) (j) :
    (extCoproductIso X i Y).Hom ≫ Pi.π _ _ = ((ext i).map (Sigma.ι X j : X j ⟶ ∐ X).op).app Y := by
  rw [← iso.eq_inv_comp, ι_Ext_coprodut_iso]

theorem extCoproductIso_naturality [AB4 A] {α : Type v} (X₁ X₂ : α → BoundedHomotopyCategory A)
    [UniformlyBounded X₁] [UniformlyBounded X₂] (g : X₁ ⟶ X₂) (i : ℤ) (Y) :
    ((ext i).map (Sigma.desc fun b => g b ≫ Sigma.ι X₂ b : ∐ X₁ ⟶ ∐ X₂).op).app Y ≫
        (extCoproductIso _ _ _).Hom =
      (extCoproductIso _ _ _).Hom ≫ Pi.lift fun b => Pi.π _ b ≫ ((ext i).map (g b).op).app Y :=
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
  apply lift_ext (∐ X₂).π; swap; infer_instance
  dsimp [Quiver.Hom.unop_op]
  simp only [category.assoc, lift_lifts, lift_lifts_assoc]
  dsimp [uniform_π]
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc, lift_lifts_assoc]

theorem extCoproductIso_naturality' [AB4 A] {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] (i : ℤ) (Y₁ Y₂) (f : Y₁ ⟶ Y₂) :
    ((ext i).obj (op (sigmaObj X))).map f ≫ (extCoproductIso _ _ _).Hom =
      (extCoproductIso _ _ _).Hom ≫ Pi.lift fun a => Pi.π _ a ≫ ((ext i).obj _).map f :=
  by
  dsimp only [Ext_coproduct_iso, Ext, Ext0, Ext_iso, functor.comp_map, whiskering_left,
    whisker_left, iso.trans_hom, functor.map_iso, preadditive_yoneda_coproduct_iso, functor.flip,
    pi_iso, as_iso, preadditive_yoneda_coproduct_to_product, functor.comp_map, functor.comp_obj]
  simp only [category.assoc]
  simp only [Quiver.Hom.unop_op, iso.op_hom, replacement_iso_hom, iso.op_inv, replacement_iso_inv,
    iso.symm_mk]
  apply limit.hom_ext
  intro j
  simp only [category.assoc, limit.lift_π, fan.mk_π_app, limit.lift_π_assoc]
  erw [nat_trans.naturality]
  erw [nat_trans.naturality_assoc]
  erw [nat_trans.naturality_assoc]
  rfl

end BoundedHomotopyCategory

-- TODO: find better names... And move this stuff!
instance chainComplexEmbedCofanUniformlyBounded {α : Type v} (X : α → ChainComplex A ℕ) :
    BoundedHomotopyCategory.UniformlyBounded fun a =>
      ChainComplex.toBoundedHomotopyCategory.obj (X a) :=
  by
  constructor; use 1; intro a i hi
  rcases i with ((_ | i) | _)
  · exfalso; revert hi; decide
  · exact is_zero_zero _
  · exfalso; revert hi; decide

universe u'

def whiskerDiscreteFunctor {α : Type v} {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (X : α → C) : Discrete.functor X ⋙ F ≅ Discrete.functor (F.obj ∘ X) :=
  Discrete.natIso fun i => Iso.refl _

noncomputable theorem preservesCoproductsAux {α : Type v} {C : Type u} {D : Type u'}
    [Category.{v} C] [Category.{v} D] (F : C ⥤ D) [HasCoproductsOfShape α C]
    [∀ X : α → C, HasCoproduct fun a => F.obj (X a)]
    (e : ∀ X : α → C, F.obj (∐ X) ≅ ∐ fun a => F.obj (X a))
    (he : ∀ (X : α → C) (a : α), F.map (Sigma.ι X a) ≫ (e X).Hom = Sigma.ι _ a) :
    PreservesColimitsOfShape (Discrete α) F :=
  by
  constructor; intro K
  let E : K ≅ discrete.functor (K.obj ∘ discrete.mk) := discrete.nat_iso fun ⟨a⟩ => iso.refl _
  apply preserves_colimit_of_iso_diagram _ E.symm
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit _)
  swap; infer_instance
  let P := _; change is_colimit P
  let P' := (cocones.precompose (whiskerDiscreteFunctor F _).inv).obj P
  suffices is_colimit P' by exact is_colimit.precompose_inv_equiv _ _ this
  apply is_colimit.of_iso_colimit (colimit.is_colimit _); swap
  change has_colimit (discrete.functor fun a : α => F.obj (K.obj ⟨a⟩))
  infer_instance
  symm
  fapply cocones.ext
  apply e
  rintro ⟨a⟩
  convert (he fun b => K.obj ⟨b⟩) a
  dsimp [P', whiskerDiscreteFunctor]
  rw [category.id_comp]

noncomputable instance homologicalComplexEmbedPreservesCoproducts {α : Type v} {M N : Type}
    (c₁ : ComplexShape M) (c₂ : ComplexShape N) (e : c₁.Embedding c₂) :
    PreservesColimitsOfShape (Discrete α)
      (HomologicalComplex.embed e : HomologicalComplex A _ ⥤ _) :=
  preservesCoproductsAux (HomologicalComplex.embed e : HomologicalComplex A _ ⥤ _)
    (fun X : α → HomologicalComplex A c₁ =>
      HomologicalComplex.Hom.isoOfComponents
        (fun i => by
          rcases h : e.r i with (_ | j)
          · refine' HomologicalComplex.Embed.xIsoOfNone _ h ≪≫ _
            refine' _ ≪≫ (preserves_colimit_iso (HomologicalComplex.eval A c₂ i) _).symm
            refine' (is_zero.iso_zero _).symm
            apply is_zero_colimit
            intro a
            dsimp
            exact HomologicalComplex.Embed.x_isZero_of_none _ h
          · refine' HomologicalComplex.Embed.xIsoOfSome _ h ≪≫ _
            refine' preserves_colimit_iso (HomologicalComplex.eval _ _ _) _ ≪≫ _
            refine' _ ≪≫ (preserves_colimit_iso (HomologicalComplex.eval _ _ _) _).symm
            refine' has_colimit.iso_of_nat_iso _
            refine' discrete.nat_iso _
            intro b
            dsimp
            refine' (HomologicalComplex.Embed.xIsoOfSome _ h).symm)
        (by
          intro i j h
          rcases h₁ : e.r i with (_ | i') <;> rcases h₂ : e.r j with (_ | j')
          · apply is_zero.eq_of_src
            apply HomologicalComplex.Embed.x_isZero_of_none
            assumption
          · apply is_zero.eq_of_src
            apply HomologicalComplex.Embed.x_isZero_of_none
            assumption
          · apply is_zero.eq_of_tgt
            refine' is_zero.of_iso _ (preserves_colimit_iso (HomologicalComplex.eval _ _ _) _)
            apply is_zero_colimit; intro b
            apply HomologicalComplex.Embed.x_isZero_of_none
            assumption
          · simp_rw [h₁, h₂]; dsimp
            simp only [category.assoc]
            rw [← iso.eq_inv_comp]
            dsimp [HomologicalComplex.embed, HomologicalComplex.Embed.obj]
            rw [HomologicalComplex.Embed.d_of_some_of_some (∐ X) h₁ h₂]
            simp only [category.assoc, iso.inv_hom_id_assoc]
            apply (is_colimit_of_preserves (HomologicalComplex.eval A c₁ i') _).hom_ext
            rintro ⟨a⟩
            simp only [functor.map_cocone_ι_app, colimit.cocone_ι, HomologicalComplex.eval_map]
            slice_lhs 1 2 => erw [(is_colimit_of_preserves (HomologicalComplex.eval A c₁ i') _).fac]
            dsimp
            simp only [has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app, iso.symm_hom,
              category.assoc, ι_preserves_colimits_iso_inv, HomologicalComplex.eval_map,
              HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc]
            dsimp
            rw [iso.inv_comp_eq]
            slice_rhs 3 4 => erw [(is_colimit_of_preserves (HomologicalComplex.eval A c₁ j') _).fac]
            dsimp
            simp only [has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app, iso.symm_hom,
              category.assoc, ι_preserves_colimits_iso_inv, HomologicalComplex.eval_map]
            slice_rhs 1 3 => erw [← HomologicalComplex.Embed.d_of_some_of_some (X a) h₁ h₂]
            apply colimit.is_colimit
            infer_instance))
    (-- still annoying
    by
      intro X a; ext i
      rcases h : e.r i with (_ | i')
      · apply is_zero.eq_of_tgt
        refine' is_zero.of_iso _ (preserves_colimit_iso (HomologicalComplex.eval _ _ _) _)
        apply is_zero_colimit; intro b
        apply HomologicalComplex.Embed.x_isZero_of_none
        exact h
      dsimp [HomologicalComplex.Hom.isoOfComponents]
      simp_rw [h]; dsimp
      simp only [← category.assoc, iso.comp_inv_eq]
      simp_rw [← iso.eq_comp_inv, category.assoc]
      slice_rhs 1 2 => erw [(is_colimit_of_preserves (HomologicalComplex.eval A c₂ i) _).fac]
      dsimp
      simp only [has_colimit.iso_of_nat_iso_ι_inv, discrete.nat_iso_inv_app, iso.symm_inv,
        category.assoc, ι_preserves_colimits_iso_inv, HomologicalComplex.eval_map]
      apply HomologicalComplex.Embed.f_of_some)

noncomputable def embedCoproductIso {α : Type v} (X : α → ChainComplex A ℕ) :
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj (∐ X) ≅
      ∐ fun a : α => (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj (X a) :=
  preservesColimitIso (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp) _ ≪≫
    HasColimit.isoOfNatIso (whiskerDiscreteFunctor _ _)

noncomputable def chainComplexEmbedCofanIso {α : Type v} (X : α → ChainComplex A ℕ) :
    (BoundedHomotopyCategory.cofan fun a => ChainComplex.toBoundedHomotopyCategory.obj (X a)) ≅
      (Cocones.precompose (whiskerDiscreteFunctor _ X).inv).obj
        (ChainComplex.toBoundedHomotopyCategory.mapCocone (colimit.cocone (Discrete.functor X))) :=
  Cocones.ext
    (BoundedHomotopyCategory.mkIso <|
      (HomotopyCategory.quotient _ _).mapIso <| (embedCoproductIso X).symm)
    (by
      rintro ⟨a⟩
      dsimp [BoundedHomotopyCategory.cofan, HomotopyCategory.colimitCofan, whiskerDiscreteFunctor]
      erw [category.id_comp, ← functor.map_comp]
      congr 1
      dsimp [embedCoproductIso]
      simp only [category.assoc]
      erw [colimit.ι_desc_assoc]
      rw [iso.comp_inv_eq]
      erw [(is_colimit_of_preserves (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp)
            _).fac]
      dsimp [whiskerDiscreteFunctor]
      rw [category.id_comp])

noncomputable instance chainComplexToBoundedHomotopyCategoryPreservesCoproducts {α : Type v} :
    PreservesColimitsOfShape (Discrete α)
      (ChainComplex.toBoundedHomotopyCategory : ChainComplex A _ ⥤ _) :=
  by
  constructor; intro K
  let E : K ≅ discrete.functor (K.obj ∘ discrete.mk) := discrete.nat_iso fun ⟨a⟩ => iso.refl _
  apply preserves_colimit_of_iso_diagram _ E.symm
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit _)
  let Q : α → BoundedHomotopyCategory A := fun a =>
    chain_complex.to_bounded_homotopy_category.obj (K.obj ⟨a⟩)
  let P := _; change is_colimit P
  let T :
    discrete.functor (K.obj ∘ discrete.mk) ⋙ ChainComplex.toBoundedHomotopyCategory ≅
      discrete.functor Q :=
    discrete.nat_iso fun _ => iso.refl _
  let P' := (cocones.precompose T.inv).obj P
  suffices is_colimit P' by exact is_colimit.precompose_inv_equiv _ _ this
  apply is_colimit.of_iso_colimit (BoundedHomotopyCategory.isColimitCofan Q)
  swap; infer_instance
  apply chainComplexEmbedCofanIso

