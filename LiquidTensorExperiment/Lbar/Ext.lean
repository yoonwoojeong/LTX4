import LiquidTensorExperiment.Lbar.ExtAux4
import LiquidTensorExperiment.Lbar.Iota

#align_import Lbar.ext

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

namespace Lbar

open ProFiltPseuNormGrpWithTinv₁ ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

open BoundedHomotopyCategory

variable (r r')

def tinvSub (S : Profinite.{u}) (V : SemiNormedGroupCat.{u}) [NormedWithAut r V] (i : ℤ) :
    ((ext' i).obj (op <| (Lbar.condensed.{u} r').obj S)).obj V.toCond ⟶
      ((ext' i).obj (op <| (Lbar.condensed.{u} r').obj S)).obj V.toCond :=
  ((ext' i).map ((condensifyTinv _).app S).op).app _ -
    ((ext' i).obj _).map
      (Condensed.ofTopAbMap NormedWithAut.t.inv.toAddMonoidHom (NormedAddGroupHom.continuous _))

-- move me
attribute [simps] Condensed.ofTopAbMap

variable (S : Profinite.{0}) (V : SemiNormedGroupCat.{0})

variable [CompleteSpace V] [SeparatedSpace V]

variable (r')

-- TODO(!): TC loop? using "by apply_instance" causes a maximum TC error
instance (X : Profinite.{0}) :
    PreservesLimitsOfShape.{0, 0, 0, 0, 1, 1} (DiscreteQuotient.{0} ↥X) (pFPNGT₁ToCHFPNG₁ₑₗ.{0} r')
    where

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

def condensifyIsoExtend :
    condensify (fintypeLbar.{0, 0} r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r') ≅
      Profinite.extend (fintypeLbar.{0, 0} r') ⋙
        pFPNGT₁ToCHFPNG₁ₑₗ r' ⋙ cHFPNG₁ToCHFPNGₑₗ.{0} ⋙ CompHausFiltPseuNormGrp.toCondensed.{0} :=
  (((whiskeringLeft _ _ _).mapIso <|
          Profinite.extendCommutes (fintypeLbar.{0, 0} r') (pFPNGT₁ToCHFPNG₁ₑₗ r')).app
      (cHFPNG₁ToCHFPNGₑₗ.{0} ⋙ CompHausFiltPseuNormGrp.toCondensed.{0})).symm

def condensifyIsoExtend' :
    (condensify (fintypeLbar.{0, 0} r' ⋙ pFPNGT₁ToCHFPNG₁ₑₗ r')).obj S ≅
      ((Profinite.extend (fintypeLbar.{0, 0} r')).obj S).toCondensed :=
  (condensifyIsoExtend r').app S

section MoveMe

--universes u'
open Profinite

variable {C : Type u} [Category.{v} C] (F : FintypeCat.{v} ⥤ C)

variable {D : Type u'} [Category.{v} D]

variable [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]

@[reassoc]
theorem extendCommutes_comp_extend_extends' (G : C ⥤ D)
    [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) G]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ G)] :
    whiskerLeft FintypeCat.toProfinite (extendCommutes F G).hom =
      (Functor.associator _ _ _).inv ≫
        whiskerRight (extendExtends _).hom G ≫ (extendExtends _).inv :=
  by rw [← Category.assoc, Iso.eq_comp_inv, Profinite.extendCommutes_comp_extendExtends]

@[reassoc]
theorem extendCommutes_comp_extend_extends'' (G : C ⥤ D)
    [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) G]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ G)] :
    whiskerLeft FintypeCat.toProfinite (extendCommutes F G).inv =
      (extendExtends _).hom ≫
        whiskerRight (extendExtends _).inv G ≫ (Functor.associator _ _ _).hom :=
  by
  rw [← Iso.inv_comp_eq, ← CategoryTheory.isoWhiskerLeft_inv, Iso.comp_inv_eq, CategoryTheory.isoWhiskerLeft_hom,
    Lbar.extendCommutes_comp_extend_extends', Category.assoc, Iso.hom_inv_id_assoc, ←
    CategoryTheory.isoWhiskerRight_hom, ← CategoryTheory.isoWhiskerRight_inv, Iso.inv_hom_id_assoc]

end MoveMe

theorem condensifyTinv_iso :
    condensifyTinv (fintypeLbar.{0, 0} r') ≫ (condensifyIsoExtend r').hom =
      (condensifyIsoExtend r').hom ≫ @whiskerRight _ _ _ _ _ _ _ _ (tinvNatTrans _) _ :=
  by
  delta Tinv_cond condensifyTinv condensifyNonstrict Lbar.condensifyIsoExtend' Lbar.condensifyIsoExtend
  ext S : 2
  rw [Iso.symm_hom, Iso.app_inv, Functor.mapIso_inv, NatTrans.comp_app, NatTrans.comp_app,
    CategoryTheory.whiskeringLeft_map_app_app, ← Iso.app_inv, ← Functor.mapIso_inv, Iso.comp_inv_eq,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.comp_map, Functor.comp_map, CategoryTheory.whiskerRight_app,
    CategoryTheory.whiskerRight_app, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [Iso.app_inv, Iso.app_hom, ← CategoryTheory.whiskerRight_app, ← CategoryTheory.whiskerRight_app, ← NatTrans.comp_app, ←
    NatTrans.comp_app]
  congr 1
  refine' nonstrict_extend_ext _ _ r'⁻¹ (1 * (r'⁻¹ * 1)) _ _ _
  · intro X; apply nonstrictExtendBoundBy
  · intro X
    apply ComphausFilteredPseudoNormedGroupHom.BoundBy.comp
    apply ComphausFilteredPseudoNormedGroupHom.BoundBy.comp
    · apply StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.boundByOne
    · apply tinvBoundBy
    · apply StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.boundByOne
  · rw [whisker_left_comp, whisker_left_comp, ← CategoryTheory.whiskerRight_left, ← CategoryTheory.whiskerRight_left,
      Lbar.extendCommutes_comp_extend_extends', Lbar.extendCommutes_comp_extend_extends'']
    rw [nonstrictExtend_whiskerLeft]
    ext X : 2
    simp only [CategoryTheory.whiskerLeft_app, CategoryTheory.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc,
      Functor.map_comp]
    slice_rhs 2 3 => skip
    congr 2
    simp only [← Iso.app_hom, ← Iso.app_inv, ← Functor.mapIso_hom, ← Functor.mapIso_inv,
      Category.assoc, Iso.eq_inv_comp]
    ext x : 1
    exact
      (ComphausFilteredPseudoNormedGroupWithTinvHom.map_tinv
          ((Profinite.extendExtends (fintypeLbar.{0, 0} r')).app X).hom x).symm

theorem condensifyTinv_iso' :
    (condensifyTinv (fintypeLbar.{0, 0} r')).app S ≫ (condensifyIsoExtend' r' S).hom =
      (condensifyIsoExtend' r' S).hom ≫
        ((Profinite.extend (fintypeLbar.{0, 0} r')).obj S).tinvCond :=
  by
  have := condensify_Tinv_iso r'
  apply_fun fun η => η.app S at this 
  exact this

def usefulCommsq (i : ℤ) (ι : ULift.{1} ℕ → ℝ≥0) (hι : Monotone ι) [NormedWithAut r V] :=
  shiftSubId.commsq
    (ExtQprime.tinv2 r r' BreenDeligne.eg.data (fun c n => c * BreenDeligne.eg.κ r r' n)
      (fun c n => r' * (c * BreenDeligne.eg.κ r r' n)) ((Lbar.functor.{0, 0} r').obj S) V i)
    ι hι

section

open BreenDeligne thm95.UniversalConstants

variable (i : ℕ)

theorem usefulCommsq_bicartesian (ι : ULift.{1} ℕ → ℝ≥0) (hι : Monotone ι) [NormedWithAut r V]
    (H1 : ∀ j, c₀ r r' eg (fun n => eg.κ r r' n) (eg.κ' r r') (i + 1) ⟨ℤ⟩ ≤ ι j)
    (H2 : ∀ j, k (eg.κ' r r') i ^ 2 * ι j ≤ ι (j + 1))
    (H3 : ∀ j, k (eg.κ' r r') (i + 1) ^ 2 * ι j ≤ ι (j + 1)) :
    (usefulCommsq r r' S V i ι hι).Bicartesian :=
  by
  apply
    shiftSubId.bicartesian_iso _ _ (extQprimeIsoAuxSystem r' _ _ _ V i).symm
      (extQprimeIsoAuxSystem r' _ _ _ V i).symm ι hι (extQprimeIsoAuxSystem_comm' _ _ _ _ _ _ _ _)
  rw [← CategoryTheory.whiskerRight_twice]
  refine' shiftSubId.bicartesian (auxSystem.incl'.{0, 1} r r' _ _ _ (eg.κ r r')) _ i ι hι _ _ _
  · apply (config := { instances := false }) SystemOfComplexes.shift_eq_zero
    pick_goal 3; · apply Thm94.explicit r r' _ _ (eg.κ' r r')
    any_goals infer_instance
    · intro j
      refine' le_trans _ ((c₀_mono _ _ _ _ _ _ (i + 1)).out.trans (H1 j))
      rw [Nat.add_sub_cancel]
    · exact H2
  · apply (config := { instances := false }) SystemOfComplexes.shift_eq_zero
    pick_goal 3; · apply Thm94.explicit r r' _ _ (eg.κ' r r')
    any_goals infer_instance
    · exact H1
    · exact H3
  · intro c n
    let κ := eg.κ r r'
    apply auxSystem.shortExact r r' _ _ _ (fun c n => r' * (c * κ n)) κ
    intro c; dsimp; infer_instance

theorem bicartesian_of_isZero {𝓒 : Type _} [Category 𝓒] [Abelian 𝓒] {A B C D : 𝓒} (f₁ : A ⟶ B)
    (g₁ : A ⟶ C) (g₂ : B ⟶ D) (f₂ : C ⟶ D) (h : Commsq f₁ g₁ g₂ f₂) (hA : IsZero A) (hB : IsZero B)
    (hC : IsZero C) (hD : IsZero D) : h.Bicartesian :=
  by
  delta Commsq.Bicartesian
  apply (config := { instances := false }) ShortExact.mk
  · refine' ⟨fun X f g h => _⟩; apply hA.eq_of_tgt
  · refine' ⟨fun X f g h => _⟩; apply hD.eq_of_src
  · apply CategoryTheory.Limits.exact_of_isZero ((CategoryTheory.Limits.isZero_biprod _ _ hB hC).of_iso (h.sum.iso (SumStr.biprod _ _)))

theorem isZero_pi {𝓒 : Type _} [Category 𝓒] [Abelian 𝓒] {ι : Type _} (f : ι → 𝓒) [HasProduct f]
    (hf : ∀ i, IsZero (f i)) : IsZero (∏ f) :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero]
  ext ⟨j⟩
  apply (hf j).eq_of_tgt

theorem usefulCommsq_bicartesian_neg (ι : ULift.{1} ℕ → ℝ≥0) (hι : Monotone ι) [NormedWithAut r V]
    (i : ℤ) (hi : i < 0) : (usefulCommsq r r' S V i ι hι).Bicartesian :=
  by
  have : 1 + i ≤ 0 := by linarith only [hi]
  apply Lbar.bicartesian_of_isZero <;> apply Lbar.isZero_pi <;> intro x <;>
    apply ext_single_right_isZero _ _ 1 _ _ (ChainComplex.boundedByOne _) this

theorem isIso_sq {𝓒 : Type _} [Category 𝓒] {X Y : 𝓒} (f₁ : X ⟶ X) (f₂ : Y ⟶ Y) (e : X ≅ Y)
    (h : f₁ ≫ e.hom = e.hom ≫ f₂) (h₁ : IsIso f₁) : IsIso f₂ := by rw [← Iso.inv_comp_eq] at h ;
  rw [← h]; infer_instance

open CategoryTheory.Preadditive

theorem isIso_sq' {𝓒 : Type _} [Category 𝓒] [Abelian 𝓒] [EnoughProjectives 𝓒]
    {X Y Z : BoundedHomotopyCategory 𝓒} (f₁ : X ⟶ X) (f₂ : Y ⟶ Y) (f₃ : Z ⟶ Z) (e : Y ≅ X)
    (h : e.hom ≫ f₁ = f₂ ≫ e.hom) (i : ℤ)
    (h₁ : IsIso (((ext i).map f₁.op).app Z - ((ext i).obj _).map f₃)) :
    IsIso (((ext i).map f₂.op).app Z - ((ext i).obj _).map f₃) :=
  by
  refine' Lbar.isIso_sq _ _ ((Functor.mapIso _ e.op).app _) _ h₁
  rw [Iso.app_hom, Functor.mapIso_hom, sub_comp, comp_sub, NatTrans.naturality, ←
    NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, Iso.op_hom, ←
    op_comp, ← op_comp, h]

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem isIso_tinvSub [NormedWithAut r V] : ∀ i, IsIso (tinvSub r r' S V i) :=
  by
  erw [Condensed.bd_lemma _ _ _ _]
  swap; · apply Lbar.Obj.noZeroSMulDivisors
  intro i
  refine' Lbar.isIso_sq' _ _ _ (Functor.mapIso _ <| Lbar.condensifyIsoExtend' _ _) _ _ _
  · refine' CategoryTheory.Functor.map _ _; refine' Tinv_cond _
  · rw [Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp, condensify_Tinv_iso']
  revert i
  refine'
    tinv2_iso_of_bicartesian' r BreenDeligne.eg (fun c n => c * BreenDeligne.eg.κ r r' n)
      (fun c n => r' * (c * BreenDeligne.eg.κ r r' n)) ((Lbar.functor.{0, 0} r').obj S) V _
  rintro (i | (_ | i))
  · refine' ⟨ι r r' i, hι r r' i, _, _, _, _⟩
    · intro s m
      apply Lbar.sufficiently_increasing_eg
    · intro s m
      apply Lbar.sufficiently_increasing_eg'
    all_goals apply Lbar.usefulCommsq_bicartesian
    · rintro ⟨j⟩; apply Hι1
    · rintro ⟨j⟩; apply Hι2a
    · rintro ⟨j⟩; apply Hι2b
    · rintro ⟨j⟩; apply Hι1'
    · rintro ⟨j⟩; apply Hι2b
    · rintro ⟨j⟩; apply Hι2c
  · refine' ⟨ι r r' 0, hι r r' 0, _, _, _, _⟩
    · intro s m; apply Lbar.sufficiently_increasing_eg
    · intro s m; apply Lbar.sufficiently_increasing_eg'
    · apply Lbar.usefulCommsq_bicartesian_neg; decide
    · apply Lbar.usefulCommsq_bicartesian
      · rintro ⟨j⟩; apply Hι1
      · rintro ⟨j⟩; apply Hι2a
      · rintro ⟨j⟩; apply Hι2b
  · refine' ⟨ι r r' 0, hι r r' 0, _, _, _, _⟩
    · intro s m; apply Lbar.sufficiently_increasing_eg
    · intro s m; apply Lbar.sufficiently_increasing_eg'
    · apply Lbar.usefulCommsq_bicartesian_neg; decide
    · apply Lbar.usefulCommsq_bicartesian_neg
      rw [Int.negSucc_eq']
      simp only [Int.ofNat_succ, neg_add_rev, sub_add_cancel, add_neg_lt_iff_le_add', add_zero]
      decide

/-- Thm 9.4bis of [Analytic]. More precisely: the first observation in the proof 9.4 => 9.1. -/
theorem isIso_Tinv2 [NormedWithAut r V] (hV : ∀ v : V, NormedWithAut.t.inv v = 2 • v) :
    ∀ i,
      IsIso
        (((ext' i).map ((condensifyTinv2 (fintypeLbar.{0, 0} r')).app S).op).app
          (Condensed.ofTopAb ↥V)) :=
  by
  intro i
  rw [condensifyTinv2_eq, ← Functor.flip_obj_map, NatTrans.app_sub, CategoryTheory.op_sub,
    NatTrans.app_nsmul, CategoryTheory.op_nsmul, two_nsmul, NatTrans.id_app, op_id,
    Functor.map_sub, Functor.map_add, CategoryTheory.Functor.map_id]
  convert is_iso_Tinv_sub r r' S V i using 2
  suffices Condensed.ofTopAbMap (NormedAddGroupHom.toAddMonoidHom normed_with_aut.T.inv) _ = 2 • 𝟙 _
    by rw [this, two_nsmul, Functor.map_add, CategoryTheory.Functor.map_id]; rfl
  ext T f t
  dsimp only [Condensed.ofTopAbMap_val, CategoryTheory.whiskerRight_app, Ab.uLift_map_apply_down,
    AddMonoidHom.mk'_apply, ContinuousMap.coe_mk, Function.comp_apply]
  erw [hV, two_nsmul, two_nsmul]
  rfl

end

end Lbar

