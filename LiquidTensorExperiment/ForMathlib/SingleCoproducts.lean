import LiquidTensorExperiment.ForMathlib.Derived.ExtCoproducts
import LiquidTensorExperiment.ForMathlib.ProductOp

#align_import for_mathlib.single_coproducts

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]

namespace HomologicalComplex

noncomputable def sigmaSingleComponent {α : Type v} (i : ℤ) (X : α → A) :
    (∐ fun a => (single A (ComplexShape.up ℤ) i).obj (X a)).pt i ≅ ∐ X
    where
  hom :=
    (isColimitOfPreserves (eval _ _ i)
          (colimit.isColimit
            (Discrete.functor fun a => (single A (ComplexShape.up ℤ) i).obj (X a)))).desc
      ⟨∐ X, Discrete.natTrans fun a => eqToHom (if_pos rfl) ≫ Sigma.ι _ a.as⟩
  inv :=
    Sigma.desc fun a =>
      eqToHom (if_pos rfl).symm ≫
        (Sigma.ι (fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)) a).f i
  hom_inv_id :=
    by
    apply
      (CategoryTheory.Limits.isColimitOfPreserves (eval A (ComplexShape.up ℤ) i)
          (colimit.isColimit
            (Discrete.functor fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)))).hom_ext
    rintro ⟨j⟩
    dsimp
    rw [Category.comp_id]
    slice_lhs 1 2 =>
      erw [(CategoryTheory.Limits.isColimitOfPreserves (eval A (ComplexShape.up ℤ) i)
            (colimit.isColimit
              (Discrete.functor fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)))).fac]
    dsimp
    rw [Category.assoc, colimit.ι_desc]; dsimp
    simp only [CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp]
  inv_hom_id := by
    ext ⟨j⟩
    simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, Category.assoc, Category.comp_id]
    erw [(CategoryTheory.Limits.isColimitOfPreserves (eval A (ComplexShape.up ℤ) i)
          (colimit.isColimit
            (Discrete.functor fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)))).fac]
    dsimp; simp only [CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp]

noncomputable def sigmaSingleComponentOfEq {α : Type v} (j i : ℤ) (X : α → A) (h : j = i) :
    (∐ fun a => (single A (ComplexShape.up ℤ) i).obj (X a)).pt j ≅ ∐ X :=
  eqToIso (congr_arg _ h) ≪≫ sigmaSingleComponent i X

noncomputable def singleSigmaIso {α : Type v} (i : ℤ) (X : α → A) :
    (single A (ComplexShape.up ℤ) i).obj (∐ X) ≅ ∐ fun a => (single A _ i).obj (X a)
    where
  hom :=
    { f := fun j =>
        if h : j = i then
          eqToHom (if_pos h) ≫
            Sigma.desc fun a => Sigma.ι _ _ ≫ (sigmaSingleComponentOfEq j i X h).inv
        else 0
      comm' := by
        rintro j k (rfl : _ = _)
        rcases eq_or_ne j i with (rfl | hij)
        · rw [dif_pos rfl, dif_neg]; swap; · exact succ_ne_self j
          simp only [Category.assoc, single_obj_d, zero_comp, Preadditive.IsIso.comp_left_eq_zero,
            HomologicalComplex.sigmaSingleComponentOfEq, Iso.trans_inv, HomologicalComplex.sigmaSingleComponent, CategoryTheory.eqToHom_refl,
            colimit.ι_desc_assoc, eq_to_iso, Category.comp_id, Cofan.mk_ι_app, colimit.ι_desc]
          ext; simp
        · rw [dif_neg hij, zero_comp]
          split_ifs with hij'
          · subst i; simp only [single_obj_d, zero_comp]
          · rw [comp_zero] }
  inv :=
    Sigma.desc fun a =>
      { f := fun j =>
          if h : j = i then eqToHom (if_pos h) ≫ Sigma.ι _ _ ≫ eqToHom (if_pos h).symm else 0
        comm' := by
          rintro j k (rfl : _ = _)
          rcases eq_or_ne j i with (rfl | hij)
          · rw [dif_pos rfl, dif_neg]; swap; · exact succ_ne_self j
            simp only [Category.assoc, single_obj_d, zero_comp, comp_zero]
          · rw [dif_neg hij, zero_comp]
            split_ifs with hij'
            · subst i; simp only [single_obj_d, zero_comp]
            · rw [comp_zero] }
  hom_inv_id := by
    ext j; dsimp
    rcases eq_or_ne j i with (rfl | hij)
    · rw [dif_pos rfl]
      simp only [Category.assoc]
      rw [← IsIso.eq_inv_comp (eq_to_hom _)]; swap; infer_instance
      ext ⟨a⟩;
      simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, Category.assoc, CategoryTheory.inv_eqToHom,
        Category.comp_id]
      dsimp [HomologicalComplex.sigmaSingleComponentOfEq, HomologicalComplex.sigmaSingleComponent]
      simp only [Category.comp_id, colimit.ι_desc_assoc, Cofan.mk_ι_app, Category.assoc]
      rw [← HomologicalComplex.comp_f, colimit.ι_desc]; dsimp
      rw [dif_pos rfl]; simp only [CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp]
    · rw [dif_neg hij, zero_comp, if_neg hij, eq_comm, ← CategoryTheory.Limits.isZero_iff_id_eq_zero]
      exact Limits.isZero_zero A
  inv_hom_id := by
    apply colimit.hom_ext; rintro ⟨j⟩
    rw [colimit.ι_desc_assoc, Cofan.mk_ι_app, Category.comp_id]
    ext n
    simp only [comp_f]
    rcases eq_or_ne n i with (rfl | hin)
    · rw [dif_pos rfl, dif_pos rfl]
      simp only [Category.assoc, CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp,
        colimit.ι_desc, Cofan.mk_ι_app, HomologicalComplex.sigmaSingleComponentOfEq, Iso.trans_inv,
        HomologicalComplex.sigmaSingleComponent, colimit.ι_desc_assoc, eq_to_iso, Category.comp_id]
    · rw [dif_neg hin, zero_comp]; apply IsZero.eq_of_src
      dsimp; rw [if_neg hin]; exact Limits.isZero_zero A

noncomputable instance preservesCoproductsSingle {α : Type v} (i : ℤ) :
    PreservesColimitsOfShape (Discrete α) (single A (ComplexShape.up ℤ) i) :=
  preservesCoproductsAux _ (fun X => singleSigmaIso _ _) fun X a =>
    by
    ext j
    simp only [comp_f, single_map_f, single_sigma_iso]
    split_ifs with hj
    · subst j
      simp only [Category.assoc, CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, eq_to_iso_refl,
        Iso.trans_inv, Iso.refl_inv, Category.comp_id, HomologicalComplex.sigmaSingleComponent, Category.id_comp,
        colimit.ι_desc, Cofan.mk_ι_app, HomologicalComplex.sigmaSingleComponentOfEq]
    · apply IsZero.eq_of_tgt
      apply IsZero.of_iso _ ((HomologicalComplex.eval _ _ j).mapIso <| single_sigma_iso _ _).symm
      dsimp; rw [if_neg hj]; apply Limits.isZero_zero

end HomologicalComplex

namespace HomotopyCategory

noncomputable instance preservesCoproductsSingle {α : Type v} (i : ℤ) :
    PreservesColimitsOfShape (Discrete α) (single A i) :=
  Limits.compPreservesColimitsOfShape (HomologicalComplex.single A (ComplexShape.up ℤ) i)
    (quotient A (ComplexShape.up ℤ))

end HomotopyCategory

namespace BoundedHomotopyCategory

instance uniformlyBoundedSingle {α : Type v} (i : ℤ) (X : α → A) :
    UniformlyBounded fun a : α => (single A i).obj (X a) :=
  by
  refine' ⟨⟨i + 1, fun a k hk => _⟩⟩
  dsimp only [single, HomotopyCategory.single, Functor.comp_obj, Function.comp_apply,
    HomotopyCategory.quotient_obj_as, HomologicalComplex.single]
  rw [if_neg]
  · exact is_zero_zero _
  · rintro rfl; linarith only [hk]

instance hasCoproduct_of_shape_single {α : Type v} (i : ℤ) (X : α → A) :
    HasCoproduct fun a => (single A i).obj (X a) :=
  BoundedHomotopyCategory.hasCoproduct_of_uniform_bound _

noncomputable def singleSigmaIso {α : Type v} (i : ℤ) (X : α → A) :
    (single A i).obj (∐ X) ≅ ∐ fun a : α => (single A i).obj (X a) :=
  let E :
    Discrete.functor X ⋙ HomotopyCategory.single A i ≅
      (Discrete.functor fun a : α => (single A i).obj (X a)) ⋙ forget A :=
    Discrete.natIso fun a => Iso.refl _
  mkIso <|
    preservesColimitIso (HomotopyCategory.single A i) (Discrete.functor X) ≪≫
      HasColimit.isoOfNatIso E ≪≫
        (preservesColimitIso (forget A) <| Discrete.functor fun a => (single A i).obj (X a)).symm

noncomputable instance preservesCoproductsSingle {α : Type v} [HasCoproducts.{v} A] (i : ℤ) :
    PreservesColimitsOfShape (Discrete α) (single A i) :=
  preservesCoproductsAux _ (fun X => singleSigmaIso i X)
    (by
      intro X a
      let f : _ := _; show _ = f
      apply (forget A).map_injective; rw [Functor.map_comp]
      dsimp only [single_sigma_iso, forget, mk_iso, Iso.trans_hom, Iso.symm_hom, _root_.id, single]
      simp_rw [← Category.assoc]; rw [Iso.comp_inv_eq]
      change _ = (forget A).map f ≫ _
      erw [ι_preserves_colimits_iso_hom]
      erw [ι_preserves_colimits_iso_hom]
      rw [HasColimit.isoOfNatIso_ι_hom]
      simp only [Discrete.natIso_hom_app, Iso.refl_hom, Category.id_comp]
      rfl)

variable [EnoughProjectives A]

noncomputable instance preservesCoproductsExt' {α : Type v} (i : ℤ) (Y : A) [AB4 A] :
    PreservesColimitsOfShape (Discrete α) ((ext' i).flip.obj Y).rightOp :=
  preservesCoproductsAux _
    (fun X => by
      let e₁ : (single A 0).obj (∐ X) ≅ ∐ _ := single_sigma_iso _ _
      let e₂ :
        ((Ext i).obj (Opposite.op ((single A 0).obj (∐ X)))).obj ((single A 0).obj Y) ≅
          ((Ext i).obj (Opposite.op (∐ _))).obj ((single A 0).obj Y) :=
        ((Ext i).mapIso e₁.symm.op).app _
      let e₃ :
        ((Ext i).obj (Opposite.op (∐ fun a : α => (single A 0).obj (X a)))).obj
            ((single A 0).obj Y) ≅
          ∏ _ :=
        Ext_coproduct_iso _ _ _
      let e₄ :
        Opposite.op
            (∏ fun a : α =>
              ((Ext i).obj (Opposite.op ((single A 0).obj (X a)))).obj ((single A 0).obj Y)) ≅
          ∐ _ :=
        CategoryTheory.Limits.opProductIso _
      refine' (e₃.symm ≪≫ e₂.symm).op ≪≫ e₄)
    (by
      intro X a; dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.op_hom, ext', op_comp, ← Iso.op_inv]
      simp only [← Category.assoc]
      rw [← Iso.eq_comp_inv, Iso.comp_inv_eq]
      dsimp only [CategoryTheory.Limits.opProductIso]
      erw [colimit.ι_desc]
      dsimp
      simp_rw [← op_comp]
      rw [ι_Ext_coproduct_iso']
      rw [← NatTrans.comp_app, ← Functor.map_comp, ← op_comp]
      congr 4
      dsimp [single_sigma_iso]; simp only [Category.assoc]
      dsimp [CategoryTheory.preservesColimitIso, IsColimit.coconePointUniqueUpToIso]
      erw [(PreservesColimit.preserves (colimit.isColimit (Discrete.functor X))).fac_assoc]
      erw [colimit.ι_desc_assoc]
      dsimp; simpa)

end BoundedHomotopyCategory

