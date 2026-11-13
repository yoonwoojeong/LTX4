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
  Hom :=
    (isColimitOfPreserves (eval _ _ i)
          (colimit.isColimit
            (Discrete.functor fun a => (single A (ComplexShape.up ℤ) i).obj (X a)))).desc
      ⟨∐ X, Discrete.natTrans fun a => eqToHom (if_pos rfl) ≫ Sigma.ι _ a.as⟩
  inv :=
    Sigma.desc fun a =>
      eqToHom (if_pos rfl).symm ≫
        (Sigma.ι (fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)) a).f i
  hom_inv_id' :=
    by
    apply
      (is_colimit_of_preserves (eval A (ComplexShape.up ℤ) i)
          (colimit.is_colimit
            (discrete.functor fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)))).hom_ext
    rintro ⟨j⟩
    dsimp
    rw [category.comp_id]
    slice_lhs 1 2 =>
      erw [(is_colimit_of_preserves (eval A (ComplexShape.up ℤ) i)
            (colimit.is_colimit
              (discrete.functor fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)))).fac]
    dsimp
    rw [category.assoc, colimit.ι_desc]; dsimp
    simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp]
  inv_hom_id' := by
    ext ⟨j⟩
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, category.comp_id]
    erw [(is_colimit_of_preserves (eval A (ComplexShape.up ℤ) i)
          (colimit.is_colimit
            (discrete.functor fun a : α => (single A (ComplexShape.up ℤ) i).obj (X a)))).fac]
    dsimp; simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp]

noncomputable def sigmaSingleComponentOfEq {α : Type v} (j i : ℤ) (X : α → A) (h : j = i) :
    (∐ fun a => (single A (ComplexShape.up ℤ) i).obj (X a)).pt j ≅ ∐ X :=
  eqToIso (congr_arg _ h) ≪≫ sigmaSingleComponent i X

noncomputable def singleSigmaIso {α : Type v} (i : ℤ) (X : α → A) :
    (single A (ComplexShape.up ℤ) i).obj (∐ X) ≅ ∐ fun a => (single A _ i).obj (X a)
    where
  Hom :=
    { f := fun j =>
        if h : j = i then
          eqToHom (if_pos h) ≫
            Sigma.desc fun a => Sigma.ι _ _ ≫ (sigmaSingleComponentOfEq j i X h).inv
        else 0
      comm' := by
        rintro j k (rfl : _ = _)
        rcases eq_or_ne j i with (rfl | hij)
        · rw [dif_pos rfl, dif_neg]; swap; · exact succ_ne_self j
          simp only [category.assoc, single_obj_d, zero_comp, preadditive.is_iso.comp_left_eq_zero,
            sigma_single_component_of_eq, iso.trans_inv, sigma_single_component, eq_to_hom_refl,
            colimit.ι_desc_assoc, eq_to_iso, category.comp_id, cofan.mk_ι_app, colimit.ι_desc]
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
            simp only [category.assoc, single_obj_d, zero_comp, comp_zero]
          · rw [dif_neg hij, zero_comp]
            split_ifs with hij'
            · subst i; simp only [single_obj_d, zero_comp]
            · rw [comp_zero] }
  hom_inv_id' := by
    ext j; dsimp
    rcases eq_or_ne j i with (rfl | hij)
    · rw [dif_pos rfl]
      simp only [category.assoc]
      rw [← is_iso.eq_inv_comp (eq_to_hom _)]; swap; infer_instance
      ext ⟨a⟩;
      simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, inv_eq_to_hom,
        category.comp_id]
      dsimp [sigma_single_component_of_eq, sigma_single_component]
      simp only [category.comp_id, colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc]
      rw [← HomologicalComplex.comp_f, colimit.ι_desc]; dsimp
      rw [dif_pos rfl]; simp only [eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp]
    · rw [dif_neg hij, zero_comp, if_neg hij, eq_comm, ← is_zero_iff_id_eq_zero]
      exact limits.is_zero_zero A
  inv_hom_id' := by
    apply colimit.hom_ext; rintro ⟨j⟩
    rw [colimit.ι_desc_assoc, cofan.mk_ι_app, category.comp_id]
    ext n
    simp only [comp_f]
    rcases eq_or_ne n i with (rfl | hin)
    · rw [dif_pos rfl, dif_pos rfl]
      simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp,
        colimit.ι_desc, cofan.mk_ι_app, sigma_single_component_of_eq, iso.trans_inv,
        sigma_single_component, colimit.ι_desc_assoc, eq_to_iso, category.comp_id]
    · rw [dif_neg hin, zero_comp]; apply is_zero.eq_of_src
      dsimp; rw [if_neg hin]; exact limits.is_zero_zero A

noncomputable instance preservesCoproductsSingle {α : Type v} (i : ℤ) :
    PreservesColimitsOfShape (Discrete α) (single A (ComplexShape.up ℤ) i) :=
  preservesCoproductsAux _ (fun X => singleSigmaIso _ _) fun X a =>
    by
    ext j
    simp only [comp_f, single_map_f, single_sigma_iso]
    split_ifs with hj
    · subst j
      simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, eq_to_iso_refl,
        iso.trans_inv, iso.refl_inv, category.comp_id, sigma_single_component, category.id_comp,
        colimit.ι_desc, cofan.mk_ι_app, sigma_single_component_of_eq]
    · apply is_zero.eq_of_tgt
      apply is_zero.of_iso _ ((HomologicalComplex.eval _ _ j).mapIso <| single_sigma_iso _ _).symm
      dsimp; rw [if_neg hj]; apply limits.is_zero_zero

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
  dsimp only [single, HomotopyCategory.single, functor.comp_obj, Function.comp_apply,
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
      apply (forget A).map_injective; rw [functor.map_comp]
      dsimp only [single_sigma_iso, forget, mk_iso, iso.trans_hom, iso.symm_hom, _root_.id, single]
      simp_rw [← category.assoc]; rw [iso.comp_inv_eq]
      change _ = (forget A).map f ≫ _
      erw [ι_preserves_colimits_iso_hom]
      erw [ι_preserves_colimits_iso_hom]
      rw [has_colimit.iso_of_nat_iso_ι_hom]
      simp only [discrete.nat_iso_hom_app, iso.refl_hom, category.id_comp]
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
        op_product_iso _
      refine' (e₃.symm ≪≫ e₂.symm).op ≪≫ e₄)
    (by
      intro X a; dsimp only [iso.trans_hom, iso.symm_hom, iso.op_hom, ext', op_comp, ← iso.op_inv]
      simp only [← category.assoc]
      rw [← iso.eq_comp_inv, iso.comp_inv_eq]
      dsimp only [op_product_iso]
      erw [colimit.ι_desc]
      dsimp
      simp_rw [← op_comp]
      rw [ι_Ext_coproduct_iso']
      rw [← nat_trans.comp_app, ← functor.map_comp, ← op_comp]
      congr 4
      dsimp [single_sigma_iso]; simp only [category.assoc]
      dsimp [preserves_colimit_iso, is_colimit.cocone_point_unique_up_to_iso]
      erw [(preserves_colimit.preserves (colimit.is_colimit (discrete.functor X))).fac_assoc]
      erw [colimit.ι_desc_assoc]
      dsimp; simpa)

end BoundedHomotopyCategory

