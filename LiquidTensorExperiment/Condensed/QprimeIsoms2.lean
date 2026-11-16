import LiquidTensorExperiment.Condensed.QprimeIsoms

#align_import condensed.Qprime_isoms2

noncomputable section

universe v u u₁ u₂

open CategoryTheory CategoryTheory.Limits BreenDeligne Opposite

open BoundedHomotopyCategory

namespace Condensed

variable (BD : Package)

variable (M N : Condensed.{u} Ab.{u + 1}) (f : M ⟶ N)

theorem homology'FunctorIso_natural' (C₁ C₂ : CochainComplex (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) ℤ)
    (g : C₁ ⟶ C₂) (S : Profinite.{u}ᵒᵖ) (i : ℤ) :
    (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj S).homology'FunctorIso
                (ComplexShape.up ℤ) i).inv.app
          C₁ ≫
        ((homology'Functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (ComplexShape.up ℤ) i).map g).app S =
      CategoryTheory.Functor.map _ g ≫
        (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj S).homology'FunctorIso
                (ComplexShape.up ℤ) i).inv.app
          C₂ :=
  ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj S).homology'FunctorIso _
            i).inv.naturality
      g).symm

theorem homology'FunctorIso_natural (S : ExtrDiscᵒᵖ) (i : ℤ) :
    (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                    (op (unop S).val)).homology'FunctorIso
                (ComplexShape.up ℤ) i).inv.app
          ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj M)) ≫
        ((homology'Functor (Profiniteᵒᵖ ⥤ Ab) (ComplexShape.up ℤ) i).map
              ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f))).app
          (extrDiscToProfinite.op.obj S) =
      CategoryTheory.Functor.map _ (CategoryTheory.Functor.map _ (CategoryTheory.Functor.map _ f)) ≫
        (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                    (op (unop S).val)).homology'FunctorIso
                (ComplexShape.up ℤ) i).inv.app
          ((BD.eval' freeFunc).obj (condensedAbToPresheaf.obj N)) :=
  homology'FunctorIso_natural' _ _ _ _ _

theorem eval_freeAb_iso_component_natural_zero (S : ExtrDiscᵒᵖ) :
    ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                      (op (unop S).val)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
              ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f))).f
          (Int.ofNat 0) ≫
        (EvalFreeAbIso.componentZero BD N (unop S)).hom =
      (EvalFreeAbIso.componentZero BD M (unop S)).hom ≫
        ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map
              (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op (unop S).val)).map
                f.val)).f
          (Int.ofNat 0) :=
  by
  dsimp only [EvalFreeAbIso.componentZero, Functor.mapHomologicalComplex_map_f,
    CategoryTheory.evaluation_obj_map]
  erw [embed_f_0, embed_f_0]
  simp only [Functor.mapBiproduct, Data.evalFunctor_obj_map_f, CategoryTheory.whiskeringRight_obj_map,
    CategoryTheory.whiskerRight_app, Functor.comp_map, Functor.mapIso_hom, biproduct.uniqueUpToIso_hom, ←
    Functor.map_comp]
  congr 2
  apply biproduct.hom_ext; intro j
  simp only [Category.assoc]
  erw [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc]
  simp only [Functor.mapBicone_π, biproduct.bicone_π, evaluation_obj_map]
  simp only [← NatTrans.comp_app]; congr 1
  rw [biproduct.map_π]; rfl

theorem eval_freeAb_iso_component_natural_neg (S : ExtrDiscᵒᵖ) (n : ℕ) :
    ((((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                      (op (unop S).val)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
              ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f))).f
          -[n+1] ≫
        (EvalFreeAbIso.componentNeg BD N (unop S) n).hom =
      (EvalFreeAbIso.componentNeg BD M (unop S) n).hom ≫
        ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map
              (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op (unop S).val)).map
                f.val)).f
          -[n+1] :=
  by
  dsimp only [EvalFreeAbIso.componentNeg, Functor.mapHomologicalComplex_map_f,
    CategoryTheory.evaluation_obj_map]
  erw [embed_f_neg, embed_f_neg]
  simp only [Functor.mapBiproduct, Data.evalFunctor_obj_map_f, CategoryTheory.whiskeringRight_obj_map,
    CategoryTheory.whiskerRight_app, Functor.comp_map, Functor.mapIso_hom, biproduct.uniqueUpToIso_hom, ←
    Functor.map_comp]
  congr 2
  apply biproduct.hom_ext; intro j
  simp only [Category.assoc]
  erw [biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc]
  simp only [Functor.mapBicone_π, biproduct.bicone_π, evaluation_obj_map]
  simp only [← NatTrans.comp_app]; congr 1
  rw [biproduct.map_π]; rfl

theorem evalFreeAbIsoComponent_natural (S : ExtrDiscᵒᵖ) :
    (evalFreeAbIsoComponent BD M (unop S)).inv ≫
        (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj
                  (op (unop S).val)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map
          ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f)) =
      (BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map
          (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op (unop S).val)).map
            f.val) ≫
        (evalFreeAbIsoComponent BD N (unop S)).inv :=
  by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  ext ((_ | n) | n) : 2
  · apply eval_freeAb_iso_component_natural_zero
  · apply IsZero.eq_of_tgt; apply is_zero_zero
  · apply eval_freeAb_iso_component_natural_neg

theorem evalFreeAbIsoComponent_natural_bis (S : ExtrDiscᵒᵖ) (i : ℤ) :
    (homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i).map
          (evalFreeAbIsoComponent BD M (unop S)).inv ≫
        (((CategoryTheory.evaluation Profiniteᵒᵖ Ab).obj (op (unop S).val)).mapHomologicalComplex
                (ComplexShape.up ℤ) ⋙
              homology'Functor Ab (ComplexShape.up ℤ) i).map
          ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f)) =
      CategoryTheory.Functor.map _
          (CategoryTheory.Functor.map _
            (((CategoryTheory.evaluation Profinite.{u}ᵒᵖ Ab.{u + 1}).obj (op (unop S).val)).map
              f.val)) ≫
        (homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i).map
          (evalFreeAbIsoComponent BD N (unop S)).inv :=
  by
  rw [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]; congr 1
  apply eval_freeAb_iso_component_natural

theorem tensor_to_unsheafified_homology_natural'_aux (S : ExtrDiscᵒᵖ) (x) :
    (AddCommGroupCat.adj.homEquiv PUnit (N.val.obj (op (unop S).val))).symm
        (point
          ((((extrSheafExtrSheafProdEquiv Ab).Functor.map
                    ((condensedExtrSheafEquiv Ab).inverse.map f)).val.app
              S)
            x)) =
      (AddCommGroupCat.adj.homEquiv PUnit (M.val.obj (op (unop S).val))).symm (point x) ≫
        ((CategoryTheory.evaluation Profiniteᵒᵖ Ab).obj (op (unop S).val)).map f.val :=
  by
  dsimp [AddCommGroupCat.adj, Adjunction.mkOfHomEquiv_homEquiv]
  apply FreeAbelianGroup.lift.ext; rintro ⟨⟩
  rw [FreeAbelianGroup.lift.of, comp_apply, FreeAbelianGroup.lift.of]
  rfl

theorem aaaahrg (i : ℤ) {A B : Ab} (f : A ⟶ B) :
    (HomotopyCategory.homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i).map
        ((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map f) =
      (homology'Functor AddCommGroupCat (ComplexShape.up ℤ) i).map
        ((BD.eval' (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).map f) :=
  rfl

theorem tensorToUnsheafifiedHomology_natural' (i : ℤ) :
    tensorToUnsheafifiedHomology BD M i ≫
        whiskerLeft extrDiscToProfinite.op
          ((homology'Functor (Profiniteᵒᵖ ⥤ Ab) (ComplexShape.up ℤ) i).map
            ((BD.eval' freeFunc).map (condensedAbToPresheaf.map f))) =
      (ExtrSheafProd.mapTensor
            ((extrSheafExtrSheafProdEquiv Ab).Functor.map
              ((condensedExtrSheafEquiv Ab).inverse.map f))
            (𝟙
              (((BD.eval (forget AddCommGroupCat ⋙ AddCommGroupCat.free)).obj
                        (AddCommGroupCat.free.obj PUnit)).val.as.homology'
                i))).val ≫
        tensorToUnsheafifiedHomology BD N i :=
  by
  ext S : 2
  dsimp only [Condensed.tensorToUnsheafifiedHomology, NatTrans.comp_app, CategoryTheory.whiskerLeft_app,
    ExtrSheafProd.mapTensor_val_app]
  apply AddCommGroupCat.tensor_ext; intro x y
  simp only [comp_apply, id_apply, AddCommGroupCat.mapTensor, TensorProduct.map_tmul,
    AddCommGroupCat.tensorUncurry, LinearMap.toAddMonoidHom_coe, TensorProduct.lift.tmul,
    AddMonoidHom.coe_mk, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]
  dsimp only [Condensed.tensorToUnsheafifiedHomologyComponent, AddMonoidHom.mk'_apply,
    Condensed.tensorToUnsheafifiedHomologyComponentApplied]
  simp only [← comp_apply, Category.assoc]; congr 1
  rw [Condensed.homology'FunctorIso_natural]
  simp only [← Category.assoc]; congr 1; simp only [Category.assoc]
  rw [eval_freeAb_iso_component_natural_bis]
  simp only [← Category.assoc]; congr 1
  rw [tensor_to_unsheafified_homology_natural'_aux]
  rw [aaaahrg, aaaahrg, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]

theorem tensorToHomology_natural (i : ℤ) :
    tensorToHomology.{u} BD M i ≫
        (homology'Functor (Condensed.{u} Ab.{u + 1}) _ i).map ((BD.eval' freeCond').map f) =
      mapTensor f (𝟙 _) ≫ tensorToHomology.{u} BD N i :=
  by
  simp only [Condensed.tensorToHomology, Category.assoc, ← Functor.map_comp,
    eval_freeCond'_iso_component_natural]
  simp only [Functor.map_comp]
  simp only [← Category.assoc]; refine' congr_arg₂ _ _ rfl; simp only [Category.assoc]
  have :=
    (Condensed.homologyFunctorSheafificationIso (ComplexShape.up ℤ) i).hom.naturality
      ((condensedAbToPresheaf ⋙ BD.eval' freeFunc).map f)
  erw [← this]; clear this
  simp only [← Category.assoc]; refine' congr_arg₂ _ _ rfl; simp only [Category.assoc]
  dsimp only [Iso.app_hom]
  have :=
    (condensedExtrSheafEquiv Ab.{u + 1}).counitIso.hom.naturality
      ((homology'Functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) _ i ⋙ presheafToCondensedAb).map
        ((condensedAbToPresheaf ⋙ BD.eval' freeFunc.{u, u + 1}).map f))
  erw [← this]; clear this
  simp only [← Category.assoc]; refine' congr_arg₂ _ _ rfl; simp only [Category.assoc]
  dsimp only [map_tensor, Functor.comp_map]
  simp only [← Functor.map_comp]; congr 1
  have :=
    ExtrDisc_sheafification_iso.hom.naturality
      ((homology'Functor (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) _ i).map
        ((BD.eval' freeFunc).map (Condensed_Ab_to_presheaf.map f)))
  erw [← this]; clear this
  simp only [← Category.assoc]; refine' congr_arg₂ _ _ rfl
  ext1
  dsimp only [Condensed.tensorToHomologyAux]
  simp only [Functor.comp_map, CategoryTheory.whiskeringLeft_obj_map, Sheaf.category_theory.category_comp_val,
    presheaf_to_Sheaf_map_val, ExtrSheaf.mapTensor_val,
    GrothendieckTopology.toSheafify_naturality, Category.assoc,
    GrothendieckTopology.toSheafify_naturality_assoc, ← GrothendieckTopology.sheafifyMap_comp]
  rw [Condensed.tensorToUnsheafifiedHomology_natural']

theorem homologyBdEval_natural [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (M.val.obj (op S.val))]
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (N.val.obj (op S.val))] (i : ℤ) :
    (homologyBdEval BD M i).inv ≫ (homology'Functor _ _ i).map ((BD.eval' freeCond').map f) =
      mapTensor f (𝟙 _) ≫ (homologyBdEval BD N i).inv :=
  tensorToHomology_natural BD M N f i

end Condensed

