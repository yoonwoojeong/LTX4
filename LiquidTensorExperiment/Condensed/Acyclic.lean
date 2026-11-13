import LiquidTensorExperiment.ForMathlib.Derived.ExtLemmas
import LiquidTensorExperiment.ForMathlib.Cech.Homotopy
import LiquidTensorExperiment.ForMathlib.Acyclic
import LiquidTensorExperiment.ForMathlib.ExactSeq4
import LiquidTensorExperiment.ForMathlib.Cech
import LiquidTensorExperiment.ForMathlib.ChainComplexExact
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Exact
import LiquidTensorExperiment.ForMathlib.WidePullbackIso
import LiquidTensorExperiment.ForMathlib.EquivalenceAdditive
import LiquidTensorExperiment.Condensed.Adjunctions2
import LiquidTensorExperiment.Condensed.ProjectiveResolution
import LiquidTensorExperiment.Condensed.Extr.Equivalence

#align_import condensed.acyclic

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopyCategory Opposite

open Function (Surjective)

namespace Condensed

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

-- ANNOYING!
instance presheafAbelian : Abelian (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  CategoryTheory.functorCategoryIsAbelian.{u + 2, u, u + 1}

-- ANNOYING!
instance extrDiscPresheafAbelian : Abelian (ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  CategoryTheory.functorCategoryIsAbelian.{u + 2, u, u + 1}

instance extrSheafAbelian' : Abelian (Sheaf ExtrDisc.proetaleTopology.{u} Ab.{u + 1}) :=
  CategoryTheory.Sheaf.abelian.{u + 2, u, u + 1}

instance extrSheafAbelian : Abelian (ExtrSheaf.{u} Ab.{u + 1}) :=
  CategoryTheory.Sheaf.abelian.{u + 2, u, u + 1}

def profiniteToPresheafAb : Profinite.{u} ⥤ Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  yoneda ⋙ (whiskeringRight _ _ _).obj (uliftFunctor.{u + 1} ⋙ AddCommGroupCat.free)

def profiniteToExtrDiscPresheaf : Profinite.{u} ⥤ ExtrDisc.{u}ᵒᵖ ⥤ Type (u + 1) :=
  yoneda ⋙
    (whiskeringLeft _ _ _).obj extrDiscToProfinite.op ⋙
      (whiskeringRight _ _ _).obj uliftFunctor.{u + 1}

def profiniteToExtrDiscPresheafAb : Profinite.{u} ⥤ ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  yoneda ⋙
    (whiskeringLeft _ _ _).obj extrDiscToProfinite.op ⋙
      (whiskeringRight _ _ _).obj (uliftFunctor.{u + 1} ⋙ AddCommGroupCat.free)

def unsheafifiedFreeCech' (F : Arrow Profinite.{u}) :
    ChainComplex (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) ℕ :=
  SimplicialObject.Augmented.toComplex <|
    ((SimplicialObject.Augmented.whiskering _ _).obj profiniteToPresheafAb).obj F.augmentedCechNerve

def unsheafifiedFreeExtrDiscrCech (F : Arrow Profinite.{u}) :
    ChainComplex (ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u + 1}) ℕ :=
  SimplicialObject.Augmented.toComplex <|
    ((SimplicialObject.Augmented.whiskering _ _).obj profiniteToExtrDiscPresheafAb).obj
      F.augmentedCechNerve

def freeCech' (F : Arrow Profinite.{u}) : ChainComplex (Condensed.{u} Ab.{u + 1}) ℕ :=
  (((SimplicialObject.Augmented.whiskering _ _).obj
          (profiniteToCondensed ⋙ condensedSetToCondensedAb)).obj
      F.augmentedCechNerve).toComplex

def freeExtrDiscCech' (F : Arrow Profinite.{u}) : ChainComplex (ExtrSheaf.{u} Ab.{u + 1}) ℕ :=
  (((SimplicialObject.Augmented.whiskering _ _).obj
          (profiniteToExtrDiscPresheafAb ⋙ presheafToSheaf _ _)).obj
      F.augmentedCechNerve).toComplex

def freeCech (F : Arrow Profinite.{u}) : ChainComplex (Condensed.{u} Ab.{u + 1}) ℤ :=
  (HomologicalComplex.embed <| ComplexShape.Embedding.natDownIntDown).obj (freeCech' F)

instance condensedExtrSheafEquiv_additive :
    Functor.Additive (condensedExtrSheafEquiv Ab.{u + 1}).inverse := by constructor

def whiskeringCechCompIso {C : Type _} [Category C] {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]
    {𝓑 : Type _} [Category 𝓑] [Abelian 𝓑] (f : Arrow C)
    [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i : Fin (n + 1) => f.hom]
    (F : C ⥤ 𝓐) (G : 𝓐 ⥤ 𝓑) (H : C ⥤ 𝓑) (E : F ⋙ G ≅ H) [G.Additive] :
    (G.mapHomologicalComplex _).obj
        (((SimplicialObject.Augmented.whiskering _ _).obj F).obj f.augmentedCechNerve).toComplex ≅
      (((SimplicialObject.Augmented.whiskering _ _).obj H).obj f.augmentedCechNerve).toComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      match i with
      | 0 => E.app _
      | i + 1 => E.app _)
    (by
      rintro i j (rfl : j + 1 = i)
      dsimp only [Functor.mapHomologicalComplex_obj_d, unsheafified_free_ExtrDiscr_Cech,
        free_ExtrDisc_Cech', SimplicialObject.Augmented.toComplex]
      rw [ChainComplex.of_d, ChainComplex.of_d]
      cases j
      · dsimp only [whiskering_Cech_comp_iso._match_1]
        dsimp only [SimplicialObject.Augmented.toComplexD,
          simplicial_object.augmented.whiskering_obj_2, SimplicialObject.Augmented.whiskeringObj,
          NatTrans.comp_app, CategoryTheory.whiskerRight_app, Functor.constComp_hom_app]
        rw [Category.comp_id, Category.comp_id, NatIso.app_hom, ← E.hom.naturality]
        rfl
      · dsimp only [whiskering_Cech_comp_iso._match_1]
        dsimp only [SimplicialObject.Augmented.toComplexD, SimplicialObject.Augmented.drop_obj,
          simplicial_object.augmented.whiskering_obj_2, SimplicialObject.Augmented.whiskeringObj,
          SimplicialObject.whiskering_obj_obj_map, SimplicialObject.boundary, NatIso.app_hom]
        simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum, Preadditive.comp_zsmul,
          Preadditive.sum_comp, Preadditive.zsmul_comp]
        apply Finset.sum_congr rfl; intro _ _
        erw [← E.hom.naturality]
        rfl)

def freeCech'IsoExtrDisc (F : Arrow Profinite.{u}) :
    ((condensedExtrSheafEquiv _).inverse.mapHomologicalComplex _).obj (freeCech' F) ≅
      freeExtrDiscCech' F :=
  let e := extrDiscSheafificationIso
  whiskeringCechCompIso F (profiniteToCondensed.{u} ⋙ condensedSetToCondensedAb.{u})
      (condensedExtrSheafEquiv.{u, u + 2} Ab.{u + 1}).inverse
      (profiniteToExtrDiscPresheafAb.{u} ⋙
        presheafToSheaf.{u + 2, u, u + 1} ExtrDisc.proetaleTopology.{u} Ab.{u + 1}) <|
    NatIso.ofComponents (fun S => e.symm.app _)
      (by
        intro S T f
        dsimp only [NatIso.app_hom]
        erw [e.symm.hom.naturality]
        rfl)

instance presheafToSheaf_additive :
    (presheafToSheaf.{u + 2, u, u + 1} ExtrDisc.proetaleTopology.{u} Ab.{u + 1}).Additive :=
  CategoryTheory.Sheaf.presheafToSheaf_additive.{u + 2, u, u + 1}

def AcyclicOfExact.inductionStepEx₂Aux {C : Type _} [Category C] {𝓐 : Type _} [Category 𝓐]
    [Abelian 𝓐] {𝓑 : Type _} [Category 𝓑] [Abelian 𝓑] (f : Arrow C)
    [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i : Fin (n + 1) => f.hom]
    (F : C ⥤ 𝓐) (G : 𝓐ᵒᵖ ⥤ 𝓑) [G.Additive] :
    (G.mapHomologicalComplex _).obj
        (((SimplicialObject.Augmented.whiskering _ _).obj F).obj
              f.augmentedCechNerve).toComplex.op ≅
      (((CosimplicialObject.Augmented.whiskering _ _).obj (F.op ⋙ G)).obj
          f.augmentedCechNerve.rightOp).toCocomplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      match i with
      | 0 => Iso.refl _
      | i + 1 => Iso.refl _)
    (by
      rintro i j (rfl : i + 1 = j)
      dsimp only [Functor.mapHomologicalComplex_obj_d, unsheafified_free_ExtrDiscr_Cech,
        free_ExtrDisc_Cech', CosimplicialObject.Augmented.toCocomplex,
        SimplicialObject.Augmented.toComplex, HomologicalComplex.op_d]
      rw [CochainComplex.of_d, ChainComplex.of_d]
      cases i
      · refine' (Category.id_comp _).trans ((Category.comp_id _).trans _).symm
        dsimp only [SimplicialObject.Augmented.toComplexD,
          CosimplicialObject.Augmented.toCocomplexD,
          simplicial_object.augmented.whiskering_obj_2, SimplicialObject.Augmented.whiskeringObj,
          cosimplicial_object.augmented.whiskering_obj_2,
          CosimplicialObject.Augmented.whiskeringObj, NatTrans.comp_app, CategoryTheory.whiskerRight_app,
          Functor.constComp_hom_app, Functor.constComp_inv_app]
        rw [Category.comp_id, Category.id_comp]
        rfl
      · refine' (Category.id_comp _).trans ((Category.comp_id _).trans _).symm
        dsimp only [SimplicialObject.Augmented.toComplexD, SimplicialObject.Augmented.drop_obj,
          simplicial_object.augmented.whiskering_obj_2, SimplicialObject.Augmented.whiskeringObj,
          SimplicialObject.whiskering_obj_obj_map, SimplicialObject.boundary,
          CosimplicialObject.Augmented.toCocomplexD, CosimplicialObject.Augmented.drop_obj,
          cosimplicial_object.augmented.whiskering_obj_2,
          CosimplicialObject.Augmented.whiskeringObj, CosimplicialObject.whiskering_obj_obj_map,
          CosimplicialObject.coboundary]
        simp only [G.map_sum, G.map_zsmul, op_sum, op_zsmul]
        rfl)

def freeExtrDiscCech'Iso (F : Arrow Profinite.{u}) :
    freeExtrDiscCech' F ≅
      ((presheafToSheaf _ _).mapHomologicalComplex _).obj (unsheafifiedFreeExtrDiscrCech F) :=
  (whiskeringCechCompIso F _ _ _ <| Iso.refl _).symm

/-
homological_complex.hom.iso_of_components
(λ i,
match i with
| 0 := iso.refl _
| i+1 := iso.refl _
end)
begin
  rintros i j (rfl : j + 1 = i),
  dsimp only [functor.map_homological_complex_obj_d,
    unsheafified_free_ExtrDiscr_Cech, free_ExtrDisc_Cech',
    simplicial_object.augmented.to_complex],
  rw [chain_complex.of_d, chain_complex.of_d],
  cases j,
  { refine (category.id_comp _).trans ((category.comp_id _).trans _).symm,
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      nat_trans.comp_app, whisker_right_app, functor.const_comp_hom_app],
    rw [category.comp_id, category.comp_id],
    refl, },
  { refine (category.id_comp _).trans ((category.comp_id _).trans _).symm,
    dsimp only [simplicial_object.augmented.to_complex_d,
      simplicial_object.augmented.drop_obj,
      simplicial_object.augmented.whiskering_obj_2,
      simplicial_object.augmented.whiskering_obj,
      simplicial_object.whiskering_obj_obj_map,
      simplicial_object.boundary],
    simp only [functor.map_sum, functor.map_zsmul],
    refl, },
end
-/
/-
def free_Cech_iso (F : arrow Profinite.{u}) :
  free_Cech F ≅ (homological_complex.embed $ complex_shape.embedding.nat_down_int_down).obj
  ((presheaf_to_Condensed_Ab.map_homological_complex _).obj
  (unsheafified_free_Cech' F)) :=
homological_complex.hom.iso_of_components
(λ i,
match i with
| int.of_nat 0 := iso.refl _
| int.of_nat (n+1) := iso.refl _
| -[1+i] := iso.refl _
end)
(by admit)
-/
-- SO ANNOYING
instance evaluation_additive' (X : ExtrDisc.{u}) :
    Functor.Additive ((evaluation ExtrDisc.{u}ᵒᵖ Ab.{u + 1}).obj (op X)) :=
  CategoryTheory.evaluation_additive.{u + 2, u, u + 1} _

def evaluatedFreeExtrDiscCech (F : Arrow Profinite.{u}) (X : ExtrDisc.{u}) :
    ChainComplex Ab.{u + 1} ℕ :=
  (((SimplicialObject.Augmented.whiskering _ _).obj AddCommGroupCat.free).obj <|
      ((profiniteToExtrDiscPresheaf.flip.obj (op X)).mapArrow.obj F).augmentedCechNerve).toComplex

def yetAnotherIso (F : Arrow Profinite.{u}) (X : ExtrDisc.{u}) :
    (((evaluation.{u, u + 1, u + 1, u + 2} ExtrDisc.{u}ᵒᵖ Ab.{u + 1}).obj
                (op X)).mapHomologicalComplex
            (ComplexShape.down.{0} ℕ)).obj
        (unsheafifiedFreeExtrDiscrCech.{u} F) ≅
      evaluatedFreeExtrDiscCech F X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i =>
      match i with
      | 0 => Iso.refl _
      | i + 1 => by apply AddCommGroup.free.map_iso; apply CategoryTheory.uliftWidePullbackIso)
    (by
      rintro (_ | i) (_ | j) ⟨rfl⟩
      · dsimp [yet_another_iso._match_1, Iso.refl_hom]; rw [Category.comp_id]
        dsimp [evaluated_free_ExtrDisc_Cech, unsheafified_free_ExtrDiscr_Cech]
        rw [if_pos (rfl : (1 : ℕ) = 0 + 1)]; erw [Category.id_comp]
        rw [if_pos (rfl : (1 : ℕ) = 0 + 1)]; erw [Category.id_comp]
        apply FreeAbelianGroup.lift.ext
        rintro ⟨t⟩
        dsimp [AddCommGroupCat.free, SimplicialObject.Augmented.toComplexD]
        simp only [Category.comp_id, comp_apply, FreeAbelianGroup.map_of_apply]
        dsimp at t 
        dsimp [CategoryTheory.uliftWidePullbackIso, CategoryTheory.uliftWidePullbackIsoHomAux,
          Profinite_to_ExtrDisc_presheaf_Ab]
        congr 1
        have :=
          types_comp_apply
            (WidePullback.lift
              (uliftFunctor.{u + 1, u}.map
                ((yoneda.{u, u + 1}.map (WidePullback.base fun _x : Fin (0 + 0 + 1) => F.hom)).app
                  (op.{u + 2} X.val)))
              (fun q : Fin (0 + 0 + 1) =>
                uliftFunctor.{u + 1, u}.map
                  ((yoneda.{u, u + 1}.map
                        (wide_pullback.π (fun _x : Fin (0 + 0 + 1) => F.hom) q)).app
                    (op.{u + 2} X.val)))
              _)
            (WidePullback.base fun i : Fin (0 + 0 + 1) =>
              (profiniteToExtrDiscPresheaf.{u}.map F.hom).app (op.{u + 2} X))
            (ULift.up t)
        rw [← this]; clear this; rw [WidePullback.lift_base]; rfl
      · dsimp [yet_another_iso._match_1, evaluated_free_ExtrDisc_Cech,
          unsheafified_free_ExtrDiscr_Cech]
        rw [if_pos, if_pos]; swap; rfl; swap; rfl; rw [Category.id_comp, Category.id_comp]
        dsimp [SimplicialObject.Augmented.toComplexD, SimplicialObject.boundary]
        simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, CategoryTheory.NatTrans.app_sum,
          CategoryTheory.NatTrans.app_zsmul]
        apply Finset.sum_congr rfl; rintro i -; congr 1
        dsimp [CategoryTheory.SimplicialObject.δ]
        apply FreeAbelianGroup.lift.ext
        rintro ⟨t⟩
        simp only [comp_apply]
        dsimp [AddCommGroupCat.free, Profinite_to_ExtrDisc_presheaf_Ab]; congr 1
        dsimp [CategoryTheory.uliftWidePullbackIso, CategoryTheory.uliftWidePullbackIsoHomAux]
        let f1 :=
          WidePullback.lift
            (WidePullback.base fun i : Fin (j + 1 + 1) =>
              (profiniteToExtrDiscPresheaf.{u}.map F.hom).app (op.{u + 2} X))
            (fun k : Fin (j + 1) =>
              wide_pullback.π
                (fun i : Fin (j + 1 + 1) =>
                  (profiniteToExtrDiscPresheaf.{u}.map F.hom).app (op.{u + 2} X))
                ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) k))
            _
        let f2 :=
          WidePullback.lift
            (uliftFunctor.{u + 1, u}.map
              ((yoneda.{u, u + 1}.map
                    (WidePullback.base fun _x : Fin (j.succ + 0 + 1) => F.hom)).app
                (op.{u + 2} X.val)))
            (fun q : Fin (j.succ + 0 + 1) =>
              uliftFunctor.{u + 1, u}.map
                ((yoneda.{u, u + 1}.map
                      (wide_pullback.π (fun _x : Fin (j.succ + 0 + 1) => F.hom) q)).app
                  (op.{u + 2} X.val)))
            _
        let f3 :=
          WidePullback.lift
            (uliftFunctor.{u + 1, u}.map
              ((yoneda.{u, u + 1}.map (WidePullback.base fun _x : Fin (j + 0 + 1) => F.hom)).app
                (op.{u + 2} X.val)))
            (fun q : Fin (j + 0 + 1) =>
              uliftFunctor.{u + 1, u}.map
                ((yoneda.{u, u + 1}.map (wide_pullback.π (fun _x : Fin (j + 0 + 1) => F.hom) q)).app
                  (op.{u + 2} X.val)))
            _
        change (f2 ≫ f1) _ = f3 _
        let f4 :=
          WidePullback.lift (WidePullback.base fun i : Fin (j + 1 + 1) => F.hom)
            (fun k : Fin (j + 1) =>
              wide_pullback.π (fun i : Fin (j + 1 + 1) => F.hom)
                ((SimplexCategory.Hom.toOrderHom (SimplexCategory.δ i)) k))
            _
        suffices f2 ≫ f1 = (yoneda'.map f4).app (op X.val) ≫ f3 by rw [this]; rfl
        apply WidePullback.hom_ext
        · intro k
          dsimp [f4, f3, f2, f1]
          simp only [Category.assoc, WidePullback.lift_π, WidePullback.lift_π_assoc]
          erw [WidePullback.lift_π]
          erw [← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp, WidePullback.lift_π]
        · dsimp [f4, f3, f2, f1]
          simp only [Category.assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]
          erw [WidePullback.lift_base]
          erw [← Functor.map_comp, ← NatTrans.comp_app, ← Functor.map_comp,
            WidePullback.lift_base])

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.op_induction' -/
theorem freeCech_exact (F : Arrow Profinite.{u}) (hF : Function.Surjective F.Hom) :
    ∀ n : ℤ, IsZero <| (freeCech F).homology' n :=
  by
  dsimp only [free_Cech]
  rw [ChainComplex.homology'_zero_iff_homology'_zero]
  rw [ChainComplex.homology'_zero_iff_map_homology'_zero _
      (condensedExtrSheafEquiv Ab.{u + 1}).symm]
  intro i
  dsimp only [Equivalence.symm_functor]
  let E := (_root_.homology_functor _ _ i).mapIso (free_Cech'_iso_ExtrDisc F)
  apply IsZero.of_iso _ E; clear E
  let E := (_root_.homology_functor _ _ i).mapIso (free_ExtrDisc_Cech'_iso F)
  apply IsZero.of_iso _ E; clear E
  dsimp only [_root_.homology_functor]
  revert i
  apply CategoryTheory.Sheaf.map_presheafToSheaf_homology'_zero_of_homology'_zero.{u + 2, u, u + 1}
  apply CategoryTheory.homology'_zero_of_eval.{u + 2, u, u + 1}
  any_goals infer_instance
  intro X;
  run_tac
    tactic.op_induction'
  intro i
  let E := (_root_.homology_functor _ _ i).mapIso (Condensed.yetAnotherIso F X)
  apply IsZero.of_iso _ E
  -- Now we can use the splitting similarly to arrow.conerve_to_cocomplex_homology_is_zero
  -- but we need a dual variant.
  let G := (Profinite_to_ExtrDisc_presheaf.flip.obj (op X)).mapArrow.obj F
  have : G.split :=
    by
    suffices Function.Surjective G.hom
      by
      refine' ⟨fun i => (this i).some, _⟩
      ext1 i; exact (this i).choose_spec
    dsimp [G, Functor.mapArrow, Profinite_to_ExtrDisc_presheaf, CategoryTheory.uliftFunctor, yoneda]
    rintro ⟨e⟩
    use ExtrDisc.lift _ hF e
    ext1
    dsimp
    rw [ExtrDisc.lift_lifts]
  apply Arrow.nerve_toComplex_homology'_isZero AddCommGroupCat.free G
  recover skip

theorem freeCech_kernel_SES (F : Arrow Profinite.{u}) (hF : Function.Surjective F.Hom) :
    ∀ n,
      ShortExact (kernel.ι <| (freeCech F).d (n + 1 + 1) (n + 1))
        (deltaToKernel _ (n + 1 + 1) (n + 1) n) :=
  by erw [← is_acyclic_iff_shortExact_to_cycles' (free_Cech F)]; exact free_Cech_exact F hF

variable (M : Condensed.{u} Ab.{u + 1})

abbrev hH (i : ℤ) (S : Profinite.{u}) (M : Condensed.{u} Ab.{u + 1}) :=
  ((ext' i).obj (op <| condensedSetToCondensedAb.obj <| Profinite.toCondensed S)).obj M

def AcyclicOfExact.IH (n : ℤ) : Prop :=
  ∀ S, ∀ i > 0, i ≤ n → IsZero (hH i S M)

/-- Consider the following commutative diagram
```
     O₀
     ↓
A₁ → B₁ → C₁ → O₁
   ↘ ↓
     B₂
     ↓  ↘
O₃ → B₃ → C₃
```
where `O₀`, `O₁`, and `O₃` are zero objects, and all sequence are exact.

Then `C₁` is also a zero object.
-/
theorem AcyclicOfExact.induction_step_aux {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]
    {O₀ O₁ O₃ A₁ B₁ C₁ B₂ B₃ C₃ : 𝓐} {α₁ : A₁ ⟶ B₁} {β₁ : B₁ ⟶ C₁} {γ₁ : C₁ ⟶ O₁}
    (ex₁ : ExactSeq 𝓐 [α₁, β₁, γ₁]) {d₁ : A₁ ⟶ B₂} {d₂ : B₂ ⟶ C₃} (exd : Exact d₁ d₂) {b₀ : O₀ ⟶ B₁}
    {b₁ : B₁ ⟶ B₂} {b₂ : B₂ ⟶ B₃} (exb : ExactSeq 𝓐 [b₀, b₁, b₂]) {α₃ : O₃ ⟶ B₃} {β₃ : B₃ ⟶ C₃}
    (ex₃ : Exact α₃ β₃) (hO₀ : IsZero O₀) (hO₁ : IsZero O₁) (hO₃ : IsZero O₃) (tr₁ : α₁ ≫ b₁ = d₁)
    (tr₂ : b₂ ≫ β₃ = d₂) : IsZero C₁ :=
  by
  refine'
    (ex₁.drop 1).pair.isZero_of_eq_zero_eq_zero (ex₁.pair.eq_zero_of_epi _) (hO₁.eq_of_tgt _ _)
  haveI : mono b₁ := exb.pair.mono_of_eq_zero (hO₀.eq_of_src _ _)
  haveI : mono β₃ := ex₃.mono_of_eq_zero (hO₃.eq_of_src _ _)
  let l' := Abelian.isLimitOfExactOfMono _ _ (exb.drop 1).pair
  let l := CategoryTheory.Limits.isKernelCompMono l' β₃ tr₂.symm
  obtain rfl :
    α₁ = kernel.lift _ _ exd.w ≫ (IsLimit.conePointUniqueUpToIso (limit.isLimit _) l).hom :=
    by
    erw [← cancel_mono b₁, Category.assoc,
      IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero, IsLimit.fac,
      Fork.ofι_π_app, tr₁]
  apply epi_comp

theorem AcyclicOfExact.induction_step_ex₁ (F : Arrow Profinite.{u})
    (h :
      ∀ i,
        IsZero
          ((((CosimplicialObject.Augmented.whiskering _ _).obj M.val).obj
                  F.augmentedCechNerve.rightOp).toCocomplex.homology'
            i)) :
    let C :=
      (((CosimplicialObject.Augmented.whiskering Profiniteᵒᵖ Ab).obj
              ((profiniteToCondensed ⋙ condensedSetToCondensedAb).op ⋙ preadditiveYoneda.obj M)).obj
          F.augmentedCechNerve.rightOp).toCocomplex
    ∀ i, IsZero (C.homology' i) :=
  by
  intro C i
  apply IsZero.of_iso (h i)
  refine' (_root_.homology_functor _ _ i).mapIso _
  refine' cosimplicial_object.augmented.cocomplex.map_iso _
  refine' Iso.app (Functor.mapIso _ (Condensed.profiniteFreeAdj _)) _

theorem AcyclicOfExact.induction_step_ex₂ (F : Arrow Profinite.{u})
    (h :
      let C :=
        (((CosimplicialObject.Augmented.whiskering Profiniteᵒᵖ Ab).obj
                ((profiniteToCondensed ⋙ condensedSetToCondensedAb).op ⋙
                  preadditiveYoneda.obj M)).obj
            F.augmentedCechNerve.rightOp).toCocomplex
      ∀ i, IsZero (C.homology' i)) :
    ∀ i,
      IsZero
        ((((preadditiveYoneda.obj M).mapHomologicalComplex _).obj (freeCech' F).op).homology' i) :=
  by
  intro i; apply (h i).of_iso
  refine' (_root_.homology_functor _ _ _).mapIso _
  apply AcyclicOfExact.inductionStepEx₂Aux

theorem Int.ofNat_add_one (i : ℕ) : Int.ofNat i + 1 = Int.ofNat (i + 1) :=
  rfl

theorem ComplexShape.Embedding.NatDownIntDown.r_int_ofNat (i : ℕ) :
    ComplexShape.Embedding.natDownIntDown.R (Int.ofNat i) = Option.some i :=
  rfl

-- move me
theorem CochainComplex.mono_of_isZero_homology'_0 {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]
    (C : CochainComplex 𝓐 ℕ) (h : IsZero <| C.homology' 0) : Mono (C.d 0 1) :=
  by
  replace h := CategoryTheory.exact_of_homology'_isZero h
  rw [C.d_from_eq (show (ComplexShape.up ℕ).Rel 0 1 by simp), exact_comp_iso] at h 
  refine' mono_of_exact_of_eq_zero _ _ _ _ _ h _
  rw [HomologicalComplex.dTo_eq_zero]
  simp only [CochainComplex.prev_nat_zero, ComplexShape.up_Rel, Nat.one_ne_zero, not_false_iff]

theorem AcyclicOfExact.induction_step_ex₃ (F : Arrow Profinite.{u}) (i : ℤ)
    (h :
      ∀ i,
        IsZero
          ((((preadditiveYoneda.obj M).mapHomologicalComplex _).obj (freeCech' F).op).homology'
            i)) :
    Exact ((preadditiveYoneda.obj M).map <| ((freeCech F).d (i + 1) i).op)
      ((preadditiveYoneda.obj M).map <| ((freeCech F).d (i + 1 + 1) (i + 1)).op) :=
  by
  rcases i with (i | i)
  · delta free_Cech
    dsimp only [HomologicalComplex.embed, HomologicalComplex.Embed.obj]
    rw [Int.ofNat_add_one, Int.ofNat_add_one]
    erw [ComplexShape.Embedding.NatDownIntDown.r_int_ofNat]
    erw [ComplexShape.Embedding.NatDownIntDown.r_int_ofNat]
    erw [ComplexShape.Embedding.NatDownIntDown.r_int_ofNat]
    dsimp only [HomologicalComplex.Embed.d]
    refine' CategoryTheory.exact_of_homology'_isZero ((h (i + 1)).of_iso <| _)
    · rw [← Functor.map_comp, ← op_comp, HomologicalComplex.d_comp_d, op_zero, Functor.map_zero]
    clear h
    refine' _ ≪≫ (homology_iso _ i (i + 1) (i + 1 + 1) _ _).symm
    swap; · dsimp; rfl; swap; · dsimp; rfl
    rfl
  · have aux : (preadditive_yoneda.obj M).map ((free_Cech F).d (-[i+1] + 1) -[i+1]).op = 0 := by
      cases i <;> erw [op_zero, Functor.map_zero]
    rw [aux]; clear aux; apply (config := { instances := false }) exact_zero_left_of_mono;
    · infer_instance
    cases i
    · exact CochainComplex.mono_of_isZero_homology'_0 _ (h 0)
    · apply mono_of_isZero_object
      rw [CategoryTheory.Limits.isZero_iff_id_eq_zero, ← CategoryTheory.Functor.map_id, is_zero_iff_id_eq_zero.mp,
        Functor.map_zero]
      refine' (is_zero_zero _).op

theorem AcyclicOfExact.induction_step_ex₄ (F : Arrow Profinite.{u}) (i : ℤ)
    (h :
      Exact ((preadditiveYoneda.obj M).map <| ((freeCech F).d (i + 1) i).op)
        ((preadditiveYoneda.obj M).map <| ((freeCech F).d (i + 1 + 1) (i + 1)).op)) :
    Exact (((ext' 0).flip.obj M).map <| ((freeCech F).d (i + 1) i).op)
      (((ext' 0).flip.obj M).map <| ((freeCech F).d (i + 1 + 1) (i + 1)).op) :=
  by
  let e := (BoundedDerivedCategory.ext'ZeroFlipIso _ M).symm
  apply Preadditive.exact_of_iso_of_exact' _ _ _ _ (e.app _) (e.app _) (e.app _) _ _ h
  · simp only [NatIso.app_hom, NatTrans.naturality]
  · simp only [NatIso.app_hom, NatTrans.naturality]

theorem AcyclicOfExact.induction_step_ex (F : Arrow Profinite.{u})
    (surj : Function.Surjective F.Hom)
    (h :
      ∀ i,
        IsZero
          ((((CosimplicialObject.Augmented.whiskering _ _).obj M.val).obj
                  F.augmentedCechNerve.rightOp).toCocomplex.homology'
            i))
    (i : ℤ) :
    Exact (((ext' 0).flip.obj M).map <| ((freeCech F).d (i + 1) i).op)
      (((ext' 0).flip.obj M).map <| ((freeCech F).d (i + 1 + 1) (i + 1)).op) :=
  by
  apply AcyclicOfExact.induction_step_ex₄
  apply AcyclicOfExact.induction_step_ex₃
  apply AcyclicOfExact.induction_step_ex₂
  apply AcyclicOfExact.induction_step_ex₁ _ F h

theorem AcyclicOfExact.induction_step
    (h :
      ∀ (F : Arrow Profinite.{u}) (surj : Function.Surjective F.Hom),
        ∀ i,
          IsZero
            ((((CosimplicialObject.Augmented.whiskering _ _).obj M.val).obj
                    F.augmentedCechNerve.rightOp).toCocomplex.homology'
              i))
    (n : ℤ) (ih : AcyclicOfExact.IH M n) : AcyclicOfExact.IH M (n + 1) :=
  by
  intro S i h1 h2
  rw [le_iff_eq_or_lt, or_comm', Int.lt_add_one_iff] at h2 
  cases' h2 with h2 h2; · exact ih S i h1 h2
  subst i
  let F := arrow.mk S.projective_presentation.f
  have hF : Function.Surjective F.hom := by rw [← Profinite.epi_iff_surjective];
    apply ProjectivePresentation.epi
  let E i := (ext' i).flip.obj M
  have ih' :
    ∀ (i j : ℤ) (h0i : 0 < i) (hin : i ≤ n), is_zero ((E i).obj (op ((free_Cech F).pt j))) :=
    by
    intro i j h0i hin
    cases' j with j j
    · cases j <;> exact ih _ _ h0i hin
    · apply BoundedDerivedCategory.ext'_zero_left_isZero
      exact (is_zero_zero _).op
  let K i := kernel ((free_Cech F).d (i + 1) i)
  have LES := fun i j => (free_Cech_kernel_SES F hF i).ext'_five_term_exactSeq M j
  have H1 : ∀ i > 0, is_zero ((E i).obj (op ((free_Cech F).pt 1))) :=
    by
    intro i hi
    apply BoundedDerivedCategory.ext'_isZero_of_projective _ _ _ _ hi
    apply (config := { instances := false }) CondensedAb.free.CategoryTheory.projective
    rw [SimplicialObject.Augmented.drop_obj, Arrow.augmentedCechNerve_left]
    apply Projective.of_iso (Arrow.cechNerveObj0 F).symm
    apply ProjectivePresentation.projective
  have aux0 :
    ∀ (i : ℤ) (h0i : 0 < i + 1) (H : is_zero ((E i).obj (op <| K 0))),
      is_zero ((E (i + 1)).obj (op <| K (-1))) :=
    by
    intro i h0i H
    refine' CategoryTheory.Limits.isZero_of_exact_isZero_isZero _ _ ((LES (-1) i).drop 2).pair H (H1 _ h0i)
  have aux :
    ∀ (i j : ℤ) (h0i : 0 < i + 1) (hi : i + 1 ≤ n) (H : is_zero ((E i).obj (op <| K (j + 1)))),
      is_zero ((E (i + 1)).obj (op <| K j)) :=
    by
    intro i j h0i hi H
    refine' CategoryTheory.Limits.isZero_of_exact_isZero_isZero _ _ ((LES j i).drop 2).pair H _
    refine' ih' _ _ h0i hi
  suffices ∀ i j, 0 < i → -1 ≤ j → i + j = n → is_zero ((E i).obj (op <| K j))
    by
    refine' CategoryTheory.Limits.isZero_of_exact_isZero_isZero _ _ (LES (-2) (n + 1)).pair _ _ <;> clear LES
    · apply BoundedDerivedCategory.ext'_zero_left_isZero
      refine' (CategoryTheory.Limits.isZero_of_mono (kernel.ι _) _).op; refine' is_zero_zero _
    · refine' this (n + 1) (-1) h1 le_rfl _; rw [← sub_eq_add_neg, add_sub_cancel]
  obtain ⟨n, rfl⟩ : ∃ k, k + 1 = n := ⟨n - 1, sub_add_cancel _ _⟩
  suffices is_zero ((E 1).obj (op <| K n)) by
    intro i
    apply Int.inductionOn' i 1 <;> clear i
    · intro j h0i hj hijn; rw [add_comm (1 : ℤ), add_left_inj] at hijn ; subst j; exact this
    · intro i hi IH j hi' hj hijn
      rw [le_iff_eq_or_lt] at hj ; cases' hj with hj hj
      · subst j; apply aux0 _ hi'; apply IH <;> linarith only [hi, hijn]
      · apply aux _ _ hi' _ (IH _ _ _ _) <;> linarith only [hi, hijn, hj]
    · intro i hi IH j hi'; exfalso; linarith only [hi, hi']
  clear aux0 aux
  have aux := fun i => ((LES i (-1)).drop 2).pair.cons (LES i 0)
  have exd := AcyclicOfExact.induction_step_ex M F hF (h F hF) (n + 1 + 1)
  apply
      AcyclicOfExact.induction_step_aux ((LES n 0).drop 1) exd ((aux (n + 1)).extract 0 3)
        (aux (n + 1 + 1)).pair <;>
    clear LES aux exd
  · apply ext'_isZero_of_neg; decide
  · obtain rfl | hn : n = -1 ∨ 1 ≤ n + 1 := by rw [Classical.or_iff_not_imp_right]; intro h2;
      linarith only [h1, h2]
    · exact H1 _ zero_lt_one
    · exact ih' _ _ zero_lt_one hn
  · apply ext'_isZero_of_neg; decide
  · conv_rhs => rw [← deltaToKernel_ι _ _ _ (n + 1), op_comp, Functor.map_comp]; rfl
  · conv_rhs => rw [← deltaToKernel_ι _ _ _ (n + 1 + 1), op_comp, Functor.map_comp]; rfl

theorem acyclic_of_exact
    (h :
      ∀ (F : Arrow Profinite.{u}) (surj : Function.Surjective F.Hom),
        ∀ i,
          IsZero
            ((((CosimplicialObject.Augmented.whiskering _ _).obj M.val).obj
                    F.augmentedCechNerve.rightOp).toCocomplex.homology'
              i))
    (S : Profinite.{u}) : ∀ i > 0, IsZero (hH i S M) :=
  by
  intro i hi
  suffices AcyclicOfExact.IH M i by apply this S i hi le_rfl
  apply Int.inductionOn' i 0 <;> clear hi i S
  · intro S i h1 h2; exfalso; exact h2.not_lt h1
  · intro k hk; apply AcyclicOfExact.induction_step M h
  · rintro k hk aux S i h1 h2; exfalso; linarith only [hk, h1, h2]

end Condensed

