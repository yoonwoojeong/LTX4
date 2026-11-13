import LiquidTensorExperiment.FreePfpng.Main
import LiquidTensorExperiment.Condensed.Acyclic
import LiquidTensorExperiment.Prop819
import LiquidTensorExperiment.LocallyConstant.Completion

#align_import free_pfpng.acyclic

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite ProFiltPseuNormGrp₁

open Function (Surjective)

open scoped NNReal

variable (S : Profinite.{u})

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

namespace CosimplicialObject

variable {C D E : Type _} [Category C] [Category D] [Category E]

variable (F : C ⥤ D) (G : D ⥤ E)

@[simps]
def whiskeringComp :
    (CosimplicialObject.whiskering C E).obj (F ⋙ G) ≅
      (CosimplicialObject.whiskering C D).obj F ⋙ (CosimplicialObject.whiskering D E).obj G :=
  (NatIso.ofComponents fun X =>
      (NatIso.ofComponents fun n => Iso.refl _) <| by intros; dsimp;
        simp only [category.comp_id, category.id_comp]) <|
    by intros; ext; dsimp; simp only [category.comp_id, category.id_comp]

namespace Augmented

def whiskeringComp :
    (CosimplicialObject.Augmented.whiskering C E).obj (F ⋙ G) ≅
      (CosimplicialObject.Augmented.whiskering C D).obj F ⋙
        (CosimplicialObject.Augmented.whiskering D E).obj G :=
  NatIso.ofComponents
    (fun X =>
      Comma.isoMk (Iso.refl _) ((CosimplicialObject.whiskeringComp F G).app _)
        (by
          ext
          dsimp
          simp only [iso.refl_hom, CategoryTheory.Functor.map_id, category.id_comp, iso.app_hom,
            functor.id_map, category.comp_id]))
    (by intros;
      ext <;> dsimp <;>
        simp only [iso.refl_hom, CategoryTheory.Functor.map_id, category.id_comp, iso.app_hom,
          functor.id_map, category.comp_id])

-- move me
attribute [simps obj map] cosimplicial_object.augmented.cocomplex

def cocomplexWhiskeringAdditive [Preadditive C] [Preadditive D] [F.Additive] :
    (CosimplicialObject.Augmented.whiskering C D).obj F ⋙ CosimplicialObject.Augmented.cocomplex ≅
      CosimplicialObject.Augmented.cocomplex ⋙ F.mapHomologicalComplex _ :=
  NatIso.ofComponents
    (fun X =>
      HomologicalComplex.Hom.isoOfComponents (fun i => by cases i <;> exact iso.refl _)
        (by
          rintro i j (rfl : i + 1 = j); cases i
          · dsimp;
            rw [category.id_comp, category.comp_id, if_pos rfl, if_pos rfl, category.comp_id,
              category.comp_id]
            delta cosimplicial_object.augmented.to_cocomplex_d
            dsimp; simp only [category.id_comp]
          · dsimp;
            rw [category.id_comp, category.comp_id, if_pos rfl, if_pos rfl, category.comp_id,
              category.comp_id]
            delta cosimplicial_object.augmented.to_cocomplex_d cosimplicial_object.coboundary id
            dsimp; simp only [← functor.map_add_hom_apply, map_sum, map_zsmul]; rfl))
    (by intros; ext n; dsimp; cases n <;> · dsimp; rw [category.id_comp, category.comp_id]; rfl)

end Augmented

end CosimplicialObject

section

universe v

-- move me
instance Ab.ulift_additive : Ab.ulift.{u, v}.Additive where

end

theorem free_acyclic_aux (F : Arrow Profinite) (hF : Surjective F.Hom) (i : ℕ) :
    IsZero
      ((((CosimplicialObject.Augmented.whiskering Profiniteᵒᵖ Ab).obj
                  (lCC V ⋙ Ab.ulift.{u + 1})).obj
              F.augmentedCechNerve.rightOp).toCocomplex.homology'
        i) :=
  by
  let U := forget₂.{u + 1, u + 1, u, u, u} SemiNormedGroupCat.{u} Ab.{u} ⋙ Ab.ulift.{u + 1, u}
  show
    is_zero
      (HomologicalComplex.homology'.{u + 1, u + 2, 0}
        (((CosimplicialObject.Augmented.whiskering.{u, u + 1, u + 1, u + 2} Profinite.{u}ᵒᵖ
                    Ab.{u + 1}).obj
                (SemiNormedGroupCat.lCC.{u, u}.obj V ⋙ U)).obj
            F.augmented_cech_nerve.right_op).toCocomplex
        i)
  rw [← homology'Functor_obj, ← CategoryTheory.CosimplicialObject.Augmented.cocomplex_obj]
  let e1 :=
    (homology'Functor _ (ComplexShape.up.{0} ℕ) i).mapIso
      (cosimplicial_object.augmented.cocomplex.map_iso
        ((CosimplicialObject.Augmented.whiskeringComp _ U).app F.augmented_cech_nerve.right_op))
  refine' is_zero_of_iso_of_zero _ e1.symm
  let e2 :=
    (homology'Functor Ab (ComplexShape.up.{0} ℕ) i).mapIso
      ((CosimplicialObject.Augmented.cocomplexWhiskeringAdditive U).app _)
  refine' is_zero_of_iso_of_zero _ e2.symm
  clear e1 e2
  let C :=
    (U.map_homological_complex (ComplexShape.up.{0} ℕ)).obj
      (((cosimplicial_object.augmented.whiskering Profinite.{u}ᵒᵖ _).obj
              (SemiNormedGroupCat.lCC.{u, u}.obj V)).obj
          F.augmented_cech_nerve.right_op).toCocomplex
  show is_zero (C.homology i)
  cases i
  · apply exact.homology_is_zero
    rw [AddCommGroupCat.exact_iff', HomologicalComplex.dTo_comp_dFrom, eq_self_iff_true,
      true_and_iff, HomologicalComplex.dTo_eq_zero]
    swap;
    · simp only [CochainComplex.prev_nat_zero, ComplexShape.up_Rel, Nat.one_ne_zero, not_false_iff]
    intro f hf; refine' ⟨0, ULift.down_injective (prop819_degree_zero F hF V f.down _).symm⟩
    rw [AddMonoidHom.mem_ker] at hf 
    have h01 : (ComplexShape.up.{0} ℕ).Rel 0 1 := rfl
    have := HomologicalComplex.dFrom_comp_xNextIso C h01
    rw [← iso.eq_comp_inv] at this 
    apply_fun (C.X_next_iso h01).Hom at hf 
    rw [this, ← Ab.comp_apply, category.assoc, iso.inv_hom_id, category.comp_id, map_zero] at hf 
    exact congr_arg ULift.down hf
  · let e := homology_iso C i (i + 1) (i + 2) rfl rfl
    refine' is_zero_of_iso_of_zero _ e.symm
    apply exact.homology_is_zero
    rw [AddCommGroupCat.exact_iff', HomologicalComplex.d_comp_d, eq_self_iff_true, true_and_iff]
    intro f hf
    -- use `prop819` from `prop819.lean`
    obtain ⟨g, hg, -⟩ := prop819 F hF V 1 zero_lt_one f.down (congr_arg ULift.down hf)
    refine' ⟨ULift.up g, ULift.down_injective hg⟩

theorem free_acyclic (i : ℤ) (hi : 0 < i) :
    IsZero
      (((ext' i).obj (op ((profiniteToCondensed ⋙ condensedSetToCondensedAb).obj S))).obj
        (Condensed.ofTopAb V)) :=
  by
  apply Condensed.acyclic_of_exact _ _ _ i hi
  intro F hF i
  apply is_zero_of_iso_of_zero (free_acyclic_aux V F hF i)
  refine' (homology'Functor _ _ i).mapIso _
  refine' cosimplicial_object.augmented.cocomplex.map_iso _
  conv_lhs => rw [← functor.flip_obj_obj]
  conv_rhs => rw [← functor.flip_obj_obj]
  refine' functor.map_iso _ _
  refine' iso_whisker_right _ _
  exact lCCIsoCondOfTopAb V

theorem free_pfpng_acyclic (i : ℤ) (hi : 0 < i) :
    IsZero
      (((ext' i).obj (op ((condensify (freePfpngFunctor ⋙ pFPNG₁ToCHFPNG₁ₑₗ)).obj S))).obj
        (Condensed.ofTopAb V)) :=
  by
  refine' is_zero_of_iso_of_zero (free_acyclic S V i hi) _
  conv =>
    rw [← functor.flip_obj_obj]
    congr
    skip
    rw [← functor.flip_obj_obj]
  refine' functor.map_iso _ (iso.app _ _).op
  exact freePfpngProfiniteIso

