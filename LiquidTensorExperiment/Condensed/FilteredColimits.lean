import LiquidTensorExperiment.Condensed.IsProetaleSheaf
import LiquidTensorExperiment.Condensed.Adjunctions
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitLimits

#align_import condensed.filtered_colimits

open CategoryTheory

open CategoryTheory.Limits

universe u

variable {J : Type (u + 1)} [SmallCategory J] [IsFiltered J] {C : Type (u + 2)} [Category.{u + 1} C]
  [ConcreteCategory.{u + 1} C] [HasLimits C] [HasColimitsOfShape J C]
  [PreservesColimitsOfShape J (forget C)] [ReflectsLimits (forget C)] [PreservesLimits (forget C)]
  (F : J ⥤ Condensed.{u} C)

open Opposite

namespace IsSheafColimitPresheafAux

namespace Empty

variable (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable def comparisonComponent (j : J) : (G.obj j).obj (op Profinite.empty) ⟶ ⊤_ _ :=
  terminal.from _

variable [∀ j, IsIso (comparisonComponent G j)]

noncomputable def firstIso :
    (colimit G).obj (op Profinite.empty) ≅ colimit (limit (Functor.empty _ ⋙ G.flip)) :=
  let e₁ := isColimitOfPreserves ((evaluation _ _).obj (op Profinite.empty)) (colimit.isColimit G)
  let e₂ := e₁.coconePointUniqueUpToIso (colimit.isColimit _)
  let e₃ :
    G ⋙ (evaluation Profiniteᵒᵖ C).obj (op Profinite.empty) ≅
      limit (Functor.empty Profiniteᵒᵖ ⋙ G.flip) :=
    NatIso.ofComponents
      (fun j =>
        let e₄ :=
          isLimitOfPreserves ((evaluation _ _).obj j) (limit.isLimit (Functor.empty _ ⋙ G.flip))
        let e₅ := (limit.isLimit _).conePointUniqueUpToIso e₄
        let e₆ : Functor.empty C ≅ (Functor.empty Profiniteᵒᵖ ⋙ G.flip) ⋙ (evaluation J C).obj j :=
          NatIso.ofComponents (fun i => i.as.elim) fun i => i.as.elim
        asIso (comparisonComponent G j) ≪≫ HasLimit.isoOfNatIso e₆ ≪≫ e₅)
      (by
        intro X Y f; dsimp [comparison_component]
        apply
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj Y)
              (limit.isLimit (Functor.empty Profiniteᵒᵖ ⋙ G.flip))).hom_ext
        intro j; rcases j with ⟨⟨⟩⟩)
  e₂ ≪≫ HasColimit.isoOfNatIso e₃

-- Move this!
noncomputable instance preservesFiniteLimitsOfConcrete :
    PreservesFiniteLimits (colim : (J ⥤ C) ⥤ C) :=
  by
  apply CategoryTheory.Limits.preservesFiniteLimitsOfPreservesFiniteLimitsOfSize
  intro K _ _
  exact Limits.filteredColimPreservesFiniteLimits

noncomputable def secondIso :
    colimit (limit (Functor.empty.{0} _ ⋙ G.flip)) ≅
      limit (colimit (Functor.empty.{0} _ ⋙ G.flip).flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm

--colimit_limit_iso _ -- TODO: Fix universes in `colimit_limit_iso`.
noncomputable def thirdIso : limit (colimit (Functor.empty _ ⋙ G.flip).flip) ≅ ⊤_ _ :=
  HasLimit.isoOfNatIso <| NatIso.ofComponents (fun i => i.as.elim) fun i => i.as.elim

noncomputable def comparison : (colimit G).obj (op Profinite.empty) ⟶ ⊤_ _ :=
  terminal.from _

theorem isIso_comparison : IsIso (comparison G) :=
  by
  suffices comparison G = (first_iso G).hom ≫ (second_iso G).hom ≫ (third_iso G).hom by rw [this];
    infer_instance
  simp

end Empty

namespace Prod

variable (X Y : Profinite.{u}) (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable def comparisonComponent (j : J) :
    (G.obj j).obj (op <| Profinite.sum X Y) ⟶ Prod ((G.obj j).obj (op X)) ((G.obj j).obj (op Y)) :=
  prod.lift ((G.obj j).map (Profinite.sum.inl _ _).op) ((G.obj j).map (Profinite.sum.inr _ _).op)

variable [∀ j, IsIso (comparisonComponent X Y G j)]

noncomputable def firstIsoAuxAux (j) :
    (G ⋙ (evaluation Profiniteᵒᵖ C).obj (op (X.Sum Y))).obj j ≅
      (G.flip.obj (op X) ⨯ G.flip.obj (op Y)).obj j :=
  let e₄ :
    pair ((G.obj j).obj (op X)) ((G.obj j).obj (op Y)) ≅
      pair (G.flip.obj (op X)) (G.flip.obj (op Y)) ⋙ (evaluation J C).obj j :=
    NatIso.ofComponents
      (fun p =>
        match p with
        | Discrete.mk WalkingPair.left => Iso.refl _
        | Discrete.mk WalkingPair.right => Iso.refl _)
      (by rintro (_ | _) (_ | _) (_ | _); rfl; rfl)
  asIso (comparisonComponent X Y G j) ≪≫
    HasLimit.isoOfNatIso e₄ ≪≫
      (limit.isLimit _).conePointUniqueUpToIso
        (isLimitOfPreserves ((evaluation _ _).obj j) (limit.isLimit _))

noncomputable def firstIsoAux :
    G ⋙ (evaluation Profiniteᵒᵖ C).obj (op (X.Sum Y)) ≅ G.flip.obj (op X) ⨯ G.flip.obj (op Y) :=
  NatIso.ofComponents (fun j => firstIsoAuxAux X Y G j)
    (by
      intro i j f; dsimp [comparison_component, first_iso_aux_aux]
      apply
        (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
            (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).hom_ext
      rintro (_ | _)
      · dsimp [IsLimit.conePointUniqueUpToIso]
        have h1 :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
                (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (Discrete.mk WalkingPair.left)
        have h2 :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj i)
                (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (Discrete.mk WalkingPair.left)
        dsimp at h1 h2 ; simp [h1, reassoc_of h2]
        dsimp [first_iso_aux_aux._match_1]; simp
      · dsimp [IsLimit.conePointUniqueUpToIso]
        have h1 :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
                (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (Discrete.mk WalkingPair.right)
        have h2 :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj i)
                (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (Discrete.mk WalkingPair.right)
        dsimp at h1 h2 ; simp [h1, reassoc_of h2]
        dsimp [first_iso_aux_aux._match_1]; simp)

noncomputable def firstIso :
    (colimit G).obj (op <| Profinite.sum X Y) ≅
      colimit (Prod (G.flip.obj (op X)) (G.flip.obj (op Y))) :=
  let e₁ :=
    isColimitOfPreserves ((evaluation _ _).obj (op <| Profinite.sum X Y)) (colimit.isColimit G)
  let e₂ := e₁.coconePointUniqueUpToIso (colimit.isColimit _)
  e₂ ≪≫ HasColimit.isoOfNatIso (firstIsoAux X Y G)

noncomputable def secondIso :
    colimit (Prod (G.flip.obj (op X)) (G.flip.obj (op Y))) ≅
      limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm

--colimit_limit_iso _
noncomputable def thirdIsoAuxLeft :
    (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip).obj
        (Discrete.mk WalkingPair.left) ≅
      (colimit G).obj (op X) :=
  let e₁ :=
    isColimitOfPreserves ((evaluation _ _).obj (Discrete.mk WalkingPair.left))
      (colimit.isColimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)
  let e₂ := isColimitOfPreserves ((evaluation _ _).obj (op X)) (colimit.isColimit G)
  e₁.coconePointUniqueUpToIso e₂

noncomputable def thirdIsoAuxRight :
    (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip).obj
        (Discrete.mk WalkingPair.right) ≅
      (colimit G).obj (op Y) :=
  let e₁ :=
    isColimitOfPreserves ((evaluation _ _).obj (Discrete.mk WalkingPair.right))
      (colimit.isColimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)
  let e₂ := isColimitOfPreserves ((evaluation _ _).obj (op Y)) (colimit.isColimit G)
  e₁.coconePointUniqueUpToIso e₂

/-- /
noncomputable
def third_iso_aux : cone (pair (op X) (op Y) ⋙ colimit G) :=
{ X := limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limit.π _ walking_pair.left ≫ (third_iso_aux_left X Y G).hom
    | walking_pair.right := limit.π _ walking_pair.right ≫ (third_iso_aux_right X Y G).hom
    end,
    naturality' := admit } }

noncomputable
def third_iso_aux' : cone (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) :=
{ X := limit (pair (op X) (op Y) ⋙ colimit G),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limit.π _ walking_pair.left ≫ (third_iso_aux_left X Y G).inv
    | walking_pair.right := limit.π _ walking_pair.right ≫ (third_iso_aux_right X Y G).inv
    end,
    naturality' := admit } }
-/
noncomputable def thirdIsoAux : Cone (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)
    where
  pt := Prod ((colimit G).obj (op X)) ((colimit G).obj (op Y))
  π :=
    { app := fun p =>
        match p with
        | Discrete.mk WalkingPair.left => Limits.prod.fst ≫ (thirdIsoAuxLeft _ _ _).inv
        | Discrete.mk WalkingPair.right => Limits.prod.snd ≫ (thirdIsoAuxRight _ _ _).inv
      naturality := by
        rintro (_ | _) (_ | _) (_ | _)
        · dsimp [third_iso_aux._match_1]; simp
        · dsimp [third_iso_aux._match_1]; simp }

noncomputable def thirdIso :
    limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) ≅
      Prod ((colimit G).obj (op X)) ((colimit G).obj (op Y))
    where
  hom :=
    prod.lift (limit.π _ (Discrete.mk WalkingPair.left) ≫ (thirdIsoAuxLeft _ _ _).hom)
      (limit.π _ (Discrete.mk WalkingPair.right) ≫ (thirdIsoAuxRight _ _ _).hom)
  inv := limit.lift _ (thirdIsoAux _ _ _)
  hom_inv_id := by
    ext (_ | _)
    · simp only [Category.assoc, limit.lift_π, Category.id_comp]
      dsimp [third_iso_aux, third_iso_aux._match_1]; simp
    · simp only [Category.assoc, limit.lift_π, Category.id_comp]
      dsimp [third_iso_aux, third_iso_aux._match_1]; simp
  inv_hom_id := by
    ext
    · simp only [prod.comp_lift, limit.lift_π_assoc, prod.lift_fst, Category.id_comp]
      dsimp [third_iso_aux]; simp
    · simp only [prod.comp_lift, limit.lift_π_assoc, prod.lift_snd, Category.id_comp]
      dsimp [third_iso_aux]; simp

/-
noncomputable
def fourth_iso_aux : cone (pair (op X) (op Y) ⋙ colimit G) :=
{ X := prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)),
  π :=
  { app := λ p,
    match p with
    | walking_pair.left := limits.prod.fst
    | walking_pair.right := limits.prod.snd
    end,
    naturality' := admit } }

noncomputable
def fourth_iso : limit (pair (op X) (op Y) ⋙ colimit G) ≅
  prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)) :=
{ hom := prod.lift (limit.π _ walking_pair.left) (limit.π _ walking_pair.right),
  inv := limit.lift _ (fourth_iso_aux _ _ _),
  hom_inv_id' := admit,
  inv_hom_id' := admit }
-/
noncomputable def comparison :
    (colimit G).obj (op <| Profinite.sum X Y) ⟶
      Prod ((colimit G).obj (op X)) ((colimit G).obj (op Y)) :=
  prod.lift ((colimit G).map (Profinite.sum.inl _ _).op)
    ((colimit G).map (Profinite.sum.inr _ _).op)

theorem isIso_comparison_aux_fst (j) :
    (colimit.ι G j).app (op (X.Sum Y)) ≫ comparison X Y G ≫ Limits.prod.fst =
      (colimit.ι G j).app (op (X.Sum Y)) ≫
        (firstIso X Y G).hom ≫ (secondIso X Y G).hom ≫ (thirdIso X Y G).hom ≫ Limits.prod.fst :=
  by
  dsimp [comparison, first_iso, second_iso, third_iso, CategoryTheory.Limits.colimitLimitIso]
  simp only [prod.comp_lift, prod.lift_fst, Category.assoc, HasLimit.isoOfNatIso_hom_π_assoc,
    Iso.symm_hom, CategoryTheory.Limits.colimitFlipIsoCompColim_inv_app,
    limit.conePointUniqueUpToIso_hom_comp_assoc, Functor.mapCone_π_app, CategoryTheory.Limits.BinaryFan.π_app_left]
  dsimp [HasColimit.isoOfNatIso, colim, colim_map, IsColimit.map,
    IsColimit.coconePointUniqueUpToIso, CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation,
    third_iso_aux, IsSheafColimitPresheafAux.Prod.thirdIsoAuxLeft, CategoryTheory.preservesColimitIso]
  have :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op (X.sum Y)))
          (colimit.isColimit G)).fac
      _ j
  dsimp at this ; slice_rhs 1 2 => rw [this]; clear this
  simp only [colimit.cocone_ι, colimit.ι_desc, Cocones.precompose_obj_ι, NatTrans.comp_app,
    Category.assoc, CategoryTheory.flipCompEvaluation_inv_app, Functor.mapCocone_ι_app, evaluation_obj_map]
  dsimp [first_iso_aux, first_iso_aux_aux, comparison_component,
    IsLimit.conePointUniqueUpToIso]
  simp only [HasLimit.lift_isoOfNatIso_hom_assoc, Category.id_comp, Category.assoc]
  have :=
    (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
          (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
      _ (Discrete.mk WalkingPair.left)
  dsimp at this 
  slice_rhs 2 3 => rw [this]; clear this
  simp only [limit.cone_π, Category.assoc, limit.lift_π_assoc, Cones.postcompose_obj_π,
    NatTrans.comp_app, NatIso.ofComponents_hom_app]
  have :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation _ C).obj (Discrete.mk WalkingPair.left))
          (colimit.isColimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)).fac
      _ j
  dsimp at this ; slice_rhs 3 4 => rw [this]; clear this
  dsimp [first_iso_aux_aux._match_1]; simp only [Category.id_comp, NatTrans.naturality]

theorem isIso_comparison_aux_snd (j) :
    (colimit.ι G j).app (op (X.Sum Y)) ≫ comparison X Y G ≫ Limits.prod.snd =
      (colimit.ι G j).app (op (X.Sum Y)) ≫
        (firstIso X Y G).hom ≫ (secondIso X Y G).hom ≫ (thirdIso X Y G).hom ≫ Limits.prod.snd :=
  by
  dsimp [comparison, first_iso, second_iso, third_iso, CategoryTheory.Limits.colimitLimitIso]
  simp only [prod.comp_lift, prod.lift_snd, Category.assoc, HasLimit.isoOfNatIso_hom_π_assoc,
    Iso.symm_hom, CategoryTheory.Limits.colimitFlipIsoCompColim_inv_app,
    limit.conePointUniqueUpToIso_hom_comp_assoc, Functor.mapCone_π_app,
    CategoryTheory.Limits.BinaryFan.π_app_right]
  dsimp [HasColimit.isoOfNatIso, colim, colim_map, IsColimit.map,
    IsColimit.coconePointUniqueUpToIso, CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation,
    third_iso_aux, IsSheafColimitPresheafAux.Prod.thirdIsoAuxRight, CategoryTheory.preservesColimitIso]
  have :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op (X.sum Y)))
          (colimit.isColimit G)).fac
      _ j
  dsimp at this ; slice_rhs 1 2 => rw [this]; clear this
  simp only [colimit.cocone_ι, colimit.ι_desc, Cocones.precompose_obj_ι, NatTrans.comp_app,
    Category.assoc, CategoryTheory.flipCompEvaluation_inv_app, Functor.mapCocone_ι_app, evaluation_obj_map]
  dsimp [first_iso_aux, first_iso_aux_aux, comparison_component,
    IsLimit.conePointUniqueUpToIso]
  simp only [HasLimit.lift_isoOfNatIso_hom_assoc, Category.id_comp, Category.assoc]
  have :=
    (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
          (limit.isLimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
      _ (Discrete.mk WalkingPair.right)
  dsimp at this 
  slice_rhs 2 3 => rw [this]; clear this
  simp only [limit.cone_π, Category.assoc, limit.lift_π_assoc, Cones.postcompose_obj_π,
    NatTrans.comp_app, NatIso.ofComponents_hom_app]
  have :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation _ C).obj (Discrete.mk WalkingPair.right))
          (colimit.isColimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)).fac
      _ j
  dsimp at this ; slice_rhs 3 4 => rw [this]; clear this
  dsimp [first_iso_aux_aux._match_1]; simp only [Category.id_comp, NatTrans.naturality]

theorem isIso_comparison : IsIso (comparison X Y G) :=
  by
  suffices comparison X Y G = (first_iso X Y G).hom ≫ (second_iso X Y G).hom ≫ (third_iso X Y G).hom
    by rw [this]; infer_instance
  ext
  · simp only [Category.assoc, IsSheafColimitPresheafAux.Prod.isIso_comparison_aux_fst]
  · simp only [Category.assoc, IsSheafColimitPresheafAux.Prod.isIso_comparison_aux_snd]

end Prod

namespace Eq

variable {X Y : Profinite.{u}} (f : X ⟶ Y) (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)

noncomputable def comparisonComponent (j : J) :
    (G.obj j).obj (op <| Y) ⟶
      equalizer ((G.obj j).map (Profinite.pullback.fst f f).op)
        ((G.obj j).map (Profinite.pullback.snd f f).op) :=
  equalizer.lift ((G.obj j).map f.op)
    (by simp_rw [← (G.obj j).map_comp, ← op_comp, Profinite.pullback.condition])

variable [∀ j, IsIso (comparisonComponent f G j)]

def firstIsoAuxAux (j) :
    parallelPair ((G.obj j).map (Profinite.pullback.fst f f).op)
        ((G.obj j).map (Profinite.pullback.snd f f).op) ≅
      parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
          (G.flip.map (Profinite.pullback.snd f f).op) ⋙
        (evaluation J C).obj j :=
  NatIso.ofComponents
    (fun p =>
      match p with
      | WalkingParallelPair.zero => Iso.refl _
      | WalkingParallelPair.one => Iso.refl _)
    (by
      rintro (_ | _) (_ | _) (_ | _)
      rfl
      dsimp [first_iso_aux_aux._match_1]; simp
      dsimp [first_iso_aux_aux._match_1]; simp
      rfl)

noncomputable def firstIsoAux :
    G ⋙ (evaluation Profiniteᵒᵖ C).obj (op Y) ≅
      equalizer (G.flip.map (Profinite.pullback.fst f f).op)
        (G.flip.map (Profinite.pullback.snd f f).op) :=
  NatIso.ofComponents
    (fun j =>
      asIso (comparisonComponent f G j) ≪≫
        HasLimit.isoOfNatIso (firstIsoAuxAux _ _ _) ≪≫
          (limit.isLimit _).conePointUniqueUpToIso
            (isLimitOfPreserves ((evaluation _ _).obj j) (limit.isLimit _)))
    (by
      intro i j g; dsimp [comparison_component, first_iso_aux_aux]
      apply
        (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
            (limit.isLimit
              (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                (G.flip.map (Profinite.pullback.snd f f).op)))).hom_ext
      rintro (_ | _)
      · dsimp [IsLimit.conePointUniqueUpToIso]
        have :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
                (limit.isLimit
                  (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) WalkingParallelPair.zero
        dsimp at this ; simp only [Category.assoc, this]; clear this
        have :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj i)
                (limit.isLimit
                  (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) WalkingParallelPair.zero
        dsimp at this ; simp only [NatTrans.naturality, Category.assoc, reassoc_of this];
        clear this
        simp only [HasLimit.isoOfNatIso_hom_π, NatIso.ofComponents_hom_app,
          equalizer.lift_ι_assoc, Functor.flip_obj_map, HasLimit.isoOfNatIso_hom_π_assoc]
        dsimp [first_iso_aux_aux._match_1]
        simp only [Category.comp_id, Category.id_comp, NatTrans.naturality]
      · dsimp [IsLimit.conePointUniqueUpToIso]
        have :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
                (limit.isLimit
                  (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) WalkingParallelPair.one
        dsimp at this ; simp only [Category.assoc, this]; clear this
        have :=
          (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj i)
                (limit.isLimit
                  (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) WalkingParallelPair.one
        dsimp at this ; simp only [NatTrans.naturality, Category.assoc, reassoc_of this];
        clear this
        simp only [HasLimit.isoOfNatIso_hom_π, NatIso.ofComponents_hom_app,
          limit.lift_π_assoc, Fork.ofι_π_app, Category.assoc, Functor.flip_obj_map,
          HasLimit.isoOfNatIso_hom_π_assoc]
        dsimp [first_iso_aux_aux._match_1]
        simp only [Category.comp_id, Category.id_comp, NatTrans.naturality,
          NatTrans.naturality_assoc])

noncomputable def firstIso :
    (colimit G).obj (op <| Y) ≅
      colimit
        (equalizer (G.flip.map (Profinite.pullback.fst f f).op)
          (G.flip.map (Profinite.pullback.snd f f).op)) :=
  let e₁ := isColimitOfPreserves ((evaluation _ _).obj (op <| Y)) (colimit.isColimit G)
  let e₂ := e₁.coconePointUniqueUpToIso (colimit.isColimit _)
  e₂ ≪≫ HasColimit.isoOfNatIso (firstIsoAux f G)

noncomputable def secondIso :
    colimit
        (equalizer (G.flip.map (Profinite.pullback.fst f f).op)
          (G.flip.map (Profinite.pullback.snd f f).op)) ≅
      limit
        (colimit
          (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
              (G.flip.map (Profinite.pullback.snd f f).op)).flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm

--colimit_limit_iso _
noncomputable def thirdIsoAux :
    (colimit
            (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                (G.flip.map (Profinite.pullback.snd f f).op)).flip).obj
        WalkingParallelPair.zero ≅
      (colimit G).obj (op X) :=
  let e₁ :=
    isColimitOfPreserves ((evaluation _ _).obj WalkingParallelPair.zero)
      (colimit.isColimit
        (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
            (G.flip.map (Profinite.pullback.snd f f).op)).flip)
  let e₂ := isColimitOfPreserves ((evaluation _ _).obj (op X)) (colimit.isColimit G)
  e₁.coconePointUniqueUpToIso e₂

noncomputable def thirdIsoAux'' :
    (colimit
            (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                (G.flip.map (Profinite.pullback.snd f f).op)).flip).obj
        WalkingParallelPair.one ≅
      (colimit G).obj (op <| Profinite.pullback f f) :=
  let e₁ :=
    isColimitOfPreserves ((evaluation _ _).obj WalkingParallelPair.one)
      (colimit.isColimit
        (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
            (G.flip.map (Profinite.pullback.snd f f).op)).flip)
  let e₂ :=
    isColimitOfPreserves ((evaluation _ _).obj (op <| Profinite.pullback f f)) (colimit.isColimit G)
  e₁.coconePointUniqueUpToIso e₂

theorem thirdIsoAux_fst :
    (thirdIsoAux f G).inv ≫
        (colimit
              (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                  (G.flip.map (Profinite.pullback.snd f f).op)).flip).map
          WalkingParallelPairHom.left =
      (colimit G).map (Profinite.pullback.fst f f).op ≫ (thirdIsoAux'' f G).inv :=
  by
  dsimp [third_iso_aux, IsSheafColimitPresheafAux.Eq.thirdIsoAux'']
  apply
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.isColimit G)).hom_ext
  intro j
  dsimp [IsColimit.coconePointUniqueUpToIso]
  have h1 :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.isColimit G)).fac _ j
  have h2 :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op <| Profinite.pullback f f))
          (colimit.isColimit G)).fac
      _ j
  dsimp at h1 h2 
  slice_lhs 1 2 => rw [h1]; clear h1
  rw [← NatTrans.naturality_assoc]
  slice_rhs 2 3 => rw [h2]; clear h2
  dsimp; rw [← NatTrans.naturality]; rfl

theorem thirdIsoAux_snd :
    (thirdIsoAux f G).inv ≫
        (colimit
              (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                  (G.flip.map (Profinite.pullback.snd f f).op)).flip).map
          WalkingParallelPairHom.right =
      (colimit G).map (Profinite.pullback.snd f f).op ≫ (thirdIsoAux'' f G).inv :=
  by
  dsimp [third_iso_aux, IsSheafColimitPresheafAux.Eq.thirdIsoAux'']
  apply
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.isColimit G)).hom_ext
  intro j
  dsimp [IsColimit.coconePointUniqueUpToIso]
  have h1 :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.isColimit G)).fac _ j
  have h2 :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op <| Profinite.pullback f f))
          (colimit.isColimit G)).fac
      _ j
  dsimp at h1 h2 
  slice_lhs 1 2 => rw [h1]; clear h1
  rw [← NatTrans.naturality_assoc]
  slice_rhs 2 3 => rw [h2]; clear h2
  dsimp; rw [← NatTrans.naturality]; rfl

noncomputable def thirdIsoAux' :
    Cone
      (colimit
        (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
            (G.flip.map (Profinite.pullback.snd f f).op)).flip)
    where
  pt :=
    equalizer ((colimit G).map (Profinite.pullback.fst f f).op)
      ((colimit G).map (Profinite.pullback.snd f f).op)
  π :=
    { app := fun p =>
        match p with
        | WalkingParallelPair.zero => equalizer.ι _ _ ≫ (thirdIsoAux _ _).inv
        | WalkingParallelPair.one =>
          equalizer.ι _ _ ≫
            (thirdIsoAux f G).inv ≫ CategoryTheory.Functor.map _ WalkingParallelPairHom.left
      naturality := by
        rintro (_ | _) (_ | _) ⟨⟩
        · dsimp; simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
        · dsimp [third_iso_aux'._match_1]; simp only [Category.id_comp, Category.assoc]
        · dsimp [third_iso_aux'._match_1]; simp only [Category.id_comp, Category.assoc]
          rw [IsSheafColimitPresheafAux.Eq.thirdIsoAux_fst, IsSheafColimitPresheafAux.Eq.thirdIsoAux_snd]
          simp only [Category.assoc, equalizer.condition_assoc]
        · dsimp; simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id] }

noncomputable def thirdIso :
    limit
        (colimit
          (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
              (G.flip.map (Profinite.pullback.snd f f).op)).flip) ≅
      equalizer ((colimit G).map (Profinite.pullback.fst f f).op)
        ((colimit G).map (Profinite.pullback.snd f f).op)
    where
  hom :=
    equalizer.lift (limit.π _ WalkingParallelPair.zero ≫ (thirdIsoAux f G).hom)
      (by
        have := IsSheafColimitPresheafAux.Eq.thirdIsoAux_fst f G; rw [Iso.eq_comp_inv] at this ; rw [← this]; clear this
        have := IsSheafColimitPresheafAux.Eq.thirdIsoAux_snd f G; rw [Iso.eq_comp_inv] at this ; rw [← this]; clear this
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        simp only [← Category.assoc]; congr 1
        let F := _; change limit.π F _ ≫ F.map _ = limit.π F _ ≫ F.map _
        simp [limit.w F WalkingParallelPairHom.left])
  inv := limit.lift _ (thirdIsoAux' _ _)
  hom_inv_id := by
    ext (_ | _)
    · simp only [Category.assoc, limit.lift_π, Category.id_comp]
      dsimp [IsSheafColimitPresheafAux.Eq.thirdIsoAux', third_iso_aux'._match_1]
      simp only [equalizer.lift_ι_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp only [Category.assoc, limit.lift_π, Category.id_comp]
      dsimp [IsSheafColimitPresheafAux.Eq.thirdIsoAux', third_iso_aux'._match_1]
      simp only [equalizer.lift_ι_assoc, Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id,
        Category.id_comp, limit.w]
  inv_hom_id := by
    ext
    simp only [Category.assoc, equalizer.lift_ι, limit.lift_π_assoc, Category.id_comp]
    dsimp [third_iso_aux, IsSheafColimitPresheafAux.Eq.thirdIsoAux']
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def comparison :
    (colimit G).obj (op <| Y) ⟶
      equalizer ((colimit G).map (Profinite.pullback.fst f f).op)
        ((colimit G).map (Profinite.pullback.snd f f).op) :=
  equalizer.lift ((colimit G).map f.op)
    (by simp only [← Functor.map_comp, ← op_comp, Profinite.pullback.condition])

theorem isIso_comparison : IsIso (comparison f G) :=
  by
  suffices comparison f G = (first_iso f G).hom ≫ (second_iso f G).hom ≫ (third_iso f G).hom by
    rw [this]; infer_instance
  ext
  dsimp [comparison, first_iso, second_iso, third_iso, CategoryTheory.Limits.colimitLimitIso]
  simp only [Category.assoc, equalizer.lift_ι, HasLimit.isoOfNatIso_hom_π_assoc, Iso.symm_hom,
    CategoryTheory.Limits.colimitFlipIsoCompColim_inv_app, limit.conePointUniqueUpToIso_hom_comp_assoc,
    Functor.mapCone_π_app, equalizer.fork_π_app_zero]
  dsimp [HasColimit.isoOfNatIso, IsColimit.coconePointUniqueUpToIso, colim, colim_map,
    IsColimit.map, CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation, CategoryTheory.preservesColimitIso, third_iso_aux]
  have :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ C).obj (op Y)) (colimit.isColimit G)).fac _ j
  dsimp at this 
  slice_rhs 1 2 => rw [this]; clear this
  simp only [colimit.cocone_ι, colimit.ι_desc, Cocones.precompose_obj_ι, NatTrans.comp_app,
    Category.assoc, CategoryTheory.flipCompEvaluation_inv_app, Functor.mapCocone_ι_app, evaluation_obj_map]
  dsimp [first_iso_aux, comparison_component]
  simp only [HasLimit.lift_isoOfNatIso_hom_assoc, Category.id_comp, Category.assoc]
  dsimp [IsLimit.conePointUniqueUpToIso]
  have :=
    (CategoryTheory.Limits.isColimitOfPreserves ((evaluation CategoryTheory.Limits.WalkingParallelPair C).obj WalkingParallelPair.zero)
          (colimit.isColimit
            (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                (G.flip.map (Profinite.pullback.snd f f).op)).flip)).fac
      _ j
  dsimp at this ; slice_rhs 4 5 => rw [this]; clear this
  have :=
    (CategoryTheory.Limits.isLimitOfPreserves ((evaluation J C).obj j)
          (limit.isLimit
            (CategoryTheory.Limits.parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
              (G.flip.map (Profinite.pullback.snd f f).op)))).fac
      _ WalkingParallelPair.zero
  dsimp at this ⊢; slice_rhs 2 3 => erw [this]; clear this
  dsimp
  simp only [limit.lift_π_assoc, Cones.postcompose_obj_π, NatTrans.comp_app, Fork.ofι_π_app,
    Category.assoc]
  dsimp [first_iso_aux_aux]
  simp only [Category.id_comp, NatTrans.naturality]

end Eq

end IsSheafColimitPresheafAux

open IsSheafColimitPresheafAux

/-
variables {K : Type (u+1)} [small_category K] [fin_category K]
  (E : K ⥤ Profinite.{u}ᵒᵖ) [has_limit E] (G : J ⥤ Profinite.{u}ᵒᵖ ⥤ C)
  [∀ j, preserves_limits_of_shape K (G.obj j)]

noncomputable
def comparison_map_component (j : J) : (G.obj j).obj (limit E) ⟶ limit (E ⋙ G.obj j) :=
limit.lift (E ⋙ G.obj j) $ (G.obj j).map_cone (limit.cone E)

noncomputable
def comparison_map : (colimit G).obj (limit E) ⟶ limit (E ⋙ colimit G) :=
limit.lift (E ⋙ colimit G) $ (colimit G).map_cone (limit.cone E)

noncomputable
def first_iso : (colimit G).obj (limit E) ≅ colimit (limit (E ⋙ G.flip)) :=
let e := is_colimit_of_preserves ((evaluation _ _).obj (limit E))
  (colimit.is_colimit G),
  ee := e.cocone_point_unique_up_to_iso (colimit.is_colimit _),
  tt : G ⋙ (evaluation Profiniteᵒᵖ C).obj (limit E) ≅ limit (E ⋙ G.flip) :=
    nat_iso.of_components (λ j, begin
      dsimp,
      refine (is_limit_of_preserves (G.obj j) (limit.is_limit E)).cone_point_unique_up_to_iso
        (limit.is_limit _) ≪≫ _,
      refine _ ≪≫ (limit.is_limit _).cone_point_unique_up_to_iso
        ((is_limit_of_preserves ((evaluation _ _).obj j) (limit.is_limit _))),
      dsimp,
      refine has_limit.iso_of_nat_iso _,
      refine nat_iso.of_components _ _,
      intros k, exact iso.refl _,
      intros k₁ k₂ f, dsimp, simp,
    end) admit in
ee ≪≫ has_colimit.iso_of_nat_iso tt

noncomputable
def second_iso : colimit (limit (E ⋙ G.flip)) ≅ limit (colimit (E ⋙ G.flip).flip) :=
  colimit_limit_iso _

noncomputable
def third_iso : limit (colimit (E ⋙ G.flip).flip) ≅ limit (E ⋙ colimit G) :=
has_limit.iso_of_nat_iso $
nat_iso.of_components (λ k,
  let ee := (is_colimit_of_preserves ((evaluation _ _).obj k)
    (colimit.is_colimit (E ⋙ G.flip).flip)).cocone_point_unique_up_to_iso
    (colimit.is_colimit _) in
  ee ≪≫
  begin
    dsimp,
    refine _ ≪≫
      (colimit.is_colimit _).cocone_point_unique_up_to_iso
      ((is_colimit_of_preserves ((evaluation _ _).obj (E.obj k)) (colimit.is_colimit _))),
    dsimp,
    refine has_colimit.iso_of_nat_iso _,
    refine nat_iso.of_components _ _,
    intros j, exact iso.refl _,
    intros i j f, dsimp, simp,
  end) admit

lemma is_iso : is_iso (comparison_map E G) :=
begin
  suffices : comparison_map E G =
    (first_iso E G).hom ≫ (second_iso E G).hom ≫ (third_iso E G).hom,
  { rw this, apply_instance },
  admit,
end

-- Use the comparison map above
variable (K)
def key : preserves_limits_of_shape K (colimit G) := admit

end is_sheaf_colimit_presheaf_aux
open is_sheaf_colimit_presheaf_aux

theorem empty_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.empty_condition' ↔
  nonempty (preserves_limits_of_shape (discrete pempty.{u+1}) G) := admit

theorem product_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.product_condition' ↔
  nonempty (preserves_limits_of_shape (discrete walking_pair.{u+1}) G) := admit

theorem equalizer_condition_iff_preserves (G : Profiniteᵒᵖ ⥤ C) :
  G.equalizer_condition' ↔
  nonempty (preserves_limits_of_shape (walking_parallel_pair.{u+1}) G) := admit
-/
theorem isSheaf_colimit_presheaf :
    Presheaf.IsSheaf proetaleTopology (colimit (F ⋙ sheafToPresheaf _ _)) :=
  by
  --rw is_sheaf_iff_is_sheaf_of_type,
  let G := colimit (F ⋙ Sheaf_to_presheaf _ _)
  let Gs := F ⋙ Sheaf_to_presheaf _ _
  have hGs : ∀ j, Presheaf.IsSheaf proetaleTopology (Gs.obj j) := by intro j; exact (F.obj j).2
  have hGsempty : ∀ j, (Gs.obj j).EmptyCondition' :=
    by
    intro j; specialize hGs j
    rw [(Gs.obj j).isProetaleSheaf_tFAE.out 0 3] at hGs 
    exact hGs.1
  have hGsprod : ∀ j, (Gs.obj j).ProductCondition' :=
    by
    intro j; specialize hGs j
    rw [(Gs.obj j).isProetaleSheaf_tFAE.out 0 3] at hGs 
    exact hGs.2.1
  have hGseq : ∀ j, (Gs.obj j).EqualizerCondition' :=
    by
    intro j; specialize hGs j
    rw [(Gs.obj j).isProetaleSheaf_tFAE.out 0 3] at hGs 
    exact hGs.2.2
  rw [G.is_proetale_sheaf_tfae.out 0 3]
  refine' ⟨_, _, _⟩
  · apply (config := { instances := false }) Empty.isIso_comparison
    exact hGsempty
    all_goals infer_instance
  · intro X Y
    apply (config := { instances := false }) Prod.isIso_comparison
    intro j; apply hGsprod
    all_goals infer_instance
  · intro X Y f hf
    apply (config := { instances := false }) Eq.isIso_comparison
    intro j; apply hGseq; assumption'

@[simps]
noncomputable def filteredCocone : Cocone F
    where
  pt := ⟨colimit (F ⋙ sheafToPresheaf _ _), isSheaf_colimit_presheaf _⟩
  ι :=
    { app := fun j => Sheaf.Hom.mk <| colimit.ι (F ⋙ sheafToPresheaf _ _) j
      naturality := by
        intro i j f
        ext1; dsimp
        simpa using colimit.w (F ⋙ Sheaf_to_presheaf _ _) f }

noncomputable def filteredCoconeIsColimit : IsColimit (filteredCocone F)
    where
  desc S :=
    Sheaf.Hom.mk <| colimit.desc (F ⋙ sheafToPresheaf _ _) ((sheafToPresheaf _ _).mapCocone S)
  fac := by
    intro S j
    ext1; dsimp
    simp
  uniq := by
    intro S m hm
    ext1; dsimp
    apply colimit.hom_ext
    intro j; specialize hm j; apply_fun fun e => e.val at hm 
    dsimp at hm ; simpa using hm

section

attribute [-simp] forget_map_eq_coe

noncomputable def preservesLimitsAux1 (G : J ⥤ Condensed.{u} Ab.{u + 1}) :
    colimit (G ⋙ sheafToPresheaf proetaleTopology Ab) ⋙ forget Ab ≅
      colimit (G ⋙ sheafToPresheaf _ _ ⋙ (whiskeringRight _ _ _).obj (forget Ab)) :=
  NatIso.ofComponents
    (by
      intro X
      let E := G ⋙ Sheaf_to_presheaf _ _ ⋙ (whiskering_right _ _ _).obj (forget Ab)
      let e₀ := colimit.isColimit E
      let e₁ := CategoryTheory.Limits.isColimitOfPreserves ((evaluation _ _).obj X) e₀
      refine' _ ≪≫ (colimit.isColimit _).coconePointUniqueUpToIso e₁
      change (forget Ab).obj _ ≅ colimit _
      let e₂ := colimit.isColimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab)
      let e₃ := CategoryTheory.Limits.isColimitOfPreserves ((evaluation _ _).obj X) e₂
      let e₄ := e₃.coconePointUniqueUpToIso (colimit.isColimit _)
      refine' (forget Ab).mapIso e₄ ≪≫ _
      change (forget Ab).obj (colimit _) ≅ _
      let e₅ :=
        CategoryTheory.Limits.isColimitOfPreserves (forget Ab)
          (colimit.isColimit
            ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙ (evaluation Profiniteᵒᵖ Ab).obj X))
      exact e₅.coconePointUniqueUpToIso (colimit.isColimit _))
    (by
      intro X Y f; dsimp; simp only [Category.assoc]
      dsimp [IsColimit.coconePointUniqueUpToIso]
      let E₀ :=
        CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ Ab).obj X)
          (colimit.isColimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))
      let E := CategoryTheory.Limits.isColimitOfPreserves (forget Ab) E₀
      apply E.hom_ext; intro j; dsimp
      -- Let's work on the LHS
      slice_lhs 1 3 =>
        simp only [← (forget Ab).map_comp]
        rw [← (colimit.ι (G ⋙ Sheaf_to_presheaf proetaleTopology Ab) j).naturality_assoc]
      have :=
        (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ Ab).obj Y)
              (colimit.isColimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))).fac
          _ j
      dsimp at this ; rw [this]; clear this
      dsimp
      have :=
        (CategoryTheory.Limits.isColimitOfPreserves (forget Ab)
              (colimit.isColimit
                ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙
                  (evaluation Profiniteᵒᵖ Ab).obj Y))).fac
          _ j
      simp only [(forget Ab).map_comp, Category.assoc]
      dsimp at this ; slice_lhs 2 3 => rw [this]; clear this
      erw [colimit.ι_desc]
      -- Now for the RHS
      slice_rhs 1 2 => rw [← (forget Ab).map_comp]
      have :=
        (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ Ab).obj X)
              (colimit.isColimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))).fac
          _ j
      dsimp at this ; rw [this]; clear this
      have :=
        (CategoryTheory.Limits.isColimitOfPreserves (forget Ab)
              (colimit.isColimit
                ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙
                  (evaluation Profiniteᵒᵖ Ab).obj X))).fac
          _ j
      dsimp at this ; slice_rhs 1 2 => erw [this]; clear this; erw [colimit.ι_desc]
      dsimp; erw [← NatTrans.naturality]; rfl)

attribute [-simp] types_comp_apply FunctorToTypes.comp

noncomputable def preservesLimitsOfShapeOfFilteredAux (G : J ⥤ Condensed.{u} Ab.{u + 1}) :
    condensedAbToCondensedSet.{u}.mapCocone (filteredCocone G) ≅
      filteredCocone (G ⋙ condensedAbToCondensedSet.{u}) :=
  Cocones.ext
    { hom := Sheaf.Hom.mk <| (preservesLimitsAux1 G).hom
      inv := Sheaf.Hom.mk <| (preservesLimitsAux1 G).inv
      hom_inv_id := by ext1; simp
      inv_hom_id := by ext1; simp }
    (by
      intro j; ext; dsimp [preservesLimitsAux1, IsColimit.coconePointUniqueUpToIso]
      simp only [← Category.assoc, ← (forget Ab).map_comp]
      have :=
        (CategoryTheory.Limits.isColimitOfPreserves ((evaluation Profiniteᵒᵖ Ab).obj x)
              (colimit.isColimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))).fac
          _ j
      dsimp at this ; rw [this]; clear this; dsimp; simp only [Category.assoc]
      have :=
        (CategoryTheory.Limits.isColimitOfPreserves (forget Ab)
              (colimit.isColimit
                ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙
                  (evaluation Profiniteᵒᵖ Ab).obj x))).fac
          _ j
      dsimp at this ; simp only [← Category.assoc]; rw [this]; clear this; erw [colimit.ι_desc]
      rfl)

end

noncomputable instance condensedAbToCondensedSetPreservesLimitsOfShapeOfFiltered :
    PreservesColimitsOfShape J condensedAbToCondensedSet.{u} :=
  by
  constructor
  intro G
  apply CategoryTheory.Limits.preservesColimitOfPreservesColimitCocone (filteredCoconeIsColimit G)
  apply IsColimit.ofIsoColimit (filteredCoconeIsColimit (G ⋙ condensedAbToCondensedSet))
  exact (preservesLimitsOfShapeOfFilteredAux G).symm

