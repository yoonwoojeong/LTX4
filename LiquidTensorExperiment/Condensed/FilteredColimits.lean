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
          (is_limit_of_preserves ((evaluation J C).obj Y)
              (limit.is_limit (functor.empty Profiniteᵒᵖ ⋙ G.flip))).hom_ext
        intro j; rcases j with ⟨⟨⟩⟩)
  e₂ ≪≫ HasColimit.isoOfNatIso e₃

-- Move this!
noncomputable instance preservesFiniteLimitsOfConcrete :
    PreservesFiniteLimits (colim : (J ⥤ C) ⥤ C) :=
  by
  apply preserves_finite_limits_of_preserves_finite_limits_of_size
  intro K _ _
  exact limits.filtered_colim_preserves_finite_limits

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
  suffices comparison G = (first_iso G).Hom ≫ (second_iso G).Hom ≫ (third_iso G).Hom by rw [this];
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
        | discrete.mk walking_pair.left => Iso.refl _
        | discrete.mk walking_pair.right => Iso.refl _)
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
        (is_limit_of_preserves ((evaluation J C).obj j)
            (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).hom_ext
      rintro (_ | _)
      · dsimp [is_limit.cone_point_unique_up_to_iso]
        have h1 :=
          (is_limit_of_preserves ((evaluation J C).obj j)
                (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (discrete.mk walking_pair.left)
        have h2 :=
          (is_limit_of_preserves ((evaluation J C).obj i)
                (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (discrete.mk walking_pair.left)
        dsimp at h1 h2 ; simp [h1, reassoc_of h2]
        dsimp [first_iso_aux_aux._match_1]; simp
      · dsimp [is_limit.cone_point_unique_up_to_iso]
        have h1 :=
          (is_limit_of_preserves ((evaluation J C).obj j)
                (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (discrete.mk walking_pair.right)
        have h2 :=
          (is_limit_of_preserves ((evaluation J C).obj i)
                (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
            (limit.cone _) (discrete.mk walking_pair.right)
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
        | discrete.mk walking_pair.left => Limits.prod.fst ≫ (thirdIsoAuxLeft _ _ _).inv
        | discrete.mk walking_pair.right => Limits.prod.snd ≫ (thirdIsoAuxRight _ _ _).inv
      naturality' := by
        rintro (_ | _) (_ | _) (_ | _)
        · dsimp [third_iso_aux._match_1]; simp
        · dsimp [third_iso_aux._match_1]; simp }

noncomputable def thirdIso :
    limit (colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip) ≅
      Prod ((colimit G).obj (op X)) ((colimit G).obj (op Y))
    where
  Hom :=
    prod.lift (limit.π _ (Discrete.mk WalkingPair.left) ≫ (thirdIsoAuxLeft _ _ _).Hom)
      (limit.π _ (Discrete.mk WalkingPair.right) ≫ (thirdIsoAuxRight _ _ _).Hom)
  inv := limit.lift _ (thirdIsoAux _ _ _)
  hom_inv_id' := by
    ext (_ | _)
    · simp only [category.assoc, limit.lift_π, category.id_comp]
      dsimp [third_iso_aux, third_iso_aux._match_1]; simp
    · simp only [category.assoc, limit.lift_π, category.id_comp]
      dsimp [third_iso_aux, third_iso_aux._match_1]; simp
  inv_hom_id' := by
    ext
    · simp only [prod.comp_lift, limit.lift_π_assoc, prod.lift_fst, category.id_comp]
      dsimp [third_iso_aux]; simp
    · simp only [prod.comp_lift, limit.lift_π_assoc, prod.lift_snd, category.id_comp]
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
        (firstIso X Y G).Hom ≫ (secondIso X Y G).Hom ≫ (thirdIso X Y G).Hom ≫ Limits.prod.fst :=
  by
  dsimp [comparison, first_iso, second_iso, third_iso, colimit_limit_iso]
  simp only [prod.comp_lift, prod.lift_fst, category.assoc, has_limit.iso_of_nat_iso_hom_π_assoc,
    iso.symm_hom, colimit_flip_iso_comp_colim_inv_app,
    limit.cone_point_unique_up_to_iso_hom_comp_assoc, functor.map_cone_π_app, binary_fan.π_app_left]
  dsimp [has_colimit.iso_of_nat_iso, colim, colim_map, is_colimit.map,
    is_colimit.cocone_point_unique_up_to_iso, colimit_obj_iso_colimit_comp_evaluation,
    third_iso_aux, third_iso_aux_left, preserves_colimit_iso]
  have :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op (X.sum Y)))
          (colimit.is_colimit G)).fac
      _ j
  dsimp at this ; slice_rhs 1 2 => rw [this]; clear this
  simp only [colimit.cocone_ι, colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app,
    category.assoc, flip_comp_evaluation_inv_app, functor.map_cocone_ι_app, evaluation_obj_map]
  dsimp [first_iso_aux, first_iso_aux_aux, comparison_component,
    is_limit.cone_point_unique_up_to_iso]
  simp only [has_limit.lift_iso_of_nat_iso_hom_assoc, category.id_comp, category.assoc]
  have :=
    (is_limit_of_preserves ((evaluation J C).obj j)
          (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
      _ (discrete.mk walking_pair.left)
  dsimp at this 
  slice_rhs 2 3 => rw [this]; clear this
  simp only [limit.cone_π, category.assoc, limit.lift_π_assoc, cones.postcompose_obj_π,
    nat_trans.comp_app, nat_iso.of_components_hom_app]
  have :=
    (is_colimit_of_preserves ((evaluation _ C).obj (discrete.mk walking_pair.left))
          (colimit.is_colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)).fac
      _ j
  dsimp at this ; slice_rhs 3 4 => rw [this]; clear this
  dsimp [first_iso_aux_aux._match_1]; simp only [category.id_comp, nat_trans.naturality]

theorem isIso_comparison_aux_snd (j) :
    (colimit.ι G j).app (op (X.Sum Y)) ≫ comparison X Y G ≫ Limits.prod.snd =
      (colimit.ι G j).app (op (X.Sum Y)) ≫
        (firstIso X Y G).Hom ≫ (secondIso X Y G).Hom ≫ (thirdIso X Y G).Hom ≫ Limits.prod.snd :=
  by
  dsimp [comparison, first_iso, second_iso, third_iso, colimit_limit_iso]
  simp only [prod.comp_lift, prod.lift_snd, category.assoc, has_limit.iso_of_nat_iso_hom_π_assoc,
    iso.symm_hom, colimit_flip_iso_comp_colim_inv_app,
    limit.cone_point_unique_up_to_iso_hom_comp_assoc, functor.map_cone_π_app,
    binary_fan.π_app_right]
  dsimp [has_colimit.iso_of_nat_iso, colim, colim_map, is_colimit.map,
    is_colimit.cocone_point_unique_up_to_iso, colimit_obj_iso_colimit_comp_evaluation,
    third_iso_aux, third_iso_aux_right, preserves_colimit_iso]
  have :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op (X.sum Y)))
          (colimit.is_colimit G)).fac
      _ j
  dsimp at this ; slice_rhs 1 2 => rw [this]; clear this
  simp only [colimit.cocone_ι, colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app,
    category.assoc, flip_comp_evaluation_inv_app, functor.map_cocone_ι_app, evaluation_obj_map]
  dsimp [first_iso_aux, first_iso_aux_aux, comparison_component,
    is_limit.cone_point_unique_up_to_iso]
  simp only [has_limit.lift_iso_of_nat_iso_hom_assoc, category.id_comp, category.assoc]
  have :=
    (is_limit_of_preserves ((evaluation J C).obj j)
          (limit.is_limit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))))).fac
      _ (discrete.mk walking_pair.right)
  dsimp at this 
  slice_rhs 2 3 => rw [this]; clear this
  simp only [limit.cone_π, category.assoc, limit.lift_π_assoc, cones.postcompose_obj_π,
    nat_trans.comp_app, nat_iso.of_components_hom_app]
  have :=
    (is_colimit_of_preserves ((evaluation _ C).obj (discrete.mk walking_pair.right))
          (colimit.is_colimit (pair (G.flip.obj (op X)) (G.flip.obj (op Y))).flip)).fac
      _ j
  dsimp at this ; slice_rhs 3 4 => rw [this]; clear this
  dsimp [first_iso_aux_aux._match_1]; simp only [category.id_comp, nat_trans.naturality]

theorem isIso_comparison : IsIso (comparison X Y G) :=
  by
  suffices comparison X Y G = (first_iso X Y G).Hom ≫ (second_iso X Y G).Hom ≫ (third_iso X Y G).Hom
    by rw [this]; infer_instance
  ext
  · simp only [category.assoc, is_iso_comparison_aux_fst]
  · simp only [category.assoc, is_iso_comparison_aux_snd]

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
      | walking_parallel_pair.zero => Iso.refl _
      | walking_parallel_pair.one => Iso.refl _)
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
        (is_limit_of_preserves ((evaluation J C).obj j)
            (limit.is_limit
              (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                (G.flip.map (Profinite.pullback.snd f f).op)))).hom_ext
      rintro (_ | _)
      · dsimp [is_limit.cone_point_unique_up_to_iso]
        have :=
          (is_limit_of_preserves ((evaluation J C).obj j)
                (limit.is_limit
                  (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) walking_parallel_pair.zero
        dsimp at this ; simp only [category.assoc, this]; clear this
        have :=
          (is_limit_of_preserves ((evaluation J C).obj i)
                (limit.is_limit
                  (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) walking_parallel_pair.zero
        dsimp at this ; simp only [nat_trans.naturality, category.assoc, reassoc_of this];
        clear this
        simp only [has_limit.iso_of_nat_iso_hom_π, nat_iso.of_components_hom_app,
          equalizer.lift_ι_assoc, functor.flip_obj_map, has_limit.iso_of_nat_iso_hom_π_assoc]
        dsimp [first_iso_aux_aux._match_1]
        simp only [category.comp_id, category.id_comp, nat_trans.naturality]
      · dsimp [is_limit.cone_point_unique_up_to_iso]
        have :=
          (is_limit_of_preserves ((evaluation J C).obj j)
                (limit.is_limit
                  (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) walking_parallel_pair.one
        dsimp at this ; simp only [category.assoc, this]; clear this
        have :=
          (is_limit_of_preserves ((evaluation J C).obj i)
                (limit.is_limit
                  (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                    (G.flip.map (Profinite.pullback.snd f f).op)))).fac
            (limit.cone _) walking_parallel_pair.one
        dsimp at this ; simp only [nat_trans.naturality, category.assoc, reassoc_of this];
        clear this
        simp only [has_limit.iso_of_nat_iso_hom_π, nat_iso.of_components_hom_app,
          limit.lift_π_assoc, fork.of_ι_π_app, category.assoc, functor.flip_obj_map,
          has_limit.iso_of_nat_iso_hom_π_assoc]
        dsimp [first_iso_aux_aux._match_1]
        simp only [category.comp_id, category.id_comp, nat_trans.naturality,
          nat_trans.naturality_assoc])

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
  dsimp [third_iso_aux, third_iso_aux'']
  apply
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.is_colimit G)).hom_ext
  intro j
  dsimp [is_colimit.cocone_point_unique_up_to_iso]
  have h1 :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.is_colimit G)).fac _ j
  have h2 :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op <| Profinite.pullback f f))
          (colimit.is_colimit G)).fac
      _ j
  dsimp at h1 h2 
  slice_lhs 1 2 => rw [h1]; clear h1
  rw [← nat_trans.naturality_assoc]
  slice_rhs 2 3 => rw [h2]; clear h2
  dsimp; rw [← nat_trans.naturality]; rfl

theorem thirdIsoAux_snd :
    (thirdIsoAux f G).inv ≫
        (colimit
              (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
                  (G.flip.map (Profinite.pullback.snd f f).op)).flip).map
          WalkingParallelPairHom.right =
      (colimit G).map (Profinite.pullback.snd f f).op ≫ (thirdIsoAux'' f G).inv :=
  by
  dsimp [third_iso_aux, third_iso_aux'']
  apply
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.is_colimit G)).hom_ext
  intro j
  dsimp [is_colimit.cocone_point_unique_up_to_iso]
  have h1 :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op X)) (colimit.is_colimit G)).fac _ j
  have h2 :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op <| Profinite.pullback f f))
          (colimit.is_colimit G)).fac
      _ j
  dsimp at h1 h2 
  slice_lhs 1 2 => rw [h1]; clear h1
  rw [← nat_trans.naturality_assoc]
  slice_rhs 2 3 => rw [h2]; clear h2
  dsimp; rw [← nat_trans.naturality]; rfl

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
        | walking_parallel_pair.zero => equalizer.ι _ _ ≫ (thirdIsoAux _ _).inv
        | walking_parallel_pair.one =>
          equalizer.ι _ _ ≫
            (thirdIsoAux f G).inv ≫ CategoryTheory.Functor.map _ WalkingParallelPairHom.left
      naturality' := by
        rintro (_ | _) (_ | _) ⟨⟩
        · dsimp; simp only [category.id_comp, CategoryTheory.Functor.map_id, category.comp_id]
        · dsimp [third_iso_aux'._match_1]; simp only [category.id_comp, category.assoc]
        · dsimp [third_iso_aux'._match_1]; simp only [category.id_comp, category.assoc]
          rw [third_iso_aux_fst, third_iso_aux_snd]
          simp only [category.assoc, equalizer.condition_assoc]
        · dsimp; simp only [category.id_comp, CategoryTheory.Functor.map_id, category.comp_id] }

noncomputable def thirdIso :
    limit
        (colimit
          (parallelPair (G.flip.map (Profinite.pullback.fst f f).op)
              (G.flip.map (Profinite.pullback.snd f f).op)).flip) ≅
      equalizer ((colimit G).map (Profinite.pullback.fst f f).op)
        ((colimit G).map (Profinite.pullback.snd f f).op)
    where
  Hom :=
    equalizer.lift (limit.π _ WalkingParallelPair.zero ≫ (thirdIsoAux f G).Hom)
      (by
        have := third_iso_aux_fst f G; rw [iso.eq_comp_inv] at this ; rw [← this]; clear this
        have := third_iso_aux_snd f G; rw [iso.eq_comp_inv] at this ; rw [← this]; clear this
        simp only [category.assoc, iso.hom_inv_id_assoc]
        simp only [← category.assoc]; congr 1
        let F := _; change limit.π F _ ≫ F.map _ = limit.π F _ ≫ F.map _
        simp [limit.w F walking_parallel_pair_hom.left])
  inv := limit.lift _ (thirdIsoAux' _ _)
  hom_inv_id' := by
    ext (_ | _)
    · simp only [category.assoc, limit.lift_π, category.id_comp]
      dsimp [third_iso_aux', third_iso_aux'._match_1]
      simp only [equalizer.lift_ι_assoc, category.assoc, iso.hom_inv_id, category.comp_id]
    · simp only [category.assoc, limit.lift_π, category.id_comp]
      dsimp [third_iso_aux', third_iso_aux'._match_1]
      simp only [equalizer.lift_ι_assoc, category.assoc, iso.hom_inv_id_assoc, category.comp_id,
        category.id_comp, limit.w]
  inv_hom_id' := by
    ext
    simp only [category.assoc, equalizer.lift_ι, limit.lift_π_assoc, category.id_comp]
    dsimp [third_iso_aux, third_iso_aux']
    simp only [category.assoc, iso.inv_hom_id, category.comp_id]

noncomputable def comparison :
    (colimit G).obj (op <| Y) ⟶
      equalizer ((colimit G).map (Profinite.pullback.fst f f).op)
        ((colimit G).map (Profinite.pullback.snd f f).op) :=
  equalizer.lift ((colimit G).map f.op)
    (by simp only [← functor.map_comp, ← op_comp, Profinite.pullback.condition])

theorem isIso_comparison : IsIso (comparison f G) :=
  by
  suffices comparison f G = (first_iso f G).Hom ≫ (second_iso f G).Hom ≫ (third_iso f G).Hom by
    rw [this]; infer_instance
  ext
  dsimp [comparison, first_iso, second_iso, third_iso, colimit_limit_iso]
  simp only [category.assoc, equalizer.lift_ι, has_limit.iso_of_nat_iso_hom_π_assoc, iso.symm_hom,
    colimit_flip_iso_comp_colim_inv_app, limit.cone_point_unique_up_to_iso_hom_comp_assoc,
    functor.map_cone_π_app, equalizer.fork_π_app_zero]
  dsimp [has_colimit.iso_of_nat_iso, is_colimit.cocone_point_unique_up_to_iso, colim, colim_map,
    is_colimit.map, colimit_obj_iso_colimit_comp_evaluation, preserves_colimit_iso, third_iso_aux]
  have :=
    (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ C).obj (op Y)) (colimit.is_colimit G)).fac _ j
  dsimp at this 
  slice_rhs 1 2 => rw [this]; clear this
  simp only [colimit.cocone_ι, colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app,
    category.assoc, flip_comp_evaluation_inv_app, functor.map_cocone_ι_app, evaluation_obj_map]
  dsimp [first_iso_aux, comparison_component]
  simp only [has_limit.lift_iso_of_nat_iso_hom_assoc, category.id_comp, category.assoc]
  dsimp [is_limit.cone_point_unique_up_to_iso]
  have :=
    (is_colimit_of_preserves ((evaluation walking_parallel_pair C).obj walking_parallel_pair.zero)
          (colimit.is_colimit
            (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
                (G.flip.map (Profinite.pullback.snd f f).op)).flip)).fac
      _ j
  dsimp at this ; slice_rhs 4 5 => rw [this]; clear this
  have :=
    (is_limit_of_preserves ((evaluation J C).obj j)
          (limit.is_limit
            (parallel_pair (G.flip.map (Profinite.pullback.fst f f).op)
              (G.flip.map (Profinite.pullback.snd f f).op)))).fac
      _ walking_parallel_pair.zero
  dsimp at this ⊢; slice_rhs 2 3 => erw [this]; clear this
  dsimp
  simp only [limit.lift_π_assoc, cones.postcompose_obj_π, nat_trans.comp_app, fork.of_ι_π_app,
    category.assoc]
  dsimp [first_iso_aux_aux]
  simp only [category.id_comp, nat_trans.naturality]

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
  have hGs : ∀ j, presheaf.is_sheaf proetaleTopology (Gs.obj j) := by intro j; exact (F.obj j).2
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
  · apply (config := { instances := false }) empty.is_iso_comparison
    exact hGsempty
    all_goals infer_instance
  · intro X Y
    apply (config := { instances := false }) prod.is_iso_comparison
    intro j; apply hGsprod
    all_goals infer_instance
  · intro X Y f hf
    apply (config := { instances := false }) eq.is_iso_comparison
    intro j; apply hGseq; assumption'

@[simps]
noncomputable def filteredCocone : Cocone F
    where
  pt := ⟨colimit (F ⋙ sheafToPresheaf _ _), isSheaf_colimit_presheaf _⟩
  ι :=
    { app := fun j => Sheaf.Hom.mk <| colimit.ι (F ⋙ sheafToPresheaf _ _) j
      naturality' := by
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
      let e₀ := colimit.is_colimit E
      let e₁ := is_colimit_of_preserves ((evaluation _ _).obj X) e₀
      refine' _ ≪≫ (colimit.is_colimit _).coconePointUniqueUpToIso e₁
      change (forget Ab).obj _ ≅ colimit _
      let e₂ := colimit.is_colimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab)
      let e₃ := is_colimit_of_preserves ((evaluation _ _).obj X) e₂
      let e₄ := e₃.cocone_point_unique_up_to_iso (colimit.is_colimit _)
      refine' (forget Ab).mapIso e₄ ≪≫ _
      change (forget Ab).obj (colimit _) ≅ _
      let e₅ :=
        is_colimit_of_preserves (forget Ab)
          (colimit.is_colimit
            ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙ (evaluation Profiniteᵒᵖ Ab).obj X))
      exact e₅.cocone_point_unique_up_to_iso (colimit.is_colimit _))
    (by
      intro X Y f; dsimp; simp only [category.assoc]
      dsimp [is_colimit.cocone_point_unique_up_to_iso]
      let E₀ :=
        is_colimit_of_preserves ((evaluation Profiniteᵒᵖ Ab).obj X)
          (colimit.is_colimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))
      let E := is_colimit_of_preserves (forget Ab) E₀
      apply E.hom_ext; intro j; dsimp
      -- Let's work on the LHS
      slice_lhs 1 3 =>
        simp only [← (forget Ab).map_comp]
        rw [← (colimit.ι (G ⋙ Sheaf_to_presheaf proetaleTopology Ab) j).naturality_assoc]
      have :=
        (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ Ab).obj Y)
              (colimit.is_colimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))).fac
          _ j
      dsimp at this ; rw [this]; clear this
      dsimp
      have :=
        (is_colimit_of_preserves (forget Ab)
              (colimit.is_colimit
                ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙
                  (evaluation Profiniteᵒᵖ Ab).obj Y))).fac
          _ j
      simp only [(forget Ab).map_comp, category.assoc]
      dsimp at this ; slice_lhs 2 3 => rw [this]; clear this
      erw [colimit.ι_desc]
      -- Now for the RHS
      slice_rhs 1 2 => rw [← (forget Ab).map_comp]
      have :=
        (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ Ab).obj X)
              (colimit.is_colimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))).fac
          _ j
      dsimp at this ; rw [this]; clear this
      have :=
        (is_colimit_of_preserves (forget Ab)
              (colimit.is_colimit
                ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙
                  (evaluation Profiniteᵒᵖ Ab).obj X))).fac
          _ j
      dsimp at this ; slice_rhs 1 2 => erw [this]; clear this; erw [colimit.ι_desc]
      dsimp; erw [← nat_trans.naturality]; rfl)

attribute [-simp] types_comp_apply functor_to_types.comp

noncomputable def preservesLimitsOfShapeOfFilteredAux (G : J ⥤ Condensed.{u} Ab.{u + 1}) :
    condensedAbToCondensedSet.{u}.mapCocone (filteredCocone G) ≅
      filteredCocone (G ⋙ condensedAbToCondensedSet.{u}) :=
  Cocones.ext
    { Hom := Sheaf.Hom.mk <| (preservesLimitsAux1 G).Hom
      inv := Sheaf.Hom.mk <| (preservesLimitsAux1 G).inv
      hom_inv_id' := by ext1; simp
      inv_hom_id' := by ext1; simp }
    (by
      intro j; ext; dsimp [preservesLimitsAux1, is_colimit.cocone_point_unique_up_to_iso]
      simp only [← category.assoc, ← (forget Ab).map_comp]
      have :=
        (is_colimit_of_preserves ((evaluation Profiniteᵒᵖ Ab).obj x)
              (colimit.is_colimit (G ⋙ Sheaf_to_presheaf proetaleTopology Ab))).fac
          _ j
      dsimp at this ; rw [this]; clear this; dsimp; simp only [category.assoc]
      have :=
        (is_colimit_of_preserves (forget Ab)
              (colimit.is_colimit
                ((G ⋙ Sheaf_to_presheaf proetaleTopology Ab) ⋙
                  (evaluation Profiniteᵒᵖ Ab).obj x))).fac
          _ j
      dsimp at this ; simp only [← category.assoc]; rw [this]; clear this; erw [colimit.ι_desc]
      rfl)

end

noncomputable instance condensedAbToCondensedSetPreservesLimitsOfShapeOfFiltered :
    PreservesColimitsOfShape J condensedAbToCondensedSet.{u} :=
  by
  constructor
  intro G
  apply preserves_colimit_of_preserves_colimit_cocone (filteredCoconeIsColimit G)
  apply is_colimit.of_iso_colimit (filteredCoconeIsColimit (G ⋙ condensedAbToCondensedSet))
  exact (preservesLimitsOfShapeOfFilteredAux G).symm

