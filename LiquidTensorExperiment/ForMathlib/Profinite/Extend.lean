import Mathlib.Topology.Category.Profinite.AsLimit
import LiquidTensorExperiment.ForMathlib.Fintype
import LiquidTensorExperiment.HacksAndTricks.AsyncI

#align_import for_mathlib.Profinite.extend

noncomputable section

namespace Profinite

open CategoryTheory

open CategoryTheory.Limits

universe v u u'

variable {C : Type u} [Category.{v} C] (F : FintypeCat.{v} ⥤ C)

variable {D : Type u'} [Category.{v} D]

/-- Change a cone with respect to a morphism from `Profinite`. -/
@[simps]
def changeCone {X Y : Profinite} (f : X ⟶ Y) (D : Cone (X.fintypeDiagram ⋙ F)) :
    Cone (Y.fintypeDiagram ⋙ F) where
  pt := D.pt
  π :=
    { app := fun S => D.π.app (S.comap f.continuous) ≫ F.map (DiscreteQuotient.map <| le_refl _)
      naturality := by
        rintro I J h
        dsimp
        simp only [Category.id_comp, Category.assoc]
        rw [← D.w (hom_of_le <| DiscreteQuotient.comap_mono _ <| CategoryTheory.leOfHom h)]
        simp only [Category.assoc, ← F.map_comp, Functor.comp_map]
        congr 2
        ext ⟨t⟩; rfl }

-- Assume that C has enough limits.
variable [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]

-- PROJECT: Prove that this is isomorphic to the right Kan extension along `Fintype.to_Profinite`.
/-- Extend a functor `Fintype ⥤ C` to `Profinite`. -/
@[simps]
def extend : Profinite ⥤ C where
  obj X := limit (X.fintypeDiagram ⋙ F)
  map X Y f := limit.lift _ (changeCone _ f _)
  map_id := by
    intro X
    ext S
    dsimp
    simp only [limit.lift_π, coe_id, change_cone_π_app, limit.cone_π, Category.id_comp]
    erw [DiscreteQuotient.map_id]
    change _ ≫ F.map (𝟙 _) = _
    rw [F.map_id, Category.comp_id]
    congr
    exact S.comap_id
  map_comp := by
    intro X Y Z f g
    ext S
    dsimp
    simp only [limit.lift_π, change_cone_π_app, limit.cone_π, limit.lift_π_assoc, coe_comp,
      Category.assoc, ← F.map_comp]
    congr
    exact DiscreteQuotient.map_comp _ _

/-- discrete quotients of a finite type has an initial object given by `⊥`. -/
@[simps]
def botInitial (X : FintypeCat) : IsInitial (⊥ : DiscreteQuotient (FintypeCat.toProfinite.obj X))
    where desc S := homOfLE bot_le

/-- The extension of `F : Fintype ⥤ C` extends `F`. -/
@[simps]
def extendExtends : FintypeCat.toProfinite ⋙ extend F ≅ F :=
  (NatIso.ofComponents fun X => by
      dsimp only [extend, Functor.comp_obj]
      let Y := Fintype.to_Profinite.obj X
      let D := limit.isLimit (Y.fintype_diagram ⋙ F)
      let E := CategoryTheory.Limits.limitOfDiagramInitial (Profinite.botInitial X) (Y.fintype_diagram ⋙ F)
      letI : TopologicalSpace X := ⊥
      let e : FintypeCat.of (⊥ : DiscreteQuotient X) ≅ X :=
        FintypeCat.isoOfEquiv (Equiv.ofBijective _ DiscreteQuotient.proj_bot_bijective).symm
      let g := D.cone_point_unique_up_to_iso E
      exact g ≪≫ F.map_iso e) <|
    by
    intro X Y f
    letI : TopologicalSpace X := ⊥
    letI : TopologicalSpace Y := ⊥
    have hf : Continuous f := continuous_bot
    let A := Fintype.to_Profinite.obj X
    let B := Fintype.to_Profinite.obj Y
    dsimp [IsLimit.conePointUniqueUpToIso, CategoryTheory.Limits.limitOfDiagramInitial]
    simp only [change_cone_π_app, limit.cone_π, limit.lift_π_assoc, Category.assoc]
    let e : (⊥ : DiscreteQuotient X) ⟶ (⊥ : DiscreteQuotient Y).comap hf := hom_of_le bot_le
    erw [← limit.w (A.fintype_diagram ⋙ F) e]
    simp only [Category.assoc, ← F.map_comp, Functor.comp_map]
    congr 2
    simp_rw [← Iso.inv_comp_eq, ← Category.assoc]
    symm
    rw [← Iso.comp_inv_eq]
    rfl

/-
instance extend_preserves_limit (X : Profinite) : preserves_limit X.diagram (extend F) :=
{ preserves := λ D hD,
    let e : X.diagram ⋙ extend F ≅ X.fintype_diagram ⋙ F :=
          iso_whisker_left _ (extend_extends F),
        D' : cone (X.fintype_diagram ⋙ F) :=
          (cones.postcompose e.hom).obj ((extend F).map_cone D) in
  { lift := λ E, begin
      dsimp,
      let D'' : cone X.diagram := X.as_limit_cone,
      let f' : X ⟶ D.X := hD.lift D'',
      admit
    end,
    fac' := _,
    uniq' := _ } }
-/
/-- `extend` is characterized by the fact that it preserves the correct limits and
  that its composition with `Profinite.to_Fintype` is the original functor. -/
def extendUnique (G : Profinite ⥤ C) [∀ X : Profinite, PreservesLimit X.diagram G]
    (w : FintypeCat.toProfinite ⋙ G ≅ F) : G ≅ extend F :=
  (NatIso.ofComponents fun X =>
      let D := X.asLimitCone
      let hD := X.asLimit
      let E := G.mapCone D
      let hE : IsLimit E := PreservesLimit.preserves hD
      let f : X.diagram ⋙ G ≅ X.fintypeDiagram ⋙ F := isoWhiskerLeft _ w
      let E' : Cone (X.fintypeDiagram ⋙ F) := (Cones.postcompose f.hom).obj E
      let hE' : IsLimit E' := (IsLimit.postcomposeHomEquiv f _).symm hE
      hE'.conePointUniqueUpToIso (limit.isLimit _)) <|
    by
    intro A B f
    dsimp [IsLimit.postcomposeHomEquiv, IsLimit.ofConeEquiv,
      IsLimit.conePointUniqueUpToIso]
    ext S
    simp only [← NatTrans.naturality w.hom, limit.lift_π, Cones.postcompose_obj_π,
      Functor.comp_map, Functor.mapCone_π_app, change_cone_π_app, limit.cone_π, limit.lift_π_assoc,
      CategoryTheory.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
    simp only [← Category.assoc, ← G.map_comp]
    rfl

@[simps]
def extendCommutes (G : C ⥤ D) [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) G]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ G)] : extend F ⋙ G ≅ extend (F ⋙ G) :=
  (NatIso.ofComponents fun X =>
      (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)) <|
    by
    intro X Y f
    ext
    dsimp
    simp only [Category.assoc, limit.lift_π, change_cone_π_app, limit.cone_π, Functor.comp_map]
    erw [limit.lift_π, limit.lift_π_assoc]
    dsimp
    rw [← G.map_comp, limit.lift_π, ← G.map_comp]
    rfl

@[reassoc]
theorem extendCommutes_comp_extendExtends (G : C ⥤ D)
    [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) G]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ G)] :
    whiskerLeft FintypeCat.toProfinite (extendCommutes F G).hom ≫ (extendExtends _).hom =
      (Functor.associator _ _ _).inv ≫ whiskerRight (extendExtends _).hom G :=
  by
  ext
  simp only [NatTrans.comp_app, CategoryTheory.whiskerLeft_app, Profinite.extendExtends_hom_app, Functor.comp_map,
    Functor.associator_inv_app, CategoryTheory.whiskerRight_app, Functor.map_comp, Category.id_comp,
    Profinite.extendCommutes_hom_app]
  rw [← Category.assoc]; congr 1
  rw [← Iso.eq_comp_inv]
  ext
  simp only [IsLimit.conePointUniqueUpToIso, Category.assoc, Functor.mapIso_hom,
    IsLimit.uniqueUpToIso_hom, Cones.forget_map, IsLimit.liftConeMorphism_hom,
    limit.isLimit_lift]
  erw [limit.lift_π, limit.lift_π]
  simp only [Functor.mapCone_π_app, limit.cone_π, Functor.mapIso_inv, Cones.forget_map,
    IsLimit.uniqueUpToIso_inv, IsLimit.liftConeMorphism_hom, limit.isLimit_lift,
    cone_of_diagram_initial_π_app, Functor.comp_map, CategoryTheory.Limits.limitOfDiagramInitial]
  rw [← Functor.map_comp]; congr 1; symm
  exact limit.w _ ((Profinite.botInitial x).to j)

/-- A natural transformation induces a natural transformation on extensions. -/
@[simps]
def extendNatTrans {F G : FintypeCat ⥤ C} [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)] (η : F ⟶ G) : extend F ⟶ extend G
    where app X := CategoryTheory.Limits.limMap <| whiskerLeft _ η

@[simp]
theorem extendNatTrans_id (F : FintypeCat ⥤ C) [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)] :
    extendNatTrans (𝟙 F) = 𝟙 _ := by
  ext S
  dsimp
  simp

@[simp]
theorem extendNatTrans_comp {F G H : FintypeCat ⥤ C}
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ H)] (α : F ⟶ G) (β : G ⟶ H) :
    extendNatTrans (α ≫ β) = extendNatTrans α ≫ extendNatTrans β :=
  by
  ext S
  dsimp
  simp

theorem extend_π (F G : FintypeCat ⥤ C) [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)] (α : extend F ⟶ extend G) (X : Profinite)
    (T : DiscreteQuotient X) :
    α.app X ≫ limit.π _ T =
      (extend F).map (X.asLimitCone.π.app T) ≫
        α.app (Profinite.of T) ≫ (extendExtends G).hom.app _ :=
  by
  have : (extend_extends G).hom.app (X.fintype_diagram.obj T) = limit.π _ ⊥ ≫ _ := rfl
  erw [this, α.naturality_assoc]; congr 1
  dsimp [extend]
  simp only [limit.lift_π_assoc, change_cone_π_app, limit.cone_π, Category.assoc, ← G.map_comp]
  convert (limit.w _ _).symm
  swap
  · apply hom_of_le; intro x y h; dsimp [DiscreteQuotient.comap] at h 
    change _ = _ at h ; dsimp [Profinite.asLimitCone] at h 
    exact Quotient.exact' h
  ext t; rcases t with ⟨t⟩
  dsimp
  let E : ↥(X.fintype_diagram.obj T) ≃ (⊥ : DiscreteQuotient T) :=
    Equiv.ofBijective _ DiscreteQuotient.proj_bot_bijective
  change E.symm _ = _
  apply_fun E
  rw [Equiv.apply_symm_apply]; rfl

theorem extend_nat_trans_ext {F G : FintypeCat ⥤ C}
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)] (α β : extend F ⟶ extend G)
    (h : whiskerLeft FintypeCat.toProfinite α = whiskerLeft FintypeCat.toProfinite β) : α = β :=
  by
  ext S T
  dsimp
  let p : S ⟶ of T := S.as_limit_cone.π.app T
  let E : FintypeCat.toProfinite ⋙ extend G ≅ G := extend_extends G
  apply_fun fun e => (extend F).map p ≫ e.app ⟨T⟩ ≫ E.hom.app _ at h 
  simpa only [extend_π] using h

theorem extendNatTrans_whiskerLeft {F G : FintypeCat ⥤ C}
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)] (α : F ⟶ G) :
    whiskerLeft FintypeCat.toProfinite (extendNatTrans α) =
      (extendExtends F).hom ≫ α ≫ (extendExtends G).inv :=
  by
  ext S
  simp only [lim_map, IsLimit.map, CategoryTheory.whiskerLeft_app, Profinite.extendNatTrans_app, limit.isLimit_lift,
    limit.lift_π, Cones.postcompose_obj_π, NatTrans.comp_app, limit.cone_π, Profinite.extendExtends_hom_app,
    Profinite.extendExtends_inv_app, Category.assoc, NatTrans.naturality_assoc, ← G.map_iso_hom, ←
    G.map_iso_inv, Iso.hom_inv_id_assoc]
  rw [← Iso.inv_comp_eq]
  erw [limit.conePointUniqueUpToIso_inv_comp, limit.conePointUniqueUpToIso_inv_comp_assoc]
  simp only [cone_of_diagram_initial_π_app, Functor.comp_map]
  erw [NatTrans.naturality]

theorem extendNatTrans_whiskerRight {F G : FintypeCat ⥤ C}
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)] (α : F ⟶ G) (E : C ⥤ D)
    [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) E]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ E)]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ G ⋙ E)] :
    extendNatTrans (whiskerRight α E) =
      (extendCommutes _ _).inv ≫ whiskerRight (extendNatTrans α) E ≫ (extendCommutes _ _).hom :=
  by
  apply extend_nat_trans_ext
  simp only [Profinite.extendNatTrans_whiskerLeft, ← CategoryTheory.whiskerRight_left, Category.assoc, whisker_left_comp,
    whisker_right_comp]
  rw [← CategoryTheory.isoWhiskerLeft_inv, Iso.eq_inv_comp, CategoryTheory.isoWhiskerLeft_hom,
    Profinite.extendCommutes_comp_extendExtends_assoc]
  simp only [← Category.assoc, Iso.comp_inv_eq]
  simp only [Category.assoc, Profinite.extendCommutes_comp_extendExtends]
  ext
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app]
  erw [Category.id_comp, Category.id_comp]
  simp only [← NatTrans.comp_app, ← CategoryTheory.isoWhiskerRight_hom, ← CategoryTheory.isoWhiskerRight_inv, Iso.inv_hom_id]
  erw [Category.comp_id]

end Profinite

