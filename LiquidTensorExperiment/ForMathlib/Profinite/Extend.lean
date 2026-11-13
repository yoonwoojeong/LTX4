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

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ rintros [ident I, ident J, ident h], dsimp [] [] [] [],
    simp [] [] ["only"] ["[", expr category.id_comp, ",", expr category.assoc, "]"] [] [],
    rw ["<-", expr D.w «expr $ »(hom_of_le, «expr $ »(discrete_quotient.comap_mono _, le_of_hom h))] [],
    simp [] [] ["only"] ["[", expr category.assoc, ",", "<-", expr F.map_comp, ",", expr functor.comp_map, "]"] [] [],
    congr' [2] [], ext [] ["⟨", ident t, "⟩"] [], refl }] -/
/-- Change a cone with respect to a morphism from `Profinite`. -/
@[simps]
def changeCone {X Y : Profinite} (f : X ⟶ Y) (D : Cone (X.fintypeDiagram ⋙ F)) :
    Cone (Y.fintypeDiagram ⋙ F) where
  pt := D.pt
  π :=
    { app := fun S => D.π.app (S.comap f.Continuous) ≫ F.map (DiscreteQuotient.map <| le_refl _)
      naturality' := by
        trace
          "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ rintros [ident I, ident J, ident h], dsimp [] [] [] [],\n    simp [] [] [\"only\"] [\"[\", expr category.id_comp, \",\", expr category.assoc, \"]\"] [] [],\n    rw [\"<-\", expr D.w «expr $ »(hom_of_le, «expr $ »(discrete_quotient.comap_mono _, le_of_hom h))] [],\n    simp [] [] [\"only\"] [\"[\", expr category.assoc, \",\", \"<-\", expr F.map_comp, \",\", expr functor.comp_map, \"]\"] [] [],\n    congr' [2] [], ext [] [\"⟨\", ident t, \"⟩\"] [], refl }]" }

-- Assume that C has enough limits.
variable [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X], ext [] [ident S] [], dsimp [] [] [] [],
    simp [] [] ["only"] ["[", expr limit.lift_π, ",", expr coe_id, ",", expr change_cone_π_app, ",", expr limit.cone_π, ",", expr category.id_comp, "]"] [] [],
    erw [expr discrete_quotient.map_id] [], change [expr «expr = »(«expr ≫ »(_, F.map («expr𝟙»() _)), _)] [] [],
    rw ["[", expr F.map_id, ",", expr category.comp_id, "]"] [], congr, exact [expr S.comap_id] }] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X, ident Y, ident Z, ident f, ident g], ext [] [ident S] [], dsimp [] [] [] [],
    simp [] [] ["only"] ["[", expr limit.lift_π, ",", expr change_cone_π_app, ",", expr limit.cone_π, ",", expr limit.lift_π_assoc, ",", expr coe_comp, ",", expr category.assoc, ",", "<-", expr F.map_comp, "]"] [] [],
    congr, exact [expr discrete_quotient.map_comp _ _] }] -/
-- PROJECT: Prove that this is isomorphic to the right Kan extension along `Fintype.to_Profinite`.
/-- Extend a functor `Fintype ⥤ C` to `Profinite`. -/
@[simps]
def extend : Profinite ⥤ C where
  obj X := limit (X.fintypeDiagram ⋙ F)
  map X Y f := limit.lift _ (changeCone _ f _)
  map_id' := by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X], ext [] [ident S] [], dsimp [] [] [] [],\n    simp [] [] [\"only\"] [\"[\", expr limit.lift_π, \",\", expr coe_id, \",\", expr change_cone_π_app, \",\", expr limit.cone_π, \",\", expr category.id_comp, \"]\"] [] [],\n    erw [expr discrete_quotient.map_id] [], change [expr «expr = »(«expr ≫ »(_, F.map («expr𝟙»() _)), _)] [] [],\n    rw [\"[\", expr F.map_id, \",\", expr category.comp_id, \"]\"] [], congr, exact [expr S.comap_id] }]"
  map_comp' := by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X, ident Y, ident Z, ident f, ident g], ext [] [ident S] [], dsimp [] [] [] [],\n    simp [] [] [\"only\"] [\"[\", expr limit.lift_π, \",\", expr change_cone_π_app, \",\", expr limit.cone_π, \",\", expr limit.lift_π_assoc, \",\", expr coe_comp, \",\", expr category.assoc, \",\", \"<-\", expr F.map_comp, \"]\"] [] [],\n    congr, exact [expr discrete_quotient.map_comp _ _] }]"

/-- discrete quotients of a finite type has an initial object given by `⊥`. -/
@[simps]
def botInitial (X : FintypeCat) : IsInitial (⊥ : DiscreteQuotient (FintypeCat.toProfinite.obj X))
    where desc S := homOfLE bot_le

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X, ident Y, ident f], letI [] [":", expr topological_space X] [":=", expr «expr⊥»()],
    letI [] [":", expr topological_space Y] [":=", expr «expr⊥»()],
    have [ident hf] [":", expr continuous f] [":=", expr continuous_bot],
    let [ident A] [] [":=", expr Fintype.to_Profinite.obj X], let [ident B] [] [":=", expr Fintype.to_Profinite.obj Y],
    dsimp [] ["[", expr is_limit.cone_point_unique_up_to_iso, ",", expr limit_of_diagram_initial, "]"] [] [],
    simp [] [] ["only"] ["[", expr change_cone_π_app, ",", expr limit.cone_π, ",", expr limit.lift_π_assoc, ",", expr category.assoc, "]"] [] [],
    let [ident e] [":", expr «expr ⟶ »((«expr⊥»() : discrete_quotient X),
      («expr⊥»() : discrete_quotient Y).comap hf)] [":=", expr hom_of_le bot_le],
    erw ["<-", expr limit.w «expr ⋙ »(A.fintype_diagram, F) e] [],
    simp [] [] ["only"] ["[", expr category.assoc, ",", "<-", expr F.map_comp, ",", expr functor.comp_map, "]"] [] [],
    congr' [2] [], simp_rw ["[", "<-", expr iso.inv_comp_eq, ",", "<-", expr category.assoc, "]"] [], symmetry,
    rw ["<-", expr iso.comp_inv_eq] [], refl }] -/
/-- The extension of `F : Fintype ⥤ C` extends `F`. -/
@[simps]
def extendExtends : FintypeCat.toProfinite ⋙ extend F ≅ F :=
  (NatIso.ofComponents fun X => by
      dsimp only [extend, functor.comp_obj]
      let Y := Fintype.to_Profinite.obj X
      let D := limit.is_limit (Y.fintype_diagram ⋙ F)
      let E := limit_of_diagram_initial (bot_initial X) (Y.fintype_diagram ⋙ F)
      letI : TopologicalSpace X := ⊥
      let e : FintypeCat.of (⊥ : DiscreteQuotient X) ≅ X :=
        FintypeCat.isoOfEquiv (Equiv.ofBijective _ DiscreteQuotient.proj_bot_bijective).symm
      let g := D.cone_point_unique_up_to_iso E
      exact g ≪≫ F.map_iso e) <|
    by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X, ident Y, ident f], letI [] [\":\", expr topological_space X] [\":=\", expr «expr⊥»()],\n    letI [] [\":\", expr topological_space Y] [\":=\", expr «expr⊥»()],\n    have [ident hf] [\":\", expr continuous f] [\":=\", expr continuous_bot],\n    let [ident A] [] [\":=\", expr Fintype.to_Profinite.obj X], let [ident B] [] [\":=\", expr Fintype.to_Profinite.obj Y],\n    dsimp [] [\"[\", expr is_limit.cone_point_unique_up_to_iso, \",\", expr limit_of_diagram_initial, \"]\"] [] [],\n    simp [] [] [\"only\"] [\"[\", expr change_cone_π_app, \",\", expr limit.cone_π, \",\", expr limit.lift_π_assoc, \",\", expr category.assoc, \"]\"] [] [],\n    let [ident e] [\":\", expr «expr ⟶ »((«expr⊥»() : discrete_quotient X),\n      («expr⊥»() : discrete_quotient Y).comap hf)] [\":=\", expr hom_of_le bot_le],\n    erw [\"<-\", expr limit.w «expr ⋙ »(A.fintype_diagram, F) e] [],\n    simp [] [] [\"only\"] [\"[\", expr category.assoc, \",\", \"<-\", expr F.map_comp, \",\", expr functor.comp_map, \"]\"] [] [],\n    congr' [2] [], simp_rw [\"[\", \"<-\", expr iso.inv_comp_eq, \",\", \"<-\", expr category.assoc, \"]\"] [], symmetry,\n    rw [\"<-\", expr iso.comp_inv_eq] [], refl }]"

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident A, ident B, ident f],
    dsimp [] ["[", expr is_limit.postcompose_hom_equiv, ",", expr is_limit.of_cone_equiv, ",", expr is_limit.cone_point_unique_up_to_iso, "]"] [] [],
    ext [] [ident S] [],
    simp [] [] ["only"] ["[", "<-", expr nat_trans.naturality
     w.hom, ",", expr limit.lift_π, ",", expr cones.postcompose_obj_π, ",", expr functor.comp_map, ",", expr functor.map_cone_π_app, ",", expr change_cone_π_app, ",", expr limit.cone_π, ",", expr limit.lift_π_assoc, ",", expr whisker_left_app, ",", expr nat_trans.comp_app, ",", expr category.assoc, "]"] [] [],
    simp [] [] ["only"] ["[", "<-", expr category.assoc, ",", "<-", expr G.map_comp, "]"] [] [], refl }] -/
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
      let E' : Cone (X.fintypeDiagram ⋙ F) := (Cones.postcompose f.Hom).obj E
      let hE' : IsLimit E' := (IsLimit.postcomposeHomEquiv f _).symm hE
      hE'.conePointUniqueUpToIso (limit.isLimit _)) <|
    by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident A, ident B, ident f],\n    dsimp [] [\"[\", expr is_limit.postcompose_hom_equiv, \",\", expr is_limit.of_cone_equiv, \",\", expr is_limit.cone_point_unique_up_to_iso, \"]\"] [] [],\n    ext [] [ident S] [],\n    simp [] [] [\"only\"] [\"[\", \"<-\", expr nat_trans.naturality\n     w.hom, \",\", expr limit.lift_π, \",\", expr cones.postcompose_obj_π, \",\", expr functor.comp_map, \",\", expr functor.map_cone_π_app, \",\", expr change_cone_π_app, \",\", expr limit.cone_π, \",\", expr limit.lift_π_assoc, \",\", expr whisker_left_app, \",\", expr nat_trans.comp_app, \",\", expr category.assoc, \"]\"] [] [],\n    simp [] [] [\"only\"] [\"[\", \"<-\", expr category.assoc, \",\", \"<-\", expr G.map_comp, \"]\"] [] [], refl }]"

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X, ident Y, ident f], ext [] [] [], dsimp [] [] [] [],
    simp [] [] ["only"] ["[", expr category.assoc, ",", expr limit.lift_π, ",", expr change_cone_π_app, ",", expr limit.cone_π, ",", expr functor.comp_map, "]"] [] [],
    erw ["[", expr limit.lift_π, ",", expr limit.lift_π_assoc, "]"] [], dsimp [] [] [] [],
    rw ["[", "<-", expr G.map_comp, ",", expr limit.lift_π, ",", "<-", expr G.map_comp, "]"] [], refl }] -/
@[simps]
def extendCommutes (G : C ⥤ D) [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) G]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ G)] : extend F ⋙ G ≅ extend (F ⋙ G) :=
  (NatIso.ofComponents fun X =>
      (isLimitOfPreserves G (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)) <|
    by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `asyncI #[{ intros [ident X, ident Y, ident f], ext [] [] [], dsimp [] [] [] [],\n    simp [] [] [\"only\"] [\"[\", expr category.assoc, \",\", expr limit.lift_π, \",\", expr change_cone_π_app, \",\", expr limit.cone_π, \",\", expr functor.comp_map, \"]\"] [] [],\n    erw [\"[\", expr limit.lift_π, \",\", expr limit.lift_π_assoc, \"]\"] [], dsimp [] [] [] [],\n    rw [\"[\", \"<-\", expr G.map_comp, \",\", expr limit.lift_π, \",\", \"<-\", expr G.map_comp, \"]\"] [], refl }]"

@[reassoc]
theorem extendCommutes_comp_extendExtends (G : C ⥤ D)
    [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) G]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ G)] :
    whiskerLeft FintypeCat.toProfinite (extendCommutes F G).Hom ≫ (extendExtends _).Hom =
      (Functor.associator _ _ _).inv ≫ whiskerRight (extendExtends _).Hom G :=
  by
  ext
  simp only [nat_trans.comp_app, whisker_left_app, extend_extends_hom_app, functor.comp_map,
    functor.associator_inv_app, whisker_right_app, functor.map_comp, category.id_comp,
    extend_commutes_hom_app]
  rw [← category.assoc]; congr 1
  rw [← iso.eq_comp_inv]
  ext
  simp only [is_limit.cone_point_unique_up_to_iso, category.assoc, functor.map_iso_hom,
    is_limit.unique_up_to_iso_hom, cones.forget_map, is_limit.lift_cone_morphism_hom,
    limit.is_limit_lift]
  erw [limit.lift_π, limit.lift_π]
  simp only [functor.map_cone_π_app, limit.cone_π, functor.map_iso_inv, cones.forget_map,
    is_limit.unique_up_to_iso_inv, is_limit.lift_cone_morphism_hom, limit.is_limit_lift,
    cone_of_diagram_initial_π_app, functor.comp_map, limit_of_diagram_initial]
  rw [← functor.map_comp]; congr 1; symm
  exact limit.w _ ((bot_initial x).to j)

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
        α.app (Profinite.of T) ≫ (extendExtends G).Hom.app _ :=
  by
  have : (extend_extends G).Hom.app (X.fintype_diagram.obj T) = limit.π _ ⊥ ≫ _ := rfl
  erw [this, α.naturality_assoc]; congr 1
  dsimp [extend]
  simp only [limit.lift_π_assoc, change_cone_π_app, limit.cone_π, category.assoc, ← G.map_comp]
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
      (extendExtends F).Hom ≫ α ≫ (extendExtends G).inv :=
  by
  ext S
  simp only [lim_map, is_limit.map, whisker_left_app, extend_nat_trans_app, limit.is_limit_lift,
    limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app, limit.cone_π, extend_extends_hom_app,
    extend_extends_inv_app, category.assoc, nat_trans.naturality_assoc, ← G.map_iso_hom, ←
    G.map_iso_inv, iso.hom_inv_id_assoc]
  rw [← iso.inv_comp_eq]
  erw [limit.cone_point_unique_up_to_iso_inv_comp, limit.cone_point_unique_up_to_iso_inv_comp_assoc]
  simp only [cone_of_diagram_initial_π_app, functor.comp_map]
  erw [nat_trans.naturality]

theorem extendNatTrans_whiskerRight {F G : FintypeCat ⥤ C}
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ F)]
    [∀ X : Profinite, HasLimit (X.fintypeDiagram ⋙ G)] (α : F ⟶ G) (E : C ⥤ D)
    [∀ X : Profinite.{v}, PreservesLimitsOfShape (DiscreteQuotient X) E]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ F ⋙ E)]
    [∀ X : Profinite.{v}, HasLimit (X.fintypeDiagram ⋙ G ⋙ E)] :
    extendNatTrans (whiskerRight α E) =
      (extendCommutes _ _).inv ≫ whiskerRight (extendNatTrans α) E ≫ (extendCommutes _ _).Hom :=
  by
  apply extend_nat_trans_ext
  simp only [extend_nat_trans_whisker_left, ← whisker_right_left, category.assoc, whisker_left_comp,
    whisker_right_comp]
  rw [← iso_whisker_left_inv, iso.eq_inv_comp, iso_whisker_left_hom,
    extend_commutes_comp_extend_extends_assoc]
  simp only [← category.assoc, iso.comp_inv_eq]
  simp only [category.assoc, extend_commutes_comp_extend_extends]
  ext
  simp only [nat_trans.comp_app, functor.associator_hom_app, functor.associator_inv_app]
  erw [category.id_comp, category.id_comp]
  simp only [← nat_trans.comp_app, ← iso_whisker_right_hom, ← iso_whisker_right_inv, iso.inv_hom_id]
  erw [category.comp_id]

end Profinite

