import Mathlib.CategoryTheory.Sites.DenseSubsite

#align_import for_mathlib.sheafification_equiv_compatibility

/-!
Content pulled from mathlib PR #14512
-/


universe w v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

variable (A : Type w) [Category.{max v u} A] [HasLimits A]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable [ConcreteCategory.{max v u} A] [PreservesLimits (forget A)]
  [ReflectsIsomorphisms (forget A)] [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget A)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]
  [∀ X : D, PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget A)]
  [∀ X : D, HasColimitsOfShape (K.Cover X)ᵒᵖ A]

namespace CategoryTheory.Sites

/-- The isomorphism exhibiting compatibility between pullback and sheafification. -/
def pullbackSheafificationCompatibility {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CategoryTheory.Functor.IsCocontinuous J K G) (Hc : CompatiblePreserving K G) :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙ Functor.sheafPushforwardContinuous A Hc Hp :=
  let A1 : (whiskeringLeft _ _ A).obj G.op ⊣ _ := Ran.adjunction _ _
  let A2 : presheafToSheaf J A ⊣ _ := sheafificationAdjunction _ _
  let B1 : presheafToSheaf K A ⊣ _ := sheafificationAdjunction _ _
  let B2 : Functor.sheafPushforwardContinuous A Hc Hp ⊣ _ :=
    Functor.sheafAdjunctionCocontinuous _ _ Hl _
  let A12 := A1.comp A2
  let B12 := B1.comp B2
  A12.leftAdjointUniq B12

theorem toSheafify_pullbackSheafificationCompatibility {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CategoryTheory.Functor.IsCocontinuous J K G) (Hc : CompatiblePreserving K G) (F) :
    J.toSheafify (G.op ⋙ F) ≫
        ((pullbackSheafificationCompatibility.{w, v, u} A Hp Hl Hc).Hom.app F).val =
      whiskerLeft _ (K.toSheafify _) :=
  by
  dsimp [CategoryTheory.Sites.pullbackSheafificationCompatibility, adjunction.left_adjoint_uniq]
  apply Quiver.Hom.op_inj
  apply coyoneda.map_injective; swap; infer_instance
  ext E f : 2
  dsimp [functor.preimage, full.preimage, coyoneda, adjunction.left_adjoints_coyoneda_equiv]
  simp only [adjunction.hom_equiv_unit, functor.comp_map, Sheaf_to_presheaf_map,
    adjunction.hom_equiv_naturality_left_symm, whiskering_left_obj_map, adjunction.hom_equiv_counit,
    Sheaf.category_theory.category_comp_val, presheaf_to_Sheaf_map_val]
  dsimp [adjunction.comp]
  simp only [sheafification_adjunction_unit_app, category.comp_id, Functor.map_id, whisker_left_id',
    category.assoc, grothendieck_topology.sheafify_map_sheafify_lift, category.id_comp,
    grothendieck_topology.to_sheafify_sheafify_lift]
  ext t
  dsimp only [whisker_left, nat_trans.comp_app]
  simp only [category.assoc]
  -- for some reason the proof that works in mathllib does not work here...
  -- we have to be a little more forceful.
  erw [(Ran G.op).map_id, category.id_comp]
  congr 1; simp only [← category.assoc]
  convert category.id_comp _
  dsimp only [pullback_sheaf]
  have := (Ran.adjunction A G.op).left_triangle
  apply_fun fun e => (e.app (K.sheafify F)).app x at this 
  exact this

@[simp]
theorem pullbackSheafificationCompatibility_hom_apply_val {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : CategoryTheory.Functor.IsCocontinuous J K G) (Hc : CompatiblePreserving K G) (F) :
    ((pullbackSheafificationCompatibility.{w, v, u} A Hp Hl Hc).Hom.app F).val =
      J.sheafifyLift (whiskerLeft _ <| K.toSheafify _) (Sheaf.cond _) :=
  by
  apply J.sheafify_lift_unique
  apply to_sheafify_pullback_sheafification_compatibility

end CategoryTheory.Sites

namespace CategoryTheory.Functor.IsCoverDense

variable {G : C ⥤ D} [Full G] [Faithful G]

variable (Hd : CategoryTheory.Functor.IsCoverDense K G) (Hp : CoverPreserving J K G)
  (Hl : CategoryTheory.Functor.IsCocontinuous J K G)

#print CategoryTheory.Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLiftingSheafificationCompatibility /-
/-- The isomorphism exhibiting the compatibiility of
`Sheaf_equiv_of_cover_preserving_cover_lifting` with sheafification. -/
noncomputable abbrev
  CategoryTheory.Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLiftingSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf _ _ ≅
      presheafToSheaf _ _ ⋙
        (CategoryTheory.Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting Hd Hp
            Hl).inverse :=
  CategoryTheory.Sites.pullbackSheafificationCompatibility _ _ Hl _
-/

end CategoryTheory.Functor.IsCoverDense

