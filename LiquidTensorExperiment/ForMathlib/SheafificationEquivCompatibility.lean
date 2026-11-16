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

-- Porting note: in mathlib4 `cover_lifting` is the class `Functor.IsCocontinuous`, `Sites.pullback`
-- is `Functor.sheafPushforwardContinuous` (which needs the `Functor.IsContinuous` instance, built
-- from `Hc` and `Hp`), and `Sites.pullback_copullback_adjunction` is
-- `Functor.sheafAdjunctionCocontinuous`.  The universe of `Hc` is forced to be `max v u`.
/-- The isomorphism exhibiting compatibility between pullback and sheafification. -/
def pullbackSheafificationCompatibility {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : Functor.IsCocontinuous G J K) (Hc : CompatiblePreserving.{max v u} K G) :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙
        @Functor.sheafPushforwardContinuous _ _ _ _ G A _ J K
          (Functor.isContinuous_of_coverPreserving Hc Hp) :=
  letI := Hl
  letI := Functor.isContinuous_of_coverPreserving Hc Hp
  let A1 : (whiskeringLeft _ _ A).obj G.op ⊣ _ := Ran.adjunction _ _
  let A2 : presheafToSheaf J A ⊣ _ := sheafificationAdjunction _ _
  let B1 : presheafToSheaf K A ⊣ _ := sheafificationAdjunction _ _
  let B2 : G.sheafPushforwardContinuous A J K ⊣ _ :=
    Functor.sheafAdjunctionCocontinuous _ _ _ _
  let A12 := A1.comp A2
  let B12 := B1.comp B2
  A12.leftAdjointUniq B12

theorem toSheafify_pullbackSheafificationCompatibility {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : Functor.IsCocontinuous G J K) (Hc : CompatiblePreserving.{max v u} K G) (F) :
    J.toSheafify (G.op ⋙ F) ≫
        ((pullbackSheafificationCompatibility.{w, v, u} A Hp Hl Hc).hom.app F).val =
      whiskerLeft G.op (K.toSheafify F) := by
  -- Porting note: the proof is now the corresponding statement from mathlib
  letI := Hl
  letI := Functor.isContinuous_of_coverPreserving Hc Hp
  exact Functor.toSheafify_pullbackSheafificationCompatibility G A J K F

@[simp]
theorem pullbackSheafificationCompatibility_hom_apply_val {G : C ⥤ D} (Hp : CoverPreserving J K G)
    (Hl : Functor.IsCocontinuous G J K) (Hc : CompatiblePreserving.{max v u} K G) (F) :
    ((pullbackSheafificationCompatibility.{w, v, u} A Hp Hl Hc).hom.app F).val =
      J.sheafifyLift (whiskerLeft G.op <| K.toSheafify F)
        -- Porting note: the `Sheaf.cond _` argument is given explicitly (elaboration timed out)
        (by
          letI := Hl
          letI := Functor.isContinuous_of_coverPreserving Hc Hp
          exact ((presheafToSheaf K A ⋙ G.sheafPushforwardContinuous A J K).obj F).cond) := by
  apply J.sheafifyLift_unique
  apply CategoryTheory.Sites.toSheafify_pullbackSheafificationCompatibility

end CategoryTheory.Sites

namespace CategoryTheory.Functor.IsCoverDense

variable {G : C ⥤ D} [Full G] [Faithful G]

variable (Hd : CategoryTheory.Functor.IsCoverDense G K) (Hp : CoverPreserving J K G)
  (Hl : CategoryTheory.Functor.IsCocontinuous G J K)

-- Porting note: `Hd` is used as an instance and `IsContinuous` is derived from `Hd` and `Hp`
-- (in mathlib4, `sheafEquivOfCoverPreservingCoverLifting` takes these as instance arguments).
/-- The isomorphism exhibiting the compatibiility of
`Sheaf_equiv_of_cover_preserving_cover_lifting` with sheafification. -/
-- Porting note: Lean 3 `cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting_sheafification_compatibility`
-- was upstreamed to mathlib4 under that name, with the hypotheses as instance arguments; LTE's
-- version (explicit hypotheses `Hd Hp Hl`) is kept under a primed name.
noncomputable abbrev sheafEquivOfCoverPreservingCoverLiftingSheafificationCompatibility' :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙
        Equivalence.inverse
        (letI : G.IsCoverDense K := Hd
         letI : G.IsCocontinuous J K := Hl
         letI : G.IsContinuous J K := IsCoverDense.isContinuous (G := G) (J := J) (K := K) Hp
         sheafEquivOfCoverPreservingCoverLifting G J K A) :=
  letI : G.IsCoverDense K := Hd
  CategoryTheory.Sites.pullbackSheafificationCompatibility _ Hp Hl
    (IsCoverDense.compatiblePreserving K G)

end CategoryTheory.Functor.IsCoverDense
