import Mathlib.CategoryTheory.Sites.Sheafification

#align_import for_mathlib.SheafOfTypes_sheafification

-- Porting note: `noncomputable theory` moved before the first namespace so that the
-- `end`s match
noncomputable section

namespace CategoryTheory

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

@[simps]
def presheafToSheafOfTypes : (Cᵒᵖ ⥤ Type max v u) ⥤ SheafOfTypes J
    where
  obj P :=
    { val := J.sheafify P
      cond := by
        rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact GrothendieckTopology.Plus.isSheaf_plus_plus J P }
  map η := ⟨J.sheafifyMap η⟩
  map_id P := SheafOfTypes.Hom.ext _ _ <| J.sheafifyMap_id _
  map_comp η γ := SheafOfTypes.Hom.ext _ _ <| J.sheafifyMap_comp _ _

-- Sanity check
def presheafToSheafOfTypesIso :
    presheafToSheafOfTypes J ≅ presheafToSheaf J _ ⋙ (sheafEquivSheafOfTypes J).functor :=
  eqToIso rfl

-- The adjunction for sheaves of types
def sheafificationAdjunctionTypes : presheafToSheafOfTypes J ⊣ sheafOfTypesToPresheaf J :=
  show
    presheafToSheaf J (Type max v u) ⋙ (sheafEquivSheafOfTypes J).functor ⊣
      (sheafEquivSheafOfTypes J).inverse ⋙ sheafToPresheaf J (Type max v u)
    from
    Adjunction.comp (sheafificationAdjunction J (Type max v u)) <|
      (sheafEquivSheafOfTypes J).toAdjunction

@[simp]
theorem sheafificationAdjunctionTypes_homEquiv_apply (X : Cᵒᵖ ⥤ Type max v u) (Y : SheafOfTypes J)
    (e : (presheafToSheafOfTypes _).obj X ⟶ Y) :
    (sheafificationAdjunctionTypes J).homEquiv _ _ e = J.toSheafify _ ≫ e.val :=
  rfl

@[simp]
theorem sheafificationAdjunctionTypes_homEquiv_symm_apply (X : Cᵒᵖ ⥤ Type max v u)
    (Y : SheafOfTypes J) (e : X ⟶ (sheafOfTypesToPresheaf _).obj Y) :
    (((sheafificationAdjunctionTypes J).homEquiv _ _).symm e).val =
      J.sheafifyLift e (by rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]; exact Y.2) :=
  rfl

-- Porting note: computing the simp-lemma keys for this lemma exceeds the default heartbeat limit
-- (unfolding `sheafificationAdjunctionTypes`); a bounded increase is used.
set_option maxHeartbeats 1000000 in
@[simp]
theorem sheafificationAdjunctionTypes_unit_app (X : Cᵒᵖ ⥤ Type max v u) :
    (sheafificationAdjunctionTypes J).unit.app X = J.toSheafify X :=
  rfl

-- Porting note: computing the simp-lemma keys for this lemma exceeds the default heartbeat limit
-- (unfolding `sheafificationAdjunctionTypes`); a bounded increase is used.
set_option maxHeartbeats 1000000 in
@[simp]
theorem sheafificationAdjunctionTypes_counit_app (Y : SheafOfTypes J) :
    ((sheafificationAdjunctionTypes J).counit.app Y).val =
      J.sheafifyLift (𝟙 Y.val) (by rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]; exact Y.2) :=
  rfl

instance isIso_sheafification_types_adjunction_counit_app (X : SheafOfTypes J) :
    IsIso ((sheafificationAdjunctionTypes J).counit.app X) :=
  by
  -- Porting note: `apply` already closes the remaining goal by instance search
  apply CategoryTheory.isIso_of_reflects_iso _ (sheafEquivSheafOfTypes J).inverse

instance sheafification_types_reflective : IsIso (sheafificationAdjunctionTypes J).counit :=
  NatIso.isIso_of_isIso_app _

end CategoryTheory

