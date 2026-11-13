import Mathlib.CategoryTheory.Sites.Sheafification

#align_import for_mathlib.SheafOfTypes_sheafification

namespace CategoryTheory

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

noncomputable section

@[simps]
def presheafToSheafOfTypes : (Cᵒᵖ ⥤ Type max v u) ⥤ SheafOfTypes J
    where
  obj P :=
    { val := J.sheafify P
      cond := by
        rw [← is_sheaf_iff_is_sheaf_of_type]
        exact grothendieck_topology.plus.is_sheaf_plus_plus J P }
  map P Q η := ⟨J.sheafifyMap η⟩
  map_id' P := SheafOfTypes.Hom.ext _ _ <| J.sheafifyMap_id _
  map_comp' P Q R η γ := SheafOfTypes.Hom.ext _ _ <| J.sheafifyMap_comp _ _

-- Sanity check
def presheafToSheafOfTypesIso :
    presheafToSheafOfTypes J ≅ presheafToSheaf J _ ⋙ (sheafEquivSheafOfTypes J).Functor :=
  eqToIso rfl

-- The adjunction for sheaves of types
def sheafificationAdjunctionTypes : presheafToSheafOfTypes J ⊣ sheafOfTypesToPresheaf J :=
  show
    presheafToSheaf J _ ⋙ (sheafEquivSheafOfTypes J).Functor ⊣
      (sheafEquivSheafOfTypes J).inverse ⋙ sheafToPresheaf J _
    from Adjunction.comp (sheafificationAdjunction _ _) <| (sheafEquivSheafOfTypes J).toAdjunction

@[simp]
theorem sheafificationAdjunctionTypes_homEquiv_apply (X : Cᵒᵖ ⥤ Type max v u) (Y : SheafOfTypes J)
    (e : (presheafToSheafOfTypes _).obj X ⟶ Y) :
    (sheafificationAdjunctionTypes J).homEquiv _ _ e = J.toSheafify _ ≫ e.val :=
  rfl

@[simp]
theorem sheafificationAdjunctionTypes_homEquiv_symm_apply (X : Cᵒᵖ ⥤ Type max v u)
    (Y : SheafOfTypes J) (e : X ⟶ (sheafOfTypesToPresheaf _).obj Y) :
    (((sheafificationAdjunctionTypes J).homEquiv _ _).symm e).val =
      J.sheafifyLift e (by rw [is_sheaf_iff_is_sheaf_of_type]; exact Y.2) :=
  rfl

@[simp]
theorem sheafificationAdjunctionTypes_unit_app (X : Cᵒᵖ ⥤ Type max v u) :
    (sheafificationAdjunctionTypes J).Unit.app X = J.toSheafify X :=
  rfl

@[simp]
theorem sheafificationAdjunctionTypes_counit_app (Y : SheafOfTypes J) :
    ((sheafificationAdjunctionTypes J).counit.app Y).val =
      J.sheafifyLift (𝟙 _) (by rw [is_sheaf_iff_is_sheaf_of_type]; exact Y.2) :=
  rfl

instance isIso_sheafification_types_adjunction_counit_app (X : SheafOfTypes J) :
    IsIso ((sheafificationAdjunctionTypes J).counit.app X) :=
  by
  apply is_iso_of_reflects_iso _ (Sheaf_equiv_SheafOfTypes J).inverse
  change
    is_iso
      ((sheafification_adjunction J (Type max v u)).counit.app
        ((Sheaf_equiv_SheafOfTypes J).inverse.obj X))
  infer_instance

instance sheafification_types_reflective : IsIso (sheafificationAdjunctionTypes J).counit :=
  NatIso.isIso_of_isIso_app _

end CategoryTheory

