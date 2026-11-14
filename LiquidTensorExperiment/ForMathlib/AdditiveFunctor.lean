import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Preadditive
import LiquidTensorExperiment.ForMathlib.IsBiprod

#align_import for_mathlib.additive_functor

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Functor

variable {𝒜 ℬ : Type _} [Category 𝒜] [Category ℬ]

variable [Preadditive 𝒜] [Preadditive ℬ]

variable (F : 𝒜 ⥤ ℬ)

theorem additive_of_map_fst_add_snd [HasBinaryBiproducts 𝒜]
    (h :
      ∀ A : 𝒜, F.map (biprod.fst + biprod.snd : A ⊞ A ⟶ A) = F.map biprod.fst + F.map biprod.snd) :
    F.Additive :=
  {
    map_add := fun {A B} {f g} =>
      by
      have : f + g = biprod.lift f g ≫ (biprod.fst + biprod.snd) := by
        rw [Preadditive.comp_add, biprod.lift_fst, biprod.lift_snd]
      rw [this, F.map_comp, h, Preadditive.comp_add, ← F.map_comp, ← F.map_comp, biprod.lift_fst,
        biprod.lift_snd] }

noncomputable def objBiprodIso (F : 𝒜 ⥤ ℬ) [F.Additive] (A B : 𝒜) [HasBinaryBiproduct A B]
    [HasBinaryBiproduct (F.obj A) (F.obj B)] : F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B :=
  IsBiprod.isoBiprod _ (F.mapIsBiprod _ (Biprod.isBiprod A B))

instance forget₂_additive (R : Type _) [Ring R] : (forget₂ (ModuleCat R) AddCommGroupCat).Additive where
  map_add := rfl

/-! Porting note: LTE's `CategoryTheory.Functor.map_isZero` (for additive functors) is superseded by
mathlib's lemma of the same name, which only assumes `F.PreservesZeroMorphisms` (an instance for
additive functors), so LTE's copy is removed. -/

end Functor

end CategoryTheory

