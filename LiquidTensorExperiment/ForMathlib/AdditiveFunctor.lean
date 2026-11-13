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
    map_add' := fun A B f g =>
      by
      have : f + g = biprod.lift f g ≫ (biprod.fst + biprod.snd) := by
        rw [preadditive.comp_add, biprod.lift_fst, biprod.lift_snd]
      rw [this, F.map_comp, h, preadditive.comp_add, ← F.map_comp, ← F.map_comp, biprod.lift_fst,
        biprod.lift_snd] }

noncomputable def objBiprodIso (F : 𝒜 ⥤ ℬ) [F.Additive] (A B : 𝒜) [HasBinaryBiproduct A B]
    [HasBinaryBiproduct (F.obj A) (F.obj B)] : F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B :=
  IsBiprod.isoBiprod _ (F.mapIsBiprod _ (Biprod.isBiprod A B))

instance forget₂_additive (R : Type _) [Ring R] : (forget₂ (ModuleCat R) AddCommGroupCat).Additive
    where map_add' M N f g := rfl

theorem map_isZero {X : 𝒜} [F.Additive] (hX : Limits.IsZero X) : Limits.IsZero (F.obj X) :=
  by
  rw [limits.is_zero.iff_id_eq_zero] at hX ⊢
  convert congr_arg (@CategoryTheory.Functor.map _ _ _ _ F _ _) hX <;> simp

end Functor

end CategoryTheory

