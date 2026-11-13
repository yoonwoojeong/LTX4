import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Generator
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.InjectiveResolution
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Preadditive.OfBiproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.Tactic.IntervalCases

#align_import for_mathlib.fin_functor

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Fin3FunctorMk

variable (F : Fin 3 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2)

def map' : ∀ (i j : Fin 3) (hij : i ≤ j), F i ⟶ F j
  | ⟨0, hi⟩, ⟨0, hj⟩, _ => 𝟙 _
  | ⟨1, hi⟩, ⟨1, hj⟩, _ => 𝟙 _
  | ⟨2, hi⟩, ⟨2, hj⟩, _ => 𝟙 _
  | ⟨0, hi⟩, ⟨1, hj⟩, _ => a
  | ⟨1, hi⟩, ⟨2, hj⟩, _ => b
  | ⟨0, hi⟩, ⟨2, hj⟩, _ => a ≫ b
  | ⟨i + 3, hi⟩, _, _ => by exfalso; revert hi; decide
  | _, ⟨j + 3, hj⟩, _ => by exfalso; revert hj; decide
  | ⟨i + 1, hi⟩, ⟨0, hj⟩, H => by exfalso; revert H; decide
  | ⟨i + 2, hi⟩, ⟨1, hj⟩, H => by exfalso; revert H; decide

theorem map'_id : ∀ i : Fin 3, map' F a b i i le_rfl = 𝟙 _
  | ⟨0, hi⟩ => rfl
  | ⟨1, hi⟩ => rfl
  | ⟨2, hi⟩ => rfl
  | ⟨i + 3, hi⟩ => by exfalso; revert hi; decide

theorem map'_comp :
    ∀ (i j k : Fin 3) (hij : i ≤ j) (hjk : j ≤ k),
      map' F a b i j hij ≫ map' F a b j k hjk = map' F a b i k (hij.trans hjk)
  | ⟨0, _⟩, ⟨0, _⟩, k, _, _ => Category.id_comp _
  | ⟨1, _⟩, ⟨1, _⟩, k, _, _ => Category.id_comp _
  | i, ⟨1, _⟩, ⟨1, _⟩, _, _ => Category.comp_id _
  | i, ⟨2, _⟩, ⟨2, _⟩, _, _ => Category.comp_id _
  | ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩, _, _ => rfl
  | ⟨i + 3, hi⟩, _, _, _, _ => by exfalso; revert hi; decide
  | _, ⟨j + 3, hj⟩, _, _, _ => by exfalso; revert hj; decide
  | _, _, ⟨k + 3, hk⟩, _, _ => by exfalso; revert hk; decide
  | ⟨i + 1, hi⟩, ⟨0, hj⟩, _, H, _ => by exfalso; revert H; decide
  | ⟨i + 2, hi⟩, ⟨1, hj⟩, _, H, _ => by exfalso; revert H; decide
  | _, ⟨i + 1, hi⟩, ⟨0, hj⟩, _, H => by exfalso; revert H; decide
  | _, ⟨i + 2, hi⟩, ⟨1, hj⟩, _, H => by exfalso; revert H; decide

end Fin3FunctorMk

def fin3FunctorMk (F : Fin 3 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) : Fin 3 ⥤ C
    where
  obj := F
  map i j hij := Fin3FunctorMk.map' F a b i j hij.le
  map_id i := Fin3FunctorMk.map'_id F a b i
  map_comp i j k hij hjk := by rw [Fin3FunctorMk.map'_comp F a b i j k hij.le hjk.le]

namespace Fin4FunctorMk

variable (F : Fin 4 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) (c : F 2 ⟶ F 3)

def map' : ∀ (i j : Fin 4) (hij : i ≤ j), F i ⟶ F j
  | ⟨0, hi⟩, ⟨0, hj⟩, _ => 𝟙 _
  | ⟨1, hi⟩, ⟨1, hj⟩, _ => 𝟙 _
  | ⟨2, hi⟩, ⟨2, hj⟩, _ => 𝟙 _
  | ⟨3, hi⟩, ⟨3, hj⟩, _ => 𝟙 _
  | ⟨0, hi⟩, ⟨1, hj⟩, _ => a
  | ⟨1, hi⟩, ⟨2, hj⟩, _ => b
  | ⟨2, hi⟩, ⟨3, hj⟩, _ => c
  | ⟨0, hi⟩, ⟨2, hj⟩, _ => a ≫ b
  | ⟨1, hi⟩, ⟨3, hj⟩, _ => b ≫ c
  | ⟨0, hi⟩, ⟨3, hj⟩, _ => a ≫ b ≫ c
  | ⟨i + 4, hi⟩, _, _ => by exfalso; revert hi; decide
  | _, ⟨j + 4, hj⟩, _ => by exfalso; revert hj; decide
  | ⟨i + 1, hi⟩, ⟨0, hj⟩, H => by exfalso; revert H; decide
  | ⟨i + 2, hi⟩, ⟨1, hj⟩, H => by exfalso; revert H; decide
  | ⟨3, hi⟩, ⟨2, hj⟩, H => by exfalso; revert H; decide

theorem map'_id : ∀ i : Fin 4, map' F a b c i i le_rfl = 𝟙 _
  | ⟨0, hi⟩ => rfl
  | ⟨1, hi⟩ => rfl
  | ⟨2, hi⟩ => rfl
  | ⟨3, hi⟩ => rfl
  | ⟨i + 4, hi⟩ => by exfalso; revert hi; decide

theorem map'_comp :
    ∀ (i j k : Fin 4) (hij : i ≤ j) (hjk : j ≤ k),
      map' F a b c i j hij ≫ map' F a b c j k hjk = map' F a b c i k (hij.trans hjk)
  | ⟨0, _⟩, ⟨0, _⟩, k, _, _ => Category.id_comp _
  | ⟨1, _⟩, ⟨1, _⟩, k, _, _ => Category.id_comp _
  | ⟨2, _⟩, ⟨2, _⟩, k, _, _ => Category.id_comp _
  | i, ⟨1, _⟩, ⟨1, _⟩, _, _ => Category.comp_id _
  | i, ⟨2, _⟩, ⟨2, _⟩, _, _ => Category.comp_id _
  | i, ⟨3, _⟩, ⟨3, _⟩, _, _ => Category.comp_id _
  | ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩, _, _ => rfl
  | ⟨0, _⟩, ⟨1, _⟩, ⟨3, _⟩, _, _ => rfl
  | ⟨0, _⟩, ⟨2, _⟩, ⟨3, _⟩, _, _ => Category.assoc a b c
  | ⟨1, _⟩, ⟨2, _⟩, ⟨3, _⟩, _, _ => rfl
  | ⟨i + 4, hi⟩, _, _, _, _ => by exfalso; revert hi; decide
  | _, ⟨j + 4, hj⟩, _, _, _ => by exfalso; revert hj; decide
  | _, _, ⟨k + 4, hk⟩, _, _ => by exfalso; revert hk; decide
  | ⟨i + 1, hi⟩, ⟨0, hj⟩, _, H, _ => by exfalso; revert H; decide
  | ⟨i + 2, hi⟩, ⟨1, hj⟩, _, H, _ => by exfalso; revert H; decide
  | ⟨3, hi⟩, ⟨2, hj⟩, _, H, _ => by exfalso; revert H; decide
  | _, ⟨i + 1, hi⟩, ⟨0, hj⟩, _, H => by exfalso; revert H; decide
  | _, ⟨i + 2, hi⟩, ⟨1, hj⟩, _, H => by exfalso; revert H; decide
  | _, ⟨3, hi⟩, ⟨2, hj⟩, _, H => by exfalso; revert H; decide

end Fin4FunctorMk

def fin4FunctorMk (F : Fin 4 → C) (a : F 0 ⟶ F 1) (b : F 1 ⟶ F 2) (c : F 2 ⟶ F 3) : Fin 4 ⥤ C
    where
  obj := F
  map i j hij := Fin4FunctorMk.map' F a b c i j hij.le
  map_id i := Fin4FunctorMk.map'_id F a b c i
  map_comp i j k hij hjk := by rw [Fin4FunctorMk.map'_comp F a b c i j k hij.le hjk.le]

end CategoryTheory

