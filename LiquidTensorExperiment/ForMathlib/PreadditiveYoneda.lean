import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective

#align_import for_mathlib.preadditiveYoneda

open Opposite

namespace CategoryTheory

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A]

theorem isIso_of_isIso_preadditiveYoneda_map_app {X Y : A} (f : X ⟶ Y)
    [∀ W : A, IsIso ((preadditiveYoneda.map f).app (op W))] : IsIso f :=
  by
  let e := (preadditive_yoneda.map f).app (op Y)
  let g := (preadditive_yoneda.map f).app (op X)
  use inv e (𝟙 _)
  constructor
  · apply_fun g
    swap
    · intro i j h
      apply_fun inv g at h 
      simpa only [← comp_apply, IsIso.hom_inv_id] using h
    dsimp [g]
    simp only [Category.id_comp, Category.assoc]
    change f ≫ e _ = _
    simp only [← comp_apply, IsIso.hom_inv_id]
    simp
  · change e (inv e (𝟙 _)) = _
    simp only [← comp_apply, IsIso.inv_hom_id]
    simpa

end CategoryTheory

