import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective

#align_import for_mathlib.preadditive_yoneda

open Opposite

namespace CategoryTheory

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A]

theorem isIso_of_isIso_preadditiveYoneda_map_app {X Y : A} (f : X ⟶ Y)
    [∀ W : A, IsIso ((preadditiveYoneda.map f).app (op W))] : IsIso f :=
  by
  let e := (preadditiveYoneda.map f).app (op Y)
  let g := (preadditiveYoneda.map f).app (op X)
  use inv e (𝟙 _)
  constructor
  -- Porting note: the Lean 3 proof used `simp only [← comp_apply, IsIso.hom_inv_id]`, which no
  -- longer fires; we evaluate `IsIso.hom_inv_id`/`inv_hom_id` at an element instead.
  · apply_fun g
    swap
    · intro i j h
      have key : ∀ x, inv g (g x) = x := fun x =>
        FunLike.congr_fun (IsIso.hom_inv_id g) x
      rw [← key i, h, key j]
    show (f ≫ inv e (𝟙 Y)) ≫ f = 𝟙 X ≫ f
    have : inv e (𝟙 Y) ≫ f = 𝟙 Y := FunLike.congr_fun (IsIso.inv_hom_id e) (𝟙 Y)
    rw [Category.assoc, this, Category.comp_id, Category.id_comp]
  · exact FunLike.congr_fun (IsIso.inv_hom_id e) (𝟙 Y)

end CategoryTheory

