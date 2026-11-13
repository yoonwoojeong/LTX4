import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Types

#align_import for_mathlib.wide_pullback_iso

namespace CategoryTheory

open CategoryTheory.Limits

universe u

variable {C : Type (u + 1)} [Category.{u} C] [HasWidePullbacks.{0} C]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

open Opposite

noncomputable section

def uliftWidePullbackIsoHomAux (i : ℕ) (T B X : C) (f : X ⟶ B) :
    uliftFunctor.{u + 1}.obj (T ⟶ widePullback B (fun _ : Fin i => X) fun _ => f) ⟶
      widePullback (ULift.{u + 1, u} <| T ⟶ B) (fun _ : Fin i => ULift.{u + 1, u} <| T ⟶ X) fun _ =>
        uliftFunctor.map <| (yoneda.map f).app (Opposite.op T) :=
  WidePullback.lift (uliftFunctor.map <| (yoneda.map <| WidePullback.base _).app (Opposite.op T))
    (fun q => uliftFunctor.map <| (yoneda.map <| WidePullback.π _ <| q).app (Opposite.op T))
    (by
      rintro ⟨j⟩
      rw [← functor.map_comp]
      congr 1
      ext q
      dsimp [yoneda]
      rw [← wide_pullback.π_arrow]
      rw [category.assoc])

def uliftWidePullbackIsoInvAux (i : ℕ) (T B X : C) (f : X ⟶ B) :
    (widePullback (ULift.{u + 1, u} <| T ⟶ B) (fun _ : Fin i => ULift.{u + 1, u} <| T ⟶ X) fun _ =>
        uliftFunctor.map <| (yoneda.map f).app (Opposite.op T)) ⟶
      uliftFunctor.{u + 1}.obj (T ⟶ widePullback B (fun _ : Fin i => X) fun _ => f) :=
  let b :
    (widePullback (ULift.{u + 1, u} <| T ⟶ B) (fun _ : Fin i => ULift.{u + 1, u} <| T ⟶ X) fun _ =>
        uliftFunctor.map <| (yoneda.map f).app (Opposite.op T)) ⟶
      _ :=
    WidePullback.base _
  let π :
    ∀ q : Fin i,
      (widePullback (ULift.{u + 1, u} <| T ⟶ B) (fun _ : Fin i => ULift.{u + 1, u} <| T ⟶ X)
          fun _ => uliftFunctor.map <| (yoneda.map f).app (Opposite.op T)) ⟶
        _ :=
    WidePullback.π _
  fun t =>
  ULift.up <|
    WidePullback.lift (b t).down (fun q : Fin i => (π q t).down)
      (by
        rintro ⟨j⟩
        dsimp [b, π]; rw [← wide_pullback.π_arrow]; rfl)

def uliftWidePullbackIso (i : ℕ) (T B X : C) (f : X ⟶ B) :
    uliftFunctor.{u + 1}.obj (T ⟶ widePullback B (fun _ : Fin i => X) fun _ => f) ≅
      widePullback (ULift.{u + 1, u} <| T ⟶ B) (fun _ : Fin i => ULift.{u + 1, u} <| T ⟶ X) fun _ =>
        uliftFunctor.map <| (yoneda.map f).app (Opposite.op T)
    where
  Hom := uliftWidePullbackIsoHomAux _ _ _ _ _
  inv := uliftWidePullbackIsoInvAux _ _ _ _ _
  hom_inv_id' :=
    by
    dsimp [ulift_wide_pullback_iso_hom_aux, ulift_wide_pullback_iso_inv_aux]
    ext t : 2; dsimp; apply wide_pullback.hom_ext; rintro ⟨j⟩
    · simp only [wide_pullback.lift_π]
      have :=
        types_comp_apply
          (wide_pullback.lift
            (uliftFunctor.{u + 1, u}.map
              ((yoneda.{u, u + 1}.map (wide_pullback.base fun _x : Fin i => f)).app (op.{u + 2} T)))
            (fun q : Fin i =>
              uliftFunctor.{u + 1, u}.map
                ((yoneda.{u, u + 1}.map (wide_pullback.π (fun _x : Fin i => f) q)).app
                  (op.{u + 2} T)))
            _)
          (wide_pullback.π
            (fun _x : Fin i =>
              uliftFunctor.{u + 1, u}.map ((yoneda.{u, u + 1}.map f).app (op.{u + 2} T)))
            _)
          t
      rw [← this, wide_pullback.lift_π]; rfl
    · simp only [wide_pullback.lift_base]
      have :=
        types_comp_apply
          (wide_pullback.lift
            (uliftFunctor.{u + 1, u}.map
              ((yoneda.{u, u + 1}.map (wide_pullback.base fun _x : Fin i => f)).app (op.{u + 2} T)))
            (fun q : Fin i =>
              uliftFunctor.{u + 1, u}.map
                ((yoneda.{u, u + 1}.map (wide_pullback.π (fun _x : Fin i => f) q)).app
                  (op.{u + 2} T)))
            _)
          (wide_pullback.base fun _x : Fin i =>
            uliftFunctor.{u + 1, u}.map ((yoneda.{u, u + 1}.map f).app (op.{u + 2} T)))
          t
      rw [← this, limits.wide_pullback.lift_base]; rfl
  inv_hom_id' :=
    by
    dsimp [ulift_wide_pullback_iso_hom_aux, ulift_wide_pullback_iso_inv_aux]
    ext ⟨t⟩ : 1
    · simp only [category.assoc, wide_pullback.lift_π, category.id_comp]
      ext x; dsimp; simp
    · simp only [category.assoc, wide_pullback.lift_base, category.id_comp]
      ext x; dsimp; simp

end CategoryTheory

