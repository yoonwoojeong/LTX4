import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

#align_import for_mathlib.pullbacks

namespace CategoryTheory

open CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D] (e : C ≌ D) {X Y B : D} (f : X ⟶ B) (g : Y ⟶ B)
  [HasPullback (e.inverse.map f) (e.inverse.map g)]

theorem Equivalence.hom_eq_map {X Y : C} (f : e.Functor.obj X ⟶ e.Functor.obj Y) (g : X ⟶ Y) :
    e.inverse.map f = e.symm.counit.app _ ≫ g ≫ e.Unit.app _ → f = e.Functor.map g :=
  by
  intro h
  change _ = (e.unit_iso.app _).inv ≫ g ≫ (e.unit_iso.app _).hom at h 
  rw [iso.eq_inv_comp] at h 
  replace h := h.symm
  rw [← iso.eq_comp_inv] at h 
  rw [h]
  simp
  nth_rw 1 [← category.id_comp f]
  simp_rw [← category.assoc]
  congr 1
  simp

noncomputable section

/-
I would like to do something for more general shapes, but universes make this difficult
(as usual...)
-/
@[simps]
def Equivalence.pullbackCone : Cone (cospan f g)
    where
  pt := e.Functor.obj <| pullback (e.inverse.map f) (e.inverse.map g)
  π :=
    { app := fun i =>
        match i with
        | none => e.Functor.map pullback.fst ≫ e.counit.app X ≫ f
        | walking_cospan.left => e.Functor.map pullback.fst ≫ e.counit.app X
        | walking_cospan.right => e.Functor.map pullback.snd ≫ e.counit.app Y
      naturality' := by
        rintro (i | i | i) (j | j | j) (h | h)
        · dsimp; simp only [category.id_comp, Functor.map_id]; dsimp; simp only [category.comp_id]
        · dsimp; simp only [category.id_comp]; dsimp [equivalence.pullback_cone._match_1]
          simp only [category.assoc]
        · dsimp; simp only [category.id_comp, Functor.map_id]; dsimp; simp only [category.comp_id]
        · unfold_aux
          dsimp; simp; delta id
          have : e.counit.app X ≫ f = e.functor.map (e.inverse.map f) ≫ e.counit.app B := by tidy
          rw [this]; clear this
          have : e.counit.app Y ≫ g = e.functor.map (e.inverse.map g) ≫ e.counit.app B := by tidy
          rw [this]; clear this
          simp_rw [← category.assoc, ← e.functor.map_comp, limits.pullback.condition]
        · tidy }

attribute [reassoc] equivalence.unit_inverse_comp

-- This is a mess :-(
-- Please fix before moving this file to mathlib!
def Equivalence.isLimitPullbackCone : Limits.IsLimit (e.PullbackCone f g)
    where
  lift S :=
    e.symm.Unit.app S.pt ≫
      e.Functor.map
        (pullback.lift (e.inverse.map (S.π.app WalkingCospan.left))
          (e.inverse.map (S.π.app WalkingCospan.right))
          (by
            simp_rw [← e.inverse.map_comp]
            change
              e.inverse.map (_ ≫ (cospan f g).map walking_cospan.hom.inl) =
                e.inverse.map (_ ≫ (cospan f g).map walking_cospan.hom.inr)
            rw [S.w, S.w]))
  fac := by
    rintro S (j | j | j)
    · dsimp [equivalence.pullback_cone._match_1]
      simp only [category.assoc]
      have : e.counit.app X ≫ f = e.functor.map (e.inverse.map f) ≫ e.counit.app B :=
        by
        dsimp;
        simp only [equivalence.fun_inv_map, category.assoc, iso.inv_hom_id_app,
          nat_iso.cancel_nat_iso_hom_left]
        erw [category.comp_id]
      rw [this]; clear this
      simp_rw [← category.assoc _ _ (e.counit.app B), ← e.functor.map_comp]
      simp only [functor.map_comp, pullback.lift_fst_assoc, equivalence.fun_inv_map, category.assoc,
        iso.inv_hom_id_app_assoc, iso.inv_hom_id_app]
      dsimp
      simp only [category.comp_id]
      change _ ≫ (cospan f g).map walking_cospan.hom.inl = _
      rw [S.w]
    · dsimp [equivalence.pullback_cone._match_1]
      simp only [category.assoc]
      simp_rw [← category.assoc _ _ (e.counit.app X), ← e.functor.map_comp]
      simp only [pullback.lift_fst, equivalence.fun_inv_map, iso.inv_hom_id_app_assoc,
        category.assoc, iso.inv_hom_id_app]
      dsimp
      rw [category.comp_id]
    · dsimp [equivalence.pullback_cone._match_1]
      simp only [category.assoc]
      simp_rw [← category.assoc _ _ (e.counit.app Y), ← e.functor.map_comp]
      simp only [pullback.lift_snd, equivalence.fun_inv_map, iso.inv_hom_id_app_assoc,
        category.assoc, iso.inv_hom_id_app]
      dsimp
      rw [category.comp_id]
  uniq := by
    intro S m h
    --dsimp at *,
    change m = (e.counit_iso.app S.X).inv ≫ _
    rw [iso.eq_inv_comp]
    apply equivalence.hom_eq_map
    change _ = (e.unit_iso.app _).inv ≫ _ ≫ (e.unit_iso.app _).hom
    rw [iso.eq_inv_comp]
    symm
    rw [← iso.eq_comp_inv]
    simp only [category.assoc]
    apply pullback.hom_ext
    · simp only [functor.map_comp, pullback.lift_fst, iso.app_hom, iso.app_inv, category.assoc]
      specialize h walking_cospan.left
      rw [← h]
      simp only [functor.map_comp, equivalence.inv_fun_map, category.assoc,
        equivalence.unit_inverse_comp_assoc, category.comp_id, equivalence.pullback_cone,
        equivalence.pullback_cone_π_app, functor.map_comp, equivalence.unit_inverse_comp]
    · simp only [functor.map_comp, pullback.lift_snd, iso.app_hom, iso.app_inv, category.assoc]
      specialize h walking_cospan.right
      rw [← h]
      simp only [functor.map_comp, equivalence.inv_fun_map, category.assoc,
        equivalence.unit_inverse_comp_assoc, category.comp_id, equivalence.pullback_cone,
        equivalence.pullback_cone_π_app, functor.map_comp, equivalence.unit_inverse_comp]

theorem Equivalence.hasPullback {X Y B : D} (f : X ⟶ B) (g : Y ⟶ B)
    [HasPullback (e.inverse.map f) (e.inverse.map g)] : HasPullback f g :=
  Limits.HasLimit.mk ⟨e.PullbackCone _ _, e.isLimitPullbackCone _ _⟩

theorem Equivalence.hasPullbacks [HasPullbacks C] : HasPullbacks D :=
  by
  apply has_pullbacks_of_has_limit_cospan _
  intro X Y B f g
  apply e.has_pullback

end CategoryTheory

