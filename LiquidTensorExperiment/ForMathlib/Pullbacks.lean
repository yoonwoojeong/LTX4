import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

#align_import for_mathlib.pullbacks

namespace CategoryTheory

open CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D] (e : C ≌ D) {X Y B : D} (f : X ⟶ B) (g : Y ⟶ B)
  [HasPullback (e.inverse.map f) (e.inverse.map g)]

theorem Equivalence.hom_eq_map {X Y : C} (f : e.functor.obj X ⟶ e.functor.obj Y) (g : X ⟶ Y) :
    e.inverse.map f = e.symm.counit.app _ ≫ g ≫ e.unit.app _ → f = e.functor.map g :=
  by
  intro h
  change _ = (e.unitIso.app _).inv ≫ g ≫ (e.unitIso.app _).hom at h 
  rw [CategoryTheory.Iso.eq_inv_comp] at h 
  replace h := h.symm
  rw [← CategoryTheory.Iso.eq_comp_inv] at h 
  rw [h]
  simp
  nth_rw 1 [← CategoryTheory.Category.id_comp f]
  simp_rw [← CategoryTheory.Category.assoc]
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
        | WalkingCospan.left => e.Functor.map pullback.fst ≫ e.counit.app X
        | WalkingCospan.right => e.Functor.map pullback.snd ≫ e.counit.app Y
      naturality := by
        rintro (i | i | i) (j | j | j) (h | h)
        · dsimp; simp only [Category.id_comp, Functor.map_id]; dsimp; simp only [Category.comp_id]
        · dsimp; simp only [Category.id_comp]; dsimp [equivalence.pullbackCone._match_1]
          simp only [Category.assoc]
        · dsimp; simp only [Category.id_comp, Functor.map_id]; dsimp; simp only [Category.comp_id]
        · unfold_aux
          dsimp; simp; delta id
          have : e.counit.app X ≫ f = e.functor.map (e.inverse.map f) ≫ e.counit.app B := by tidy
          rw [this]; clear this
          have : e.counit.app Y ≫ g = e.functor.map (e.inverse.map g) ≫ e.counit.app B := by tidy
          rw [this]; clear this
          simp_rw [← Category.assoc, ← e.functor.map_comp, Limits.pullback.condition]
        · tidy }

attribute [reassoc] CategoryTheory.Equivalence.unit_inverse_comp

-- This is a mess :-(
-- Please fix before moving this file to mathlib!
def Equivalence.isLimitPullbackCone : Limits.IsLimit (e.pullbackCone f g)
    where
  lift S :=
    e.symm.unit.app S.pt ≫
      e.functor.map
        (pullback.lift (e.inverse.map (S.π.app WalkingCospan.left))
          (e.inverse.map (S.π.app WalkingCospan.right))
          (by
            simp_rw [← e.inverse.map_comp]
            change
              e.inverse.map (_ ≫ (cospan f g).map WalkingCospan.Hom.inl) =
                e.inverse.map (_ ≫ (cospan f g).map WalkingCospan.Hom.inr)
            rw [S.w, S.w]))
  fac := by
    rintro S (j | j | j)
    · dsimp [equivalence.pullbackCone._match_1]
      simp only [Category.assoc]
      have : e.counit.app X ≫ f = e.functor.map (e.inverse.map f) ≫ e.counit.app B :=
        by
        dsimp;
        simp only [Equivalence.fun_inv_map, Category.assoc, Iso.inv_hom_id_app,
          NatIso.cancel_natIso_hom_left]
        erw [Category.comp_id]
      rw [this]; clear this
      simp_rw [← Category.assoc _ _ (e.counit.app B), ← e.functor.map_comp]
      simp only [Functor.map_comp, pullback.lift_fst_assoc, Equivalence.fun_inv_map, Category.assoc,
        Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
      dsimp
      simp only [Category.comp_id]
      change _ ≫ (cospan f g).map WalkingCospan.Hom.inl = _
      rw [S.w]
    · dsimp [equivalence.pullbackCone._match_1]
      simp only [Category.assoc]
      simp_rw [← Category.assoc _ _ (e.counit.app X), ← e.functor.map_comp]
      simp only [pullback.lift_fst, Equivalence.fun_inv_map, Iso.inv_hom_id_app_assoc,
        Category.assoc, Iso.inv_hom_id_app]
      dsimp
      rw [Category.comp_id]
    · dsimp [equivalence.pullbackCone._match_1]
      simp only [Category.assoc]
      simp_rw [← Category.assoc _ _ (e.counit.app Y), ← e.functor.map_comp]
      simp only [pullback.lift_snd, Equivalence.fun_inv_map, Iso.inv_hom_id_app_assoc,
        Category.assoc, Iso.inv_hom_id_app]
      dsimp
      rw [Category.comp_id]
  uniq := by
    intro S m h
    --dsimp at *,
    change m = (e.counitIso.app S.X).inv ≫ _
    rw [CategoryTheory.Iso.eq_inv_comp]
    apply Equivalence.hom_eq_map
    change _ = (e.unitIso.app _).inv ≫ _ ≫ (e.unitIso.app _).hom
    rw [Iso.eq_inv_comp]
    symm
    rw [← Iso.eq_comp_inv]
    simp only [Category.assoc]
    apply pullback.hom_ext
    · simp only [Functor.map_comp, pullback.lift_fst, Iso.app_hom, Iso.app_inv, Category.assoc]
      specialize h WalkingCospan.left
      rw [← h]
      simp only [Functor.map_comp, Equivalence.inv_fun_map, Category.assoc,
        Equivalence.unit_inverse_comp_assoc, Category.comp_id, Equivalence.pullbackCone,
        Equivalence.pullbackCone_π_app, Functor.map_comp, Equivalence.unit_inverse_comp]
    · simp only [Functor.map_comp, pullback.lift_snd, Iso.app_hom, Iso.app_inv, Category.assoc]
      specialize h WalkingCospan.right
      rw [← h]
      simp only [Functor.map_comp, Equivalence.inv_fun_map, Category.assoc,
        Equivalence.unit_inverse_comp_assoc, Category.comp_id, Equivalence.pullbackCone,
        Equivalence.pullbackCone_π_app, Functor.map_comp, Equivalence.unit_inverse_comp]

theorem Equivalence.hasPullback {X Y B : D} (f : X ⟶ B) (g : Y ⟶ B)
    [HasPullback (e.inverse.map f) (e.inverse.map g)] : HasPullback f g :=
  Limits.HasLimit.mk ⟨e.pullbackCone _ _, e.isLimitPullbackCone _ _⟩

theorem Equivalence.hasPullbacks [HasPullbacks C] : HasPullbacks D :=
  by
  apply CategoryTheory.Limits.hasPullbacks_of_hasLimit_cospan _
  intro X Y B f g
  apply e.hasPullback

end CategoryTheory

