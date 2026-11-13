import Mathlib.AlgebraicTopology.CechNerve

#align_import for_mathlib.Cech.adjunction

universe v u

noncomputable section

open scoped Simplicial

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

namespace SimplicialObject

variable
  [∀ (n : ℕ) (f : Arrow C),
      HasWidePullback.{0} f.right (fun i : Fin (n + 1) => f.left) fun i => f.hom]

section

open SimplexCategory Opposite Limits.WidePullback

#print CategoryTheory.SimplicialObject.hom_ext /-
theorem hom_ext (X : SimplicialObject.Augmented C) (F : Arrow C) (f g : X ⟶ F.augmentedCechNerve)
    (hl : f.left.app (op [0]) = g.left.app (op [0])) (hr : f.right = g.right) : f = g :=
  by
  apply (cech_nerve_equiv X F).symm.Injective
  dsimp only [cech_nerve_equiv_symm_apply]
  ext1
  · simp only [equivalence_right_to_left_left]
    rw [hl]
  · exact hr
-/

-- move this
@[simps]
def augmentedCechNerve.leftObjZeroIso (F : Arrow C) :
    F.augmentedCechNerve.left.obj (op [0]) ≅ F.left
    where
  hom := π _ 0
  inv := lift F.Hom (fun _ => 𝟙 _) fun _ => Category.id_comp _
  hom_inv_id' := by
    ext
    · rw [category.assoc, lift_π, category.id_comp, category.comp_id]
      congr 2; dsimp at j ⊢; exact Subsingleton.elim _ _
    · simp only [π_arrow, category.id_comp, limits.wide_pullback.lift_base, category.assoc]
  inv_hom_id' := lift_π _ _ _ _ _

-- move this
theorem augmentedCechNerve.left_map_comp_obj_zero_iso (F : Arrow C) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    F.augmentedCechNerve.left.map (n.const i).op ≫ (augmentedCechNerve.leftObjZeroIso F).Hom =
      WidePullback.π _ i :=
  by
  rw [← CategoryTheory.Iso.eq_comp_inv]
  dsimp only [arrow.augmented_cech_nerve_left, arrow.cech_nerve_map,
    augmented_cech_nerve.left_obj_zero_iso_inv]
  ext1 ⟨j⟩
  · rw [limits.wide_pullback.lift_π, category.assoc, limits.wide_pullback.lift_π, category.comp_id]
    cases i; rfl
  ·
    rw [limits.wide_pullback.lift_base, category.assoc, limits.wide_pullback.lift_base,
      limits.wide_pullback.π_arrow]

@[simp]
theorem equivalenceLeftToRight_left_app_zero_comp_π (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : Augmented.toArrow.obj X ⟶ F) (i) :
    (equivalenceLeftToRight X F G).left.app (op [0]) ≫ Limits.WidePullback.π _ i = G.left :=
  by
  dsimp only [equivalence_left_to_right_left_app, unop_op]
  rw [limits.wide_pullback.lift_π, SimplexCategory.hom_zero_zero ([0].const i), op_id,
    X.left.map_id, category.id_comp]

end

end SimplicialObject

end CategoryTheory

