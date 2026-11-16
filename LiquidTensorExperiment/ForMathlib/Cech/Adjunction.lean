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

-- Porting note: Lean 3 LTE called this `simplicial_object.hom_ext`. mathlib4 has since added
-- `CategoryTheory.SimplicialObject.hom_ext` with a different statement (ext for morphisms of
-- simplicial objects), so LTE's lemma is renamed to `hom_ext_augmentedCechNerve`.
theorem hom_ext_augmentedCechNerve (X : SimplicialObject.Augmented C) (F : Arrow C) (f g : X ⟶ F.augmentedCechNerve)
    (hl : f.left.app (op [0]) = g.left.app (op [0])) (hr : f.right = g.right) : f = g :=
  by
  apply (CategoryTheory.SimplicialObject.cechNerveEquiv X F).symm.injective
  dsimp only [CategoryTheory.SimplicialObject.cechNerveEquiv_symm_apply]
  ext1
  · simp only [equivalenceRightToLeft_left]
    rw [hl]
  · exact hr

-- move this
@[simps]
def augmentedCechNerve.leftObjZeroIso (F : Arrow C) :
    F.augmentedCechNerve.left.obj (op [0]) ≅ F.left
    where
  hom := π _ 0
  inv := lift F.hom (fun _ => 𝟙 _) fun _ => Category.id_comp _
  hom_inv_id := by
    -- Porting note: `ext` is not recursive in Lean 4
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, lift_π, Category.id_comp, Category.comp_id]
      congr 2
      dsimp at j ⊢
      -- Porting note: `Fin (0 + 1)` is not syntactically `Fin 1`
      exact Subsingleton.elim (α := Fin 1) _ _
    · simp only [π_arrow, Category.id_comp, Limits.WidePullback.lift_base, Category.assoc]
  inv_hom_id := lift_π _ _ _ _ _

-- move this
theorem augmentedCechNerve.left_map_comp_obj_zero_iso (F : Arrow C) (n : SimplexCategory)
    (i : Fin (n.len + 1)) :
    F.augmentedCechNerve.left.map (n.const i).op ≫ (augmentedCechNerve.leftObjZeroIso F).hom =
      -- Porting note: explicit arrows needed so that the `HasWidePullback` instance is found
      WidePullback.π (B := F.right) (objs := fun _ : Fin (n.len + 1) => F.left) (fun _ => F.hom) i :=
  by
  rw [← CategoryTheory.Iso.eq_comp_inv]
  dsimp only [Arrow.augmentedCechNerve_left, Arrow.cechNerve_map,
    augmentedCechNerve.leftObjZeroIso_inv]
  -- Porting note: `ext1` replaced by the explicit extensionality lemma
  apply WidePullback.hom_ext
  · intro j
    rw [Limits.WidePullback.lift_π, Category.assoc, Limits.WidePullback.lift_π, Category.comp_id]
    cases i
    rfl
  · rw [Limits.WidePullback.lift_base, Category.assoc, Limits.WidePullback.lift_base,
      Limits.WidePullback.π_arrow]
    -- Porting note: `rw` no longer closes the goal by `rfl` here
    rfl

@[simp]
theorem equivalenceLeftToRight_left_app_zero_comp_π (X : SimplicialObject.Augmented C) (F : Arrow C)
    (G : Augmented.toArrow.obj X ⟶ F) (i) :
    (equivalenceLeftToRight X F G).left.app (op [0]) ≫ Limits.WidePullback.π _ i = G.left :=
  by
  dsimp only [CategoryTheory.SimplicialObject.equivalenceLeftToRight_left_app, unop_op]
  rw [Limits.WidePullback.lift_π, SimplexCategory.hom_zero_zero ([0].const i), op_id,
    X.left.map_id, Category.id_comp]

end

end SimplicialObject

end CategoryTheory

