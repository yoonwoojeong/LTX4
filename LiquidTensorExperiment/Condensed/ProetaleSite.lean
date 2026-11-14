/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective
import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.Algebra.Category.GroupCat.Biproducts
import Mathlib.Algebra.Category.GroupCat.Colimits
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.GroupCat.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Category.GroupCat.Images
import Mathlib.Algebra.Category.GroupCat.Injective
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Algebra.Category.GroupCat.Preadditive
import Mathlib.Algebra.Category.GroupCat.Subobject
import Mathlib.Algebra.Category.GroupCat.Zero

#align_import condensed.proetale_site

/-!
# Proetale site of a point on Profinite

Defines the proetale site of a point on the category of Profinite sets.
-/


open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

-- This section is in the process of being generalised for mathlib, PR #7436.
section ToGeneralise

/-- A terminal Profinite type, which has the important property that morphisms to `X` are the same
thing as elements of `X`. -/
def point : Profinite.{u} :=
  Profinite.of PUnit

/-- There is a (natural) bijection between morphisms `* ⟶ X` and elements of `X`.  -/
def fromPoint {X : Profinite.{u}} : (point ⟶ X) ≃ X
    where
  toFun f := f PUnit.unit
  invFun x := ⟨fun _ => x⟩
  left_inv x := by ext ⟨⟩; rfl
  right_inv x := rfl

theorem fromPoint_apply {X Y : Profinite} (f : point ⟶ X) (g : X ⟶ Y) :
    g (fromPoint f) = fromPoint (f ≫ g) :=
  rfl

noncomputable def mkPullback {X Y Z : Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
    (h : f x = g y) : (pullback f g : Profinite) :=
  fromPoint (pullback.lift (fromPoint.symm x) (fromPoint.symm y) (by ext ⟨⟩; exact h))

theorem mkPullback_fst {X Y Z : Profinite} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y} {h : f x = g y} :
    (pullback.fst : pullback f g ⟶ _) (mkPullback h) = x :=
  by
  rw [mkPullback, fromPoint_apply]
  simp

theorem mkPullback_snd {X Y Z : Profinite.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {x : X} {y : Y}
    {h : f x = g y} : (pullback.snd : pullback f g ⟶ _) (mkPullback h) = y :=
  by
  rw [mkPullback, fromPoint_apply]
  simp

end ToGeneralise

/-- The proetale pretopology on Profinites. -/
def proetalePretopology : Pretopology.{u} Profinite.{u}
    where
  coverings X S :=
    ∃ (ι : Type u) (_ : Fintype ι) (Y : ι → Profinite) (f : ∀ i : ι, Y i ⟶ X),
      (∀ x : X, ∃ (i : _) (y : Y i), f i y = x) ∧ S = Presieve.ofArrows Y f
  has_isos X Y f i :=
    by
    refine' ⟨PUnit, inferInstance, fun _ => Y, fun _ => f, _, _⟩
    · intro x
      refine' ⟨PUnit.unit, inv f x, _⟩
      change (inv f ≫ f) x = x
      rw [CategoryTheory.IsIso.inv_hom_id]
      simp
    · rw [CategoryTheory.Presieve.ofArrows_pUnit]
  pullbacks X Y f S := by
    rintro ⟨ι, hι, Z, g, hg, rfl⟩
    refine' ⟨ι, hι, fun i => pullback (g i) f, fun i => pullback.snd, _, _⟩
    · intro y
      rcases hg (f y) with ⟨i, z, hz⟩
      exact ⟨i, mkPullback hz, mkPullback_snd⟩
    · rw [CategoryTheory.Presieve.ofArrows_pullback]
  Transitive X S Ti := by
    rintro ⟨ι, hι, Z, g, hY, rfl⟩ hTi
    choose j hj W k hk₁ hk₂ using hTi
    skip
    refine' ⟨Σ i : ι, j (g i) (CategoryTheory.Presieve.ofArrows.mk _), inferInstance, fun i => W _ _ i.2, _, _, _⟩
    · intro ij
      exact k _ _ ij.2 ≫ g ij.1
    · intro x
      obtain ⟨i, y, rfl⟩ := hY x
      obtain ⟨i', z, rfl⟩ := hk₁ (g i) (CategoryTheory.Presieve.ofArrows.mk _) y
      refine' ⟨⟨i, i'⟩, z, rfl⟩
    · have : Ti = fun Y f H => CategoryTheory.Presieve.ofArrows (W f H) (k f H) :=
        by
        ext Y f H : 3
        apply hk₂
      rw [this]
      apply CategoryTheory.Presieve.ofArrows_bind

def proetaleTopology : GrothendieckTopology.{u} Profinite.{u} :=
  proetalePretopology.toGrothendieck _

-- TODO (BM): We either want to generalise this topology to coherent? categories, or (less
-- generally) appropriate concrete categories; or (even less generally) repeat the construction for
-- ED and CH.
