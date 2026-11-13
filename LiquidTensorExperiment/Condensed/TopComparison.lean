import Mathlib.CategoryTheory.Yoneda
import LiquidTensorExperiment.Condensed.Basic
import LiquidTensorExperiment.Condensed.IsProetaleSheaf
import LiquidTensorExperiment.Condensed.Extr.Equivalence
import Mathlib.Algebra.Category.GroupCat.Adjunctions
import LiquidTensorExperiment.ForMathlib.SheafOfTypesSheafification
import LiquidTensorExperiment.ForMathlib.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits

#align_import condensed.top_comparison

--import algebra.category.Group.filtered_colimits
--import algebra.category.Group.filtered_colimits
--import condensed.ab
--import condensed.ab
universe u

open CategoryTheory

#print Profinite.toCondensed /-
def Profinite.toCondensed (T : Profinite.{u}) : CondensedSet
    where
  val := yoneda'.{u + 1}.obj T
  --⋙ ulift_functor.{u+1},
  cond := by
    rw [is_sheaf_iff_is_sheaf_of_type]
    rw [(functor.is_proetale_sheaf_of_types_tfae (yoneda'.obj T)).out 0 5]
    refine' ⟨_, _, _⟩
    · dsimp [functor.empty_condition]
      constructor
      · rintro _ _ _
        ext ⟨⟩
      · intro x
        refine' ⟨⟨Profinite.empty.elim _⟩, _⟩
        ext
    · intro X Y
      constructor
      · intro x y h
        dsimp at x y h 
        ext (t | t)
        · apply_fun fun e => e.fst.down t at h ; exact h
        · apply_fun fun e => e.snd.down t at h ; exact h
      · rintro ⟨a, b⟩
        refine' ⟨⟨_⟩, _⟩
        dsimp
        refine' Profinite.sum.desc _ _ a.down b.down
        ext; rfl; rfl
    · intro X B π hh
      constructor
      · intro x y h
        dsimp [yoneda, functor.map_to_equalizer] at h 
        ext t
        obtain ⟨t, rfl⟩ := hh t
        apply_fun fun e => e.val.down t at h 
        exact h
      · rintro ⟨⟨t⟩, ht⟩
        refine' ⟨⟨Profinite.descend π t hh _⟩, _⟩
        dsimp at ht 
        apply_fun fun e => e.down at ht 
        exact ht
        dsimp [yoneda, ulift_functor, functor.map_to_equalizer]
        ext : 2
        dsimp
        apply Profinite.π_descend
-/

#print profiniteToCondensed /-
@[simps]
def profiniteToCondensed : Profinite ⥤ CondensedSet
    where
  obj X := X.toCondensed
  map X Y f := ⟨whiskerRight (yoneda.map f) _⟩
  map_id' X := by ext1; dsimp; erw [yoneda.map_id, whisker_right_id]; rfl
  map_comp' X Y Z f g := by
    ext1; dsimp
    erw [yoneda.map_comp, whisker_right_comp]
-/

def TopCat.toCondensed (T : TopCat.{u}) : CondensedSet
    where
  val := Profinite.toTopCat.op ⋙ yoneda'.{u + 1}.obj T
  cond := by
    rw [is_sheaf_iff_is_sheaf_of_type]
    rw [(functor.is_proetale_sheaf_of_types_tfae (Profinite.to_Top.op ⋙ yoneda'.obj T)).out 0 5]
    refine' ⟨_, _, _⟩
    · dsimp [functor.empty_condition]
      constructor
      · rintro _ _ _
        ext ⟨⟩
      · intro x
        dsimp
        refine' ⟨⟨⟨fun x => x.elim, by continuity⟩⟩, _⟩
        ext
    · intro X Y
      constructor
      · intro x y h
        dsimp at x y h 
        ext (t | t)
        · apply_fun fun e => e.fst.down t at h ; exact h
        · apply_fun fun e => e.snd.down t at h ; exact h
      · rintro ⟨a, b⟩
        dsimp [ulift_functor] at a b 
        refine' ⟨⟨⟨_, _⟩⟩, _⟩
        · dsimp [Profinite.sum]
          intro t
          exact Sum.recOn t a.down b.down
        · dsimp
          simp only [continuous_sup_dom, continuous_coinduced_dom]
          exact ⟨a.down.continuous, b.down.continuous⟩
        · ext; rfl; rfl
    · intro X B π hh
      constructor
      · intro x y h
        dsimp [yoneda, functor.map_to_equalizer] at h 
        ext t
        obtain ⟨t, rfl⟩ := hh t
        apply_fun fun e => e.val.down t at h 
        exact h
      · rintro ⟨⟨t⟩, ht⟩
        refine' ⟨⟨Profinite.descendToTop π t hh _⟩, _⟩
        dsimp at ht 
        apply_fun fun e => e.down at ht 
        exact ht
        dsimp [yoneda, ulift_functor, functor.map_to_equalizer]
        ext : 2
        dsimp
        apply Profinite.π_descendToTop

@[simps]
def topToCondensed : TopCat ⥤ CondensedSet
    where
  obj X := X.toCondensed
  map X Y f := ⟨whiskerLeft _ <| whiskerRight (yoneda.map f) _⟩
  map_id' := by
    intro X
    ext1
    dsimp
    erw [yoneda.map_id, whisker_right_id, whisker_left_id]
    rfl
  map_comp' := by
    intro X Y Z f g
    ext1
    dsimp
    erw [yoneda.map_comp, whisker_right_comp, whisker_left_comp]

open Opposite

@[simps]
def Condensed.evaluation (C : Type _) [Category C] (S : Profinite) : Condensed C ⥤ C :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op S)

noncomputable instance {C : Type _} [Category C] [Limits.HasLimits C] (S : Profinite.{u}) :
    Limits.PreservesLimits (Condensed.evaluation C S) :=
  by
  apply (config := { instances := false }) limits.comp_preserves_limits
  swap; infer_instance
  have e : creates_limits (Sheaf_to_presheaf proetaleTopology.{u} C) :=
    Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u + 2, u, u + 1}
  apply (config := { instances := false }) CategoryTheory.preservesLimitsOfCreatesLimitsAndHasLimits
  exact e
  infer_instance

@[simps]
def CondensedSet.evaluation (S : Profinite) : CondensedSet.{u} ⥤ Type (u + 1) :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op S)

noncomputable instance (S : Profinite.{u}) : Limits.PreservesLimits (CondensedSet.evaluation S) :=
  by
  apply (config := { instances := false }) limits.comp_preserves_limits
  swap; infer_instance
  have e : creates_limits (Sheaf_to_presheaf proetaleTopology.{u} (Type (u + 1))) :=
    Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u + 2, u, u + 1}
  apply (config := { instances := false }) CategoryTheory.preservesLimitsOfCreatesLimitsAndHasLimits
  exact e
  infer_instance

universe w

open CategoryTheory.Limits

variable (C : Type w) [Category.{u + 1} C]

noncomputable instance preservesColimitsCondensedEvaluation (S : ExtrDisc.{u}) (C : Type w)
    [Category.{u + 1} C] [HasLimits C] [HasColimits C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] : Limits.PreservesColimits (Condensed.evaluation C S.val) :=
  by
  change
    preserves_colimits
      (((Sheaf_to_presheaf _ _ : Condensed C ⥤ _) ⋙
          (whiskering_left _ _ _).obj ExtrDisc_to_Profinite.op) ⋙
        (evaluation _ _).obj (op S))
  apply (config := { instances := false }) limits.comp_preserves_colimits
  apply CategoryTheory.preservesColimitsOfCreatesColimitsAndHasColimits
  infer_instance

noncomputable instance preservesColimitsCondensedEvaluation' (S : Profinite.{u}) [Projective S]
    (C : Type w) [Category.{u + 1} C] [HasLimits C] [HasColimits C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] : Limits.PreservesColimits (Condensed.evaluation C S) :=
  preservesColimitsCondensedEvaluation ⟨S⟩ _

-- This can be generalized to categories other than `Ab`, but lean is having a really hard time
-- figuring out all the necessary typeclasses and universe parameters, so I gave up and just used
-- `Ab`.
noncomputable instance preservesFiniteBiproductsCondensedEvaluation (S : Profinite.{u}) :
    Limits.PreservesFiniteBiproducts
      (Condensed.evaluation Ab.{u + 1} S : Condensed.{u} Ab.{u + 1} ⥤ Ab.{u + 1}) :=
  by
  constructor; intro J _
  apply preserves_biproducts_of_shape_of_preserves_products_of_shape

-- TODO: Move this
instance : HasFiniteBiproducts Ab :=
  HasFiniteBiproducts.of_hasFiniteProducts

-- It looks like this was not needed for `Module A`, even though it was needed for `Ab`.
-- We're missing an instance for `Ab` in mathlib.
--instance (A : Type u) [comm_ring A] : has_finite_biproducts (Module.{u} A) :=
--has_finite_biproducts.of_has_finite_products
-- sanity check
noncomputable example (S : ExtrDisc.{u}) :
    Limits.PreservesColimits (Condensed.evaluation Ab.{u + 1} S.val) :=
  preservesColimitsCondensedEvaluation _ _

noncomputable example (S : Profinite.{u}) [Projective S] :
    Limits.PreservesColimits (Condensed.evaluation Ab.{u + 1} S) :=
  preservesColimitsCondensedEvaluation' _ _

noncomputable example (A : Type (u + 1)) [CommRing A] (S : ExtrDisc.{u}) :
    Limits.PreservesColimits (Condensed.evaluation (ModuleCat.{u + 1} A) S.val) :=
  preservesColimitsCondensedEvaluation _ _

noncomputable example (A : Type (u + 1)) [CommRing A] (S : Profinite.{u}) [Projective S] :
    Limits.PreservesColimits (Condensed.evaluation (ModuleCat.{u + 1} A) S) :=
  preservesColimitsCondensedEvaluation' _ _

