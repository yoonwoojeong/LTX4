import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Topology.Category.Profinite.Projective
import LiquidTensorExperiment.ForMathlib.Presieve
import LiquidTensorExperiment.ForMathlib.Profinite.DisjointUnion
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Main
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitLimits
import LiquidTensorExperiment.Condensed.ProetaleSite
import LiquidTensorExperiment.Condensed.IsProetaleSheaf

#align_import condensed.basic

/-!
# Condensed sets

Defines the category of condensed sets and condensed structures.
*Strictly speaking* these are pyknotic, but we hope that in the context of Lean's type theory they
serve the same purpose.

-/


open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C]

#print CondensedSet /-
/-- The category of condensed sets. -/
def CondensedSet : Type (u + 2) :=
  Sheaf proetaleTopology.{u} (Type (u + 1))
deriving Category
-/

#print Condensed /-
/-- The category of condensed `A`. Applying this to `A = Type*` is *equivalent* but not the same
as `CondensedSet`. -/
def Condensed (C : Type u) [Category.{v} C] :=
  Sheaf proetaleTopology.{w} C
deriving Category
-/

example : Category.{u + 1} (Condensed.{u} Ab.{u + 1}) :=
  inferInstance

example : Category.{u + 37} (Condensed.{u} RingCat.{u + 37}) :=
  inferInstance

open Opposite

noncomputable section

variable (X : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))

variable (P : Profinite.{w}ᵒᵖ ⥤ Type u)

theorem maps_comm {S S' : Profinite.{u}} (f : S' ⟶ S) :
    X.map f.op ≫ X.map (pullback.fst : pullback f f ⟶ S').op = X.map f.op ≫ X.map pullback.snd.op :=
  by rw [← X.map_comp, ← op_comp, pullback.condition, op_comp, X.map_comp]

def naturalFork {S S' : Profinite.{u}} (f : S' ⟶ S) :
    Fork (X.map pullback.fst.op) (X.map pullback.snd.op) :=
  Fork.ofι (X.map (Quiver.Hom.op f)) (maps_comm X f)

section

/-
There are several files where the instances below are needed, but are not found automatically
because the universe parameters involve things like `max v w` where `v = u+1` and `w = u`.
So we just add them manually here.
-/
instance : HasLimits CondensedSet.{u} :=
  Sheaf.CategoryTheory.Limits.hasLimits.{u + 2, u, u + 1}

instance : HasColimits CondensedSet.{u} :=
  Sheaf.CategoryTheory.Limits.hasColimits.{u + 2, u, u + 1}

instance (C : Type (u + 2)) [Category.{u + 1} C] [HasLimits C] : HasLimits (Condensed.{u} C) :=
  Sheaf.CategoryTheory.Limits.hasLimits.{u + 2, u, u + 1}

instance (C : Type (u + 2)) [Category.{u + 1} C] [ConcreteCategory.{u + 1} C]
    [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)] [HasColimits C]
    [∀ X : Profinite.{u}, PreservesColimitsOfShape (proetaleTopology.cover X)ᵒᵖ (forget C)]
    [∀ (P : Profiniteᵒᵖ ⥤ C) (X : Profinite) (S : proetaleTopology.cover X),
        HasMultiequalizer (S.index P)] :
    HasColimits (Condensed.{u} C) :=
  Sheaf.CategoryTheory.Limits.hasColimits.{u + 2, u, u + 1}

instance (X : Profinite) : IsFiltered (proetaleTopology.cover X)ᵒᵖ := by infer_instance

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

instance condensed_ab_hasColimits : HasColimits (Condensed.{u} Ab.{u + 1}) :=
  Sheaf.CategoryTheory.Limits.hasColimits.{u + 2, u, u + 1}

instance condensed_ab_hasLimits : HasLimits (Condensed.{u} Ab.{u + 1}) :=
  Sheaf.CategoryTheory.Limits.hasLimits.{u + 2, u, u + 1}

instance : Abelian (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  CategoryTheory.functorCategoryIsAbelian.{u + 2, u, u + 1}

instance : Abelian (Condensed Ab.{u + 1}) :=
  @CategoryTheory.Sheaf.abelian.{u + 2, u, u + 1} Profinite.{u} _ proetaleTopology Ab.{u + 1} _ _ _
    _ _ _ _ _

end

/-
-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_terminal
  (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := by admit

-- TODO (BM): put this in mathlib (it's already in a mathlib branch with API)
def category_theory.functor.preserves_binary_products
  (X : Profinite.{u}ᵒᵖ ⥤ Type (u+1)) : Prop := by admit

structure condensed_type_condition : Prop :=
(empty : nonempty X.preserves_terminal)
(bin_prod : nonempty X.preserves_binary_products)
(pullbacks : ∀ {S S' : Profinite.{u}} (f : S' ⟶ S) [epi f],
  nonempty (is_limit (natural_fork X f)))

-- (BM): I'm 90% sure this is true as stated, the forward direction is about halfway done.
lemma sheaf_condition_iff :
  presieve.is_sheaf proetale_topology X ↔ condensed_type_condition X :=
by admit
-/
-- See `Top_to_Condensed` in `condensed/top_comparison.lean`.
/-
-- TODO: Double check this definition...
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T ⋙ ulift_functor.{u+1}, by admit⟩,
  map := λ T₁ T₂ f, ⟨whisker_left _ $ whisker_right (yoneda.map f) _⟩ }
-/
/-
-- TODO: State `sheaf_condition_iff` for presheaves taking values in `A` for `A` with appropriate
-- structure.
-- TODO: Use `sheaf_condition_iff` to define the functor of Example 1.5, it might look like this:
def embed_Top : Top.{u} ⥤ CondensedSet.{u} :=
{ obj := λ T, ⟨Profinite.to_Top.op ⋙ yoneda.obj T,
  begin
    rw sheaf_condition_iff, refine ⟨⟨_⟩, ⟨_⟩, _⟩,
    all_goals { admit }
  end⟩,
  map := λ T₁ T₂ f, whisker_left Profinite.to_Top.op (yoneda.map f) }
-/
-- TODO: Use the above to prove the first part of Proposition 1.7:
-- lemma embed_Top_faithful : faithful embed_Top := by admit
-- TODO: Construct the left adjoint to `embed_Top` as in the second part of Proposition 1.7.
