import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective
import Mathlib.CategoryTheory.Arrow
import Mathlib.Data.Setoid.Partition
import LiquidTensorExperiment.ForMathlib.Profinite.QuotientMap

#align_import for_mathlib.Profinite.compat_discrete_quotient

open CategoryTheory

namespace DiscreteQuotient

universe u

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- The relation defining the largest quotient of f.right compatible with S. -/
-- Porting note: `f` is bound explicitly (Lean 4 does not include it as a parameter automatically)
inductive MakeRel (f : X ⟶ Y) (S : DiscreteQuotient X) : Y → Y → Prop
  | of (x y : X) (h : S.Rel x y) : MakeRel f S (f x) (f y)
  | trans {x y z : Y} : MakeRel f S x y → MakeRel f S y z → MakeRel f S x z

theorem makeRelImpl (S : DiscreteQuotient X) (x y : X) : S.Rel x y → S.MakeRel f (f x) (f y) :=
  MakeRel.of _ _

-- Porting note: `include surj` is not available in Lean 4; the hypothesis is now explicit
theorem makeRel_equiv (S : DiscreteQuotient X) (surj : Function.Surjective f) :
    Equivalence (S.MakeRel f) := by
  refine' ⟨fun x => _, fun {x y} h => _, fun {x y z} h1 h2 => MakeRel.trans h1 h2⟩
  · obtain ⟨x, rfl⟩ := surj x
    exact MakeRel.of _ _ (S.refl _)
  · induction h with
    | of x y h1 => exact MakeRel.of y x (S.symm x y h1)
    | trans _ _ h3 h4 => exact MakeRel.trans h4 h3

/-- The setoid assoc. to make_rel. -/
def makeSetoid (S : DiscreteQuotient X) (surj : Function.Surjective f) : Setoid Y :=
  ⟨S.MakeRel f, S.makeRel_equiv f surj⟩

/-- The quotient of make_rel. -/
-- Porting note: removed `@[nolint has_inhabited_instance]` (no such linter in Lean 4)
def MakeQuotient (S : DiscreteQuotient X) (surj : Function.Surjective f) : Type _ :=
  Quotient (S.makeSetoid f surj)

/-- The projection onto make_rel. -/
def makeProj (S : DiscreteQuotient X) (surj : Function.Surjective f) : Y → S.MakeQuotient f surj :=
  Quotient.mk''

theorem makeProj_comm (S : DiscreteQuotient X) (surj : Function.Surjective f) :
    S.makeProj f surj ∘ f = (Quotient.map' f <| by exact makeRelImpl _ _) ∘ S.proj := by
  funext x
  rfl

/-- Given a discrete quotient S of f.left, this is the compatible quotient
 of f where f.right is as large as possible. -/
def make (S : DiscreteQuotient X) (surj : Function.Surjective f) : DiscreteQuotient Y
    where
  toSetoid := S.makeSetoid f surj
  isOpen_setOf_rel := by
    intro x
    have : setOf (S.MakeRel f x) = S.makeProj f surj ⁻¹' {S.makeProj f surj x} := by
      dsimp [DiscreteQuotient.makeProj]
      ext
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq'', Set.mem_setOf_eq]
      exact ⟨fun h => Quotient.sound' ((S.makeRel_equiv f surj).symm h),
        fun h => (S.makeRel_equiv f surj).symm (Quotient.exact' h)⟩
    show IsOpen (setOf (S.MakeRel f x))
    rw [this]
    letI : TopologicalSpace (S.MakeQuotient f surj) := ⊥
    haveI : DiscreteTopology (S.MakeQuotient f surj) := ⟨rfl⟩
    suffices Continuous (S.makeProj f surj) by
      exact IsOpen.preimage this (isOpen_discrete _)
    rw [(Profinite.quotientMap f surj).continuous_iff, S.makeProj_comm f surj]
    refine Continuous.comp ?_ S.proj_continuous
    exact continuous_of_discreteTopology

-- Porting note: the Lean 3 `clopen` field is only `isOpen_setOf_rel` in Lean 4
theorem makeLeComap (S : DiscreteQuotient X) (surj : Function.Surjective f) :
    LEComap f S (S.make f surj) :=
  makeRelImpl _ _

theorem make_right_le (S : DiscreteQuotient X) (surj : Function.Surjective f)
    (T : DiscreteQuotient Y)
    (compat : LEComap f S T) : S.make f surj ≤ T := by
  intro x y h
  induction h with
  | of a b hab => exact compat hab
  | trans _ _ h1 h2 => exact T.trans _ _ _ h1 h2

theorem make_right_mono (S1 S2 : DiscreteQuotient X) (surj : Function.Surjective f)
    (h : S1 ≤ S2) : S1.make f surj ≤ S2.make f surj := by
  intro x y hxy
  induction hxy with
  | of a b hab => exact MakeRel.of _ _ (h hab)
  | trans _ _ h1 h2 => exact MakeRel.trans h1 h2

end DiscreteQuotient
