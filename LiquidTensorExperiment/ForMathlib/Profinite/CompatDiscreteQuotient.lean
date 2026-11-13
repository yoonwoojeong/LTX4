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

variable {X Y : Profinite.{u}} (f : X ⟶ Y) (surj : Function.Surjective f)

/-- The relation defining the largest quotient of f.right compatible with S. -/
inductive MakeRel (S : DiscreteQuotient X) : Y → Y → Prop
  | of (x y : X) (h : S.Rel x y) : DiscreteQuotient.MakeRel (f x) (f y)
  | trans {x y z : Y} : DiscreteQuotient.MakeRel x y → DiscreteQuotient.MakeRel y z → DiscreteQuotient.MakeRel x z

theorem makeRelImpl (S : DiscreteQuotient X) (x y : X) : S.Rel x y → S.MakeRel f (f x) (f y) :=
  MakeRel.of _ _

theorem makeRel_equiv (S : DiscreteQuotient X) : Equivalence (S.MakeRel f) :=
  by
  refine' ⟨fun x => _, fun x y h => _, fun x y z h1 h2 => MakeRel.trans h1 h2⟩
  · obtain ⟨x, rfl⟩ := surj x
    exact MakeRel.of _ _ (S.refl _)
  · induction' h with x y h1 x y z h1 h2 h3 h4
    exact MakeRel.of y x (S.symm x y h1)
    exact MakeRel.trans h4 h3

/-- The setoid assoc. to make_rel. -/
def makeSetoid (S : DiscreteQuotient X) : Setoid Y :=
  ⟨S.MakeRel f, S.makeRel_equiv f surj⟩

/-- The quotient of make_rel. -/
@[nolint has_inhabited_instance]
def MakeQuotient (S : DiscreteQuotient X) : Type _ :=
  Quotient (S.makeSetoid f surj)

/-- The projection onto make_rel. -/
def makeProj (S : DiscreteQuotient X) : Y → S.MakeQuotient f surj :=
  Quotient.mk''

theorem makeProj_comm (S : DiscreteQuotient X) :
    S.makeProj f surj ∘ f = (Quotient.map' f <| DiscreteQuotient.makeRelImpl _ _) ∘ S.proj := by ext; rfl

variable (f)

/-- Given a discrete quotient S of f.left, this is the compatible quotient
 of f where f.right is as large as possible. -/
def make (S : DiscreteQuotient X) : DiscreteQuotient Y
    where
  Rel := S.MakeRel f
  Equiv := S.makeRel_equiv f surj
  clopen := by
    intro x
    have : setOf (S.make_rel f x) = S.make_proj f surj ⁻¹' {S.make_proj f surj x} :=
      by
      dsimp [DiscreteQuotient.makeProj]
      ext
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq'', Set.mem_setOf_eq]
      refine' ⟨fun h => Setoid.symm' _ h, fun h => Setoid.symm' _ h⟩
    rw [this]
    letI : TopologicalSpace (S.make_quotient f surj) := ⊥
    haveI : DiscreteTopology (S.make_quotient f surj) := ⟨rfl⟩
    suffices Continuous (S.make_proj f surj) by
      refine' ⟨IsOpen.preimage this trivial, IsClosed.preimage this ⟨trivial⟩⟩
    rw [(Profinite.quotientMap f surj).continuous_iff, S.make_proj_comm f surj]
    exact continuous_bot.comp (proj_continuous S)

theorem makeLeComap (S : DiscreteQuotient X) : LEComap f.continuous S (S.make f surj) :=
  makeRelImpl _ _

theorem make_right_le (S : DiscreteQuotient X) (T : DiscreteQuotient Y)
    (compat : LEComap f.continuous S T) : S.make f surj ≤ T :=
  by
  intro x y h
  induction' h with a b hab a b c _ _ h1 h2
  · exact compat a b hab
  · exact trans T a b c h1 h2

theorem make_right_mono (S1 S2 : DiscreteQuotient X) (h : S1 ≤ S2) :
    S1.make f surj ≤ S2.make f surj := by
  intro x y h
  induction h
  · refine' MakeRel.of _ _ (h _ _ _)
    assumption
  · apply MakeRel.trans
    assumption'

end DiscreteQuotient

