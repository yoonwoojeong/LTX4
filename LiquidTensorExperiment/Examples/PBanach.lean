import LiquidTensorExperiment.ChallengeNotations
import LiquidTensorExperiment.ChallengePrerequisites

#align_import examples.pBanach

/-!

This file discusses `p`-Banach spaces and their associated condensed abelian groups.

-/


noncomputable section

open scoped LiquidTensorExperiment NNReal ZeroObject

open LiquidTensorExperiment CategoryTheory CategoryTheory.Limits Opposite

/-! Let `p` be a nonnegative real, `V` a `p`-Banach space, and `S` a profinite set. -/


variable (p : ℝ≥0) (V : PBanachCat.{0} p) (S : Profinite.{0})

section PBanachCat

/-! The `p`-Banach space `V` is a complete and separated topological `ℝ`-vector space. -/


example : TopologicalAddGroup V :=
  inferInstance

example : Module ℝ V :=
  inferInstance

example : ContinuousSMul ℝ V :=
  inferInstance

example : CompleteSpace V :=
  inferInstance

example : SeparatedSpace V :=
  inferInstance

/-- We may *choose* a norm on the `p`-Banach space satisfying some properties
which will be discussed below.

NOTE: This is really a *choice* that must be made, and we make this choice only within
the present section.
-/
def PBanachCat.hasNorm : Norm V :=
  (PBanach.exists_p_norm V.pBanach').some.toHasNorm

/-! We tell the typeclass system to use the norm chosen above. -/


attribute [local instance] PBanachCat.hasNorm

/-! The chosen norm on `V` scales via the rule `∥rv∥ = |r|^p * ∥v∥`. -/


/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
example (r : ℝ) (v : V) : «expr∥ ∥» (r • v) = |r| ^ (p : ℝ) * «expr∥ ∥» v :=
  (PBanach.exists_p_norm V.pBanach').some.norm_smul r v

/-! The chosen norm on `V` satisfies the triangle inequality. -/


/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
example (v w : V) : «expr∥ ∥» (v + w) ≤ «expr∥ ∥» v + «expr∥ ∥» w :=
  (PBanach.exists_p_norm V.pBanach').some.triangle v w

/-! The uniform space structure on `V` is induced by the chosen norm. -/


/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
example :
    uniformity V =
      ⨅ (ε : ℝ) (H : ε > 0), Filter.principal {p : V × V | «expr∥ ∥» (p.1 - p.2) < ε} :=
  (PBanach.exists_p_norm V.pBanach').some.uniformity

end PBanachCat

section Condensed

/-!
When `V` is viewed as condensed abelian group, the sections
over `S` are the continuous maps `S → V`.
For technical reasons related to size issues in topos theory,
we need to lift the space of continuous maps to a higher universe using `ulift.{1}`.
-/


example : (Γ_ S V : Type 1) = ULift.{1} C(S, V) :=
  rfl

/-!
The group operation on `Γ_ S V` is pointwise addition, as expected.
-/


example (f g : Γ_ S V) (s : S) : (f + g) s = f s + g s :=
  rfl

end Condensed

section lp

/-!
An example of a p-Banach space: `ℓ^p(ℕ)`.
-/


example [Fact (0 < p)] [Fact (p ≤ 1)] : PBanachCat p :=
  PBanachCat.lp p

/-!
Elements of `pBanach.lp p` can be considered as functions `ℕ → ℝ`.
-/


example [Fact (0 < p)] [Fact (p ≤ 1)] (f : PBanachCat.lp p) : ℕ → ℝ := fun i => f i

/-!
Given an element of `pBanach.lp p`, the infinite sum `∑' n, | f n |^p` exists.
-/


example [Fact (0 < p)] [Fact (p ≤ 1)] (f : PBanachCat.lp p) : Summable fun n => |f n| ^ (p : ℝ) :=
  PBanachCat.lpType.summable f

/-!
The ℝ-module structure behaves as expected.
-/


example [Fact (0 < p)] [Fact (p ≤ 1)] (f g : PBanachCat.lp p) (n : ℕ) : (f + g) n = f n + g n :=
  rfl

example [Fact (0 < p)] [Fact (p ≤ 1)] (a : ℝ) (f : PBanachCat.lp p) (n : ℕ) : (a • f) n = a * f n :=
  rfl

/-!
Conversely, we can construct elements of `pBanach.lp p` using sequences
where the sum above exists.
-/


example [Fact (0 < p)] [Fact (p ≤ 1)] (f : ℕ → ℝ) (hf : Summable fun n => |f n| ^ (p : ℝ)) :
    PBanachCat.lp p :=
  { val := f
    property := by
      change ite _ _ _
      rw [if_neg]; rw [if_neg]; assumption
      exact ENNReal.coe_ne_top
      exact ne_of_gt <| by exact_mod_cast Fact.out (0 < p) }

/-!
`pBanach.lp p` is nontrivial.
-/


example [Fact (0 < p)] [Fact (p ≤ 1)] : Nontrivial (PBanachCat.lp p) :=
  inferInstance

end lp

