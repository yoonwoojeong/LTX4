import LiquidTensorExperiment.Thm95.Default
import LiquidTensorExperiment.Statement

#align_import liquid

/-!
# Liquid Tensor Experiment

This file is the entry point for this project.
The first goal of the Liquid Tensor Experiment
is to formalize a theorem by Clausen and Scholze stated below,
namely a mix of Theorem 9.4 and Theorem 9.5 of
[Analytic]: http://www.math.uni-bonn.de/people/scholze/Analytic.pdf

**How to browse this project? See `README.md` in the root of the repository.**

We will now state the main theorem.

First we need to fix a package of data corresponding to the Breen--Deligne resolution.
If you don't know the Breen--Deligne resolution, don't worry,
we'll explain more about how to find out more about it below.
Once we have fixed this data, we can state the theorem.
-/


universe u

open scoped NNReal

-- enable the notation `ℝ≥0` for the nonnegative real numbers.
open CategoryTheory ProFiltPseuNormGrpWithTinv PolyhedralLattice Opposite

variable (r r' : ℝ≥0)

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' < 1)]

variable (BD : BreenDeligne.Package) (κ : ℕ → ℝ≥0)

variable [BD.data.VerySuitable r r' κ] [∀ i : ℕ, Fact (0 < κ i)]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr​ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation -/
/-- A mix of Theorems 9.4 and 9.5 in [Analytic] -/
theorem first_target :
    ∀ m : ℕ,
      ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)) (c₀ : ℝ≥0),
        ∀ (S : Type) [Fintype S] (V : SemiNormedGroupCat.{u}) [NormedWithAut r V],
          «expr​ »
            "./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation" :=
  by
  intro m
  obtain ⟨k, K, hk, H⟩ := thm95'' BD r r' κ m
  obtain ⟨c₀, H⟩ := H ℤ
  use k, K, hk, c₀
  intro S hS V hV
  specialize H S V
  let i := (BD.data.system κ r V r').mapIso (HomZ_iso (of r' <| Lbar r' S)).op
  refine' H.of_iso i.symm _
  intro c n
  rw [← SystemOfComplexes.apply_hom_eq_hom_apply]
  apply SemiNormedGroupCat.iso_isometry_of_normNoninc <;>
    apply BreenDeligne.Data.complex.map_normNoninc

/-!
## On the statement

Most of the theorem should be fairly readable.
We will now briefly explain some of the more peculiar syntax.
The proof reduces to `thm95''` (a variant of Theorem 9.5).

* `[BD.suitable κ]` assumes that the nonnegative reals `κ i` satisfy some suitable conditions
  with respect to the package of Breen--Deligne data `BD`.
* `[fact (0 < r)]` records the "fact" `0 < r` as an assumption to whatever comes later.
* `(S : Type) [fintype S]` is Lean's way of saying "`S` is a finite set".
  See also the "Brief note on type theory" in `README.md`.
* `[normed_with_aut r V]` adds the assumption that `V` is endowed with an automorphism `T`
  that scales elements `v` of `V` by the positive scalar `r`: `∥T(v)∥ = r * ∥v∥`.
* `Lbar_system` is the system of complexes of seminormed groups
  occuring in Theorems 9.4/9.5 of [Analytic].
* `is_bounded_exact` is the assertion that a system of complexes
  of seminormed groups satisfies a suitable exactness criterion of being
  `≤ k`-exact in degrees `≤ m` for `c ≥ c₀` (where `c` is an index to the system of complexes).
-/


example : FirstTargetStmt r r' BD κ :=
  first_target r r' BD κ

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr​ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation -/
/-- Theorem 9.4 in [Analytic] for weak bounded exactness -/
theorem thm94_weak :
    ∀ m : ℕ,
      ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)) (c₀ : ℝ≥0),
        ∀ (S : Profinite) (V : SemiNormedGroupCat.{u}) [NormedWithAut r V],
          «expr​ »
            "./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation" :=
  by
  intro m
  obtain ⟨k, K, hk, H⟩ := thm95''.profinite BD r r' κ m
  obtain ⟨c₀, H⟩ := H ℤ
  use k, K, hk, c₀
  intro S V hV
  specialize H S V
  let i := (BD.data.system κ r V r').mapIso (HomZ_iso (of r' <| (Lbar.functor.{0, 0} r').obj S)).op
  refine' H.of_iso i.symm _
  intro c n
  rw [← SystemOfComplexes.apply_hom_eq_hom_apply]
  apply SemiNormedGroupCat.iso_isometry_of_normNoninc <;>
    apply BreenDeligne.Data.complex.map_normNoninc

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr​ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation -/
/-- Theorem 9.4 in [Analytic] -/
theorem thm94 :
    ∀ m : ℕ,
      ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)) (c₀ : ℝ≥0),
        ∀ (S : Profinite) (V : SemiNormedGroupCat.{u}) [NormedWithAut r V],
          «expr​ »
            "./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation" :=
  by
  intro m
  obtain ⟨k, K, hk, c₀, H⟩ := thm94_weak r r' BD κ m
  skip
  refine' ⟨k ^ 2, K + 1, inferInstance, c₀, _⟩
  intros
  refine' SystemOfComplexes.IsWeakBoundedExact.strongOfComplete _ (H _ _) _ _ zero_lt_one
  apply BreenDeligne.Data.systemAdmissible

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr​ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation -/
/-- Theorem 9.4 in [Analytic] for weak bounded exactness -/
theorem thm94_weak' :
    ∀ m : ℕ,
      ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)) (c₀ : ℝ≥0),
        ∀ (S : Profinite) (V : SemiNormedGroupCat.{u}) [NormedWithAut r V],
          «expr​ »
            "./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation" :=
  by
  intro m
  obtain ⟨k, K, hk, H⟩ := thm95''.profinite BD r r' κ m
  obtain ⟨c₀, H⟩ := H ℤ
  use k, K, hk, c₀
  intro S V hV
  specialize H S V
  let i := (BD.data.system κ r V r').mapIso (HomZ_iso (of r' <| (Lbar.functor.{0, 0} r').obj S)).op
  refine' H.of_iso i.symm _
  intro c n
  rw [← SystemOfComplexes.apply_hom_eq_hom_apply]
  apply SemiNormedGroupCat.iso_isometry_of_normNoninc <;>
    apply BreenDeligne.Data.complex.map_normNoninc

