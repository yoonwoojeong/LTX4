import LiquidTensorExperiment.PseudoNormedGroup.SystemOfComplexes
import LiquidTensorExperiment.Lbar.PseudoNormedGroup
import LiquidTensorExperiment.BreenDeligne.Homotopy

#align_import statement

open scoped NNReal

open CategoryTheory ProFiltPseuNormGrpWithTinv Opposite

-- Porting note: Lean 3 `include r r' BD κ` made `first_target_stmt` take *all* section variables
-- below, including the instance arguments `[Fact (r < r')]` and `[∀ i, Fact (0 < κ i)]` that its
-- body does not use. Lean 4 only includes the variables that are used, which would drop these two
-- hypotheses; so the binders are written on the definition, in the Lean 3 order.
@[nolint unusedArguments]
def FirstTargetStmt (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' < 1)]
    (BD : BreenDeligne.Package) (κ : ℕ → ℝ≥0) [BD.data.VerySuitable r r' κ]
    [∀ i : ℕ, Fact (0 < κ i)] : Prop :=
  ∀ m : ℕ,
    ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)),
      ∃ c₀ : ℝ≥0,
        ∀ (S : Type) [Fintype S],
          ∀ (V : SemiNormedGroupCat.{0}) [NormedWithAut r V],
            ((BD.data.system κ r V r').obj (op <| of r' (Lbar r' S))).IsWeakBoundedExact k K m c₀

