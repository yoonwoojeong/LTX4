import LiquidTensorExperiment.PseudoNormedGroup.SystemOfComplexes
import LiquidTensorExperiment.Lbar.PseudoNormedGroup
import LiquidTensorExperiment.BreenDeligne.Homotopy

#align_import statement

open scoped NNReal

open CategoryTheory ProFiltPseuNormGrpWithTinv Opposite

variable (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' < 1)]

variable (BD : BreenDeligne.Package) (κ : ℕ → ℝ≥0)

variable [BD.data.VerySuitable r r' κ] [∀ i : ℕ, Fact (0 < κ i)]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr​ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation -/
@[nolint unused_arguments]
def FirstTargetStmt : Prop :=
  ∀ m : ℕ,
    ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)),
      ∃ c₀ : ℝ≥0,
        ∀ (S : Type) [Fintype S],
          ∀ (V : SemiNormedGroupCat.{0}) [NormedWithAut r V],
            «expr​ »
              "./././Mathport/Syntax/Translate/Expr.lean:394:14: unsupported user notation exact_notation"

