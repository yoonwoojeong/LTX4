import LiquidTensorExperiment.ChallengeNotations
import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.LaurentMeasures.Ses2
import LiquidTensorExperiment.LaurentMeasures.Ext

#align_import challenge_prerequisites

noncomputable section

open scoped LiquidTensorExperiment NNReal ZeroObject

open LiquidTensorExperiment CategoryTheory CategoryTheory.Limits

variable (p' p : ℝ≥0) [Fact (0 < p')] [Fact (0 < (p : ℝ))]

variable [Fact (p' < p)] [Fact (p' ≤ 1)] [Fact (p ≤ 1)]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

-- move me
instance : Fact (@r p < 1) := by
  constructor; delta r
  apply Real.rpow_lt_one
  · norm_num
  · norm_num
  · exact Fact.out _

