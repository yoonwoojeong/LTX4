import LiquidTensorExperiment.RealMeasures.Basic
import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.Condensed.Condensify

#align_import real_measures.condensed

open scoped NNReal

open Opposite CategoryTheory

universe u

noncomputable section

variable (p' : ℝ≥0) [Fact (0 < p')] [Fact (p' ≤ 1)]

def RealMeasures.condensed : Profinite.{u} ⥤ Condensed.{u} Ab.{u + 1} :=
  condensify (RealMeasures.functor p')

