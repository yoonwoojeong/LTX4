import LiquidTensorExperiment.Banach
import LiquidTensorExperiment.RealMeasures.Condensed
import LiquidTensorExperiment.Condensed.ProjectiveResolution
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.Derived.KProjective
import LiquidTensorExperiment.Radon.Png
import LiquidTensorExperiment.PBanach.Lp

#align_import challenge_notations

open scoped NNReal

open Opposite CategoryTheory

universe u

noncomputable section

variable (p' p : ℝ≥0) [Fact (0 < p')] [Fact (p' ≤ 1)] [Fact (p' < p)]

section

open Tactic

unsafe def tactic.extract_facts : tactic Unit := do
  let ctx ← local_context
  ctx fun hyp => do
      let hyp_tp ← infer_type hyp
      when (hyp_tp `fact) <| (mk_app `fact.out [hyp] >>= note_anon none) >> skip

/- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
unsafe def tactic.interactive.fact_arith : tactic Unit :=
  tactic.extract_facts >> sorry <|> sorry

end

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `fact_arith #[] -/
scoped[LiquidTensorExperiment]
  notation "ℳ_{" p' "}" S =>
    (@RealMeasures.condensed p' _
          (by
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `fact_arith #[]")).obj
      S

abbrev LiquidTensorExperiment.ext (i : ℤ) (A B : Condensed.{u} Ab.{u + 1}) :=
  ((ext' i).obj (op A)).obj B

instance : Coe (PBanachCat.{u} p) (Condensed.{u} Ab.{u + 1}) where coe V := Condensed.ofTopAb V

abbrev LiquidTensorExperiment.sections (S : Profinite.{0}) (F : Condensed.{0} Ab.{1}) : Ab.{1} :=
  F.val.obj (Opposite.op S)

scoped[LiquidTensorExperiment] notation "Γ_" => LiquidTensorExperiment.sections

def PBanachCat.hasCoeToFunCondensedEval (V : PBanachCat.{0} p) (S : Profinite.{0}) :
    CoeFun (Γ_ S (V : Condensed.{0} Ab.{1})) fun _ => S → V :=
  ⟨fun f => ((ULift.down f : C(S, V)) : S → V)⟩

scoped[LiquidTensorExperiment] attribute [instance] PBanachCat.hasCoeToFunCondensedEval

/-- Notation hack for LTE examples. -/
def boundedHomotopyCategoryCoeToFun {A : Type _} [Category A] [Abelian A] :
    Coe A (BoundedHomotopyCategory A) :=
  ⟨fun X => (BoundedHomotopyCategory.single _ 0).obj X⟩

/-- Notation hack for LTE examples. -/
def functorCoeToFun {C D : Type _} [Category C] [Category D] : CoeFun (C ⥤ D) fun _ => C → D :=
  ⟨fun F => F.obj⟩

/-- Notation hack for LTE examples. -/
def cHPNGCoeToFun (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0}) :
    CoeFun (Γ_ S (CompHausFiltPseuNormGrp.toCondensed.obj X)) fun f => S → X :=
  ⟨fun f s => f.down.val s⟩

/-- Notation hack for LTE examples. -/
def radonCoeToFun (S : Profinite.{0}) (p : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    CoeFun (S.radonPng p) fun f => C(S, ℝ) → ℝ :=
  ⟨fun μ => μ.1⟩

scoped[LiquidTensorExperiment] attribute [instance] boundedHomotopyCategoryCoeToFun

scoped[LiquidTensorExperiment] attribute [instance] functorCoeToFun

scoped[LiquidTensorExperiment] attribute [instance] cHPNGCoeToFun

scoped[LiquidTensorExperiment] attribute [instance] radonCoeToFun

def pBanachLpCoeToFun {p : ℝ≥0} [Fact (0 < p)] [Fact (p ≤ 1)] :
    CoeFun (PBanachCat.lp p) fun f => ℕ → ℝ :=
  ⟨fun (f : PBanachCat.lpType p) n => f n⟩

scoped[LiquidTensorExperiment] attribute [instance] pBanachLpCoeToFun

