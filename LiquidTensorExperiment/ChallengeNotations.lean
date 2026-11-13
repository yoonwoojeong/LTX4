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

open Lean Elab Tactic Meta

-- Porting note: Lean 3 `meta def tactic.extract_facts` / `tactic.interactive.fact_arith`
-- re-expressed in Lean 4 (mathport cannot translate Lean 3 metaprograms). Same behaviour:
-- add `h.out` for every hypothesis `h : Fact p`, then try
-- `norm_cast at *; simp only [← NNReal.coe_lt_coe, ← NNReal.coe_le_coe] at *;
--  refine Fact.mk ?_; linarith`, falling back to instance search.
/-- Add `h.out : p` to the context for each local hypothesis `h : Fact p`. -/
elab "extract_facts" : tactic => withMainContext do
  for h in (← getLCtx) do
    if h.isImplementationDetail then continue
    if (← instantiateMVars h.type).isAppOf ``Fact then
      let pf ← mkAppOptM ``Fact.out #[none, some h.toExpr]
      let g ← getMainGoal
      let (_, g') ← (← g.assert `this (← inferType pf) pf).intro1P
      replaceMainGoal [g']

macro "fact_arith" : tactic =>
  `(tactic| first
    | (extract_facts
       norm_cast at *
       simp only [← NNReal.coe_lt_coe, ← NNReal.coe_le_coe] at *
       refine Fact.mk ?_
       linarith)
    | infer_instance)

end

scoped[LiquidTensorExperiment]
  notation "ℳ_{" p' "}" S =>
    (@RealMeasures.condensed p' _
          (by fact_arith)).obj
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

