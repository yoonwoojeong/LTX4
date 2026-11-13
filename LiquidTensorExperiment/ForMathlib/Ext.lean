import Mathlib.CategoryTheory.Abelian.Ext
import LiquidTensorExperiment.ForMathlib.DerivedFunctor

#align_import for_mathlib.ext

noncomputable section

universe uᵣ v u

open CategoryTheory Opposite

namespace Ext

variable (R : Type uᵣ) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

local notation "Ext" i "," A "," B => ((Ext R C i).obj (op A)).obj B

def δ (n : ℕ) (A : ShortExactSequence C) (B : C) : (Ext n,A.1,B) ⟶ Ext n + 1,A.3,B :=
  let E := ((linearYoneda R C).obj B).rightOp.leftDerived n
  let E' := ((linearYoneda R C).obj B).rightOp.leftDerived (n + 1)
  Quiver.Hom.unop (show E'.obj A.3 ⟶ E.obj A.1 from Functor.leftDerived.δ _ _ _)

theorem six_term_exactSeq (n : ℕ) (A : ShortExactSequence C) (B : C) :
    ExactSeq (ModuleCat.{v} R)
      [((Ext R C n).map A.g.op).app B, ((Ext R C n).map A.f.op).app B, δ R n A B,
        ((Ext R C (n + 1)).map A.g.op).app B, ((Ext R C (n + 1)).map A.f.op).app B] :=
  by
  apply exact_seq.of_op
  exact functor.left_derived.six_term_exact_seq _ n A

end Ext

