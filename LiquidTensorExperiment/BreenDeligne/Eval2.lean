import LiquidTensorExperiment.ForMathlib.Derived.Example
import LiquidTensorExperiment.BreenDeligne.Eval

#align_import breen_deligne.eval2

noncomputable section

open CategoryTheory CategoryTheory.Preadditive

namespace BreenDeligne

namespace Package

variable (BD : Package)

variable {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜]

variable (F : 𝒜 ⥤ 𝒜)

def eval' : 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  (Data.evalFunctor F).obj BD.data ⋙ HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp

def eval : 𝒜 ⥤ BoundedHomotopyCategory 𝒜 :=
  (Data.evalFunctor F).obj BD.data ⋙ ChainComplex.toBoundedHomotopyCategory

instance eval_additive : (BD.eval F).Additive :=
  Functor.additive_of_map_fst_add_snd _ fun A =>
    by
    refine' HomotopyCategory.eq_of_homotopy _ _ _
    rw [← Functor.map_add]
    exact HomologicalComplex.embedHomotopy _ _ (BreenDeligne.Package.evalFunctorHomotopy F BD A) _

theorem evalFunctor_obj_x (X : 𝒜) (n : ℕ) :
    (((Data.evalFunctor F).obj BD.data).obj X).pt n = F.obj ((pow (BD.data.pt n)).obj X) :=
  rfl

theorem evalFunctor_obj_d (X : 𝒜) (m n : ℕ) :
    (((Data.evalFunctor F).obj BD.data).obj X).d m n =
      (UniversalMap.evalPow F (BD.data.d m n)).app X :=
  rfl

theorem eval'_obj_x (X : 𝒜) (n : ℕ) :
    ((BD.eval' F).obj X).pt (-n : ℤ) = F.obj ((pow (BD.data.pt n)).obj X) := by
  cases n <;> apply eval_functor_obj_X

theorem eval'_obj_x_0 (X : 𝒜) : ((BD.eval' F).obj X).pt 0 = F.obj ((pow (BD.data.pt 0)).obj X) :=
  rfl

theorem eval'_obj_x_succ (X : 𝒜) (n : ℕ) :
    ((BD.eval' F).obj X).pt -[n+1] = F.obj ((pow (BD.data.pt (n + 1))).obj X) :=
  rfl

theorem eval'_obj_d (X : 𝒜) (m n : ℕ) :
    ((BD.eval' F).obj X).d (-(m + 1 : ℕ) : ℤ) (-(n + 1 : ℕ) : ℤ) =
      (UniversalMap.evalPow F (BD.data.d (m + 1) (n + 1))).app X :=
  rfl

theorem eval'_obj_d_0 (X : 𝒜) (n : ℕ) :
    ((BD.eval' F).obj X).d (-(n + 1 : ℕ) : ℤ) (-(1 : ℕ) + 1 : ℤ) =
      (UniversalMap.evalPow F (BD.data.d (n + 1) 0)).app X :=
  rfl

end Package

end BreenDeligne

