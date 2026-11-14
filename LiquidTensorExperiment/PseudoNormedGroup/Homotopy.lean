import Mathlib.Algebra.Homology.Homotopy
import LiquidTensorExperiment.PseudoNormedGroup.SystemOfComplexes
import LiquidTensorExperiment.Rescale.Tinv

#align_import pseudo_normed_group.homotopy

/-!

*TODO*: find someone who can explain what is going on in this file.

-/


noncomputable section

universe u

open scoped NNReal

open CategoryTheory HomologicalComplex

namespace BreenDeligne

variable {BD BD₁ BD₂ : BreenDeligne.Data} (f g : BD₂ ⟶ BD₁)

variable (h : Homotopy f g)

variable (κ c_₁ c_₂ : ℕ → ℝ≥0)

variable [BD.Suitable κ] [BD₁.Suitable c_₁] [BD₂.Suitable c_₂]

variable (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

variable {r' : ℝ≥0} [Fact (0 < r')] [Fact (r' ≤ 1)] (c : ℝ≥0)

section Homotopy

variable (M : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ)

open HomologicalComplex

@[simps app_f]
def bDMap₂ (a₁ a₂ b₁ b₂ : ℕ → ℝ≥0) [∀ i : ℕ, Fact (b₁ i ≤ r' * a₁ i)]
    [∀ i : ℕ, Fact (b₂ i ≤ r' * a₂ i)] [BD₁.Suitable a₁] [BD₂.Suitable a₂] [BD₁.Suitable b₁]
    [BD₂.Suitable b₂] [∀ i, (f.f i).Suitable (a₂ i) (a₁ i)] [∀ i, (f.f i).Suitable (b₂ i) (b₁ i)] :
    BD₁.complex₂ r V r' a₁ b₁ ⟶ BD₂.complex₂ r V r' a₂ b₂
    where
  app M :=
    { f := fun i => ((f.f i).evalCLCFPTinv₂ r V r' (a₁ i) (b₁ i) (a₂ i) (b₂ i)).app M
      comm' := by
        intro i j _
        dsimp [Data.complex₂_obj_d, Data.complex₂D]
        have : f.f j ≫ BD₁.d j i = BD₂.d j i ≫ f.f i := f.comm j i
        simp only [← NatTrans.comp_app, ← UniversalMap.evalCLCFPTinv₂_comp r V r', this] }
  naturality := by
    intro M₁ M₂ g; ext i : 2
    exact ((f.f i).evalCLCFPTinv₂ r V r' (a₁ i) (b₁ i) (a₂ i) (b₂ i)).naturality g

@[simps app_f]
def bDMap [∀ i, (f.f i).Suitable (c_₂ i) (c_₁ i)] :
    BD₁.Complex c_₁ r V r' c ⟶ BD₂.Complex c_₂ r V r' c :=
  bDMap₂ f r V _ _ _ _

-- @[simp] lemma BD_map_app_f [∀ i, (f.f i).suitable (c_₂ i) (c_₁ i)] (i : ℕ)
--   (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
--   ((BD_map f c_₁ c_₂ r V c).app M).f i =
--     ((f.f i).eval_CLCFPTinv r V r' (c_₁ i) (c_₂ i)).app M := _
open Opposite

@[simps app_app]
def bDSystemMap [∀ i, (f.f i).Suitable (c_₂ i) (c_₁ i)] :
    BD₁.system c_₁ r V r' ⟶ BD₂.system c_₂ r V r'
    where
  app M :=
    { app := fun c => (bDMap f c_₁ c_₂ r V c.unop).app M
      naturality := fun x y hxy => by
        ext i : 2
        erw [comp_f, comp_f]
        dsimp only [Data.system_obj, BD_map, BD_map₂_app_f]
        haveI : Fact (y.unop ≤ x.unop) := ⟨le_of_hom hxy.unop⟩
        exact
          NatTrans.congr_app (UniversalMap.res_comp_evalCLCFPTinv₂ r V r' _ _ _ _ _ _ _ _ _) M }
  naturality M₁ M₂ g := by
    ext c : 2
    exact (BD_map f c_₁ c_₂ r V c.unop).naturality _

end Homotopy

end BreenDeligne

