import LiquidTensorExperiment.PseudoNormedGroup.LC
import Mathlib.Analysis.Normed.Group.HomCompletion

#align_import pseudo_normed_group.CLC

/-!

# V-hat(M_c^n)

One of the key players in the proof of the main theorem of this repo is
the normed group V-hat(M-bar_r'(S)_{≤c}^n). This file constructs

## Key defintions

- `CLCP V n`: the functor that sends a profinite set `S` to `V-hat(S^n)`
- `CLFCP v r' c n`: the functor sending a profinitely-filtered `T⁻¹`-module `M`
   to `V-hat((M_c)^n)`

-/


open scoped Classical NNReal

noncomputable section

attribute [local instance] typePow

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup

universe u

variable (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0)

variable (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

/-- `CLC V n` is the functor that sends a profinite set `S` to `V-hat(S^n)` -/
def cLC (V : SemiNormedGroupCat) : Profiniteᵒᵖ ⥤ SemiNormedGroupCat :=
  lC V ⋙ completion

namespace cLC

theorem map_normNoninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((cLC V).map f).NormNoninc :=
  completion.map_normNoninc <| lC.map_normNoninc _ _

def t [NormedWithAut r V] [Fact (0 < r)] : cLC V ≅ cLC V :=
  ((whiskeringRight _ _ _).obj _).mapIso (lC.t r V)

theorem norm_t_le [NormedWithAut r V] [Fact (0 < r)] (A) : ‖((t r V).hom.app A)‖ ≤ r :=
  le_trans (NormedAddGroupHom.norm_completion _).le <| lC.norm_t_le _ _ _

def tInv [NormedWithAut r V] [Fact (0 < r)] : cLC V ⟶ cLC V :=
  whiskerRight (lC.tInv r V) completion

theorem tInv_eq [NormedWithAut r V] [Fact (0 < r)] : (t r V).inv = tInv r V :=
  rfl

theorem norm_tInv_le [NormedWithAut r V] [Fact (0 < r)] (A) : ‖((tInv r V).app A)‖ ≤ r⁻¹ :=
  le_trans (NormedAddGroupHom.norm_completion _).le <| lC.norm_tInv_le _ _ _

end cLC

/-- `CLFCP v r' c n` is the functor sending a profinitely-filtered `T⁻¹`-module `M`
   to `V-hat((M_c)^n)` -/
def cLCFP (V : SemiNormedGroupCat) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
    (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroupCat :=
  (filtrationPow r' c n).op ⋙ cLC V

theorem cLCFP_def (V : SemiNormedGroupCat) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
    cLCFP V r' c n = lCFP V r' c n ⋙ completion :=
  rfl

namespace cLCFP

theorem map_normNoninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((cLCFP V r' c n).map f).NormNoninc :=
  cLC.map_normNoninc _ _

@[simps app]
def res [Fact (c₂ ≤ c₁)] : cLCFP V r' c₁ n ⟶ cLCFP V r' c₂ n :=
  (whiskerRight (NatTrans.op <| filtrationPow.castLe r' c₂ c₁ n) (cLC V) : _)

theorem res_def [Fact (c₂ ≤ c₁)] :
    res V r' c₁ c₂ n = whiskerRight (NatTrans.op (filtrationPow.castLe r' c₂ c₁ n)) (cLC V) :=
  rfl

theorem res_def' [Fact (c₂ ≤ c₁)] (M : ProFiltPseuNormGrpWithTinv r') :
    (res V r' c₁ c₂ n).app (op M) =
      (cLC V).map (Filtration.castLe ((ProFiltPseuNormGrpWithTinv.pow r' n).obj M) c₂ c₁).op :=
  rfl

theorem res_app' [Fact (c₂ ≤ c₁)] (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
    (res V r' c₁ c₂ n).app M = (cLC V).map ((filtrationPow.castLe r' c₂ c₁ n).app (unop M)).op :=
  rfl

@[simp]
theorem res_refl : res V r' c c n = 𝟙 _ := by
  rw [res, filtrationPow.castLe_refl, NatTrans.op_id, CategoryTheory.whiskerRight_id']; rfl

theorem res_comp_res [Fact (c₂ ≤ c₁)] [Fact (c₃ ≤ c₂)] [Fact (c₃ ≤ c₁)] :
    res V r' c₁ c₂ n ≫ res V r' c₂ c₃ n = res V r' c₁ c₃ n := by
  simp only [res, ← CategoryTheory.whiskerRight_comp, filtrationPow.castLe_comp, ← NatTrans.op_comp]

theorem res_normNoninc [Fact (c₂ ≤ c₁)] (M) : ((res V r' c₁ c₂ n).app M).NormNoninc :=
  completion.map_normNoninc <| lCFP.res_normNoninc _ _ _ _ _ _

section Tinv

-- kmb commented out the next line
--open profinitely_filtered_pseudo_normed_group_with_Tinv
variable [Fact (0 < r')] [Fact (c₂ ≤ r' * c₁)]

-- @[simps obj {fully_applied := ff}]
def tinv : cLCFP V r' c₁ n ⟶ cLCFP V r' c₂ n :=
  (whiskerRight (NatTrans.op <| filtrationPow.tinv r' c₂ c₁ n)
      (locallyConstant.obj V ⋙ completion) :
    _)

theorem tinv_def : tinv V r' c₁ c₂ n = (whiskerRight (lCFP.tinv V r' c₁ c₂ n) completion : _) :=
  rfl

theorem tinv_def' :
    tinv V r' c₁ c₂ n = whiskerRight (NatTrans.op <| filtrationPow.tinv r' c₂ c₁ n) (cLC V) :=
  rfl

theorem res_comp_tinv [Fact (c₂ ≤ c₁)] [Fact (c₃ ≤ c₂)] [Fact (c₃ ≤ r' * c₂)] :
    res V r' c₁ c₂ n ≫ tinv V r' c₂ c₃ n = tinv V r' c₁ c₂ n ≫ res V r' c₂ c₃ n :=
  by
  dsimp only [cLCFP.tinv, res, cLC, lC]
  simp only [← CategoryTheory.whiskerRight_comp, ← NatTrans.op_comp]
  rfl

end Tinv

section TInv

variable [NormedWithAut r V] [Fact (0 < r)]

@[simps (config := { fullyApplied := false })]
def t : cLCFP V r' c n ≅ cLCFP V r' c n :=
  ((whiskeringLeft _ _ _).obj (filtrationPow r' c n).op).mapIso (cLC.t r V)

@[simps (config := { fullyApplied := false }) app_apply]
def tInv : cLCFP V r' c n ⟶ cLCFP V r' c n :=
  whiskerLeft (filtrationPow r' c n).op (cLC.tInv r V)

theorem tInv_eq [NormedWithAut r V] [Fact (0 < r)] : (t r V r' c n).inv = tInv r V r' c n :=
  rfl

theorem tInv_def : tInv r V r' c n = (whiskerRight (lCFP.tInv r V r' c n) completion : _) :=
  rfl

theorem tInv_app [Fact (0 < r)] (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :
    (tInv r V r' c n).app M = (cLC.tInv r V).app ((filtrationPow r' c n).op.obj M) :=
  rfl

theorem res_comp_tInv [Fact (c₂ ≤ c₁)] :
    res V r' c₁ c₂ n ≫ tInv r V r' c₂ n = tInv r V r' c₁ n ≫ res V r' c₁ c₂ n :=
  by
  ext M : 2
  simp only [NatTrans.comp_app, res_app', tInv_app]
  exact (cLC.tInv r V).naturality _

end TInv

end cLCFP

namespace BreenDeligne

open cLCFP

variable {l m n}

namespace UniversalMap

variable (ϕ ψ : UniversalMap m n)

def evalCLCFP [ϕ.Suitable c₂ c₁] : cLCFP V r' c₁ n ⟶ cLCFP V r' c₂ m :=
  (whiskerRight (ϕ.evalLCFP V r' c₁ c₂) completion : _)

theorem evalCLCFP_of (f : BasicUniversalMap m n) [f.Suitable c₂ c₁] :
    evalCLCFP V r' c₁ c₂ (FreeAbelianGroup.of f) =
      whiskerRight (NatTrans.op <| f.evalFP r' c₂ c₁) (cLC V) :=
  by rw [evalCLCFP, evalLCFP_of, BasicUniversalMap.evalLCFP, CategoryTheory.whiskerRight_twice]; rfl

@[simp]
theorem evalCLCFP_zero : (0 : UniversalMap m n).evalCLCFP V r' c₁ c₂ = 0 :=
  by
  simp only [evalCLCFP, evalLCFP_zero]
  ext x : 2
  exact completion.map_zero _ _

@[simp]
theorem evalCLCFP_add [ϕ.Suitable c₂ c₁] [ψ.Suitable c₂ c₁] :
    (ϕ + ψ : UniversalMap m n).evalCLCFP V r' c₁ c₂ =
      ϕ.evalCLCFP V r' c₁ c₂ + ψ.evalCLCFP V r' c₁ c₂ :=
  by
  simp only [evalCLCFP, evalLCFP_add]
  ext x : 2
  exact Functor.map_add completion

@[simp]
theorem evalCLCFP_sub [ϕ.Suitable c₂ c₁] [ψ.Suitable c₂ c₁] :
    (ϕ - ψ : UniversalMap m n).evalCLCFP V r' c₁ c₂ =
      ϕ.evalCLCFP V r' c₁ c₂ - ψ.evalCLCFP V r' c₁ c₂ :=
  by
  simp only [evalCLCFP, evalLCFP_sub]
  ext x : 2
  exact Functor.map_sub completion

open CategoryTheory.Limits

theorem evalCLCFP_comp (g : UniversalMap m n) (f : UniversalMap l m) [hg : g.Suitable c₂ c₁]
    [hf : f.Suitable c₃ c₂] :
    @evalCLCFP V r' c₁ c₃ _ _ (comp g f) (Suitable.comp c₂) =
      g.evalCLCFP V r' c₁ c₂ ≫ f.evalCLCFP V r' c₂ c₃ :=
  by
  -- Porting note: unfold explicitly since the instance argument is given by `@`
  show whiskerRight (@evalLCFP V r' c₁ c₃ _ _ (comp g f) (Suitable.comp c₂)) completion = _
  rw [evalLCFP_comp V r' c₁ c₂ c₃, CategoryTheory.whiskerRight_comp]
  rfl

theorem res_comp_evalCLCFP [Fact (c₂ ≤ c₁)] [ϕ.Suitable c₄ c₂] [ϕ.Suitable c₃ c₁] [Fact (c₄ ≤ c₃)] :
    res V r' c₁ c₂ n ≫ ϕ.evalCLCFP V r' c₂ c₄ = ϕ.evalCLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
  by
  dsimp only [cLC, res]; simp only [evalCLCFP, ← CategoryTheory.whiskerRight_comp, ← CategoryTheory.whiskerRight_twice]
  congr 1; apply res_comp_evalLCFP

theorem tinv_comp_evalCLCFP [Fact (0 < r')] [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)]
    [ϕ.Suitable c₃ c₁] [ϕ.Suitable c₄ c₂] :
    tinv V r' c₁ c₂ n ≫ ϕ.evalCLCFP V r' c₂ c₄ = ϕ.evalCLCFP V r' c₁ c₃ ≫ tinv V r' c₃ c₄ m := by
  simp only [evalCLCFP, tinv_def, ← CategoryTheory.whiskerRight_comp] <;> congr 1 <;> apply tinv_comp_evalLCFP

theorem tInv_comp_evalCLCFP [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] :
    tInv r V r' c₁ n ≫ ϕ.evalCLCFP V r' c₁ c₂ = ϕ.evalCLCFP V r' c₁ c₂ ≫ tInv r V r' c₂ m := by
  simp only [evalCLCFP, tInv_def, ← CategoryTheory.whiskerRight_comp, tInv_comp_evalLCFP]

theorem norm_evalCLCFP_le [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] (N : ℕ)
    (h : ϕ.BoundBy N) (M) : ‖((ϕ.evalCLCFP V r' c₁ c₂).app M)‖ ≤ N :=
  le_trans (NormedAddGroupHom.norm_completion _).le <| norm_evalLCFP_le _ _ _ _ _ _ _ h _

end UniversalMap

end BreenDeligne

