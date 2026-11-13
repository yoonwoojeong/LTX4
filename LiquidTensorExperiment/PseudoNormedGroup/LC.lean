import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import LiquidTensorExperiment.PseudoNormedGroup.FP
import LiquidTensorExperiment.LocallyConstant.SemiNormedGroup
import LiquidTensorExperiment.LocallyConstant.Vhat

#align_import pseudo_normed_group.LC

/-!

# The category of locally constant maps

Various constructions of pseudo-normed groups of locally constant functions.

## Main definitions

- `LC V`: the functor sending a profinite set `S` to the locally constant
  functions from `S` to `V`
- `LCFP V r' c n`: the functor sending a profinitely filtered pseudo-normed
  group with T⁻¹ to V(M_c^n), the locally constant functions from M_c^n to V.

-/


namespace CategoryTheory

namespace NatTrans

@[simp]
theorem op_comp {C D} [Category C] [Category D] {F G H : C ⥤ D} {α : F ⟶ G} {β : G ⟶ H} :
    NatTrans.op (α ≫ β) = NatTrans.op β ≫ NatTrans.op α :=
  rfl

end NatTrans

end CategoryTheory

open scoped Classical NNReal BigOperators

noncomputable section

attribute [local instance] typePow

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup

universe u

variable (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0)

variable (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

/-- `LC V n` is the functor that sends a profinite set `S` to `V(S)` -/
def lC (V : SemiNormedGroupCat) : Profiniteᵒᵖ ⥤ SemiNormedGroupCat :=
  locallyConstant.obj V

namespace lC

theorem map_normNoninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((lC V).map f).NormNoninc :=
  LocallyConstant.comapHom_normNoninc _ _

instance Obj.normedWithAut [NormedWithAut r V] [Fact (0 < r)] (A : Profiniteᵒᵖ) :
    NormedWithAut r ((lC V).obj A) :=
  SemiNormedGroupCat.normedWithAutLocallyConstant _ _ _

@[simps (config := { fullyApplied := false }) hom_app_apply inv_app_apply]
def t [NormedWithAut r V] : lC V ≅ lC V :=
  locallyConstant.mapIso NormedWithAut.t

theorem t_eq [NormedWithAut r V] [Fact (0 < r)] (A) : (t r V).hom.app A = NormedWithAut.t.hom :=
  rfl

theorem norm_t_le [NormedWithAut r V] [Fact (0 < r)] (A) : ‖((lC.t r V).hom.app A)‖ ≤ r :=
  by
  rw [T_eq]
  refine' NormedAddGroupHom.opNorm_le_bound _ NNReal.zero_le_coe fun v => _
  exact le_of_eq (NormedWithAut.norm_t v)

@[simps (config := { fullyApplied := false })]
def tInv [NormedWithAut r V] [Fact (0 < r)] : lC V ⟶ lC V :=
  (locallyConstant.map (NormedWithAut.t.inv : V ⟶ V) : _)

theorem tInv_eq [NormedWithAut r V] [Fact (0 < r)] : (t r V).inv = tInv r V :=
  rfl

theorem tInv_eq' [NormedWithAut r V] [Fact (0 < r)] (A) : (tInv r V).app A = NormedWithAut.t.inv :=
  rfl

theorem norm_tInv_le [NormedWithAut r V] [Fact (0 < r)] (A) : ‖((tInv r V).app A)‖ ≤ r⁻¹ :=
  by
  rw [T_inv_eq']
  refine' NormedAddGroupHom.opNorm_le_bound _ (inv_nonneg.2 NNReal.zero_le_coe) fun v => _
  exact (NormedWithAut.norm_t_inv _ v).le

end lC

/-- The "functor" that sends `M` and `c` to `V((filtration M c)^n)` -/
def lCFP (V : SemiNormedGroupCat) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
    (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroupCat :=
  (filtrationPow r' c n).op ⋙ lC V

theorem lCFP_def (V : SemiNormedGroupCat) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
    lCFP V r' c n = (filtrationPow r' c n).op ⋙ locallyConstant.obj V :=
  rfl

namespace lCFP

theorem map_normNoninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((lCFP V r' c n).map f).NormNoninc :=
  lC.map_normNoninc _ _

@[simps (config := { fullyApplied := false })]
def res (r' : ℝ≥0) (c₁ c₂ : ℝ≥0) [Fact (c₂ ≤ c₁)] (n : ℕ) : lCFP V r' c₁ n ⟶ lCFP V r' c₂ n :=
  (whiskerRight (NatTrans.op (filtrationPow.castLe r' c₂ c₁ n)) (locallyConstant.obj V) : _)

@[simp]
theorem res_refl : res V r' c c n = 𝟙 _ := by simp [res, filtrationPow.castLe_refl]; rfl

theorem res_comp_res [h₁ : Fact (c₃ ≤ c₂)] [h₂ : Fact (c₂ ≤ c₁)] :
    res V r' c₁ c₂ n ≫ res V r' c₂ c₃ n = @res V r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n := by
  simp only [res, ← whisker_right_comp, ← nat_trans.op_comp, filtrationPow.castLe_comp]

theorem res_normNoninc [Fact (c₂ ≤ c₁)] (M) : ((res V r' c₁ c₂ n).app M).NormNoninc :=
  LocallyConstant.comapHom_normNoninc _ _

section Tinv

open ProfinitelyFilteredPseudoNormedGroupWithTinv

variable [Fact (0 < r')]

@[simps (config := { fullyApplied := false })]
def tinv [Fact (c₂ ≤ r' * c₁)] : lCFP V r' c₁ n ⟶ lCFP V r' c₂ n :=
  (whiskerRight (NatTrans.op <| filtrationPow.tinv r' c₂ c₁ n) (locallyConstant.obj V) : _)

theorem tinv_def [Fact (c₂ ≤ r' * c₁)] :
    tinv V r' c₁ c₂ n = whiskerRight (NatTrans.op <| filtrationPow.tinv r' c₂ c₁ n) (lC V) :=
  rfl

theorem res_comp_tinv [Fact (c₂ ≤ c₁)] [Fact (c₃ ≤ c₂)] [Fact (c₂ ≤ r' * c₁)]
    [Fact (c₃ ≤ r' * c₂)] :
    res V r' c₁ c₂ n ≫ tinv V r' c₂ c₃ n = tinv V r' c₁ c₂ n ≫ res V r' c₂ c₃ n :=
  by
  simp only [Tinv, res, ← whisker_right_comp, ← nat_trans.op_comp]
  rfl

theorem tinv_normNoninc [Fact (c₂ ≤ r' * c₁)] (M) : ((tinv V r' c₁ c₂ n).app M).NormNoninc :=
  LocallyConstant.comapHom_normNoninc _ _

end Tinv

section NormedWithAut

variable [NormedWithAut r V]

instance [Fact (0 < r)] (M) : NormedWithAut r ((lCFP V r' c n).obj M) :=
  lC.Obj.normedWithAut _ _ _

@[simps (config := { fullyApplied := false })]
def t [Fact (0 < r)] : lCFP V r' c n ≅ lCFP V r' c n :=
  ((whiskeringLeft _ _ _).obj _).mapIso <| lC.t _ _

@[simps (config := { fullyApplied := false }) app_apply]
def tInv [Fact (0 < r)] : lCFP V r' c n ⟶ lCFP V r' c n :=
  (whiskerLeft _ (lC.tInv r V) : _)

theorem tInv_eq [Fact (0 < r)] : (t r V r' c n).inv = tInv r V r' c n :=
  rfl

theorem tInv_def [Fact (0 < r)] :
    tInv r V r' c n =
      (whiskerLeft (filtrationPow r' c n).op (locallyConstant.map (NormedWithAut.t.inv : V ⟶ V)) :
        _) :=
  rfl

end NormedWithAut

end lCFP

namespace BreenDeligne

open lCFP

variable {l m n}

namespace BasicUniversalMap

variable (ϕ : BasicUniversalMap m n)

def evalLCFP (c₁ c₂ : ℝ≥0) [ϕ.Suitable c₂ c₁] : lCFP V r' c₁ n ⟶ lCFP V r' c₂ m :=
  (whiskerRight (NatTrans.op <| ϕ.evalFP r' c₂ c₁) (locallyConstant.obj V) : _)

def evalLCFP' (c₁ c₂ : ℝ≥0) : lCFP V r' c₁ n ⟶ lCFP V r' c₂ m :=
  if H : ϕ.Suitable c₂ c₁ then
    (whisker_right (nat_trans.op <| ϕ.eval_FP r' c₂ c₁) (LocallyConstant.obj V) : _)
  else 0

theorem evalLCFP_eq_evalLCFP' (h : ϕ.Suitable c₂ c₁) :
    ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP' V r' c₁ c₂ := by delta eval_LCFP eval_LCFP'; rw [dif_pos h]

theorem evalLCFP'_def [h : ϕ.Suitable c₂ c₁] :
    ϕ.evalLCFP' V r' c₁ c₂ =
      (whiskerRight (NatTrans.op <| ϕ.evalFP r' c₂ c₁) (locallyConstant.obj V) : _) :=
  dif_pos h

theorem evalLCFP'_not_suitable (h : ¬ϕ.Suitable c₂ c₁) : ϕ.evalLCFP' V r' c₁ c₂ = 0 :=
  dif_neg h

theorem evalLCFP'_comp (f : BasicUniversalMap m n) (g : BasicUniversalMap l m)
    [hf : f.Suitable c₂ c₁] [hg : g.Suitable c₃ c₂] :
    (BasicUniversalMap.comp f g).evalLCFP' V r' c₁ c₃ =
      f.evalLCFP' V r' c₁ c₂ ≫ g.evalLCFP' V r' c₂ c₃ :=
  by
  haveI : (basic_universal_map.comp f g).Suitable c₃ c₁ := suitable_comp c₂
  simp only [eval_LCFP'_def, eval_FP_comp r' _ c₂, nat_trans.op_comp, whisker_right_comp]

theorem evalLCFP_comp (f : BasicUniversalMap m n) (g : BasicUniversalMap l m)
    [hf : f.Suitable c₂ c₁] [hg : g.Suitable c₃ c₂] :
    @evalLCFP V r' _ _ (BasicUniversalMap.comp f g) c₁ c₃ (suitable_comp c₂) =
      f.evalLCFP V r' c₁ c₂ ≫ g.evalLCFP V r' c₂ c₃ :=
  by simp only [eval_LCFP_eq_eval_LCFP']; apply eval_LCFP'_comp

theorem res_comp_evalLCFP [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ c₃)] [ϕ.Suitable c₄ c₂] [ϕ.Suitable c₃ c₁] :
    res V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m := by
  simp only [res, eval_LCFP, ← whisker_right_comp, ← nat_trans.op_comp,
    cast_le_comp_eval_FP _ c₄ c₃ c₂ c₁]

theorem tinv_comp_evalLCFP [Fact (0 < r')] [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)]
    [ϕ.Suitable c₄ c₂] [ϕ.Suitable c₃ c₁] :
    tinv V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ tinv V r' c₃ c₄ m := by
  simp only [Tinv, eval_LCFP, ← whisker_right_comp, ← nat_trans.op_comp,
    Tinv_comp_eval_FP _ _ c₄ c₃ c₂ c₁]

theorem tInv_comp_evalLCFP [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] :
    tInv r V r' c₁ n ≫ ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP V r' c₁ c₂ ≫ tInv r V r' c₂ m :=
  by
  ext M : 2
  simp only [T_inv_def, eval_LCFP, nat_trans.comp_app, whisker_right_app, whisker_left_app,
    nat_trans.naturality]

end BasicUniversalMap

namespace UniversalMap

open FreeAbelianGroup

variable (ϕ : UniversalMap m n)

def evalLCFP [ϕ.Suitable c₂ c₁] : lCFP V r' c₁ n ⟶ lCFP V r' c₂ m :=
  ∑ g : { g : BasicUniversalMap m n // g ∈ ϕ.support },
    haveI := suitable_of_mem_support ϕ c₂ c₁ g g.2
    coeff (g : basic_universal_map m n) ϕ • basic_universal_map.eval_LCFP V r' g c₁ c₂

def evalLCFP' : lCFP V r' c₁ n ⟶ lCFP V r' c₂ m :=
  ∑ g in ϕ.support, coeff g ϕ • g.evalLCFP' V r' c₁ c₂

theorem evalLCFP_eq_evalLCFP' (h : ϕ.Suitable c₂ c₁) :
    ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP' V r' c₁ c₂ :=
  by
  simp only [eval_LCFP, eval_LCFP', basic_universal_map.eval_LCFP_eq_eval_LCFP', Subtype.val_eq_coe]
  symm
  apply Finset.sum_subtype ϕ.support fun _ => Iff.rfl

@[simp]
theorem evalLCFP'_of (f : BasicUniversalMap m n) :
    evalLCFP' V r' c₁ c₂ (of f) = f.evalLCFP' V r' c₁ c₂ := by
  simp only [eval_LCFP', support_of, coeff_of_self, one_smul, Finset.sum_singleton]

@[simp]
theorem evalLCFP_of (f : BasicUniversalMap m n) [f.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (of f) = f.evalLCFP V r' c₁ c₂ := by
  rw [eval_LCFP_eq_eval_LCFP', eval_LCFP'_of, basic_universal_map.eval_LCFP_eq_eval_LCFP']

@[simp]
theorem evalLCFP'_zero : (0 : UniversalMap m n).evalLCFP' V r' c₁ c₂ = 0 := by
  rw [eval_LCFP', support_zero, Finset.sum_empty]

@[simp]
theorem evalLCFP_zero : (0 : UniversalMap m n).evalLCFP V r' c₁ c₂ = 0 := by
  rw [eval_LCFP_eq_eval_LCFP', eval_LCFP'_zero]

@[simp]
theorem evalLCFP'_neg (f : UniversalMap m n) :
    evalLCFP' V r' c₁ c₂ (-f) = -f.evalLCFP' V r' c₁ c₂ := by
  simp only [eval_LCFP', AddMonoidHom.map_neg, Finset.sum_neg_distrib, neg_smul, support_neg]

@[simp]
theorem evalLCFP_neg (f : UniversalMap m n) [f.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (-f) = -f.evalLCFP V r' c₁ c₂ := by
  simp only [eval_LCFP_eq_eval_LCFP', eval_LCFP'_neg]

theorem evalLCFP'_add (f g : UniversalMap m n) :
    evalLCFP' V r' c₁ c₂ (f + g) = f.evalLCFP' V r' c₁ c₂ + g.evalLCFP' V r' c₁ c₂ :=
  by
  simp only [eval_LCFP']
  rw [Finset.sum_subset (support_add f g)]
  -- two goals
  simp only [AddMonoidHom.map_add _ f g, add_smul]
  convert Finset.sum_add_distrib using 2
  -- three goals
  apply Finset.sum_subset (Finset.subset_union_left _ _);
  swap
  apply Finset.sum_subset (Finset.subset_union_right _ _)
  all_goals rintro x - h; rw [not_mem_support_iff] at h ; simp [h]

theorem evalLCFP_add (f g : UniversalMap m n) [f.Suitable c₂ c₁] [g.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (f + g) = f.evalLCFP V r' c₁ c₂ + g.evalLCFP V r' c₁ c₂ := by
  simp only [eval_LCFP_eq_eval_LCFP', eval_LCFP'_add]

theorem evalLCFP_sub (f g : UniversalMap m n) [f.Suitable c₂ c₁] [g.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (f - g) = f.evalLCFP V r' c₁ c₂ - g.evalLCFP V r' c₁ c₂ := by
  simp only [sub_eq_add_neg, eval_LCFP_add, eval_LCFP_neg]

theorem evalLCFP'_comp_of (g : BasicUniversalMap m n) (f : BasicUniversalMap l m)
    [hg : g.Suitable c₂ c₁] [hf : f.Suitable c₃ c₂] :
    evalLCFP' V r' c₁ c₃ ((comp (of g)) (of f)) =
      evalLCFP' V r' c₁ c₂ (of g) ≫ evalLCFP' V r' c₂ c₃ (of f) :=
  by
  simp only [comp_of, eval_LCFP'_of]
  haveI hfg : (basic_universal_map.comp g f).Suitable c₃ c₁ := basic_universal_map.suitable_comp c₂
  rw [← basic_universal_map.eval_LCFP'_comp]

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

theorem evalLCFP'_comp (g : UniversalMap m n) (f : UniversalMap l m) [hg : g.Suitable c₂ c₁]
    [hf : f.Suitable c₃ c₂] :
    (comp g f).evalLCFP' V r' c₁ c₃ = g.evalLCFP' V r' c₁ c₂ ≫ f.evalLCFP' V r' c₂ c₃ :=
  by
  revert hf
  apply
      FreeAbelianGroup.induction_on_freePredicate (suitable c₂ c₁) (suitable_free_predicate c₂ c₁) g
        hg <;>
    clear! g
  · intro h₂
    simp only [eval_LCFP'_zero, zero_comp, Pi.zero_apply, AddMonoidHom.zero_apply,
      AddMonoidHom.map_zero]
  · intro g hg hf
    -- now do another nested induction on `f`
      apply
        FreeAbelianGroup.induction_on_freePredicate (suitable c₃ c₂) (suitable_free_predicate c₃ c₂)
          f hf <;>
      clear! f
    · simp only [eval_LCFP'_zero, comp_zero, AddMonoidHom.map_zero]
    · intro f hf
      rw [suitable_of_iff] at hf hg 
      skip
      apply eval_LCFP'_comp_of
    · intro f hf IH
      simp only [IH, eval_LCFP'_neg, AddMonoidHom.map_neg, comp_neg]
    · rintro (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂; skip
      haveI Hg₁f : (comp (of g) f₁).Suitable c₃ c₁ := suitable.comp c₂
      haveI Hg₂f : (comp (of g) f₂).Suitable c₃ c₁ := suitable.comp c₂
      simp only [AddMonoidHom.map_add, eval_LCFP'_add, IH₁, IH₂, comp_add]
  · intro g hg IH hf; skip; specialize IH
    simp only [IH, AddMonoidHom.map_neg, eval_LCFP'_neg, AddMonoidHom.neg_apply, neg_inj, neg_comp]
  · rintro (g₁ : universal_map m n) (g₂ : universal_map m n) hg₁ hg₂ IH₁ IH₂ hf; skip
    haveI Hg₁f : (comp g₁ f).Suitable c₃ c₁ := suitable.comp c₂
    haveI Hg₂f : (comp g₂ f).Suitable c₃ c₁ := suitable.comp c₂
    simp only [AddMonoidHom.map_add, AddMonoidHom.add_apply, eval_LCFP'_add, IH₁, IH₂, add_comp]

theorem evalLCFP_comp (g : UniversalMap m n) (f : UniversalMap l m) [hg : g.Suitable c₂ c₁]
    [hf : f.Suitable c₃ c₂] :
    @evalLCFP V r' c₁ c₃ _ _ (comp g f) (Suitable.comp c₂) =
      g.evalLCFP V r' c₁ c₂ ≫ f.evalLCFP V r' c₂ c₃ :=
  by simp only [eval_LCFP_eq_eval_LCFP']; apply eval_LCFP'_comp

theorem res_comp_evalLCFP [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ c₃)] [ϕ.Suitable c₃ c₁] [ϕ.Suitable c₄ c₂] :
    res V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
  by
  simp only [eval_LCFP, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.suitable c₃ c₁ := suitable_of_mem_support ϕ _ _ g hg
  haveI : g.suitable c₄ c₂ := suitable_of_mem_support ϕ _ _ g hg
  simp only [Subtype.coe_mk, g.res_comp_eval_LCFP V r' c₁ c₂ c₃ c₄]

theorem tinv_comp_evalLCFP [Fact (0 < r')] [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)]
    [ϕ.Suitable c₃ c₁] [ϕ.Suitable c₄ c₂] :
    tinv V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ tinv V r' c₃ c₄ m :=
  by
  simp only [eval_LCFP, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.suitable c₃ c₁ := suitable_of_mem_support ϕ _ _ g hg
  haveI : g.suitable c₄ c₂ := suitable_of_mem_support ϕ _ _ g hg
  congr 1; apply basic_universal_map.Tinv_comp_eval_LCFP V r'

theorem tInv_comp_evalLCFP [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] :
    tInv r V r' c₁ n ≫ ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP V r' c₁ c₂ ≫ tInv r V r' c₂ m :=
  by
  simp only [eval_LCFP, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.suitable c₂ c₁ := suitable_of_mem_support ϕ _ _ g hg
  congr 1
  apply basic_universal_map.T_inv_comp_eval_LCFP r V r'

theorem norm_evalLCFP_le [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] (N : ℕ)
    (h : ϕ.BoundBy N) (M) : ‖((ϕ.evalLCFP V r' c₁ c₂).app M)‖ ≤ N :=
  by
  rw [eval_LCFP_eq_eval_LCFP', eval_LCFP']
  have : (∑ g : basic_universal_map m n in support ϕ, (coeff g ϕ).natAbs : ℝ) ≤ N := by
    exact_mod_cast h
  simp only [← nat_trans.app_hom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul]
  refine' le_trans (norm_sum_le_of_le ϕ.support _) this
  intro g hg
  have aux := ϕ.suitable_of_mem_support c₂ c₁ g hg
  refine' le_trans (norm_zsmul_le _ _) _
  suffices ‖((nat_trans.app_hom M) (basic_universal_map.eval_LCFP' V r' g c₁ c₂))‖ ≤ 1
    by
    have aux₁ : ‖((coeff g) ϕ)‖ = ↑((coeff g) ϕ).natAbs :=
      by
      rw [@coe_coe ℕ ℤ ℝ _ _ _, ← Int.abs_eq_natAbs, Int.cast_abs]
      rfl
    rw [aux₁]
    exact mul_le_of_le_one_right ((coeff g) ϕ).natAbs.cast_nonneg this
  rw [← g.eval_LCFP_eq_eval_LCFP' V r' c₁ c₂, basic_universal_map.eval_LCFP]
  · apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
    exact LocallyConstant.comapHom_normNoninc _ _; exact aux

end UniversalMap

end BreenDeligne

