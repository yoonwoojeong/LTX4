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
  -- Porting note: the continuity hypothesis must be supplied explicitly
  SemiNormedGroupCat.locallyConstant_obj_map_normNoninc V _ _ f

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
  rw [t_eq]
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
  rw [tInv_eq']
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
  simp only [res, ← whiskerRight_comp, ← NatTrans.op_comp, filtrationPow.castLe_comp]

theorem res_normNoninc [Fact (c₂ ≤ c₁)] (M) : ((res V r' c₁ c₂ n).app M).NormNoninc :=
  -- Porting note: the continuity hypothesis must be supplied explicitly
  SemiNormedGroupCat.locallyConstant_obj_map_normNoninc V _ _ _

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
  simp only [tinv, res, ← whiskerRight_comp, ← NatTrans.op_comp]
  rfl

theorem tinv_normNoninc [Fact (c₂ ≤ r' * c₁)] (M) : ((tinv V r' c₁ c₂ n).app M).NormNoninc :=
  -- Porting note: the continuity hypothesis must be supplied explicitly
  SemiNormedGroupCat.locallyConstant_obj_map_normNoninc V _ _ _

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
    (whiskerRight (NatTrans.op <| ϕ.evalFP r' c₂ c₁) (locallyConstant.obj V) : _)
  else 0

theorem evalLCFP_eq_evalLCFP' (h : ϕ.Suitable c₂ c₁) :
    ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP' V r' c₁ c₂ := by delta evalLCFP evalLCFP'; rw [dif_pos h]

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
  haveI : (BasicUniversalMap.comp f g).Suitable c₃ c₁ := suitable_comp c₂
  simp only [evalLCFP'_def, evalFP_comp r' _ c₂, NatTrans.op_comp, whiskerRight_comp]

theorem evalLCFP_comp (f : BasicUniversalMap m n) (g : BasicUniversalMap l m)
    [hf : f.Suitable c₂ c₁] [hg : g.Suitable c₃ c₂] :
    @evalLCFP V r' _ _ (BasicUniversalMap.comp f g) c₁ c₃ (suitable_comp c₂) =
      f.evalLCFP V r' c₁ c₂ ≫ g.evalLCFP V r' c₂ c₃ :=
  by simp only [evalLCFP_eq_evalLCFP']; apply evalLCFP'_comp

theorem res_comp_evalLCFP [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ c₃)] [ϕ.Suitable c₄ c₂] [ϕ.Suitable c₃ c₁] :
    res V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m := by
  simp only [res, evalLCFP, ← whiskerRight_comp, ← NatTrans.op_comp,
    castLe_comp_evalFP _ c₄ c₃ c₂ c₁]

theorem tinv_comp_evalLCFP [Fact (0 < r')] [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)]
    [ϕ.Suitable c₄ c₂] [ϕ.Suitable c₃ c₁] :
    tinv V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ tinv V r' c₃ c₄ m := by
  simp only [tinv, evalLCFP, ← whiskerRight_comp, ← NatTrans.op_comp,
    tinv_comp_evalFP _ _ c₄ c₃ c₂ c₁]

theorem tInv_comp_evalLCFP [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] :
    tInv r V r' c₁ n ≫ ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP V r' c₁ c₂ ≫ tInv r V r' c₂ m :=
  by
  ext M : 2
  simp only [tInv_def, evalLCFP, NatTrans.comp_app, CategoryTheory.whiskerRight_app, CategoryTheory.whiskerLeft_app,
    NatTrans.naturality]

end BasicUniversalMap

namespace UniversalMap

open FreeAbelianGroup

variable (ϕ : UniversalMap m n)

def evalLCFP [ϕ.Suitable c₂ c₁] : lCFP V r' c₁ n ⟶ lCFP V r' c₂ m :=
  ∑ g : { g : BasicUniversalMap m n // g ∈ ϕ.support },
    haveI := suitable_of_mem_support ϕ c₂ c₁ g g.2
    coeff (g : BreenDeligne.BasicUniversalMap m n) ϕ • BasicUniversalMap.evalLCFP V r' g c₁ c₂

def evalLCFP' : lCFP V r' c₁ n ⟶ lCFP V r' c₂ m :=
  ∑ g in ϕ.support, coeff g ϕ • g.evalLCFP' V r' c₁ c₂

theorem evalLCFP_eq_evalLCFP' (h : ϕ.Suitable c₂ c₁) :
    ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP' V r' c₁ c₂ :=
  by
  simp only [evalLCFP, evalLCFP', BasicUniversalMap.evalLCFP_eq_evalLCFP']
  symm
  apply Finset.sum_subtype ϕ.support fun _ => Iff.rfl

@[simp]
theorem evalLCFP'_of (f : BasicUniversalMap m n) :
    evalLCFP' V r' c₁ c₂ (of f) = f.evalLCFP' V r' c₁ c₂ := by
  simp only [evalLCFP', support_of, coeff_of_self, one_smul, Finset.sum_singleton]

@[simp]
theorem evalLCFP_of (f : BasicUniversalMap m n) [f.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (of f) = f.evalLCFP V r' c₁ c₂ := by
  rw [evalLCFP_eq_evalLCFP', evalLCFP'_of, BasicUniversalMap.evalLCFP_eq_evalLCFP']

@[simp]
theorem evalLCFP'_zero : (0 : UniversalMap m n).evalLCFP' V r' c₁ c₂ = 0 := by
  rw [evalLCFP', support_zero, Finset.sum_empty]

@[simp]
theorem evalLCFP_zero : (0 : UniversalMap m n).evalLCFP V r' c₁ c₂ = 0 := by
  rw [evalLCFP_eq_evalLCFP', evalLCFP'_zero]

@[simp]
theorem evalLCFP'_neg (f : UniversalMap m n) :
    evalLCFP' V r' c₁ c₂ (-f) = -f.evalLCFP' V r' c₁ c₂ := by
  simp only [evalLCFP', AddMonoidHom.map_neg, Finset.sum_neg_distrib, neg_smul, support_neg]

@[simp]
theorem evalLCFP_neg (f : UniversalMap m n) [f.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (-f) = -f.evalLCFP V r' c₁ c₂ := by
  simp only [evalLCFP_eq_evalLCFP', evalLCFP'_neg]

theorem evalLCFP'_add (f g : UniversalMap m n) :
    evalLCFP' V r' c₁ c₂ (f + g) = f.evalLCFP' V r' c₁ c₂ + g.evalLCFP' V r' c₁ c₂ :=
  by
  -- Porting note: the Lean 3 proof (`convert ... using 2` etc.) is replaced by an explicit
  -- computation on the union of the supports.
  simp only [evalLCFP']
  have h1 : ∑ x in (f + g).support, coeff x (f + g) • BasicUniversalMap.evalLCFP' V r' x c₁ c₂ =
      ∑ x in f.support ∪ g.support, coeff x (f + g) • BasicUniversalMap.evalLCFP' V r' x c₁ c₂ :=
    Finset.sum_subset (fun x hx => by
        -- Porting note: the `DecidableEq` instances on the two sides differ, so go via `simp`
        have := support_add f g hx
        exact Finset.mem_union.2
          ((@Finset.mem_union _ (fun a b => Classical.propDecidable (a = b)) _ _ _).1 this)) fun x _ hx => by
      rw [(not_mem_support_iff _ _).1 hx, zero_smul]
  have h2 : ∑ x in f.support, coeff x f • BasicUniversalMap.evalLCFP' V r' x c₁ c₂ =
      ∑ x in f.support ∪ g.support, coeff x f • BasicUniversalMap.evalLCFP' V r' x c₁ c₂ :=
    Finset.sum_subset (Finset.subset_union_left _ _) fun x _ hx => by
      rw [(not_mem_support_iff _ _).1 hx, zero_smul]
  have h3 : ∑ x in g.support, coeff x g • BasicUniversalMap.evalLCFP' V r' x c₁ c₂ =
      ∑ x in f.support ∪ g.support, coeff x g • BasicUniversalMap.evalLCFP' V r' x c₁ c₂ :=
    Finset.sum_subset (Finset.subset_union_right _ _) fun x _ hx => by
      rw [(not_mem_support_iff _ _).1 hx, zero_smul]
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [AddMonoidHom.map_add, add_smul]

theorem evalLCFP_add (f g : UniversalMap m n) [f.Suitable c₂ c₁] [g.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (f + g) = f.evalLCFP V r' c₁ c₂ + g.evalLCFP V r' c₁ c₂ := by
  simp only [evalLCFP_eq_evalLCFP', evalLCFP'_add]

theorem evalLCFP_sub (f g : UniversalMap m n) [f.Suitable c₂ c₁] [g.Suitable c₂ c₁] :
    evalLCFP V r' c₁ c₂ (f - g) = f.evalLCFP V r' c₁ c₂ - g.evalLCFP V r' c₁ c₂ := by
  simp only [sub_eq_add_neg, evalLCFP_add, evalLCFP_neg]

theorem evalLCFP'_comp_of (g : BasicUniversalMap m n) (f : BasicUniversalMap l m)
    [hg : g.Suitable c₂ c₁] [hf : f.Suitable c₃ c₂] :
    evalLCFP' V r' c₁ c₃ ((comp (of g)) (of f)) =
      evalLCFP' V r' c₁ c₂ (of g) ≫ evalLCFP' V r' c₂ c₃ (of f) :=
  by
  simp only [comp_of, evalLCFP'_of]
  haveI hfg : (BasicUniversalMap.comp g f).Suitable c₃ c₁ := BasicUniversalMap.suitable_comp c₂
  rw [← BasicUniversalMap.evalLCFP'_comp]

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

theorem evalLCFP'_comp (g : UniversalMap m n) (f : UniversalMap l m) [hg : g.Suitable c₂ c₁]
    [hf : f.Suitable c₃ c₂] :
    (comp g f).evalLCFP' V r' c₁ c₃ = g.evalLCFP' V r' c₁ c₂ ≫ f.evalLCFP' V r' c₂ c₃ :=
  by
  -- Porting note: the induction is restated with explicit motives, and `resetI`/`unfreezingI`
  -- are no longer needed.
  -- Porting note: `suffices` avoids the implicit-lambda introduction of the instance argument.
  suffices key : f.Suitable c₃ c₂ →
      (comp g f).evalLCFP' V r' c₁ c₃ = g.evalLCFP' V r' c₁ c₂ ≫ f.evalLCFP' V r' c₂ c₃ from
    key hf
  refine FreeAbelianGroup.induction_on_freePredicate
    (P := fun (g : UniversalMap m n) => f.Suitable c₃ c₂ →
      (comp g f).evalLCFP' V r' c₁ c₃ = g.evalLCFP' V r' c₁ c₂ ≫ f.evalLCFP' V r' c₂ c₃)
    (Suitable c₂ c₁) (BreenDeligne.UniversalMap.suitable_freePredicate c₂ c₁) g hg ?_ ?_ ?_ ?_
  · intro _
    simp only [evalLCFP'_zero, zero_comp, Pi.zero_apply, AddMonoidHom.zero_apply,
      AddMonoidHom.map_zero]
  · intro g hg hf
    -- now do another nested induction on `f`
    refine FreeAbelianGroup.induction_on_freePredicate
      (P := fun (f : UniversalMap l m) => (comp (of g) f).evalLCFP' V r' c₁ c₃ =
        evalLCFP' V r' c₁ c₂ (of g) ≫ f.evalLCFP' V r' c₂ c₃)
      (Suitable c₃ c₂) (BreenDeligne.UniversalMap.suitable_freePredicate c₃ c₂) f hf ?_ ?_ ?_ ?_
    · simp only [evalLCFP'_zero, comp_zero, AddMonoidHom.map_zero]
    · intro f hf
      rw [suitable_of_iff] at hf hg
      haveI := hf
      haveI := hg
      apply evalLCFP'_comp_of
    · intro f hf IH
      simp only [IH, evalLCFP'_neg, AddMonoidHom.map_neg, comp_neg]
    · intro f₁ f₂ hf₁ hf₂ IH₁ IH₂
      haveI := hf₁
      haveI := hf₂
      haveI Hg₁f : (comp (of g) f₁).Suitable c₃ c₁ := Suitable.comp c₂
      haveI Hg₂f : (comp (of g) f₂).Suitable c₃ c₁ := Suitable.comp c₂
      simp only [AddMonoidHom.map_add, evalLCFP'_add, IH₁, IH₂, comp_add]
  · intro g hg IH hf
    specialize IH hf
    simp only [IH, AddMonoidHom.map_neg, evalLCFP'_neg, AddMonoidHom.neg_apply, neg_inj, neg_comp]
  · intro g₁ g₂ hg₁ hg₂ IH₁ IH₂ hf
    haveI := hg₁
    haveI := hg₂
    haveI := hf
    haveI Hg₁f : (comp g₁ f).Suitable c₃ c₁ := Suitable.comp c₂
    haveI Hg₂f : (comp g₂ f).Suitable c₃ c₁ := Suitable.comp c₂
    simp only [AddMonoidHom.map_add, AddMonoidHom.add_apply, evalLCFP'_add, IH₁ hf, IH₂ hf,
      add_comp]

theorem evalLCFP_comp (g : UniversalMap m n) (f : UniversalMap l m) [hg : g.Suitable c₂ c₁]
    [hf : f.Suitable c₃ c₂] :
    @evalLCFP V r' c₁ c₃ _ _ (comp g f) (Suitable.comp c₂) =
      g.evalLCFP V r' c₁ c₂ ≫ f.evalLCFP V r' c₂ c₃ :=
  by simp only [evalLCFP_eq_evalLCFP']; apply evalLCFP'_comp

theorem res_comp_evalLCFP [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ c₃)] [ϕ.Suitable c₃ c₁] [ϕ.Suitable c₄ c₂] :
    res V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ res V r' c₃ c₄ m :=
  by
  simp only [evalLCFP, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.Suitable c₃ c₁ := suitable_of_mem_support ϕ _ _ g hg
  haveI : g.Suitable c₄ c₂ := suitable_of_mem_support ϕ _ _ g hg
  simp only [Subtype.coe_mk, g.res_comp_evalLCFP V r' c₁ c₂ c₃ c₄]

theorem tinv_comp_evalLCFP [Fact (0 < r')] [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)]
    [ϕ.Suitable c₃ c₁] [ϕ.Suitable c₄ c₂] :
    tinv V r' c₁ c₂ n ≫ ϕ.evalLCFP V r' c₂ c₄ = ϕ.evalLCFP V r' c₁ c₃ ≫ tinv V r' c₃ c₄ m :=
  by
  simp only [evalLCFP, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.Suitable c₃ c₁ := suitable_of_mem_support ϕ _ _ g hg
  haveI : g.Suitable c₄ c₂ := suitable_of_mem_support ϕ _ _ g hg
  congr 1; apply BasicUniversalMap.tinv_comp_evalLCFP V r'

theorem tInv_comp_evalLCFP [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] :
    tInv r V r' c₁ n ≫ ϕ.evalLCFP V r' c₁ c₂ = ϕ.evalLCFP V r' c₁ c₂ ≫ tInv r V r' c₂ m :=
  by
  simp only [evalLCFP, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.Suitable c₂ c₁ := suitable_of_mem_support ϕ _ _ g hg
  congr 1
  apply BasicUniversalMap.tInv_comp_evalLCFP r V r'

-- Porting note: Lean 4 has no `SeminormedAddCommGroup (A ⟶ B)` instance for morphisms of
-- `SemiNormedGroupCat` (only `Norm`), so the norm estimate for sums and `ℤ`-multiples is proved
-- once and for all via `NormedAddGroupHom`, instead of by `norm_sum_le_of_le` in the main proof.
theorem norm_sum_zsmul_le_aux {ι : Type _} (s : Finset ι) {A B : SemiNormedGroupCat}
    (F : ι → (A ⟶ B)) (k : ι → ℤ) (c : ι → ℝ) (h : ∀ i ∈ s, ‖F i‖ ≤ c i) :
    ‖∑ i in s, k i • F i‖ ≤ ∑ i in s, ‖(k i : ℝ)‖ * c i := by
  refine le_trans (@norm_sum_le_of_le ι (NormedAddGroupHom A B) _ s (fun i => k i • F i)
    (fun i => ‖(k i : ℝ)‖ * c i) ?_) le_rfl
  intro i hi
  refine le_trans (norm_zsmul_le _ _) ?_
  exact mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg _)

theorem norm_evalLCFP_le [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] (N : ℕ)
    (h : ϕ.BoundBy N) (M) : ‖((ϕ.evalLCFP V r' c₁ c₂).app M)‖ ≤ N :=
  by
  rw [evalLCFP_eq_evalLCFP', evalLCFP']
  have : (∑ g : BreenDeligne.BasicUniversalMap m n in support ϕ, (coeff g ϕ).natAbs : ℝ) ≤ N := by
    exact_mod_cast h
  simp only [← NatTrans.appHom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul]
  refine le_trans (norm_sum_zsmul_le_aux ϕ.support
    (fun g => NatTrans.appHom M (BasicUniversalMap.evalLCFP' V r' g c₁ c₂)) (fun g => coeff g ϕ)
    (fun _ => 1) ?_) (le_trans (le_of_eq ?_) this)
  · intro g hg
    haveI aux := ϕ.suitable_of_mem_support c₂ c₁ g hg
    show ‖NatTrans.appHom M (BasicUniversalMap.evalLCFP' V r' g c₁ c₂)‖ ≤ 1
    rw [← g.evalLCFP_eq_evalLCFP' V r' c₁ c₂, BasicUniversalMap.evalLCFP]
    apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
    exact SemiNormedGroupCat.locallyConstant_obj_map_normNoninc V _ _ _
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_one, Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs]

end UniversalMap

end BreenDeligne

