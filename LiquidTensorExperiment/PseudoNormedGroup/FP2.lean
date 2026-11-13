import LiquidTensorExperiment.BreenDeligne.Constants
import LiquidTensorExperiment.BreenDeligne.Suitable
import LiquidTensorExperiment.PseudoNormedGroup.FP
import LiquidTensorExperiment.SystemOfComplexes.Rescale

#align_import pseudo_normed_group.FP2

noncomputable section

open scoped Classical NNReal BigOperators

attribute [local instance] typePow

universe u

namespace CategoryTheory

namespace FreeAb

def ofFunctor (C : Type _) [Category C] : C ⥤ FreeAb C
    where
  obj := of
  map X Y f := FreeAbelianGroup.of f
  map_id' X := rfl
  map_comp' X Y Z f g := rfl

end FreeAb

end CategoryTheory

open CategoryTheory BreenDeligne

namespace BreenDeligne

variable (r' : ℝ≥0)

variable (BD : BreenDeligne.Data)

variable (M : ProFiltPseuNormGrpWithTinv r')

variable (c c₁ c₂ c₃ c₄ : ℝ≥0) (l m n : ℕ)

open CategoryTheory BreenDeligne

open Profinite PseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup

/-- The "functor" that sends `M` and `c` to `(filtration M c)^n` -/
def fP2 (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) : ProFiltPseuNormGrpWithTinv r' ⥤ FreeAb Profinite :=
  filtrationPow r' c n ⋙ FreeAb.ofFunctor _

theorem fP2_def (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) :
    fP2 r' c n = filtrationPow r' c n ⋙ FreeAb.ofFunctor _ :=
  rfl

namespace FP2

@[simps (config := { fullyApplied := false })]
def res (r' : ℝ≥0) (c₁ c₂ : ℝ≥0) [Fact (c₁ ≤ c₂)] (n : ℕ) : fP2 r' c₁ n ⟶ fP2 r' c₂ n :=
  whiskerRight (filtrationPow.castLe r' c₁ c₂ n) _

@[simp]
theorem res_refl : res r' c c n = 𝟙 _ := by simp [res, filtrationPow.castLe_refl]; rfl

theorem res_comp_res [h₁ : Fact (c₁ ≤ c₂)] [h₂ : Fact (c₂ ≤ c₃)] :
    res r' c₁ c₂ n ≫ res r' c₂ c₃ n = @res r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n := by
  simp only [res, ← whisker_right_comp, filtrationPow.castLe_comp]

section Tinv

open ProfinitelyFilteredPseudoNormedGroupWithTinv

variable [Fact (0 < r')]

@[simps (config := { fullyApplied := false })]
def tinv [Fact (c₁ ≤ r' * c₂)] : fP2 r' c₁ n ⟶ fP2 r' c₂ n :=
  whiskerRight (filtrationPow.tinv r' c₁ c₂ n) _

theorem tinv_def [Fact (c₁ ≤ r' * c₂)] :
    tinv r' c₁ c₂ n = whiskerRight (filtrationPow.tinv r' c₁ c₂ n) _ :=
  rfl

theorem res_comp_tinv [Fact (c₁ ≤ c₂)] [Fact (c₂ ≤ c₃)] [Fact (c₁ ≤ r' * c₂)]
    [Fact (c₂ ≤ r' * c₃)] : res r' c₁ c₂ n ≫ tinv r' c₂ c₃ n = tinv r' c₁ c₂ n ≫ res r' c₂ c₃ n :=
  by simp only [Tinv, res, ← whisker_right_comp]; rfl

end Tinv

end FP2

open FP2

variable {l m n}

namespace BasicUniversalMap

open BasicUniversalMap

variable (ϕ : BasicUniversalMap m n)

def evalFP2 (c₁ c₂ : ℝ≥0) [ϕ.Suitable c₁ c₂] : fP2 r' c₁ m ⟶ fP2 r' c₂ n :=
  whiskerRight (ϕ.evalFP r' c₁ c₂) _

def evalFP2' (c₁ c₂ : ℝ≥0) : fP2 r' c₁ m ⟶ fP2 r' c₂ n :=
  if H : ϕ.Suitable c₁ c₂ then whisker_right (ϕ.eval_FP r' c₁ c₂) _ else 0

theorem evalFP2_eq_evalFP2' (h : ϕ.Suitable c₁ c₂) : evalFP2 r' ϕ c₁ c₂ = evalFP2' r' ϕ c₁ c₂ := by
  delta eval_FP2 eval_FP2'; rw [dif_pos h]

theorem evalFP2'_def [h : ϕ.Suitable c₁ c₂] :
    evalFP2' r' ϕ c₁ c₂ = whiskerRight (ϕ.evalFP r' c₁ c₂) _ :=
  dif_pos h

theorem evalFP2'_not_suitable (h : ¬ϕ.Suitable c₁ c₂) : evalFP2' r' ϕ c₁ c₂ = 0 :=
  dif_neg h

theorem evalFP2'_comp (f : BasicUniversalMap l m) (g : BasicUniversalMap m n)
    [hf : f.Suitable c₁ c₂] [hg : g.Suitable c₂ c₃] :
    evalFP2' r' (comp g f) c₁ c₃ = evalFP2' r' f c₁ c₂ ≫ evalFP2' r' g c₂ c₃ :=
  by
  haveI : (comp g f).Suitable c₁ c₃ := suitable_comp c₂
  simp only [eval_FP2'_def, eval_FP_comp r' _ c₂, whisker_right_comp]

theorem evalFP2_comp (f : BasicUniversalMap l m) (g : BasicUniversalMap m n) [hf : f.Suitable c₁ c₂]
    [hg : g.Suitable c₂ c₃] :
    @evalFP2 r' _ _ (comp g f) c₁ c₃ (suitable_comp c₂) = evalFP2 r' f c₁ c₂ ≫ evalFP2 r' g c₂ c₃ :=
  by simp only [eval_FP2_eq_eval_FP2']; apply eval_FP2'_comp

theorem res_comp_evalFP2 [Fact (c₁ ≤ c₂)] [Fact (c₃ ≤ c₄)] [ϕ.Suitable c₂ c₄] [ϕ.Suitable c₁ c₃] :
    res r' c₁ c₂ m ≫ evalFP2 r' ϕ c₂ c₄ = evalFP2 r' ϕ c₁ c₃ ≫ res r' c₃ c₄ n := by
  simp only [res, eval_FP2, ← whisker_right_comp, cast_le_comp_eval_FP _ c₁ c₂ c₃ c₄]

theorem tinv_comp_evalFP2 [Fact (0 < r')] [Fact (c₁ ≤ r' * c₂)] [Fact (c₃ ≤ r' * c₄)]
    [ϕ.Suitable c₁ c₃] [ϕ.Suitable c₂ c₄] :
    tinv r' c₁ c₂ m ≫ evalFP2 r' ϕ c₂ c₄ = evalFP2 r' ϕ c₁ c₃ ≫ tinv r' c₃ c₄ n := by
  simp only [Tinv, eval_FP2, ← whisker_right_comp, Tinv_comp_eval_FP _ _ c₁ c₂ c₃ c₄]

end BasicUniversalMap

namespace UniversalMap

open FreeAbelianGroup

variable (ϕ : UniversalMap m n)

def evalFP2 [ϕ.Suitable c₁ c₂] : fP2 r' c₁ m ⟶ fP2 r' c₂ n :=
  ∑ g : { g : BasicUniversalMap m n // g ∈ ϕ.support },
    haveI := suitable_of_mem_support ϕ c₁ c₂ g g.2
    coeff (g : basic_universal_map m n) ϕ • basic_universal_map.eval_FP2 r' g c₁ c₂

def evalFP2' : fP2 r' c₁ m ⟶ fP2 r' c₂ n :=
  ∑ g in ϕ.support, coeff g ϕ • g.evalFP2' r' c₁ c₂

theorem evalFP2_eq_evalFP2' (h : ϕ.Suitable c₁ c₂) : evalFP2 r' c₁ c₂ ϕ = evalFP2' r' c₁ c₂ ϕ :=
  by
  simp only [eval_FP2, eval_FP2', basic_universal_map.eval_FP2_eq_eval_FP2', Subtype.val_eq_coe]
  symm
  apply Finset.sum_subtype ϕ.support fun _ => Iff.rfl

@[simp]
theorem evalFP2'_of (f : BasicUniversalMap m n) : evalFP2' r' c₁ c₂ (of f) = f.evalFP2' r' c₁ c₂ :=
  by simp only [eval_FP2', support_of, coeff_of_self, one_smul, Finset.sum_singleton]

@[simp]
theorem evalFP2_of (f : BasicUniversalMap m n) [f.Suitable c₁ c₂] :
    evalFP2 r' c₁ c₂ (of f) = f.evalFP2 r' c₁ c₂ := by
  rw [eval_FP2_eq_eval_FP2', eval_FP2'_of, basic_universal_map.eval_FP2_eq_eval_FP2']

@[simp]
theorem evalFP2'_zero : evalFP2' r' c₁ c₂ (0 : UniversalMap m n) = 0 := by
  rw [eval_FP2', support_zero, Finset.sum_empty]

@[simp]
theorem evalFP2_zero : evalFP2 r' c₁ c₂ (0 : UniversalMap m n) = 0 := by
  rw [eval_FP2_eq_eval_FP2', eval_FP2'_zero]

@[simp]
theorem evalFP2'_neg (f : UniversalMap m n) : evalFP2' r' c₁ c₂ (-f) = -evalFP2' r' c₁ c₂ f := by
  simp only [eval_FP2', AddMonoidHom.map_neg, Finset.sum_neg_distrib, neg_smul, support_neg]

@[simp]
theorem evalFP2_neg (f : UniversalMap m n) [f.Suitable c₁ c₂] :
    evalFP2 r' c₁ c₂ (-f) = -evalFP2 r' c₁ c₂ f := by
  simp only [eval_FP2_eq_eval_FP2', eval_FP2'_neg]

theorem evalFP2'_add (f g : UniversalMap m n) :
    evalFP2' r' c₁ c₂ (f + g) = evalFP2' r' c₁ c₂ f + evalFP2' r' c₁ c₂ g :=
  by
  simp only [eval_FP2']
  rw [Finset.sum_subset (support_add f g)]
  -- two goals
  simp only [AddMonoidHom.map_add _ f g, add_smul]
  convert Finset.sum_add_distrib using 2
  -- three goals
  apply Finset.sum_subset (Finset.subset_union_left _ _);
  swap
  apply Finset.sum_subset (Finset.subset_union_right _ _)
  all_goals rintro x - h; rw [not_mem_support_iff] at h ; simp [h]

theorem evalFP2_add (f g : UniversalMap m n) [f.Suitable c₁ c₂] [g.Suitable c₁ c₂] :
    evalFP2 r' c₁ c₂ (f + g) = evalFP2 r' c₁ c₂ f + evalFP2 r' c₁ c₂ g := by
  simp only [eval_FP2_eq_eval_FP2', eval_FP2'_add]

theorem evalFP2_sub (f g : UniversalMap m n) [f.Suitable c₁ c₂] [g.Suitable c₁ c₂] :
    evalFP2 r' c₁ c₂ (f - g) = evalFP2 r' c₁ c₂ f - evalFP2 r' c₁ c₂ g := by
  simp only [sub_eq_add_neg, eval_FP2_add, eval_FP2_neg]

theorem evalFP2'_comp_of (g : BasicUniversalMap m n) (f : BasicUniversalMap l m)
    [hf : f.Suitable c₁ c₂] [hg : g.Suitable c₂ c₃] :
    evalFP2' r' c₁ c₃ ((UniversalMap.comp (of g)) (of f)) =
      evalFP2' r' c₁ c₂ (of f) ≫ evalFP2' r' c₂ c₃ (of g) :=
  by
  simp only [universal_map.comp_of, eval_FP2'_of]
  haveI hfg : (basic_universal_map.comp g f).Suitable c₁ c₃ := basic_universal_map.suitable_comp c₂
  rw [← basic_universal_map.eval_FP2'_comp]

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

theorem evalFP2'_comp (g : UniversalMap m n) (f : UniversalMap l m) [hf : f.Suitable c₁ c₂]
    [hg : g.Suitable c₂ c₃] :
    evalFP2' r' c₁ c₃ (UniversalMap.comp g f) = evalFP2' r' c₁ c₂ f ≫ evalFP2' r' c₂ c₃ g :=
  by
  revert hg
  apply
      FreeAbelianGroup.induction_on_freePredicate (universal_map.suitable c₁ c₂)
        (universal_map.suitable_free_predicate c₁ c₂) f hf <;>
    clear! f
  · intro h₂
    simp only [eval_FP2'_zero, zero_comp, Pi.zero_apply, AddMonoidHom.zero_apply,
      AddMonoidHom.map_zero]
  · intro f hf hg
    -- now do another nested induction on `f`
      apply
        FreeAbelianGroup.induction_on_freePredicate (universal_map.suitable c₂ c₃)
          (universal_map.suitable_free_predicate c₂ c₃) g hg <;>
      clear! g
    ·
      simp only [universal_map.eval_FP2'_zero, comp_zero, AddMonoidHom.map_zero,
        AddMonoidHom.zero_apply]
    · intro g hg
      rw [suitable_of_iff] at hf hg 
      skip
      apply eval_FP2'_comp_of
    · intro g hg IH
      simp only [IH, eval_FP2'_neg, AddMonoidHom.map_neg, comp_neg, AddMonoidHom.neg_apply]
    · rintro (g₁ : universal_map m n) (g₂ : universal_map m n) hg₁ hg₂ IH₁ IH₂; skip
      haveI Hg₁f : (universal_map.comp g₁ (of f)).Suitable c₁ c₃ := suitable.comp c₂
      haveI Hg₂f : (universal_map.comp g₂ (of f)).Suitable c₁ c₃ := suitable.comp c₂
      simp only [AddMonoidHom.map_add, eval_FP2'_add, IH₁, IH₂, comp_add, AddMonoidHom.add_apply]
  · intro f hf IH hg; skip; specialize IH
    simp only [IH, AddMonoidHom.map_neg, eval_FP2'_neg, AddMonoidHom.neg_apply, neg_inj, neg_comp]
  · rintro (f₁ : universal_map l m) (f₂ : universal_map l m) hf₁ hf₂ IH₁ IH₂ hf; skip
    haveI Hgf₁ : (universal_map.comp g f₁).Suitable c₁ c₃ := suitable.comp c₂
    haveI Hgf₂ : (universal_map.comp g f₂).Suitable c₁ c₃ := suitable.comp c₂
    simp only [AddMonoidHom.map_add, AddMonoidHom.add_apply, eval_FP2'_add, IH₁, IH₂, add_comp]

theorem evalFP2_comp (g : UniversalMap m n) (f : UniversalMap l m) [hf : f.Suitable c₁ c₂]
    [hg : g.Suitable c₂ c₃] :
    @evalFP2 r' c₁ c₃ _ _ (UniversalMap.comp g f) (UniversalMap.Suitable.comp c₂) =
      evalFP2 r' c₁ c₂ f ≫ evalFP2 r' c₂ c₃ g :=
  by simp only [eval_FP2_eq_eval_FP2']; apply eval_FP2'_comp

theorem res_comp_evalFP2 [Fact (c₁ ≤ c₂)] [Fact (c₃ ≤ c₄)] [ϕ.Suitable c₁ c₃] [ϕ.Suitable c₂ c₄] :
    res r' c₁ c₂ m ≫ evalFP2 r' c₂ c₄ ϕ = evalFP2 r' c₁ c₃ ϕ ≫ res r' c₃ c₄ n :=
  by
  simp only [eval_FP2, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.suitable c₁ c₃ := suitable_of_mem_support ϕ _ _ g hg
  haveI : g.suitable c₂ c₄ := suitable_of_mem_support ϕ _ _ g hg
  simp only [Subtype.coe_mk, g.res_comp_eval_FP2 r' c₁ c₂ c₃ c₄]

theorem tinv_comp_evalFP2 [Fact (0 < r')] [Fact (c₁ ≤ r' * c₂)] [Fact (c₃ ≤ r' * c₄)]
    [ϕ.Suitable c₁ c₃] [ϕ.Suitable c₂ c₄] :
    tinv r' c₁ c₂ m ≫ evalFP2 r' c₂ c₄ ϕ = evalFP2 r' c₁ c₃ ϕ ≫ tinv r' c₃ c₄ n :=
  by
  simp only [eval_FP2, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  rintro ⟨g, hg⟩ -
  haveI : g.suitable c₁ c₃ := suitable_of_mem_support ϕ _ _ g hg
  haveI : g.suitable c₂ c₄ := suitable_of_mem_support ϕ _ _ g hg
  congr 1; apply basic_universal_map.Tinv_comp_eval_FP2 r'

end UniversalMap

variable (κ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ c)]

def FPsystem.x (c : ℝ≥0) (n : ℕ) : FreeAb Profinite :=
  FreeAb.of <| (filtrationPow r' (κ c n) <| BD.pt n).obj M

def FPsystem.d (c : ℝ≥0) (n : ℕ) : FPsystem.x r' BD M κ c (n + 1) ⟶ FPsystem.x r' BD M κ c n :=
  (UniversalMap.evalFP2 r' (κ c (n + 1)) (κ c n) (BD.d (n + 1) n)).app M

theorem FPsystem.d_comp_d (c : ℝ≥0) (n : ℕ) :
    FPsystem.d r' BD M κ c (n + 1) ≫ FPsystem.d r' BD M κ c n = 0 :=
  by
  delta FPsystem.d
  rw [← nat_trans.comp_app, ← universal_map.eval_FP2_comp]
  convert nat_trans.app_zero _; rfl; rfl
  convert universal_map.eval_FP2_zero _ _ _
  show BD.d _ _ ≫ BD.d _ _ = 0
  rw [HomologicalComplex.d_comp_d]

open Opposite

def fPsystem [hκ : ∀ n, Fact (Monotone (Function.swap κ n))] :
    ℝ≥0 ⥤ ChainComplex (FreeAb Profinite) ℕ
    where
  obj c :=
    ChainComplex.of (FPsystem.x r' BD M κ c) (FPsystem.d r' BD M κ _) (FPsystem.d_comp_d _ _ _ _ _)
  map c₁ c₂ h :=
    { f := fun n => by
        refine' (@FP2.res r' _ _ (id _) (BD.X n)).app M
        have := (hκ n).out; refine' ⟨this h.le⟩
      comm' := by
        rintro i j (rfl : j + 1 = i)
        rw [ChainComplex.of_d, ChainComplex.of_d]
        delta FPsystem.d; rw [← nat_trans.comp_app, ← nat_trans.comp_app]
        congr 1
        apply universal_map.res_comp_eval_FP2 }
  map_id' c := by ext n; dsimp; rw [Filtration.castLe_refl, (FreeAb.of_functor _).map_id]; rfl
  map_comp' c₁ c₂ c₃ h₁₂ h₂₃ := by ext n; dsimp;
    rw [← (FreeAb.of_functor _).map_comp, Filtration.castLe_comp]

def fPsystem.tinv [Fact (0 < r')] (κ₁ κ₂ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ₁ c)]
    [∀ c, BD.Suitable (κ₂ c)] [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ r' * κ₂ c n)] :
    fPsystem r' BD M κ₁ ⟶ fPsystem r' BD M κ₂
    where
  app c :=
    { f := fun n => (fP2.tinv r' _ _ _).app M
      comm' := by
        rintro i j (rfl : j + 1 = i)
        dsimp only [functor.comp_obj, FPsystem]
        rw [ChainComplex.of_d, ChainComplex.of_d]
        delta FPsystem.d
        rw [← nat_trans.comp_app, ← nat_trans.comp_app]
        congr 1
        apply universal_map.Tinv_comp_eval_FP2 }
  naturality' := by
    intro c₁ c₂ h
    ext n
    dsimp only [FPsystem, Tinv_app, HomologicalComplex.comp_f, functor.comp_map, res_app]
    rw [← functor.map_comp, ← functor.map_comp]
    rfl

def fPsystem.res [Fact (r' ≤ 1)] (κ₁ κ₂ : ℝ≥0 → ℕ → ℝ≥0) [∀ c, BD.Suitable (κ₁ c)]
    [∀ c, BD.Suitable (κ₂ c)] [hκ₁ : ∀ n, Fact (Monotone (Function.swap κ₁ n))]
    [hκ₂ : ∀ n, Fact (Monotone (Function.swap κ₂ n))] [∀ c n, Fact (κ₁ c n ≤ κ₂ c n)] :
    fPsystem r' BD M κ₁ ⟶ fPsystem r' BD M κ₂
    where
  app c :=
    { f := fun n => (fP2.res r' _ _ _).app M
      comm' := by
        rintro i j (rfl : j + 1 = i)
        dsimp only [functor.comp_obj, FPsystem]
        rw [ChainComplex.of_d, ChainComplex.of_d]
        delta FPsystem.d
        rw [← nat_trans.comp_app, ← nat_trans.comp_app]
        congr 1
        apply universal_map.res_comp_eval_FP2 }
  naturality' := by
    intro c₁ c₂ h
    ext n
    dsimp only [FPsystem, res_app, HomologicalComplex.comp_f, functor.comp_map]
    rw [← functor.map_comp, ← functor.map_comp]
    rfl

end BreenDeligne

