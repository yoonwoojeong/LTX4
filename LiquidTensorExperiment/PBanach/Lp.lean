import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Topology.Instances.Real
import LiquidTensorExperiment.Banach

#align_import pBanach.lp

open scoped NNReal BigOperators uniformity TopologicalSpace

noncomputable section

namespace PBanachCat

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler module[module] exprℝ() -/
/-- The type of sequences `ℕ → ℝ` where `∑' n, |f n|^p` converges. -/
def lpType (p : ℝ≥0) :=
  lp (fun n : ℕ => ℝ) p
deriving
  «./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler module[module] exprℝ()»

variable (p : ℝ≥0)

instance : CoeFun (lpType p) fun f => ℕ → ℝ := by dsimp [lp_type]; infer_instance

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
instance : NNNorm (lpType p) :=
  NNNorm.mk fun f => ∑' n : ℕ, «expr∥ ∥₊» (f n) ^ (p : ℝ)

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
@[simps]
instance : Norm (lpType p) :=
  Norm.mk fun f => ∑' n : ℕ, «expr∥ ∥» (f n) ^ (p : ℝ)

variable {p} [Fact (0 < p)]

theorem lpType.summable (f : lpType p) : Summable fun n => |f n| ^ (p : ℝ) :=
  by
  have := f.2; dsimp [lp_type, lp, Memℓp] at this 
  rw [if_neg] at this ; rwa [if_neg] at this 
  · exact ENNReal.coe_ne_top
  · refine' ne_of_gt _
    exact_mod_cast Fact.out (0 < p)

variable [Fact (p ≤ 1)]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem lpType.triangle (f g : lpType p) : «expr∥ ∥» (f + g) ≤ «expr∥ ∥» f + «expr∥ ∥» g :=
  by
  dsimp
  have : ∀ n, |f n + g n| ^ (p : ℝ) ≤ |f n| ^ (p : ℝ) + |g n| ^ (p : ℝ) :=
    by
    intro n
    suffices
      «expr∥ ∥₊» (f n + g n) ^ (p : ℝ) ≤ «expr∥ ∥₊» (f n) ^ (p : ℝ) + «expr∥ ∥₊» (g n) ^ (p : ℝ) by
      exact_mod_cast this
    refine' le_trans _ (NNReal.rpow_add_le_add_rpow _ _ _ _)
    apply NNReal.rpow_le_rpow; apply nnnorm_add_le
    · exact_mod_cast (Fact.out (0 < p)).le
    · exact_mod_cast (Fact.out (0 < p)).le
    · exact_mod_cast Fact.out (p ≤ 1)
  refine' le_trans (tsum_le_tsum this _ _) (le_of_eq _)
  · have hh := lp_type.summable (f + g); dsimp at hh ; exact hh
  · apply Summable.add
    exact lp_type.summable f
    exact lp_type.summable g
  apply tsum_add
  exact lp_type.summable f
  exact lp_type.summable g

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
instance : PseudoMetricSpace (lpType p)
    where
  dist f g := «expr∥ ∥» (f - g)
  dist_self :=
    by
    have : (p : ℝ) ≠ (0 : ℝ) := by refine' ne_of_gt _; exact_mod_cast Fact.out (0 < p)
    intro f; dsimp
    simp only [abs_zero, sub_self, Real.zero_rpow this, tsum_zero]
  dist_comm := by
    intro f g; dsimp
    have : ∀ n, |f n - g n| = |g n - f n| := by
      intro n
      rw [← neg_neg (f n - g n), abs_neg, neg_sub]
    simp_rw [this]
  dist_triangle := by
    intro f g h
    have := lp_type.triangle (f - g) (g - h)
    rw [show f - g + (g - h) = f - h by abel] at this 
    exact this

variable (p)

/-- The p-norm structure on `lp_type p`. -/
def hasPNorm : HasPNorm (lpType p) p :=
  {
    (inferInstance :
      Norm
        (lpType
          p)) with
    norm_smul := by
      intro a f; dsimp
      have : ∀ n, |a * f n| ^ (p : ℝ) = |a| ^ (p : ℝ) * |f n| ^ (p : ℝ) :=
        by
        intro n; rw [abs_mul, Real.mul_rpow]
        any_goals exact abs_nonneg _
      simp_rw [this]
      rw [tsum_mul_left]
    Triangle := by intro f g; apply lp_type.triangle
    uniformity := rfl }

instance : NormedAddCommGroup (lpType p) :=
  normed_add_comm_group.of_core _
    { norm_eq_zero_iff := by
        intro f; dsimp; constructor
        · intro hf
          ext n;
          suffices |f n| ^ (p : ℝ) = 0
            by
            rw [Real.rpow_eq_zero_iff_of_nonneg] at this 
            simpa using this.1
            apply abs_nonneg
          refine' le_antisymm (le_trans _ (le_of_eq hf)) _
          · apply le_tsum (lp_type.summable f) n
            intro m hm; dsimp
            apply Real.rpow_nonneg_of_nonneg
            exact abs_nonneg _
          · apply Real.rpow_nonneg_of_nonneg; apply abs_nonneg
        · intro hf; rw [hf]
          simp only [lp.coeFn_zero, Pi.zero_apply, abs_zero]
          rw [Real.zero_rpow]; simp only [tsum_zero]
          refine' ne_of_gt _
          exact_mod_cast Fact.out (0 < p)
      Triangle := fun f g => HasPNorm.triangle (hasPNorm p) f g
      norm_neg := fun f => by dsimp; simp }

theorem has_continuous_smul_δ_aux₁ (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ), A * δ < ε :=
  by
  --TODO: Golf!
  by_cases hhA : A = 0
  · use 1; constructor; linarith; simp [hhA]; assumption
  use ε / (2 * A); constructor
  have : ε / (2 * A) = (2 * A)⁻¹ * ε := by field_simp; rw [this]; clear this
  apply mul_pos
  simp only [mul_inv_rev, zero_lt_mul_right, inv_pos, zero_lt_bit0, zero_lt_one]
  exact (Ne.symm hhA).lt_of_le hA; assumption
  rw [show A * (ε / (2 * A)) = ε / 2 by field_simp; ring]; linarith

theorem has_continuous_smul_δ_aux₂ (p : ℝ≥0) [Fact (0 < p)] (ε : ℝ) (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ^ ((p : ℝ) + 1) < ε :=
  by
  --TODO: Golf!
  use(ε / 2) ^ (1 / ((p : ℝ) + 1));
  constructor
  · apply Real.rpow_pos_of_pos; linarith
  · rw [← Real.rpow_mul]
    have : 1 / ((p : ℝ) + 1) * (p + 1) = 1 :=
      by
      have : (p : ℝ) + 1 ≠ 0 := by
        apply ne_of_gt
        have : 0 < (p : ℝ) := by exact_mod_cast Fact.out (0 < p)
        linarith
      field_simp
    rw [this, Real.rpow_one]; linarith; linarith

theorem has_continuous_smul_δ_aux₃ (p : ℝ≥0) [Fact (0 < p)] (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ^ (p : ℝ) * B < ε :=
  by
  --TODO: Golf!
  by_cases hhB : B = 0
  · use 1; constructor; simp; simp [hhB]; assumption
  use(ε / (2 * B)) ^ (1 / (p : ℝ))
  constructor
  · apply Real.rpow_pos_of_pos
    have : ε / (2 * B) = (2 * B)⁻¹ * ε := by field_simp; rw [this]; clear this
    apply mul_pos
    simp only [mul_inv_rev, zero_lt_mul_right, inv_pos, zero_lt_bit0, zero_lt_one]
    exact (Ne.symm hhB).lt_of_le hB; assumption
  · rw [← Real.rpow_mul]
    have : 1 / (p : ℝ) * p = 1 :=
      by
      have : (p : ℝ) ≠ 0 := by apply ne_of_gt; exact_mod_cast Fact.out (0 < p)
      field_simp
    rw [this, Real.rpow_one]
    rw [show ε / (2 * B) * B = ε / 2 by field_simp <;> ring]; linarith
    have : ε / (2 * B) = (2 * B)⁻¹ * ε := by field_simp; rw [this]; clear this
    apply mul_nonneg
    simp only [mul_inv_rev, zero_le_mul_right, inv_pos, zero_lt_bit0, zero_lt_one, inv_nonneg]
    assumption
    exact le_of_lt hε

theorem has_continuous_smul_δ_aux (p : ℝ≥0) [Fact (0 < p)] (A B ε : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 < ε) : ∃ (δ : ℝ) (hδ : 0 < δ), A * δ + δ ^ (p : ℝ) * (δ + B) < ε :=
  by
  --TODO: Golf!
  have hh : 0 < ε / 3 := by linarith
  obtain ⟨δ₁, hδ₁, Hδ₁⟩ := has_continuous_smul_δ_aux₁ A _ hA hh
  obtain ⟨δ₂, hδ₂, Hδ₂⟩ := has_continuous_smul_δ_aux₂ p _ hh
  obtain ⟨δ₃, hδ₃, Hδ₃⟩ := has_continuous_smul_δ_aux₃ p B _ hB hh
  refine' ⟨δ₁ ⊓ δ₂ ⊓ δ₃, _, _⟩
  · rw [lt_inf_iff]
    constructor
    rw [lt_inf_iff]
    constructor
    assumption'
  · rw [mul_add]
    have : ε = ε / 3 + ε / 3 + ε / 3 := by field_simp; ring
    rw [this]; clear this
    simp only [← add_assoc]
    apply add_lt_add
    apply add_lt_add
    · refine' lt_of_le_of_lt _ Hδ₁
      refine' mul_le_mul (le_refl _) _ _ _
      rw [inf_assoc]
      apply inf_le_left
      rw [le_inf_iff]; constructor
      rw [le_inf_iff]; constructor
      all_goals
        first
        | assumption
        | · apply le_of_lt; assumption
    · have : (δ₁ ⊓ δ₂ ⊓ δ₃) ^ (p : ℝ) * (δ₁ ⊓ δ₂ ⊓ δ₃) = (δ₁ ⊓ δ₂ ⊓ δ₃) ^ ((p : ℝ) + 1) :=
        by
        rw [Real.rpow_add, Real.rpow_one]
        rw [lt_inf_iff]; constructor
        rw [lt_inf_iff]; constructor
        assumption'
      rw [this]; clear this
      refine' lt_of_le_of_lt _ Hδ₂
      apply Real.rpow_le_rpow
      rw [le_inf_iff]; constructor
      rw [le_inf_iff]; constructor
      · apply le_of_lt; assumption
      · apply le_of_lt; assumption
      · apply le_of_lt; assumption
      rw [inf_comm, ← inf_assoc]; exact inf_le_right
      have : 0 < (p : ℝ) := by exact_mod_cast Fact.out (0 < p)
      linarith
    · refine' lt_of_le_of_lt _ Hδ₃
      apply mul_le_mul
      · apply Real.rpow_le_rpow
        rw [le_inf_iff]; constructor
        rw [le_inf_iff]; constructor
        · apply le_of_lt; assumption
        · apply le_of_lt; assumption
        · apply le_of_lt; assumption
        exact inf_le_right
        apply le_of_lt
        exact_mod_cast Fact.out (0 < p)
      · exact le_refl _
      · assumption
      · apply Real.rpow_nonneg_of_nonneg; apply le_of_lt; assumption

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
instance : ContinuousSMul ℝ (lpType p) := by
  constructor
  rw [Metric.continuous_iff]
  rintro ⟨a, f⟩ ε hε
  obtain ⟨δ, hδ, Hδ⟩ :
    ∃ (δ : ℝ) (hδ : 0 < δ), |a| ^ (p : ℝ) * δ + δ ^ (p : ℝ) * (δ + «expr∥ ∥» f) < ε :=
    by
    apply has_continuous_smul_δ_aux
    apply Real.rpow_nonneg_of_nonneg; exact abs_nonneg _
    exact norm_nonneg _
    exact hε
  refine' ⟨δ, hδ, _⟩
  rintro ⟨b, g⟩ (h : max _ _ < _); dsimp only [Dist.dist] at h ⊢
  refine' lt_trans _ Hδ
  rw [← norm_neg, neg_sub]
  have : «expr∥ ∥» (a • f - b • g) ≤ «expr∥ ∥» (a • f - a • g) + «expr∥ ∥» (a • g - b • g) :=
    by
    refine' le_trans (le_of_eq _) (norm_add_le _ _)
    congr 1; abel
  refine' lt_of_le_of_lt this _; clear this
  apply add_lt_add_of_le_of_lt
  · rw [← smul_sub, (HasPNorm p).norm_smul a (f - g)]
    apply mul_le_mul; exact le_refl _
    rw [← neg_neg (f - g), norm_neg, neg_sub]
    refine' le_trans (le_max_right _ _) (le_of_lt h)
    exact norm_nonneg (f - g)
    apply Real.rpow_nonneg_of_nonneg; exact abs_nonneg _
  · rw [← sub_smul, (HasPNorm p).norm_smul (a - b) g, smul_eq_mul]
    apply mul_lt_mul'
    · apply Real.rpow_le_rpow
      exact abs_nonneg _
      refine' le_trans _ (le_of_lt h)
      rw [← neg_neg (a - b), abs_neg, neg_sub]
      exact le_max_left _ _
      refine' le_of_lt (by exact_mod_cast Fact.out (0 < p))
    · rw [show g = g - f + f by abel]
      refine' lt_of_le_of_lt (norm_add_le _ _) _
      refine' add_lt_add_of_lt_of_le _ (le_refl _)
      refine' lt_of_le_of_lt (le_max_right _ _) h
    · exact norm_nonneg _
    · have : (0 : ℝ) = 0 ^ (p : ℝ) := by
        rw [Real.zero_rpow]
        refine' ne_of_gt (by exact_mod_cast Fact.out (0 < p))
      rw [this]; clear this
      apply Real.rpow_lt_rpow
      exact le_refl _
      exact hδ
      exact_mod_cast Fact.out (0 < p)

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem uniformContinuous_coe : UniformContinuous (fun f n => f n : lpType p → ℕ → ℝ) :=
  by
  rw [uniformContinuous_pi]; intro i
  rw [normed_add_comm_group.uniformity_basis_dist.uniform_continuous_iff
      NormedAddCommGroup.uniformity_basis_dist]
  intro ε hε; dsimp
  refine' ⟨ε ^ (p : ℝ), _, _⟩
  · apply Real.rpow_pos_of_pos; assumption
  rintro f g (hfg : «expr∥ ∥» (f - g) < ε ^ _)
  suffices |f i - g i| ^ (p : ℝ) < ε ^ (p : ℝ)
    by
    rw [Real.rpow_lt_rpow_iff] at this ; assumption; exact abs_nonneg _; exact le_of_lt hε
    exact_mod_cast Fact.out (0 < p)
  refine' lt_of_le_of_lt _ hfg
  apply le_tsum (lp_type.summable (f - g)) i
  intro j _; apply Real.rpow_nonneg_of_nonneg; exact abs_nonneg _

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem sum_rpow_le_norm (p : ℝ≥0) [Fact (0 < p)] (F : lpType p) (S : Finset ℕ) :
    ∑ i in S, |F i| ^ (p : ℝ) ≤ «expr∥ ∥» F :=
  by
  apply sum_le_tsum
  intro i hi; apply Real.rpow_nonneg_of_nonneg; exact abs_nonneg _
  exact lp_type.summable _

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem sum_rpow_le_of_tendsto (p : ℝ≥0) [Fact (0 < p)] {C : ℝ} {F : ℕ → lpType p}
    (hCF : ∀ᶠ k in Filter.atTop, «expr∥ ∥» (F k) ≤ C) {f : ℕ → ℝ}
    (hf : Filter.Tendsto (fun i j => F i j) (Filter.atTop : Filter ℕ) (𝓝 f)) (s : Finset ℕ) :
    ∑ i in s, |f i| ^ (p : ℝ) ≤ C :=
  by
  let G : (∀ a, ℝ) → ℝ := fun f => ∑ a in s, «expr∥ ∥» (f a) ^ (p : ℝ)
  have hG : Continuous G := by
    refine' continuous_finset_sum s _
    intro a ha
    have : Continuous fun f : ∀ a, ℝ => f a := continuous_apply a
    refine' this.norm.rpow_const _
    intro _; right; apply le_of_lt; exact_mod_cast Fact.out (0 < p)
  refine' le_of_tendsto (hG.continuous_at.tendsto.comp hf) _
  refine' hCF.mono _
  intro k hCFk
  refine' (sum_rpow_le_norm _ (F k) s).trans _; assumption

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem norm_le_of_forall_sum_le (p : ℝ≥0) [Fact (0 < p)] (f : lpType p) (C)
    (hf : ∀ s : Finset ℕ, ∑ i in s, |f i| ^ (p : ℝ) ≤ C) : «expr∥ ∥» f ≤ C := by
  apply tsum_le_of_sum_le; exact lp_type.summable f; assumption

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem norm_le_of_tendsto (p : ℝ≥0) [Fact (0 < p)] {C : ℝ} (F : ℕ → lpType p)
    (hCF : ∀ᶠ k in Filter.atTop, «expr∥ ∥» (F k) ≤ C) (f : lpType p)
    (hf : Filter.Tendsto (fun j i => F j i) (Filter.atTop : Filter ℕ) (𝓝 fun i => f i)) :
    «expr∥ ∥» f ≤ C := by
  obtain ⟨i, hi⟩ := hCF.exists
  have hC : 0 ≤ C := le_trans _ hi
  apply norm_le_of_forall_sum_le
  apply sum_rpow_le_of_tendsto; exact hCF; exact hf
  apply tsum_nonneg; intro _; apply Real.rpow_nonneg_of_nonneg; exact abs_nonneg _

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
instance : CompleteSpace (lpType p) :=
  by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete ((uniform_continuous_coe p).comp_cauchySeq hu)
  have hf' : Memℓp f p :=
    by
    obtain ⟨C, hC, H⟩ := hu.bounded_range.exists_pos_norm_le
    replace H : ∀ n, «expr∥ ∥» (u n) ≤ C := fun n => H _ ⟨n, rfl⟩
    apply memℓp_gen'; swap; use C
    intro S; simp only [Real.norm_eq_abs, ENNReal.coe_toReal]
    apply sum_rpow_le_of_tendsto; apply Filter.eventually_of_forall; exact H; assumption
  refine' ⟨⟨f, hf'⟩, _⟩
  rw [metric.nhds_basis_closed_ball.tendsto_right_iff]
  intro ε hε
  have hε' : {p : lp_type p × lp_type p | «expr∥ ∥» (p.1 - p.2) < ε} ∈ 𝓤 (lp_type p) :=
    normed_add_comm_group.uniformity_basis_dist.mem_of_mem hε
  refine' (hu.eventually_eventually hε').mono _; clear hε'
  rintro n (hn : ∀ᶠ j in Filter.atTop, «expr∥ ∥» (u n - u j) < _)
  apply norm_le_of_tendsto
  apply hn.mono; intro j hj; exact hj.le
  rw [tendsto_pi_nhds]; intro k
  exact (hf.apply k).const_sub (u n k)

theorem pBanach : PBanach (lpType p) p :=
  { exists_p_norm := Nonempty.intro <| hasPNorm p }

/-- The `lp` space of sequences `ℕ → ℝ`, as an element of `pBanach p`. -/
def lp (p : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] : PBanachCat p
    where
  V := lpType p
  pBanach' := pBanach p

instance : Nontrivial (PBanachCat.lp p) :=
  Nontrivial.mk <|
    ⟨0,
      ⟨fun i => if i = 0 then 1 else 0, by
        change ite _ _ _; rw [if_neg]; rw [if_neg]
        use 1; intro S hS; dsimp
        simp only [Filter.mem_atTop_sets, ge_iff_le, Finset.le_eq_subset, Set.mem_preimage]
        use{0}; intro T hT
        suffices (T.sum fun i : ℕ => |ite (i = 0) (1 : ℝ) 0| ^ ↑p) = 1 by rw [this];
          exact mem_of_mem_nhds hS
        have : (fun i : ℕ => |ite (i = 0) (1 : ℝ) 0| ^ (p : ℝ)) = fun i => if i = 0 then 1 else 0 :=
          by ext ⟨_ | i⟩; simp; simp; rw [Real.zero_rpow]; apply ne_of_gt;
          exact_mod_cast Fact.out (0 < p)
        erw [this, Finset.sum_dite]; simp
        have : Finset.filter (fun x : ℕ => x = 0) T = {0} := by ext; simp; intro ha; apply hT;
          rw [ha]; simp
        rw [this]; simp
        exact ENNReal.coe_ne_top
        apply ne_of_gt
        exact_mod_cast Fact.out (0 < p)⟩,
      fun c => by
      apply_fun fun t => t.1 0 at c 
      change (0 : ℝ) = (1 : ℝ) at c 
      exact zero_ne_one c⟩

end PBanachCat

