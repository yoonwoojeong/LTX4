import Mathlib.Analysis.SpecificLimits.Basic
import LiquidTensorExperiment.SystemOfComplexes.Basic
import LiquidTensorExperiment.LocallyConstant.Vhat

#align_import system_of_complexes.completion

/-!

# A technical lemma

This file has the definition of the completion of a system of
complexes of seminormed groups, and it proves a technical lemma
saying that a system of complexes of seminormed groups is admissible
and weak bounded exact, and if the groups in the complex are complete,
then it's bounded exact (for some slightly different constants).
-/


open Finset Filter

open scoped NNReal BigOperators TopologicalSpace

namespace SystemOfComplexes

universe u

noncomputable def completion (C : SystemOfComplexes) : SystemOfComplexes :=
  C ⋙ SemiNormedGroupCat.completion.mapHomologicalComplex _

namespace IsWeakBoundedExact

variable (C C₁ C₂ : SystemOfComplexes.{u})

variable {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0}

-- === We don't need the following two lemmas anytime soon
-- lemma controlled_y (hC : C.is_weak_bounded_exact k K m c₀) :
-- ∀ c ≥ c₀, ∀ i < m,
-- ∀ x : C (k^2 * c) (i+1),
-- ∀ (ε > 0) (δ > 0), ∃ y : C c i, ∥res x - C.d _ _ y∥
--                    ≤ K * ∥C.d _ (i+1) x∥ + ε ∧ ∥y∥ ≤ K*(K + 1)*∥x∥ + δ :=
-- by admit
-- lemma completion (hC : C.is_weak_bounded_exact k K m c₀) :
--   C.completion.is_weak_bounded_exact (k^2) K m c₀ :=
-- by admit
theorem strongOfComplete [hk : Fact (1 ≤ k)] [∀ c i, SeparatedSpace (C c i)]
    (hC : C.IsWeakBoundedExact k K m c₀) (hC' : Admissible C) [∀ c i, CompleteSpace (C c i)] :
    ∀ δ > 0, C.IsBoundedExact (k ^ 2) (K + δ) m c₀ :=
  by
  intro δ hδ
  refine' (hC.of_le hC' _ ⟨le_rfl⟩ le_rfl ⟨le_rfl⟩).toExact hδ _
  · constructor
    calc
      k = k * 1 := by rw [mul_one]
      _ ≤ k * k := (mul_le_mul' le_rfl hk.out)
      _ = k ^ 2 := by rw [pow_two]
  rintro c hc i hi x _ rfl hx
  haveI : Fact (k * c ≤ k ^ 2 * c) := by rw [pow_two, mul_assoc]; infer_instance
  haveI : Fact (k * (k * c) ≤ k ^ 2 * c) := by rw [pow_two, mul_assoc]; exact ⟨le_rfl⟩
  -- we need to consider the case `i = 0` separately
  obtain rfl | ⟨i, rfl⟩ : i = 0 ∨ ∃ i', i = i' + 1 := by cases i; · left; rfl;
    · right; exact ⟨_, rfl⟩
  · refine' ⟨0, rfl, 0, _⟩
    rw [map_zero, ← norm_le_zero_iff']
    apply le_of_forall_pos_le_add
    intro γ hγ
    rw [zero_add]
    obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c ⟨hc⟩ 0 (Nat.zero_le m) (res x) γ hγ
    rwa [res_res, d_eq_zero_apply, sub_zero, d_res, hx, map_zero, norm_zero, MulZeroClass.mul_zero,
      zero_add] at hy 
    decide
  -- we continue with the case `i + 1`
  have hc₀kc : k * c ≥ c₀
  calc
    c₀ ≤ c := hc
    _ ≤ 1 * c := by rw [one_mul]
    _ ≤ k * c := mul_le_mul' hk.out (le_refl _)
  let K' := if K = 0 then 1 else K
  have hK' : (0 : ℝ) < K' := by
    dsimp [K']
    split_ifs
    norm_num
    exact zero_lt_iff.mpr h
  let ε : ℕ → ℝ := fun j => 2⁻¹ * 2⁻¹ ^ j / K' / 2
  have ε_pos : ∀ j, 0 < ε j := by
    intro j
    dsimp [ε]
    refine' div_pos (div_pos (mul_pos _ _) hK') zero_lt_two <;> simp
  have ε_decr : ∀ j, ε (j + 1) ≤ ε j := by
    intro j
    dsimp [ε]
    field_simp
    apply one_div_le_one_div_of_le <;> norm_num [hK', pow_succ]
  have seq : ∀ j : ℕ, ∃ w : C (k * c) i, ‖(res x - C.d i (i + 1) w)‖ ≤ ε j :=
    by
    intro j
    specialize hC (k * c) ⟨hc₀kc⟩ _ hi (res x) (ε j) (ε_pos j)
    obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC
    simp only [d_res, res_res, map_zero, hx, norm_zero, zero_add, MulZeroClass.mul_zero] at hy 
    refine' ⟨y, hy⟩
  choose w hw using seq
  let δ : ℕ → ℝ := fun j => 2⁻¹ * 2⁻¹ ^ j
  have δ_pos : ∀ j, 0 < δ j := by norm_num [δ]
  have hεδ : ∀ j, (K : ℝ) * (2 * ε j) + δ j ≤ 1 * 2⁻¹ ^ j :=
    by
    intro j
    dsimp [ε, δ]
    conv_rhs =>
      congr
      rw [show (1 : ℝ) = 2⁻¹ + 2⁻¹ by norm_num]
    rw [add_mul (2⁻¹ : ℝ) 2⁻¹]
    by_cases hK : K = 0
    · simp only [hK, div_zero, NNReal.coe_zero, zero_div, zero_add, le_add_iff_nonneg_left,
        MulZeroClass.mul_zero, K', if_pos, MulZeroClass.zero_mul]
      apply mul_nonneg
      norm_num
      apply pow_nonneg
      norm_num
    · apply le_of_eq
      congr 1
      simp only [K', if_neg hK]
      rw [mul_div_cancel' _ (two_ne_zero : (2 : ℝ) ≠ 0),
        mul_div_cancel' _ (nnreal.coe_ne_zero.mpr hK)]
  set i₀ := i - 1 with hi₀
  have seq :
    ∀ j : ℕ,
      ∃ z : C c i₀,
        ‖(res (w (j + 1) - w j) - C.d i₀ i z)‖ ≤
          K * ‖(C.d i (i + 1) (w (j + 1) - w j))‖ + δ j :=
    by
    intro j
    have : i ≤ m := i.le_succ.trans hi
    obtain ⟨i', -, hi', rfl, hy⟩ := hC c ⟨hc⟩ i this (w (j + 1) - w j) _ (δ_pos j)
    rw [← hi₀] at hi' ; subst i'; exact hy
  choose z hz using seq
  let y : ℕ → C c i := fun j => res (w j) - ∑ l in range j, C.d _ _ (z l)
  have cau_y : CauchySeq y :=
    by
    apply cauchySeq_of_le_geometric (2⁻¹ : ℝ) 1 nnreal.two_inv_lt_one
    intro j
    have fact : ‖(C.d _ (i + 1) (w (j + 1) - w j))‖ ≤ 2 * ε j :=
      calc
        ‖(C.d _ (i + 1) (w (j + 1) - w j))‖ =
            ‖(C.d _ _ (w (j + 1)) - res x + (res x - C.d _ _ (w j)))‖ :=
          by simp only [sub_add_sub_cancel, _root_.map_sub]
        _ ≤ ‖(C.d _ _ (w (j + 1)) - res x)‖ + ‖(res x - C.d _ _ (w j))‖ :=
          (norm_add_le _ _)
        _ = ‖(res x - C.d _ _ (w (j + 1)))‖ + ‖(res x - C.d _ _ (w j))‖ := by
          rw [norm_sub_rev]
        _ ≤ ε (j + 1) + ε j := (add_le_add (hw <| j + 1) (hw j))
        _ ≤ 2 * ε j := by linarith [ε_decr j]
    calc
      dist (y j) (y (j + 1)) = ‖(y (j + 1) - y j)‖ := by rw [dist_eq_norm']
      _ =
          ‖(res (w (j + 1)) - res (w j) -
              (∑ l : ℕ in range (j + 1), C.d _ _ (z l) - ∑ l : ℕ in range j, C.d _ _ (z l)))‖ :=
        by dsimp [y]; congr 1; abel
      _ = ‖(res (w (j + 1) - w j) - C.d _ _ (z j))‖ := by
        simp [_root_.map_sub, sum_range_succ]
      _ ≤ K * ‖(C.d _ _ (w (j + 1) - w j))‖ + δ j := (hz j)
      _ ≤ K * (2 * ε j) + δ j := by apply add_le_add_right;
        apply mul_le_mul_of_nonneg_left Fact (NNReal.coe_nonneg K)
      _ ≤ 1 * 2⁻¹ ^ j := hεδ j
  have hdyj : ∀ j, C.d _ _ (y j) = res (C.d _ _ <| w j) :=
    by
    intro j
    calc
      C.d _ _ (y j) = C.d _ _ (res (w j) - ∑ l in range j, C.d _ i (z l)) := rfl
      _ = C.d _ _ (res (w j)) - ∑ l in range j, C.d i (i + 1) (C.d _ _ (z l)) := by
        rw [_root_.map_sub, map_sum]
      _ = res (C.d _ _ (w j)) := by simp only [d_res, d_d, sum_const_zero, sub_zero]
  have hblop : ∀ j, ‖(res x - C.d _ _ (y j))‖ ≤ ε j :=
    by
    intro j
    calc
      ‖(res x - C.d _ _ (y j))‖ = ‖(res x - res (C.d _ _ <| w j))‖ := by rw [hdyj]
      _ = ‖(res (res x : C (k * c) (i + 1)) - res (C.d _ _ <| w j) : C c _)‖ := by
        rw [C.res_res]
      _ = ‖(res (res x - (C.d _ _ <| w j)))‖ := by simp only [_root_.map_sub]
      _ ≤ ‖(res x - C.d _ _ (w j))‖ := by apply hC'.res_norm_noninc
      _ ≤ ε j := hw _
  rcases cauchySeq_tendsto_of_complete cau_y with ⟨y₀, hy₀⟩
  refine' ⟨_, rfl, y₀, _⟩
  refine' sub_eq_zero.1 (norm_le_zero_iff'.1 _)
  have lim_norm :
    tendsto (fun j => ‖(res x - C.d _ _ (y j))‖) at_top
      (𝓝 (‖res x - C.d _ _ y₀‖)) :=
    haveI cont : Continuous fun y : C c i => ‖res x - C.d _ _ y‖ :=
      continuous_norm.comp (continuous_const.sub <| NormedAddGroupHom.continuous _)
    (cont.tendsto y₀).comp hy₀
  have lim_ε : tendsto ε at_top (𝓝 0) :=
    by
    rw [show (0 : ℝ) = 2⁻¹ * 0 / K' / 2 by norm_num]
    refine' (tendsto.const_mul 2⁻¹ (tendsto_pow_atTop_nhds_0_of_lt_1 _ _)).div_const.div_const <;>
      norm_num
  exact le_of_tendsto_of_tendsto' lim_norm lim_ε hblop

end IsWeakBoundedExact

end SystemOfComplexes

