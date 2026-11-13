import LiquidTensorExperiment.SystemOfComplexes.Basic

#align_import normed_snake

universe u

noncomputable section

open scoped NNReal

open CategoryTheory Opposite NormedAddGroupHom SystemOfComplexes

variable (M M' N : SystemOfComplexes.{u}) (f : M ⟶ M') (g : M' ⟶ N)

--TODO Add the non weak version for complete system of complexes
/-- The normed snake lemma, weak version. See Proposition 9.10 from Analytic.pdf -/
theorem weakNormedSnake {k k' k'' K K' K'' : ℝ≥0} [hk : Fact (1 ≤ k)] [hk' : Fact (1 ≤ k')]
    [hk'' : Fact (1 ≤ k'')] {m : ℕ} {c₀ : ℝ≥0} (hM : M.IsWeakBoundedExact k K (m + 1) c₀)
    (hM' : M'.IsWeakBoundedExact k' K' (m + 1) c₀) (hM'_adm : M'.Admissible)
    (hf : ∀ c i, (f.apply : M c i ⟶ M' c i).NormNoninc)
    (Hf :
      ∀ (c : ℝ≥0) [Fact (c₀ ≤ c)] (i : ℕ) (hi : i ≤ m + 1 + 1) (x : M (k'' * c) i),
        ‖res x : M c i‖ ≤ K'' * ‖f x‖)
    (hg : ∀ c i, (g.apply : M' c i ⟶ N c i).ker = f.apply.range)
    (hgquot : SystemOfComplexes.IsQuotient g) :
    N.IsWeakBoundedExact (k'' * k * k') (K' * (K * K'' + 1)) m c₀ :=
  by
  intro c hc i hi
  let c₁ := k'' * (k * (k' * c))
  suffices
    ∀ n : N c₁ i,
      ∀ ε > 0,
        ∃ (i₀ : _) (hi₀ : i₀ = i - 1) (y : N c i₀),
          ‖res n - N.d _ _ y‖ ≤ K' * (K * K'' + 1) * ‖(N.d i (i + 1) n)‖ + ε
    by
    dsimp [c₁] at this 
    intro n₁ ε hε
    haveI hc : Fact (k'' * k * k' * c = c₁) :=
      { out := (mul_assoc _ _ _).trans ((mul_assoc _ _ _).trans rfl) }
    rcases this (res n₁) ε hε with ⟨i₀, hi₀, y, hy⟩
    rw [res_res, d_res] at hy 
    refine' ⟨i₀, _, hi₀, rfl, _⟩
    refine' ⟨y, hy.trans (add_le_add_right (mul_le_mul_of_nonneg_left _ _) ε)⟩
    · apply (SystemOfComplexes.admissibleOfQuotient hgquot hM'_adm).res_normNoninc
    · exact (NNReal.zero_le_coe : 0 ≤ K' * (K * K'' + 1))
  intro n ε hε
  let ε₁ := ε / (K' * (K * K'' + 2) + 1)
  have hε₁ : 0 < ε₁ :=
    div_pos hε (lt_of_lt_of_le zero_lt_one (nnreal.one_le_add'.out : 1 ≤ K' * (K * K'' + 2) + 1))
  obtain ⟨m' : M' c₁ i, rfl : g m' = n⟩ := (hgquot _ _).surjective _
  let m₁' := M'.d i (i + 1) m'
  have hm₁' : g m₁' = N.d i (i + 1) (g m') := (d_apply _ _ g m').symm
  obtain
    ⟨m₁'' : M' c₁ (i + 1), hgm₁'' : g m₁'' = N.d i (i + 1) (g m'), hnorm_m₁'' :
      ‖m₁''‖ < ‖(N.d i (i + 1) (g m'))‖ + ε₁⟩ :=
    (hgquot _ _).norm_lift hε₁ (N.d i (i + 1) (g m'))
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : M c₁ (i + 1), f m₁ + m₁'' = m₁' :=
    by
    have hrange : m₁' - m₁'' ∈ f.apply.range :=
      by
      rw [← hg _ _, mem_ker _ _, _root_.map_sub]
      change g m₁' - g m₁'' = 0
      rw [hm₁', hgm₁'', sub_self]
    obtain ⟨m₁, hm₁ : f m₁ = m₁' - m₁''⟩ := (mem_range _ _).1 hrange
    exact ⟨m₁, by rw [hm₁, sub_add_cancel]⟩
  have him : i + 2 ≤ m + 2 := add_le_add_right hi _
  have hm₂ : f (M.d (i + 1) (i + 2) m₁) = -M'.d (i + 1) (i + 2) m₁'' := by
    rw [← d_apply, eq_sub_of_add_eq hm₁, _root_.map_sub, ← CategoryTheory.comp_apply, d_comp_d,
      coe_zero, ← neg_inj, Pi.zero_apply, zero_sub]
  have hle : ‖(res (M.d (i + 1) (i + 2) m₁))‖ ≤ K'' * ‖m₁''‖ := by
    calc
      ‖(res (M.d (i + 1) (i + 2) m₁))‖ ≤ K'' * ‖(f (M.d (i + 1) (i + 2) m₁))‖ :=
        Hf _ _ him _
      _ = K'' * ‖(M'.d (i + 1) (i + 2) m₁'')‖ := by rw [hm₂, norm_neg]
      _ ≤ K'' * ‖m₁''‖ :=
        mul_le_mul_of_nonneg_left (hM'_adm.d_normNoninc _ _ _ _ m₁'') <| NNReal.coe_nonneg K''
  obtain ⟨i', j, hi', rfl, m₀, hm₀⟩ :=
    hM _ ⟨hc.out.trans <| le_mul_of_one_le_left' hk'.out⟩ _ (Nat.succ_le_succ hi) (res m₁) ε₁ hε₁
  rw [← Nat.pred_eq_sub_one, i.pred_succ] at hi' ; subst i'
  replace hm₀ :
    ‖(res m₁ - M.d i (i + 1) m₀)‖ ≤
      K * K'' * ‖(N.d i (i + 1) (g m'))‖ + K * K'' * ε₁ + ε₁
  ·
    calc
      ‖(res m₁ - M.d i (i + 1) m₀)‖ = ‖(res (res m₁) - M.d i (i + 1) m₀)‖ := by
        rw [res_res]
      _ ≤ K * ‖(M.d (i + 1) (i + 2) (res m₁))‖ + ε₁ := hm₀
      _ = K * ‖(res (M.d (i + 1) (i + 2) m₁))‖ + ε₁ := by rw [d_res]
      _ ≤ K * (K'' * ‖m₁''‖) + ε₁ :=
        (add_le_add_right (mul_le_mul_of_nonneg_left hle NNReal.zero_le_coe) _)
      _ ≤ K * (K'' * (‖(N.d i (i + 1) (g m'))‖ + ε₁)) + ε₁ :=
        (add_le_add_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm_m₁''.le NNReal.zero_le_coe)
            NNReal.zero_le_coe)
          ε₁)
      _ = K * K'' * ‖(N.d i (i + 1) (g m'))‖ + K * K'' * ε₁ + ε₁ := by ring
  let mnew₁' := M'.d i (i + 1) (res m' - f m₀)
  have hmnew' : mnew₁' = res m₁'' + f (res m₁ - M.d i (i + 1) m₀) := by
    calc
      mnew₁' = M'.d i (i + 1) (res m' - f m₀) := rfl
      _ = res (M'.d i (i + 1) m') - f (M.d i (i + 1) m₀) := by rw [_root_.map_sub, d_res _, d_apply]
      _ = res (M'.d i (i + 1) m') - f (res m₁) + (f (res m₁) - f (M.d i (i + 1) m₀)) := by abel
      _ = res m₁'' + f (res m₁ - M.d i (i + 1) m₀) := by
        rw [← SystemOfComplexes.map_sub, ← res_apply, ← _root_.map_sub, ←
          sub_eq_of_eq_add' hm₁.symm]
  have hnormle :
    ‖mnew₁'‖ ≤ (K * K'' + 1) * ‖(N.d i (i + 1) (g m'))‖ + (K * K'' + 2) * ε₁ := by
    calc
      ‖mnew₁'‖ = ‖(res m₁'' + f (res m₁ - M.d i (i + 1) m₀))‖ := by rw [hmnew']
      _ ≤ ‖res m₁''‖ + ‖(f (res m₁ - M.d i (i + 1) m₀))‖ := (norm_add_le _ _)
      _ ≤ ‖m₁''‖ + ‖(f (res m₁ - M.d i (i + 1) m₀))‖ :=
        (add_le_add_right (hM'_adm.res_normNoninc _ _ _ _ m₁'') _)
      _ ≤ ‖m₁''‖ + ‖(res m₁ - M.d i (i + 1) m₀)‖ := (add_le_add_left (hf _ _ _) _)
      _ ≤ ‖(N.d i (i + 1) (g m'))‖ + ε₁ + ‖(res m₁ - M.d i (i + 1) m₀)‖ :=
        (add_le_add_right (le_of_lt hnorm_m₁'') _)
      _ ≤
          ‖(N.d i (i + 1) (g m'))‖ + ε₁ +
            (K * K'' * ‖(N.d i (i + 1) (g m'))‖ + K * K'' * ε₁ + ε₁) :=
        (add_le_add_left hm₀ _)
      _ = (K * K'' + 1) * ‖(d _ _ (i + 1) (g m'))‖ + (K * K'' + 2) * ε₁ := by ring
  obtain ⟨i₀, _, hi₀, rfl, mnew₀, hmnew₀⟩ := hM' _ hc _ (hi.trans m.le_succ) (res m' - f m₀) _ hε₁
  replace hmnew₀ :
    ‖(res (res m' - f m₀) - d _ _ _ mnew₀)‖ ≤
      K' * ((K * K'' + 1) * ‖(N.d i (i + 1) (g m'))‖ + (K * K'' + 2) * ε₁) + ε₁ :=
    hmnew₀.trans (add_le_add_right (mul_le_mul_of_nonneg_left hnormle NNReal.zero_le_coe) ε₁)
  let nnew₀ : ↥(N c i₀) := g mnew₀
  have hmnewlift : g (res (res m' - f m₀) - M'.d i₀ i mnew₀) = res (g m') - N.d i₀ i nnew₀ :=
    by
    suffices h : g (res m' - f m₀) = res (g m')
    · rw [SystemOfComplexes.map_sub, ← res_apply, ← d_apply, h, res_res]
    rw [SystemOfComplexes.map_sub]
    have hker : f m₀ ∈ g.apply.ker := by
      rw [hg _ _, mem_range _ _]
      exact ⟨m₀, rfl⟩
    replace hker : g (f m₀) = 0; · rwa [mem_ker] at hker 
    rw [hker, sub_zero, ← res_apply]
  refine' ⟨i₀, hi₀, nnew₀, _⟩
  rw [← hmnewlift]
  refine' ((hgquot _ _).norm_le _).trans (hmnew₀.trans (le_of_eq _))
  have hε₁_ε : (K' * (K * K'' + 2) + 1 : ℝ) * ε₁ = ε :=
    mul_div_cancel' _
      (by
        refine' (lt_of_lt_of_le zero_lt_one _).ne'
        exact (nnreal.one_le_add'.out : 1 ≤ K' * (K * K'' + 2) + 1))
  rw [← hε₁_ε]
  ring

