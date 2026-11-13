import LiquidTensorExperiment.FreePfpng.Main
import LiquidTensorExperiment.Invpoly.Functor
import LiquidTensorExperiment.Condensed.Condensify
import LiquidTensorExperiment.LaurentMeasures.Thm69
import LiquidTensorExperiment.NormedFreePfpng.Compare
import LiquidTensorExperiment.Lbar.Ses
import LiquidTensorExperiment.LaurentMeasures.Ses2

#align_import invpoly.ses

universe u

noncomputable section

open CategoryTheory

open scoped NNReal BigOperators

namespace Invpoly

open ProFiltPseuNormGrpWithTinv₁

variable (p : ℝ≥0) [Fact (0 < p)] [Fact (p < 1)]

local notation "r" => @r p

/-- The "evaluate at 2" function, sending an S-indexed family of elements of `ℤ[T⁻¹]`
  to an S-indexed family of integers, via the assignment `T⁻¹ ↦ 2`. Note that
  this is a strict (i.e. norm-nonincreasing) morphism of normed groups,
  with the norm on a polynomial `∑aₙT⁻ⁿ` being `∑ₙ∥aₙ∥₊r⁻ⁿ` and the norm
  on an integer `z` being `∥z∥₊ᵖ`; this works because `r = 2⁻ᵖ`, the crucial
  points being that `(∑∥cₙ∥)ᵖ ≤ ∑(∥cₙ∥ᵖ)` as `0 < p ≤ 1`, and `∥z∥ᵖ ≤ ∥z∥` for an integer `z`.   -/
@[simps]
def eval2 (S : FintypeCat.{u}) :
    StrictComphausFilteredPseudoNormedGroupHom (Invpoly r S) (NormedFreePfpng p S)
    where
  toFun F s := (F s).eval 2
  map_zero' := by ext; simp only [Polynomial.eval_zero, Pi.zero_apply]
  map_add' := by intros; ext; simp only [Polynomial.eval_add, Pi.add_apply]
  strict' c F hF := by
    refine' (Finset.sum_le_sum _).trans hF
    rintro s -
    have h0p : 0 < p := Fact.out _
    have hp1 : p ≤ 1 := Fact.out _
    have h0pinv : 0 ≤ p⁻¹ := by rw [← nnreal.inv_pos] at h0p ; exact h0p.le
    calc
      ‖((F s).eval 2)‖₊ ^ (p : ℝ) =
          ‖(∑ n in Finset.range ((F s).natDegree + 1), (F s).coeff n * 2 ^ n)‖₊ ^ (p : ℝ) :=
        _
      _ ≤
          (∑ n in Finset.range ((F s).natDegree + 1), ‖((F s).coeff n * 2 ^ n)‖₊) ^
            (p : ℝ) :=
        _
      _ ≤ ∑ n in Finset.range ((F s).natDegree + 1), ‖((F s).coeff n * 2 ^ n)‖₊ ^ (p : ℝ) :=
        _
      _ ≤ ∑ n in Finset.range ((F s).natDegree + 1), ‖((F s).coeff n)‖₊ * r ^ (-n : ℤ) := _
      _ ≤ ∑' n, ‖((F s).coeff n)‖₊ * r ^ (-n : ℤ) := _
    · rw [Polynomial.eval_eq_sum_range]
    · refine' NNReal.rpow_le_rpow (nnnorm_sum_le _ _) h0p.le
    · refine' NNReal.rpow_sum_le_sum_rpow _ _ h0p hp1
    · refine' Finset.sum_le_sum _
      intro n hn
      rw [Int.nnnorm_hMul, NNReal.mul_rpow]
      refine' mul_le_mul' _ (le_of_eq _)
      · exact nnnorm_int_rpow_le p _
      · have h2n : (2 ^ n : ℤ) = (2 ^ n : ℕ) := by norm_cast
        simp only [h2n, ← NNReal.coe_natAbs, Int.natAbs_ofNat]
        rw [zpow_neg, ← inv_zpow, zpow_ofNat]
        calc
          ((2 ^ n : ℕ) : ℝ≥0) ^ (p : ℝ) = (2 ^ (n : ℝ) : ℝ≥0) ^ (p : ℝ) := _
          _ = (2⁻¹ ^ (p : ℝ) : ℝ≥0)⁻¹ ^ (n : ℝ) := _
          _ = r⁻¹ ^ n := _
        · norm_cast
        · rw [← NNReal.rpow_mul, mul_comm, NNReal.rpow_mul, ← NNReal.inv_rpow, inv_inv]
        · rw [NNReal.rpow_nat_cast]; rfl
    · refine' sum_le_tsum _ _ _
      · intros; exact zero_le'
      · exact F.nnreal_summable s
  continuous' c := continuous_of_discreteTopology

/-- The "evaluate a polynomial in `T⁻¹` by mapping `T⁻¹` to `2`" functor
 from `ℤ[T⁻¹]` to `ℤ`. -/
def eval2NatTrans :
    fintypeInvpoly.{u} r ⋙ pFPNGT₁ToCHFPNG₁ₑₗ.{u} r ⟶
      normedFreePfpngFunctor.{u} p ⋙ pFPNG₁ToCHFPNG₁ₑₗ
    where
  app S := eval2 p S
  naturality S T f := by
    ext x t
    show (map f x t).eval 2 = _
    dsimp only [Functor.comp_map, normedFreePfpngFunctor_map, CompHausFiltPseuNormGrp₁.comp_apply,
      map]
    erw [Polynomial.eval_finset_sum]; rfl
    recover exact 0

section Ses

open CompHausFiltPseuNormGrp₁

-- move this
instance (M N : Type _) [ComphausFilteredPseudoNormedGroup M]
    [ComphausFilteredPseudoNormedGroup N] :
    AddMonoidHomClass (ComphausFilteredPseudoNormedGroupHom M N) M N
    where
  coe f := f
  coe_injective' f g h := by ext; dsimp at h ; rw [h]
  map_add f := f.map_add
  map_zero f := f.map_zero

theorem Tinv2_injective (S : FintypeCat) :
    Function.Injective ((tinv2NatTrans (fintypeInvpoly r)).app S) :=
  by
  rw [injective_iff_map_eq_zero]
  intro f hf
  ext s n
  apply_fun fun φ => φ s at hf 
  simp only [tinv2NatTrans, tinvNatTrans, NatTrans.app_nsmul, NatTrans.id_app, sub_apply,
    NatTrans.app_sub, ComphausFilteredPseudoNormedGroupHom.sub_apply, Pi.smul_apply,
    ComphausFilteredPseudoNormedGroupHom.nsmul_apply, Pi.sub_apply, Pi.zero_apply] at hf 
  simp only [Pi.zero_apply, Polynomial.coeff_zero]
  induction' n with n ih
  · apply_fun fun φ => φ.coeff 0 at hf 
    simp only [Polynomial.coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_smul] at hf 
    erw [Invpoly.tinv_zero, zero_sub, neg_eq_zero, two_nsmul_eq_zero ℤ ℤ] at hf ; exact hf
  · apply_fun fun φ => φ.coeff (n + 1) at hf 
    simp only [Polynomial.coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_smul] at hf 
    erw [Invpoly.tinv_succ, ih, zero_sub, neg_eq_zero, two_nsmul_eq_zero ℤ ℤ] at hf ; exact hf

theorem Tinv2_comp_eval2_eq_zero (S : FintypeCat) :
    (tinv2NatTrans (fintypeInvpoly r)).app S ≫
        (whiskerRight (eval2NatTrans p) cHFPNG₁ToCHFPNGₑₗ).app S =
      0 :=
  by
  ext f s
  show (Polynomial.X * f s - _).eval 2 = (0 : ℤ)
  simp only [NatTrans.app_nsmul, NatTrans.id_app,
    ComphausFilteredPseudoNormedGroupHom.nsmul_apply, CategoryTheory.id_apply, Pi.smul_apply,
    nsmul_eq_mul, Nat.cast_bit0, Nat.cast_one, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_bit0, Polynomial.eval_one, sub_self]

theorem theta_eval2_aux {S : FintypeCat} (s : S) (c : ℝ≥0) {f : Invpoly r S} :
    ∑' n : ℤ, (toLaurentMeasuresFun r S f s n : ℝ) * ((2 : ℝ) ^ n)⁻¹ = ↑(Polynomial.eval 2 (f s)) :=
  by
  rw [Polynomial.eval_eq_sum_range]
  have :
    ∀ n : ℤ,
      n ∉ Finset.Icc (-(f s).natDegree : ℤ) 0 →
        (fun b : ℤ => ↑(Invpoly.toLaurentMeasuresFun r S f s b) * ((2 : ℝ) ^ b)⁻¹) n = 0 :=
    by
    rintro n hn
    rw [Finset.mem_Icc, not_and_or] at hn 
    push_neg at hn 
    dsimp only
    convert MulZeroClass.zero_mul _
    norm_cast
    cases' hn with hn hn
    · have : ∃ m : ℕ, n = -m := by
        use n.natAbs
        rw [Int.natAbs_of_nonpos]
        · simp
        exact le_trans hn.le (by simp)
      rcases this with ⟨m, rfl⟩
      rw [Invpoly.toLaurentMeasuresFun_nonpos]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      simpa using hn
    · have : ∃ m : ℕ, n = m + 1 := by
        use(n - 1).natAbs
        rw [Int.natAbs_of_nonneg]
        ring; linarith
      rcases this with ⟨m, rfl⟩
      apply Invpoly.toLaurentMeasuresFun_pos'
  rw [tsum_eq_sum this]; clear this
  push_cast
  apply Finset.sum_bij fun (n : ℤ) hn => n.natAbs
  -- this is supposed to be the easy one! all that remains
  -- is four boring pieces of easy nonsense e.g.
  --2^{-n}=2^{n.nat_abs} if n < 0 is probably the hardest one
  · intro a ha
    suffices a.natAbs < (f s).natDegree + 1 by simpa
    rw [Finset.mem_Icc] at ha 
    rw [Nat.lt_succ_iff, ← Int.ofNat_le, Int.natAbs_of_nonpos ha.2]
    linarith [ha.1]
  · intro a ha
    rw [Finset.mem_Icc] at ha 
    simp only
    congr
    · have : ∃ m : ℕ, a = -m := by
        use a.natAbs
        rw [Int.natAbs_of_nonpos ha.2]
        simp
      rcases this with ⟨m, rfl⟩
      rw [Invpoly.toLaurentMeasuresFun_nonpos]
      congr
      rw [← Int.ofNat_inj, Int.natAbs_of_nonpos ha.2, neg_neg]
    · rw [← zpow_neg, ← Int.natAbs_of_nonpos ha.2, zpow_ofNat]
  · rintro a b ha hb (habs : a.natAbs = b.natAbs)
    rw [Finset.mem_Icc] at ha hb 
    rw [← Int.ofNat_inj, Int.natAbs_of_nonpos ha.2, Int.natAbs_of_nonpos hb.2] at habs 
    exact neg_inj.mp habs
  · intro a ha
    rw [Finset.mem_range_succ_iff] at ha 
    refine' ⟨-(a : ℤ), _, _⟩
    · rw [Finset.mem_Icc, neg_le_neg_iff, neg_le, neg_zero]
      simp [ha]
    · simp

theorem theta_zero_of_eval2_zero {S : FintypeCat} (c : ℝ≥0) {f : Invpoly r S}
    (hf1 : eval2 p S f = 0) : (LaurentMeasures.Θ p S) ((toLaurentMeasuresAddhom r S) f) = 0 :=
  by
  ext s
  replace hf1 := congr_fun hf1 s
  suffices ∑' n : ℤ, ↑(Invpoly.toLaurentMeasuresFun r S f s n) * ((2 : ℝ) ^ n)⁻¹ = 0 by
    simpa [LaurentMeasures.Θ, LaurentMeasuresSes.θToAdd, θ, Theta.ϑ, Invpoly.toLaurentMeasuresAddhom]
  simp only [theta_eval2_aux p s c, Int.cast_eq_zero]
  exact hf1

theorem Int.eq_neg_nat_or_succ_nat (n : ℤ) : ∃ m : ℕ, n = -m ∨ n = m + 1 :=
  by
  cases le_or_lt n 0
  · use n.natAbs
    left
    rw [Int.natAbs_of_nonpos h, neg_neg]
  · use(n - 1).natAbs
    right
    rw [Int.natAbs_of_nonneg]
    ring; linarith

theorem phi_eq_hMul_Tinv_sub_two {S : FintypeCat} (g : Invpoly r S) :
    ϕ ((toLaurentMeasuresAddhom r S) fun s : ↥S => g s) =
      (toLaurentMeasuresAddhom r S) fun s : ↥S => (Polynomial.X - 2) * g s :=
  by
  ext s n
  delta ϕ
  simp only [LaurentMeasures.sub_apply, LaurentMeasures.shift_to_fun_to_fun,
    LaurentMeasures.nsmul_apply, nsmul_eq_mul, Int.ofNat_zero, zero_add]
  obtain ⟨m, rfl | rfl⟩ := n.eq_neg_nat_or_succ_nat
  · simp only [Invpoly.toLaurentMeasuresAddhom, Invpoly.toLaurentMeasuresFun_nonpos, AddMonoidHom.mk'_apply,
      Invpoly.toLaurentMeasures_to_fun]
    cases m
    · simp only [Nat.zero_eq, Int.ofNat_zero, neg_zero', zero_add, Polynomial.mul_coeff_zero,
        Polynomial.coeff_sub, Polynomial.coeff_X_zero, zero_sub, neg_mul]
      rw [Invpoly.toLaurentMeasuresFun_pos'' r S g s (show (0 : ℤ) < 1 by norm_num)]
      simp only [zero_sub, neg_inj, mul_eq_mul_right_iff,
        show (2 : Polynomial ℤ) = Polynomial.C 2 by simp, Polynomial.coeff_C_zero]
      left
      norm_num
    ·
      simp only [Invpoly.toLaurentMeasuresFun_nonpos, sub_mul, Int.ofNat_succ, neg_add_rev,
        neg_add_cancel_comm, Int.ofNat_bit0, Int.ofNat_zero, zero_add, Polynomial.coeff_sub,
        Polynomial.coeff_X_mul, sub_right_inj, show (2 : Polynomial ℤ) = Polynomial.C 2 by simp,
        Polynomial.coeff_C_mul]
  · norm_cast

-- didn't expect that to close it!
theorem psi_eq_div_x_sub_two {S : FintypeCat} (c : ℝ≥0) {f : Invpoly r S}
    (hf1 : ((eval2NatTrans p).app S) f = 0) :
    ((toLaurentMeasuresAddhom r S) fun s : ↥S => f s /ₘ (Polynomial.X - 2)) =
      ψ ((toLaurentMeasuresAddhom r S) f) (theta_zero_of_eval2_zero p c hf1) :=
  by
  apply injective_ϕ'
  rw [θ_ϕ_split_exact]
  have hf3 : ∀ s : S, (Polynomial.X - 2) * (f s /ₘ (Polynomial.X - 2)) = f s :=
    by
    intro s
    replace hf1 := congr_fun hf1 s
    rw [show (2 : Polynomial ℤ) = Polynomial.C (2 : ℤ) by simp]
    rwa [Polynomial.mul_divByMonic_eq_iff_isRoot]
  suffices
    ((Invpoly.toLaurentMeasuresAddhom r S) fun s => (Polynomial.X - 2) * (f s /ₘ (Polynomial.X - 2))) =
      (Invpoly.toLaurentMeasuresAddhom r S) fun s => f s
    by
    rw [← this]
    apply phi_eq_mul_Tinv_sub_two
  simp [hf3]

theorem shortExact (S : Profinite) :
    ShortExact ((condensifyTinv2 _).app S) ((condensifyMap <| eval2NatTrans p).app S) :=
  by
  let κ : ℝ≥0 → ℝ≥0 := fun c => max c (c ^ (↑p⁻¹ : ℝ))
  have hκ : id ≤ κ := fun c => le_max_left _ _
  have h0p : 0 < p := Fact.out _
  have hp1 : p ≤ 1 := Fact.out _
  have h0pinv : 0 ≤ p⁻¹ := by rw [← nnreal.inv_pos] at h0p ; exact h0p.le
  refine'
    condensifyNonstrict_exact _ _ (r⁻¹ + 2) (tinv2BoundBy _)
      (-- next line can be simplified because 1/2 < r < 1 so the max is always on the right.
      fun c => max c (c * (2 - r⁻¹)⁻¹ * (r⁻¹ + 2)))
      κ (fun c => le_max_left _ _) hκ (Tinv2_injective p) (Tinv2_comp_eval2_eq_zero p) _ _ _
  · rintro S c f ⟨hf1, hf2⟩
    have hf3 : ∀ s : S, (Polynomial.X - 2) * (f s /ₘ (Polynomial.X - 2)) = f s :=
      by
      intro s
      replace hf1 := congr_fun hf1 s
      rw [show (2 : Polynomial ℤ) = Polynomial.C (2 : ℤ) by simp]
      rwa [Polynomial.mul_divByMonic_eq_iff_isRoot]
    refine' ⟨fun s => f s /ₘ (Polynomial.X - 2), _, _⟩
    · change ‖_‖₊ ≤ c at hf2 
      change ‖_‖₊ ≤ _
      have hf1' : ((Invpoly.eval2NatTrans p).app S) f = 0 := by simpa using hf1
      rw [← Invpoly.toLaurentMeasuresAddhom_isometry] at hf2 ⊢
      refine' le_trans _ (NNReal.hMul_le_hMul_right (le_max_right _ _) _)
      rw [mul_inv_cancel_right₀ (lt_of_lt_of_le (zero_lt_two : (0 : ℝ≥0) < 2) le_add_self).ne']
      convert LaurentMeasures.psi_bound p S c (theta_zero_of_eval2_zero p c hf1') hf2
      exact psi_eq_div_X_sub_two p c hf1
    · ext1 s
      convert hf3 s
      simp [sub_mul, tinv2NatTrans, tinvNatTrans]
      rfl
  · rintro S c g (hg : _ ≤ _)
    let f : Invpoly r S := fun s => Polynomial.C (g s)
    refine' ⟨f, _, _⟩
    · show _ ≤ _
      replace hg := NNReal.rpow_le_rpow hg h0pinv
      refine' le_trans _ (le_max_right _ _)
      refine' le_trans _ hg
      refine' le_trans _ (NNReal.rpow_le_rpow (NNReal.rpow_sum_le_sum_rpow _ _ h0p hp1) h0pinv)
      rw [← NNReal.rpow_mul, ← NNReal.coe_mul, mul_inv_cancel h0p.ne', NNReal.coe_one,
        NNReal.rpow_one, Invpoly.nnnorm_def]
      refine' Finset.sum_le_sum _
      rintro s -
      simp only [f, zpow_neg, zpow_ofNat, id.def, Polynomial.coeff_C]
      rw [tsum_eq_single 0]
      · rw [if_pos rfl, pow_zero, inv_one, mul_one]
      · intro n hn; rw [if_neg hn, nnnorm_zero, MulZeroClass.zero_mul]
      · infer_instance
    · ext s; apply Polynomial.eval_C

end Ses

end Invpoly

