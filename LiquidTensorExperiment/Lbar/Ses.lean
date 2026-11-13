import LiquidTensorExperiment.Lbar.Functor
import LiquidTensorExperiment.LaurentMeasures.Functor
import LiquidTensorExperiment.LaurentMeasures.AuxLemmas
import LiquidTensorExperiment.Invpoly.Functor
import LiquidTensorExperiment.Condensed.Condensify

#align_import Lbar.ses

/-!
The short exact sequence
```
0 → ℤ[T⁻¹] → ℳ(S, ℤ((T))_r') → ℳ-bar(S)_r' → 0
```
-/


-- move me
theorem Int.coe_nat_injective : Function.Injective (coe : ℕ → ℤ) := fun m n h => Int.ofNat.inj h

theorem Int.natAbs_of_nonpos {a : ℤ} : a ≤ 0 → ↑a.natAbs = -a :=
  by
  intro h
  rw [← Int.natAbs_neg]
  apply Int.natAbs_of_nonneg
  exact neg_nonneg.mpr h

noncomputable section

open AuxThm69

open scoped NNReal

variable (r' : ℝ≥0) [Fact (0 < r')] (S : FintypeCat)

namespace Invpoly

def toLaurentMeasuresFun (F : Invpoly r' S) : S → ℤ → ℤ
  | s, 0 => (F s).coeff 0
  | s, (n + 1 : ℕ) => 0
  | s, -[n+1] => (F s).coeff (n + 1)

theorem toLaurentMeasuresFun_zero (F : Invpoly r' S) (s : S) :
    toLaurentMeasuresFun r' S F s 0 = (F s).coeff 0 :=
  rfl

theorem toLaurentMeasuresFun_pos (F : Invpoly r' S) (s : S) (n : ℕ) :
    toLaurentMeasuresFun r' S F s (n + 1 : ℕ) = 0 :=
  rfl

theorem toLaurentMeasuresFun_pos' (F : Invpoly r' S) (s : S) (n : ℕ) :
    toLaurentMeasuresFun r' S F s (n + 1) = 0 :=
  rfl

theorem toLaurentMeasuresFun_pos'' (F : Invpoly r' S) (s : S) {m : ℤ} (hn : 0 < m) :
    toLaurentMeasuresFun r' S F s m = 0 :=
  by
  convert to_laurent_measures_fun_pos' r' S F s (m - 1).natAbs
  rw [Int.natAbs_of_nonneg]
  · ring
  · linarith

theorem toLaurentMeasuresFun_neg (F : Invpoly r' S) (s : S) (n : ℕ) :
    toLaurentMeasuresFun r' S F s -[n+1] = (F s).coeff (n + 1) :=
  rfl

theorem toLaurentMeasuresFun_neg' (F : Invpoly r' S) (s : S) (n : ℕ) :
    toLaurentMeasuresFun r' S F s (-n.succ) = (F s).coeff (n + 1) :=
  rfl

theorem toLaurentMeasuresFun_nonpos (F : Invpoly r' S) (s : S) (n : ℕ) :
    toLaurentMeasuresFun r' S F s (-n) = (F s).coeff n :=
  by
  cases n
  · exact to_laurent_measures_fun_zero r' S F s
  · exact to_laurent_measures_fun_neg r' S F s n

/-- The natural inclusion from an S-indexed set of polynomials `Fₛ : ℤ[T⁻¹]` to
the corresponding power series `Fₛ : ℤ[[T]][T⁻¹]`. -/
@[simps]
def toLaurentMeasures (F : Invpoly r' S) : LaurentMeasures r' S
    where
  toFun := toLaurentMeasuresFun r' S F
  summable' s := by
    rw [← NNReal.summable_coe]
    rw [← @summable_subtype_and_compl ℝ ℤ _ _ _ _ _ {n : ℤ | n ≤ 0}]
    constructor
    · have := F.nnreal_summable s
      rw [← NNReal.summable_coe] at this 
      convert (Equiv.summable_iff (equiv.nonpos_ge_zero ℤ)).mpr _
      rotate_left
      · exact fun a => (‖((F s).coeff (Int.toNat a))‖₊ * r' ^ (-a.1) : ℝ)
      rotate_left
      · apply funext
        rintro ⟨x, hx⟩
        rcases x with (⟨_ | x⟩ | x)
        · rfl
        · rw [Int.ofNat_eq_coe, Int.ofNat_succ, Set.mem_setOf_eq] at hx 
          refine' (not_lt.mpr hx _).elim
          exact Int.add_pos_of_nonneg_of_pos (Int.ofNat_zero_le x) zero_lt_one
        · simp only [Subtype.coe_mk, zpow_negSucc, Nonneg.coe_mul, coe_nnnorm, NNReal.coe_pow,
            Subtype.val_eq_coe, zpow_neg, Function.comp_apply, NNReal.coe_eq_zero,
            equiv.nonpos_ge_zero_eval, inv_inv, inv_eq_zero, pow_eq_zero_iff, Nat.succ_pos']
          congr
      · refine' (Equiv.summable_iff (int_subtype_nonneg_equiv.symm : ℕ ≃ { z : ℤ // 0 ≤ z })).mp _
        simpa
    -- setup equiv with `ℕ` using `k → -k` and use `F.nnreal_summable s`
    · convert summable_zero; ext ⟨(_ | n) | n, hn⟩
      · simp only [Int.ofNat_eq_coe, Int.ofNat_zero, le_refl, not_true, Set.mem_compl_iff,
          Set.mem_setOf_eq] at hn 
        exact hn.elim
      · erw [nnnorm_zero, MulZeroClass.zero_mul, NNReal.coe_zero]
      · simp only [not_le, Int.negSucc_not_pos, Set.mem_compl_iff, Set.mem_setOf_eq] at hn 
        exact hn.elim

open scoped BigOperators

/-- The projection from a Laurent measure `Fₛ : ℤ[[T]][T⁻¹]` to `Fₛ : ℤ[T⁻¹]` obtained
by throwing away all the positive terms. -/
def ofLaurentMeasures [Fact (r' < 1)] (F : LaurentMeasures r' S) : Invpoly r' S := fun s =>
  ∑ n in
    Finset.range
      ((1 : ℤ) -
          (LaurentMeasures.exists_bdd_filtration
              (show (0 : ℝ) < r' by norm_cast <;> exact Fact.elim inferInstance)
              (by norm_cast <;> exact Fact.elim inferInstance) F).some).toNat,
    F s (-n) * Polynomial.X ^ n

-- move me
open Polynomial Finset

theorem Polynomial.sum_range_const_hMul_x_pow_coeff {R : Type _} [Semiring R] (f : ℕ → R)
    (d n : ℕ) : (∑ i in range d, C (f i) * X ^ i).coeff n = if n < d then f n else 0 :=
  by
  rw [finset_sum_coeff]
  split_ifs
  · suffices ∀ b, (C (f b) * X ^ b).coeff n = if n = b then f b else 0
      by
      simp_rw [this]
      simp [h]
    intro i
    simp [coeff_X_pow]
  · refine' sum_eq_zero fun i hi => coeff_eq_zero_of_degree_lt _
    apply lt_of_le_of_lt (degree_mul_le _ _)
    apply lt_of_le_of_lt (add_le_add degree_C_le (degree_X_pow_le i))
    norm_cast
    rw [Finset.mem_range] at hi 
    rw [zero_add]
    exact lt_of_lt_of_le hi (le_of_not_lt h)

-- ℤ[X] version without C
theorem Polynomial.sum_range_int_hMul_x_pow_coeff (f : ℕ → ℤ) (d n : ℕ) :
    (∑ i in range d, (f i : Polynomial ℤ) * X ^ i).coeff n = if n < d then f n else 0 :=
  Polynomial.sum_range_const_hMul_x_pow_coeff f d n

theorem ofLaurentMeasures_strict [Fact (r' < 1)] (F : LaurentMeasures r' S) :
    ‖ofLaurentMeasures r' S F‖₊ ≤ ‖F‖₊ :=
  by
  unfold NNNorm.nnnorm
  apply Finset.sum_le_sum; rintro s -
  change tsum _ ≤ tsum _
  delta of_laurent_measures
  simp_rw [polynomial.sum_range_int_mul_X_pow_coeff]
  apply tsum_le_tsum_of_inj fun n : ℕ => -(n : ℤ)
  · intro a b h; simpa using h
  · intros; apply zero_le
  · intro i
    split_ifs
    · rfl
    convert zero_le _
    simp only [norm_zero, mul_eq_zero, Nonneg.mk_eq_zero, eq_self_iff_true, true_or_iff]
  · apply summable_of_ne_finset_zero
    intro i hi
    split_ifs
    · exfalso
      apply hi
      rw [← Finset.mem_range] at h 
      exact h
    · simp
  · exact F.nnreal_summable s
  · infer_instance

theorem toLaurentMeasures_ofLaurentMeasures [Fact (r' < 1)] (F : Invpoly r' S) :
    ofLaurentMeasures r' S (toLaurentMeasures r' S F) = F :=
  by
  let d :=
    (LaurentMeasures.exists_bdd_filtration
        (show (0 : ℝ) < r' by norm_cast <;> exact Fact.elim inferInstance)
        (by norm_cast <;> exact Fact.elim inferInstance) (to_laurent_measures r' S F)).some
  have hd : ∀ (s : S) (n : ℤ), n < d → (to_laurent_measures r' S F) s n = 0 :=
    (LaurentMeasures.exists_bdd_filtration
        (show (0 : ℝ) < r' by norm_cast <;> exact Fact.elim inferInstance)
        (by norm_cast <;> exact Fact.elim inferInstance) (to_laurent_measures r' S F)).choose_spec
  ext s n
  delta of_laurent_measures
  suffices :
    (∑ n : ℕ in range (1 - d).toNat, C (to_laurent_measures r' S F s (-↑n)) * X ^ n).coeff n =
      (F s).coeff n
  simpa
  rw [polynomial.sum_range_const_mul_X_pow_coeff]
  rw [← to_laurent_measures_fun_nonpos]
  split_ifs; rfl
  symm
  apply hd
  push_neg at h 
  rw [Int.toNat_le] at h 
  linarith

-- note: can't deduce immediately from `to_laurent_measures_of_laurent_measures`
-- because `r' < 1` not assumed.
theorem toLaurentMeasures_injective : Function.Injective (toLaurentMeasures r' S) :=
  by
  intro F G h
  ext s (_ | n)
  · apply_fun fun F => F s 0 at h ; exact h
  · apply_fun fun F => F s (-n.succ) at h ; exact h

def toLaurentMeasuresAddhom : Invpoly r' S →+ LaurentMeasures r' S :=
  AddMonoidHom.mk' (toLaurentMeasures r' S) <|
    by
    intro F G; ext s ((_ | n) | n)
    ·
      simp only [to_laurent_measures_fun, add_apply, Int.ofNat_zero, to_laurent_measures_to_fun,
        LaurentMeasures.add_apply, Polynomial.coeff_add]
    · rfl
    ·
      simp only [to_laurent_measures_fun, add_apply, to_laurent_measures_to_fun,
        LaurentMeasures.add_apply, Polynomial.coeff_add]

theorem toLaurentMeasuresAddhom_isometry (p : Invpoly r' S) :
    ‖((toLaurentMeasuresAddhom r' S) p)‖₊ = ‖p‖₊ :=
  by
  unfold nnnorm
  congr
  ext s
  norm_cast
  refine' tsum_eq_tsum_of_ne_zero_bij (fun n => -((n.1 : ℕ) : ℤ)) _ _ _
  · rintro ⟨x, _⟩ ⟨y, _⟩ h; simpa using h
  · intro n hn
    rw [Function.mem_support] at hn 
    rw [Set.mem_range]
    rcases n with ((_ | n) | n)
    · exact ⟨⟨0, hn⟩, rfl⟩
    · exfalso
      simpa [to_laurent_measures_addhom, to_laurent_measures_fun_pos'] using hn
    · exact ⟨⟨n + 1, hn⟩, rfl⟩
  · rintro ⟨n, hn⟩
    simp only [to_laurent_measures_addhom, AddMonoidHom.mk'_apply, to_laurent_measures_to_fun,
      Subtype.coe_mk, zpow_neg, zpow_ofNat, mul_eq_mul_right_iff, Subtype.mk_eq_mk, inv_eq_zero]
    left
    cases' n with n
    · simp [to_laurent_measures_fun_zero]
    · simp only [to_laurent_measures_fun_neg']

def toLaurentMeasuresHom [Fact (r' < 1)] :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' (Invpoly r' S) (LaurentMeasures r' S) :=
  {
    toLaurentMeasuresAddhom r'
      S with
    strict' := by
      rintro c p hp
      simp only [AddMonoidHom.toFun_eq_coe, LaurentMeasures.mem_filtration_iff]
      simp only [mem_filtration_iff] at hp 
      rwa [to_laurent_measures_addhom_isometry]
    continuous' := fun c => continuous_bot
    map_Tinv' := by
      intro F
      ext s z
      change
        to_laurent_measures_fun r' S (fun s : ↥S => Polynomial.X * F s) s z =
          to_laurent_measures_fun r' S F s (z + 1)
      rcases lt_trichotomy 0 z with (hz | rfl | hz)
      · let n := (z - 1).natAbs
        have hn : z - 1 = n := Int.eq_natAbs_of_zero_le (Int.le_sub_one_of_lt hz)
        rw [sub_eq_iff_eq_add] at hn 
        rw [hn, to_laurent_measures_fun_pos', (by norm_cast : (n : ℤ) + 1 = (n + 1 : ℕ)),
          to_laurent_measures_fun_pos']
      · rw [to_laurent_measures_fun_zero, (by norm_cast : (0 : ℤ) + 1 = (0 + 1 : ℕ)),
          to_laurent_measures_fun_pos]
        simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, MulZeroClass.zero_mul]
      · let n := (z + 1).natAbs
        have hn : (n : ℤ) = -(z + 1) := Int.natAbs_of_nonpos (Int.add_one_le_of_lt hz)
        rw [eq_neg_iff_eq_neg] at hn 
        rw [hn]
        rw [← eq_sub_iff_add_eq] at hn 
        rw [hn, to_laurent_measures_fun_nonpos, (by simp; ring : -(n : ℤ) - 1 = -(n + 1 : ℕ)),
          to_laurent_measures_fun_nonpos, Polynomial.coeff_X_mul] }

@[simps]
def toLaurentMeasuresNatTrans [Fact (r' < 1)] : fintypeInvpoly r' ⟶ fintypeLaurentMeasures r'
    where
  app S := toLaurentMeasuresHom r' S
  naturality' S T f := by
    ext p t n
    classical
    suffices :
      to_laurent_measures_fun r' T (map f p) t n =
        (Finset.filter (fun t_1 : S.α => f t_1 = t) Finset.univ).Sum fun x : S.α =>
          to_laurent_measures_fun r' S p x n
    simpa [to_laurent_measures_hom, to_laurent_measures_addhom]
    rcases n with ((_ | n) | n)
    · convert map_apply f p t 0
    · simp only [Int.ofNat_eq_coe, to_laurent_measures_fun_pos, Finset.sum_const_zero]
    · convert map_apply f p t (n + 1)

end Invpoly

namespace LaurentMeasures

/-- `to_Lbar r S` is the function sending a Laurent measure `Fₛ : ℤ → ℤ` to its
truncation `Fₛ : {n ≥ 1} → ℤ` (often thought of as a power series `Fₛ ∈ Tℤ[[T]]`.) -/
@[simps]
def toLbar (F : LaurentMeasures r' S) : Lbar r' S
    where
  toFun s n := if n = 0 then 0 else F s n
  coeff_zero' s := if_pos rfl
  summable' s :=
    by
    have := NNReal.summable_comp_injective (F.nnreal_summable s) Int.coe_nat_injective
    refine' NNReal.summable_of_le _ this
    intro n
    split_ifs
    · simp only [Int.natAbs_zero, Nat.cast_zero, MulZeroClass.zero_mul, zero_le']
    · simp only [Function.comp_apply, NNReal.coe_natAbs, zpow_ofNat]

/-- `to_Lbar_section r S` is the natural inclusion from `Lbar r S` to `laurent_measures r S`
sending a power series `Fₛ : {n≥1} → ℤ` to the associated function `Fₛ : ℤ → ℤ` which
vanishes on non-positive integers. -/
def toLbarSection (G : Lbar r' S) : LaurentMeasures r' S :=
  ⟨fun s n => G s n.toNat, by
    intro s
    refine' (nnreal.summable_iff_on_nat_less 0 fun n n0 => _).mpr _
    · simp [Int.toNat_of_nonpos n0.le]
    · simp only [Int.toNat_coe_nat, zpow_ofNat]
      simpa only [← NNReal.coe_natAbs] using G.summable' s⟩

theorem toLbarSection_toLbar (G : Lbar r' S) : toLbar r' S (toLbarSection r' S G) = G :=
  by
  ext s (_ | n)
  · exact (G.coeff_zero s).symm
  · show ite (n.succ = 0) 0 (G s (n + 1)) = G s n.succ; exact if_neg n.succ_ne_zero

theorem tsum_nat_eq_tsum_int {α : Type _} [AddCommMonoid α] [TopologicalSpace α] [T2Space α]
    (f : ℤ → α) : ∑' n : ℕ, f n = ∑' z : ℤ, if z < 0 then 0 else f z :=
  by
  let e :
    ↥(Function.support fun x : ℕ => f ↑x) ≃ ↥(Function.support fun y : ℤ => ite (y < 0) 0 (f y)) :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun y =>
        ⟨y.1.natAbs, fun h => by
          cases' y with y hy
          apply hy
          dsimp only
          split_ifs; rfl
          convert h
          exact Int.eq_natAbs_of_zero_le (le_of_not_lt h_1)⟩
      left_inv := by
        rintro ⟨x, hx⟩
        rfl
      right_inv := by
        rintro ⟨y, hy⟩
        simp only [coe_coe, Subtype.coe_mk, Subtype.mk_eq_mk]
        refine' (Int.eq_natAbs_of_zero_le _).symm
        by_contra h
        push_neg at h 
        apply hy
        dsimp only
        rw [if_pos h] }
  apply Equiv.tsum_eq_tsum_of_support e
  rintro ⟨x, hx⟩
  have hx2 : ¬(x : ℤ) < 0 := fun h => Nat.not_lt_zero x (Int.ofNat_lt.1 h)
  simp [hx2]

theorem toLbarSection_mem_filtration (G : Lbar r' S) (c : ℝ≥0)
    (hG : G ∈ PseudoNormedGroup.filtration (Lbar r' S) c) :
    toLbarSection r' S G ∈ PseudoNormedGroup.filtration (LaurentMeasures r' S) c :=
  by
  change _ ≤ _
  convert (hG : _ ≤ _) using 1
  change finset.univ.sum _ = finset.univ.sum _
  congr 1; ext s; norm_cast
  symm
  convert tsum_nat_eq_tsum_int fun n => ‖G s n.toNat‖₊ * r' ^ n
  · ext n
    simp only [Int.natAbs, Nonneg.coe_mul, NNReal.coe_nat_cast, NNReal.coe_pow, Int.toNat_coe_nat,
      zpow_ofNat, coe_nnnorm, mul_eq_mul_right_iff, Int.natAbs, _root_.coe_nnnorm, Int.norm_eq_abs,
      Int.cast_natAbs]
    left; rfl
  · ext z
    simp only [to_Lbar_section, coe_mk, Nonneg.coe_mul, coe_nnnorm, NNReal.coe_zpow]
    split_ifs
    · simp [Int.toNat_of_nonpos h.le, G.coeff_zero]
    · simp

theorem toLbar_surjective : Function.Surjective (toLbar r' S) := fun G =>
  ⟨toLbarSection r' S G, toLbarSection_toLbar r' S G⟩

theorem nnnorm_toLbar (F : LaurentMeasures r' S) : ‖toLbar r' S F‖₊ ≤ ‖F‖₊ :=
  by
  rw [nnnorm_def, Lbar.nnnorm_def]
  refine' Finset.sum_le_sum fun s hs => _
  have := NNReal.summable_comp_injective (F.nnreal_summable s) Int.coe_nat_injective
  refine'
    (tsum_le_tsum _ ((to_Lbar r' S F).Summable s) this).trans
      (NNReal.tsum_comp_le_tsum_of_inj (F.nnreal_summable s) Int.coe_nat_injective)
  intro n
  simp only [NNReal.coe_natAbs, to_Lbar_to_fun, Function.comp_apply, zpow_ofNat]
  split_ifs; · rw [nnnorm_zero, MulZeroClass.zero_mul]; exact zero_le'; · rfl

/-- `to_Lbar_hom` is the `comphaus_filtered_pseudo_normed_group_with_Tinv_hom` version
of `to_Lbar r S`, the function which truncates a Laurent power series in `ℤ[[T]][1/T]`
to its positive terms in `Tℤ[[T]]`. -/
@[simps]
def toLbarHom : ComphausFilteredPseudoNormedGroupWithTinvHom r' (LaurentMeasures r' S) (Lbar r' S)
    where
  toFun := toLbar r' S
  map_zero' := by
    ext
    simp only [to_Lbar_to_fun, zero_apply, if_t_t, Lbar.coe_zero, Pi.zero_apply]
  map_add' F G := by
    ext; simp only [to_Lbar_to_fun, add_apply, Lbar.coe_add, Pi.add_apply]
    split_ifs; · rw [add_zero]; · rfl
  strict' c F (hF : ‖F‖₊ ≤ c) := (nnnorm_toLbar r' S F).trans hF
  continuous' c := by
    let f : _ := _; show Continuous f
    rw [LbarLe.continuous_iff]
    intro N
    let e : ℕ ↪ ℤ := ⟨coe, Int.coe_nat_injective⟩
    let T : Finset ℤ := (Finset.range (N + 1)).map e
    let g : LaurentMeasuresBdd r' S T c → LbarBdd r' ⟨S⟩ c N := fun F =>
      { toFun := fun s n => if n = 0 then 0 else F s ⟨n, _⟩
        coeff_zero' := fun s => if_pos rfl
        sum_le' := _ }
    have : LbarLe.truncate N ∘ f = g ∘ truncate T :=
      by
      dsimp [f]; ext F s ⟨_ | n, hn⟩; · simp only [Fin.mk_zero, LbarBdd.coeff_zero]
      simp only [LbarLe.truncate_to_fun, LbarBdd.coe_mk, coe_coe, Int.ofNat_succ, truncate_to_fun,
        Subtype.coe_mk, Subtype.ext_iff, Fin.val_zero, Nat.succ_ne_zero, if_false]
      exact to_Lbar_to_fun r' S F s (n + 1)
    · rw [this]; exact continuous_of_discrete_topology.comp (truncate_continuous _ _ _ _)
    ·
      simpa only [coe_coe, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk,
        Int.coe_nat_inj', exists_prop, exists_eq_right] using n.2
    · cases S; refine' le_trans (Finset.sum_le_sum _) F.bound; dsimp
      rintro s -
      erw [Finset.sum_attach', Finset.sum_map, ← Fin.sum_univ_eq_sum_range]
      refine' Finset.sum_le_sum fun i hi => _
      simp only [Finset.mem_map, Finset.mem_range, exists_prop, exists_eq_right, NNReal.coe_natAbs,
        EmbeddingLike.apply_eq_iff_eq, Function.Embedding.coeFn_mk, Subtype.coe_mk, zpow_ofNat]
      rw [dif_pos]; swap; · exact i.2
      split_ifs; · rw [nnnorm_zero, MulZeroClass.zero_mul]; exact zero_le'; · rfl
  map_Tinv' F := by
    erw [Tinv_apply, Lbar.tinv_apply]
    ext s (_ | n)
    · simp only [to_Lbar_to_fun, eq_self_iff_true, if_true, Lbar.tinv_zero]
    ·
      simp only [to_Lbar_to_fun, Nat.succ_ne_zero, Int.ofNat_succ, shift_to_fun_to_fun,
        Lbar.tinv_succ]

@[simps]
def toLbarNatTrans : fintypeLaurentMeasures r' ⟶ fintypeLbar r'
    where
  app S := toLbarHom r' S
  naturality' S₁ S₂ f := by
    ext
    simp only [fintypeLaurentMeasures_map, CategoryTheory.comp_apply, to_Lbar_hom_to_fun,
      to_Lbar_to_fun, fintypeLbar_map_to_fun, Lbar.map_to_fun, map_hom, map_apply,
      ComphausFilteredPseudoNormedGroupWithTinvHom.coe_mk]
    split_ifs; · simp only [Finset.sum_const_zero]; · rfl

end LaurentMeasures

namespace Lbar

open CategoryTheory ProFiltPseuNormGrpWithTinv₁

theorem shortExact (S : Profinite) [Fact (r' < 1)] :
    ShortExact
      ((condensifyMap
            (whiskerRight (Invpoly.toLaurentMeasuresNatTrans r') (pFPNGT₁ToCHFPNG₁ₑₗ r'))).app
        S)
      ((condensifyMap
            (whiskerRight (LaurentMeasures.toLbarNatTrans r') (pFPNGT₁ToCHFPNG₁ₑₗ r'))).app
        S) :=
  by
  refine' condensify_exact _ _ id id le_rfl le_rfl _ _ _ _ S
  · apply Invpoly.toLaurentMeasures_injective
  · intro S; ext F s (_ | n) <;> rfl
  · rintro S c F ⟨hF1, hF2⟩
    simp only [whisker_right_app, LaurentMeasures.toLbarNatTrans_app, functor.comp_map,
      Set.mem_preimage, Set.mem_singleton_iff] at hF1 hF2 
    change LaurentMeasures.toLbar r' S F = 0 at hF1 
    change F ∈ PseudoNormedGroup.filtration (LaurentMeasures r' S) c at hF2 
    show F ∈ Invpoly.toLaurentMeasures r' S '' PseudoNormedGroup.filtration (Invpoly r' S) c
    have hd :=
      LaurentMeasures.bddFiltration_spec
        (show (0 : ℝ) < r' by norm_cast <;> exact Fact.elim inferInstance)
        (by norm_cast <;> exact Fact.elim inferInstance) F
    refine' ⟨Invpoly.ofLaurentMeasures r' S F, _, _⟩
    · change ‖_‖₊ ≤ c
      change ‖_‖₊ ≤ c at hF2 
      exact le_trans (Invpoly.ofLaurentMeasures_strict r' S F) hF2
    · ext s n
      change Invpoly.toLaurentMeasuresFun r' S _ s _ = _
      rcases n with ((_ | n) | n)
      · change Invpoly.toLaurentMeasuresFun r' S _ s 0 = _
        delta Invpoly.ofLaurentMeasures
        rw [Invpoly.toLaurentMeasuresFun_zero, Invpoly.Polynomial.sum_range_int_hMul_x_pow_coeff]
        split_ifs; rfl
        push_neg at h 
        rw [Int.toNat_le, sub_le_iff_le_add, Int.ofNat_zero, zero_add] at h 
        symm
        apply hd
        rwa [Int.lt_iff_add_one_le]
      · change Invpoly.toLaurentMeasuresFun r' S _ s (n + 1 : ℕ) = _
        rw [Invpoly.toLaurentMeasuresFun_pos]
        unfold LaurentMeasures.toLbar at hF1 
        rw [ext_iff] at hF1 
        symm
        convert congr_fun (congr_fun hF1 s) (n + 1)
      · rw [Invpoly.toLaurentMeasuresFun_neg]
        delta Invpoly.ofLaurentMeasures
        rw [Invpoly.Polynomial.sum_range_int_hMul_x_pow_coeff]
        split_ifs; rfl
        symm
        apply hd
        push_neg at h 
        rw [Int.toNat_le, sub_le_iff_le_add', Int.ofNat_add, ← add_assoc, Int.ofNat_one,
          le_add_iff_nonneg_left] at h 
        rwa [Int.negSucc_coe', Int.lt_iff_add_one_le, sub_add_cancel, neg_le_iff_add_nonneg]
  · rintro S c F hF
    refine' ⟨LaurentMeasures.toLbarSection r' S F, _, _⟩
    · apply LaurentMeasures.toLbarSection_mem_filtration
      exact PseudoNormedGroup.filtration_mono le_rfl hF
    · apply LaurentMeasures.toLbarSection_toLbar

end Lbar

