import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels
import LiquidTensorExperiment.Lbar.Basic
import LiquidTensorExperiment.NormedGroup.PseudoNormedGroup
import LiquidTensorExperiment.CombinatorialLemma.Partition
import LiquidTensorExperiment.CombinatorialLemma.Lem97
import LiquidTensorExperiment.PolyhedralLattice.PseudoNormedGroup
import LiquidTensorExperiment.PseudoNormedGroup.Splittable
import LiquidTensorExperiment.HacksAndTricks.ByExactIHack

#align_import combinatorial_lemma.finite

/-!
In this file we state and prove 9.8 of [Analytic].
-/


noncomputable section

open scoped NNReal BigOperators

open PseudoNormedGroup CombinatorialLemma

variable (Λ : Type _) (r' : ℝ≥0) (S : Type _)

variable [Fintype S] [PolyhedralLattice Λ]

section

variable {S Λ r'}

-- ugly name
@[simps]
def Lbar.mkAux' (x : Λ →+ Lbar r' S) (y : S → ℕ → Λ →+ ℤ)
    (h : ∀ s n l, (y s n l).natAbs ≤ (x l s n).natAbs) : Λ →+ Lbar r' S :=
  AddMonoidHom.mk'
    (fun l =>
      { toFun := fun s n => y s n l
        coeff_zero' := fun s => by
          specialize h s 0 l
          simpa only [Int.natAbs_eq_zero, Lbar.coeff_zero, le_zero_iff, Int.natAbs_zero] using h
        summable' := by
          intro s
          apply NNReal.summable_of_le _ ((x l).Summable s)
          intro n
          refine' mul_le_mul' _ le_rfl
          norm_cast
          exact h _ _ _ })
    fun l₁ l₂ => by ext s n; exact (y s n).map_add l₁ l₂

-- jmc: It seems to me that we cannot easily define this using `Lbar.mk_aux'` above
@[simps]
def Lbar.mkAux {ι : Type} [Fintype ι] {l : ι → Λ} (hl : GeneratesNorm l) (x : Λ →+ Lbar r' S)
    (y : S → ℕ → Λ →+ ℤ) (h : ∀ s n i, (y s n (l i)).natAbs ≤ (x (l i) s n).natAbs) :
    Λ →+ Lbar r' S :=
  AddMonoidHom.mk'
    (fun l' =>
      { toFun := fun s n => y s n l'
        coeff_zero' := fun s => by
          obtain ⟨c, h1, -⟩ := hl l'
          rw [h1, AddMonoidHom.map_sum, Finset.sum_eq_zero]
          rintro i -
          suffices y s 0 (l i) = 0 by rw [AddMonoidHom.map_nsmul, this, nsmul_zero]
          specialize h s 0 i
          simpa only [Int.natAbs_eq_zero, Lbar.coeff_zero, le_zero_iff, Int.natAbs_zero] using h
        summable' := by
          intro s
          obtain ⟨c, h1, -⟩ := hl.generates_nnnorm l'
          rw [h1]
          suffices Summable fun n => ∑ i, c i • ↑(y s n (l i)).natAbs * r' ^ n
            by
            apply NNReal.summable_of_le _ this
            intro n
            rw [← Finset.sum_mul]
            refine' mul_le_mul' _ le_rfl
            simp only [AddMonoidHom.map_sum, NNReal.coe_natAbs, AddMonoidHom.map_nsmul]
            refine' le_trans (nnnorm_sum_le _ _) (le_of_eq (Fintype.sum_congr _ _ _))
            intro i
            simp only [nsmul_eq_mul, ← NNReal.coe_natAbs, Int.natAbs_mul, Int.natAbs_ofNat,
              Nat.cast_mul]
          apply summable_sum
          rintro i -
          apply NNReal.summable_of_le _ ((c i • x (l i)).Summable s)
          intro n
          refine' mul_le_mul' _ le_rfl
          simp only [nsmul_eq_mul, ← NNReal.coe_natAbs, Int.natAbs_mul, Int.natAbs_ofNat, ←
            Nat.cast_mul, Lbar.coe_nsmul, Pi.mul_apply, Pi.nat_apply]
          norm_cast
          exact Nat.mul_le_mul le_rfl (h _ _ _) })
    fun l₁ l₂ => by ext s n; exact (y s n).map_add l₁ l₂

end

variable {Λ r' S}

theorem Lbar.mkAux_mem_filtration (ι : Type) (c : ℝ≥0) (N : ℕ) (hN : 0 < N) [Fintype ι] {l : ι → Λ}
    (hl : GeneratesNorm l) {x : Λ →+ Lbar r' S} (hx : x ∈ filtration (Λ →+ Lbar r' S) c)
    (x₀' : S → ℕ → Λ →+ ℤ) (x₁' : S → ℕ → Λ →+ ℤ) (x' : S → ℕ → Λ →+ ℤ)
    (hx' : ∀ l s n, x l s n = x' s n l)
    (H : ∀ s n i, (x' s n (l i)).natAbs = N * (x₀' s n (l i)).natAbs + (x₁' s n (l i)).natAbs)
    (H' : ∀ s n i, (x₀' s n (l i)).natAbs ≤ (x (l i) s n).natAbs) :
    Lbar.mkAux hl x x₀' H' ∈ filtration (Λ →+ Lbar r' S) (c / ↑N) :=
  by
  set x₀ := Lbar.mkAux hl x x₀' H'
  have aux : c = (N : ℝ≥0) * (c / N) :=
    by
    rw [mul_comm, div_mul_cancel]
    exact_mod_cast hN.ne'
  have hN' : (0 : ℝ≥0) < N := by exact_mod_cast hN
  rw [hl.add_monoid_hom_mem_filtration_iff] at hx ⊢
  intro i
  specialize hx i
  rw [Lbar.mem_filtration_iff] at hx ⊢
  rw [← mul_le_mul_left hN', ← mul_assoc, ← aux, ← nsmul_eq_mul, ← Lbar.nnnorm_nsmul]
  refine' le_trans (Finset.sum_le_sum _) hx
  rintro s -
  refine' tsum_le_tsum _ (Lbar.summable _ s) ((x (l i)).Summable s)
  intro n
  refine' mul_le_mul' _ le_rfl
  norm_cast
  convert le_trans (le_add_right le_rfl) (H s n i).ge
  swap; · apply hx'
  rw [← Int.natAbs_ofNat N, ← Int.natAbs_mul, Int.natAbs_ofNat, ← nsmul_eq_mul]
  congr 1

@[simps]
def Lbar.mkOfAddMonoidHom [Fact (r' < 1)] (x : S → ℕ → Λ →+ ℤ) (a : Λ →+ ℤ)
    [∀ s n, Decidable (x s n = a)] : Lbar r' S :=
  Lbar.ofMask (Lbar.geom r' S) fun s n => x s n = a

@[simps apply]
def Lbar.mkTensor (a : Λ →+ ℤ) (x : Lbar r' S) : Λ →+ Lbar r' S :=
  AddMonoidHom.mk' (fun l => a l • x) fun l₁ l₂ => by rw [a.map_add, add_smul]

-- better name?
theorem lem_98_aux [Fact (r' < 1)] (A : Finset (Λ →+ ℤ)) (x₁' : S → ℕ → Λ →+ ℤ)
    [∀ s n a, Decidable (x₁' s n = a)] (hx₁' : ∀ s n, x₁' s n ∈ A) (x₁ : Λ →+ Lbar r' S)
    (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l) (l : Λ) :
    x₁ l = ∑ a in A, a l • Lbar.mkOfAddMonoidHom x₁' a :=
  by
  ext s n
  simp only [Finset.sum_apply, Lbar.coe_sum, Pi.smul_apply, Lbar.coe_zsmul, Lbar.coe_mk]
  rw [Finset.sum_eq_single (x₁' s n)]
  · simp only [true_and_iff, and_congr, if_congr, eq_self_iff_true, if_true,
      Lbar.mkOfAddMonoidHom_to_fun]
    split_ifs with hn
    · rw [smul_eq_mul, MulZeroClass.mul_zero, hn]; exact (x₁ l).coeff_zero s
    · simp only [smul_eq_mul, mul_one, hx₁]
  · intro a haA ha
    simp only [ha.symm, false_and_iff, if_false, smul_eq_mul, MulZeroClass.mul_zero,
      Lbar.mkOfAddMonoidHom_to_fun]
  · intro hsn; exact (hsn (hx₁' s n)).elim

theorem fintype_prod_nat_equiv_nat (S : Type _) [Fintype S] [hS : Nonempty S] :
    Nonempty (S × ℕ ≃ ℕ) := by
  classical
  obtain e' := Fintype.equivFin S
  refine' Nonempty.intro _
  calc
    S × ℕ ≃ Fin (Fintype.card S) × ℕ := Equiv.prodCongrLeft fun _ => e'
    _ ≃ ℕ := Classical.choice <| Cardinal.eq.1 _
  rw [← Cardinal.lift_id (Cardinal.mk ℕ), Cardinal.mk_prod, ← Cardinal.aleph0,
      Cardinal.mul_eq_right] <;>
    simp [le_of_lt (Cardinal.nat_lt_aleph0 _), le_refl]
  rw [← Fintype.card_pos_iff] at hS 
  exact_mod_cast hS.ne'

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem lem98_int [Fact (r' < 1)] (N : ℕ) (hN : 0 < N) (c : ℝ≥0) (x : Lbar r' S)
    (hx : x ∈ filtration (Lbar r' S) c) (H : ∀ s n, (x s n).natAbs ≤ 1) :
    ∃ y : Fin N → Lbar r' S, x = ∑ i, y i ∧ ∀ i, y i ∈ filtration (Lbar r' S) (c / N + 1) :=
  by
  by_cases hS : Nonempty S; swap
  · refine' ⟨fun i => 0, _, _⟩
    · ext s n; exact (hS ⟨s⟩).elim
    · intro; exact zero_mem_filtration _
  skip
  obtain ⟨e⟩ := fintype_prod_nat_equiv_nat S
  let f : ℕ → ℝ≥0 := fun n => ↑(x (e.symm n).1 (e.symm n).2).natAbs * r' ^ (e.symm n).2
  have summable_f : Summable f :=
    by
    rw [← e.summable_iff, ← (Equiv.sigmaEquivProd S ℕ).summable_iff]
    simp only [Function.comp, f, e.symm_apply_apply, NNReal.summable_sigma,
      Equiv.sigmaEquivProd_apply]
    -- TODO, missing lemma `fintype.summable`
    exact ⟨x.summable, ⟨_, hasSum_fintype _⟩⟩
  have f_aux : ∀ n, f n ≤ 1 := by
    intro n
    calc
      f n ≤ 1 * 1 := mul_le_mul' _ _
      _ = 1 := mul_one 1
    · exact_mod_cast H _ _
    · have : Fact (r' < 1) := ‹_›; exact pow_le_one _ zero_le' this.out.le
  obtain ⟨mask, h1, h2⟩ := exists_partition N hN f f_aux summable_f
  classical
  let y i := Lbar.ofMask x fun s n => e (s, n) ∈ mask i
  have hxy : x = ∑ i, y i := by
    ext s n
    simp only [Lbar.coe_sum, if_congr, Function.curry_apply, Fintype.sum_apply, Function.comp_apply,
      Lbar.ofMask_to_fun, Finset.sum_congr]
    obtain ⟨i, hi1, hi2⟩ := h1 (e (s, n))
    rw [Finset.sum_eq_single i, if_pos hi1]
    · rintro j - hj
      rw [if_neg]
      exact mt (hi2 j) hj
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  refine' ⟨y, hxy, _⟩
  intro i
  rw [Lbar.mem_filtration_iff] at hx ⊢
  suffices «expr∥ ∥₊» x = ∑' n, f n ∧ «expr∥ ∥₊» (y i) = ∑' n : ℕ, (mask i).indicator f n
    by
    calc
      «expr∥ ∥₊» (y i) = ∑' n : ℕ, (mask i).indicator f n := this.right
      _ ≤ (∑' n : ℕ, f n) / N + 1 := (h2 i)
      _ ≤ c / N + 1 := _
    simp only [div_eq_mul_inv]
    refine' add_le_add (mul_le_mul' _ le_rfl) le_rfl
    exact this.left.ge.trans hx
  constructor
  · calc
      ∑ s, ∑' n, ↑(x s n).natAbs * r' ^ n = ∑' s, ∑' n, ↑(x s n).natAbs * r' ^ n :=
        (tsum_fintype _).symm
      _ = _ := _
      _ = ∑' n, f n := e.tsum_eq _
    rw [← (Equiv.sigmaEquivProd S ℕ).tsum_eq]; swap; · infer_instance
    dsimp only [f, Equiv.sigmaEquivProd_apply]
    simp only [Equiv.symm_apply_apply]
    rw [tsum_sigma']
    · exact x.summable
    · rw [NNReal.summable_sigma]; exact ⟨x.summable, ⟨_, hasSum_fintype _⟩⟩
  · calc
      ∑ s, ∑' n, ↑(y i s n).natAbs * r' ^ n = ∑' s, ∑' n, ↑(y i s n).natAbs * r' ^ n :=
        (tsum_fintype _).symm
      _ = ∑' x, (mask i).indicator f (e x) := _
      _ = ∑' n, (mask i).indicator f n := e.tsum_eq _
    rw [← (Equiv.sigmaEquivProd S ℕ).tsum_eq]; swap; · infer_instance
    have aux :
      ∀ i s n h1,
        @ite _ (e (s, n) ∈ mask i) h1 (↑(x s n).natAbs * r' ^ n) 0 =
          ↑(@ite _ (e (s, n) ∈ mask i) h1 (x s n) 0).natAbs * r' ^ n :=
      by intros;
      split_ifs <;>
        simp only [Int.natAbs_zero, Nat.cast_zero, MulZeroClass.zero_mul, eq_self_iff_true]
    dsimp only [f, y, Set.indicator, Equiv.sigmaEquivProd_apply]
    simp only [Equiv.symm_apply_apply, Lbar.ofMask_to_fun, aux]
    rw [tsum_sigma']
    · exact (y i).Summable
    · rw [NNReal.summable_sigma]
      exact ⟨(y i).Summable, ⟨_, hasSum_fintype _⟩⟩

theorem lem98_aux' [Fact (r' < 1)] (N : ℕ) (A : Finset (Λ →+ ℤ)) (x x₀ x₁ : Λ →+ Lbar r' S)
    (x' x₀' x₁' : S → ℕ → Λ →+ ℤ) [∀ s n a, Decidable (x₁' s n = a)]
    (H : ∀ s n, x' s n = N • x₀' s n + x₁' s n) (hx : ∀ l s n, x l s n = x' s n l)
    (hx₀ : ∀ l s n, x₀ l s n = x₀' s n l) (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l)
    (Hx₁ : ∀ l : Λ, x₁ l = ∑ a : Λ →+ ℤ in A, a l • Lbar.mkOfAddMonoidHom x₁' a)
    (y' : (Λ →+ ℤ) → Fin N → Lbar r' S)
    (hy' : ∀ a : Λ →+ ℤ, Lbar.mkOfAddMonoidHom x₁' a = Finset.univ.Sum (y' a))
    (y : Fin N → Λ →+ Lbar r' S) (hy : ∀ i, y i = x₀ + ∑ a in A, Lbar.mkTensor a (y' a i)) :
    x = ∑ i : Fin N, y i := by
  intros
  ext l s n
  simp only [hx, H, hy, ← hx₁, Hx₁, hy', Lbar.coe_add, Finset.sum_apply, AddMonoidHom.add_apply,
    Lbar.coe_sum, Pi.add_apply, Lbar.mkTensor_apply, Finset.sum_congr, AddMonoidHom.smul_apply,
    Pi.smul_apply, AddMonoidHom.finset_sum_apply, Finset.smul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_comm,
    ← hx₀]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem lem98_crux [Fact (r' < 1)] {ι : Type} {l : ι → Λ} (N : ℕ) (hN : 0 < N) (A : Finset (Λ →+ ℤ))
    (x x₀ x₁ : Λ →+ Lbar r' S) (x' x₀' x₁' : S → ℕ → Λ →+ ℤ) [∀ s n a, Decidable (x₁' s n = a)]
    (xₐ : (Λ →+ ℤ) → Lbar r' S) (hx : ∀ l s n, x l s n = x' s n l)
    (hx₀ : ∀ l s n, x₀ l s n = x₀' s n l) (hx₁ : ∀ l s n, x₁ l s n = x₁' s n l)
    (hxₐ : ∀ a, xₐ a = Lbar.mkOfAddMonoidHom x₁' a)
    (Hx₁ : ∀ l : Λ, x₁ l = ∑ a : Λ →+ ℤ in A, a l • xₐ a) (hx₁'A : ∀ s n, x₁' s n ∈ A)
    (H : ∀ s n i, (x' s n (l i)).natAbs = N * (x₀' s n (l i)).natAbs + (x₁' s n (l i)).natAbs)
    (i : ι) :
    «expr∥ ∥₊» (x (l i)) =
      N • «expr∥ ∥₊» (x₀ (l i)) + ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a) :=
  by
  simp only [hx, H, ← hx₀, ← hx₁, Lbar.nnnorm_def, nsmul_eq_mul, mul_assoc, Finset.smul_sum,
    Finset.mul_sum, Nat.cast_add, Nat.cast_mul, add_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro s
  apply NNReal.eq
  simp only [NNReal.coe_tsum, NNReal.coe_sum, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_nat_cast, NNReal.coe_natAbs, coe_nnnorm]
  rw [tsum_add _ ((x₁ (l i)).summable_coe_real s)]; swap
  · rw [← summable_mul_left_iff]
    · exact (x₀ (l i)).summable_coe_real s
    · exact_mod_cast hN.ne'
  simp only [← tsum_mul_left]
  rw [← tsum_sum]; swap
  · intro a ha; exact Summable.mul_left _ ((xₐ a).summable_coe_real s)
  simp only [← mul_assoc, ← Finset.sum_mul, hxₐ, Hx₁]
  congr; ext n; congr
  simp only [Finset.sum_apply, Lbar.coe_sum, Lbar.mkOfAddMonoidHom_to_fun, Pi.smul_apply]
  rw [Finset.sum_eq_single (x₁' s n), Finset.sum_eq_single (x₁' s n)]
  · simp only [Lbar.coe_zsmul, Lbar.mkOfAddMonoidHom_to_fun, if_true, Pi.smul_apply,
      eq_self_iff_true, true_and_iff, if_congr, and_congr]
    split_ifs
    · simp only [MulZeroClass.mul_zero, norm_zero, smul_eq_mul]
    · simp only [Int.norm_eq_abs, ← abs_mul, ← Int.cast_mul, smul_eq_mul]
  all_goals try intro hsnA; exact (hsnA (hx₁'A s n)).elim
  all_goals intro a haA hasn
  ·
    simp only [hasn.symm, Lbar.mkOfAddMonoidHom_to_fun, norm_zero, MulZeroClass.mul_zero, if_congr,
      and_congr, eq_self_iff_true, if_false, false_and_iff]
  ·
    simp only [hasn.symm, Lbar.coe_zsmul, Pi.smul_apply, smul_eq_mul, Lbar.mkOfAddMonoidHom_to_fun,
      MulZeroClass.mul_zero, if_congr, and_congr, eq_self_iff_true, if_false, false_and_iff]

namespace Lem98

def ι (Λ : Type _) [PolyhedralLattice Λ] : Type :=
  (PolyhedralLattice.polyhedral Λ).some

instance : Fintype (ι Λ) :=
  (PolyhedralLattice.polyhedral Λ).choose_spec.some

variable (Λ)

def l : ι Λ → Λ :=
  (PolyhedralLattice.polyhedral Λ).choose_spec.choose_spec.some

theorem hl : GeneratesNorm (l Λ) := by
  convert (PolyhedralLattice.polyhedral Λ).choose_spec.choose_spec.choose_spec.1

theorem hl' : ∀ i, l Λ i ≠ 0 :=
  (PolyhedralLattice.polyhedral Λ).choose_spec.choose_spec.choose_spec.2

def a (N : ℕ) [hN : Fact (0 < N)] :=
  (lem97' N hN.1 (l Λ)).some

theorem hA (N : ℕ) [hN : Fact (0 < N)] (x : Λ →+ ℤ) :
    ∃ (x' : _) (H : x' ∈ a Λ N) (y : _),
      x = N • y + x' ∧ ∀ i, (x (l Λ i)).natAbs = N * (y (l Λ i)).natAbs + (x' (l Λ i)).natAbs :=
  (lem97' N hN.1 (l Λ)).choose_spec x

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
def d (N : ℕ) [hN : Fact (0 < N)] : ℝ≥0 :=
  Finset.univ.sup fun i => ∑ a in a Λ N, «expr∥ ∥₊» (a (l Λ i)) / «expr∥ ∥₊» (l Λ i)

end Lem98

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem lem98Finite [Fact (r' < 1)] (Λ : Type _) [PolyhedralLattice Λ] (S : Type _) [Fintype S]
    (N : ℕ) [hN : Fact (0 < N)] : PseudoNormedGroup.Splittable (Λ →+ Lbar r' S) N (Lem98.d Λ N) :=
  by
  classical
  constructor
  let l := Lem98.l Λ
  have hl := Lem98.hl Λ
  have hl' := Lem98.hl' Λ
  let A := Lem98.a Λ N
  have hA := Lem98.hA Λ N
  let d := Lem98.d Λ N
  intro c x hx
  -- `x` is a homomorphism `Λ →+ Lbar r' S`
  -- we split it into pieces `Λ →+ ℤ` for all coefficients indexed by `s` and `n`
  let x' : S → ℕ → Λ →+ ℤ := fun s n => (Lbar.coeff s n).comp x
  have := fun s n => hA (x' s n)
  clear hA
  choose x₁' hx₁' x₀' hx₀' H using this
  have hx₀_aux : ∀ s n i, (x₀' s n (l i)).natAbs ≤ (x (l i) s n).natAbs := fun s n i =>
    le_trans (le_add_right (Nat.le_mul_of_pos_left hN.1)) (H s n i).ge
  -- now we assemble `x₀' : S → ℕ → Λ →+ ℤ` into a homomorphism `Λ →+ Lbar r' S`
  let x₀ : Λ →+ Lbar r' S := Lbar.mkAux hl x x₀' hx₀_aux
  have hx₀ : x₀ ∈ filtration (Λ →+ Lbar r' S) (c / N) :=
    Lbar.mkAux_mem_filtration _ _ _ hN.1 hl hx x₀' x₁' x' (fun _ _ _ => rfl) H hx₀_aux
  -- and similarly for `x₁'`
  let x₁ : Λ →+ Lbar r' S :=
    Lbar.mkAux hl x x₁' fun s n i => le_trans (le_add_left le_rfl) (H s n i).ge
  -- `x₁` can be written as a sum of tensors
  -- `x₁ = ∑ a in A, a ⊗ xₐ`, for some `xₐ : Lbar r' S`
  let xₐ : (Λ →+ ℤ) → Lbar r' S := fun a => Lbar.mkOfAddMonoidHom x₁' a
  have hx₁ : ∀ l, x₁ l = ∑ a in A, a l • xₐ a := lem_98_aux _ _ hx₁' _ fun _ _ _ => rfl
  -- now it is time to start building `y`
  -- we first decompose the `xₐ a` into `N` pieces
  have hxₐ : ∀ a s n, (xₐ a s n).natAbs ≤ 1 := by intro a s n;
    dsimp [xₐ, Lbar.mkOfAddMonoidHom_to_fun]; split_ifs <;> simp
  have := fun a => lem98_int N hN.1 («expr∥ ∥₊» (xₐ a)) (xₐ a) _ (hxₐ a)
  swap
  · rw [Lbar.mem_filtration_iff]
  choose y' hy'1 hy'2 using this
  -- the candidate `y` combines `x₀` together with the pieces `y'` of `xₐ a`
  let y : Fin N → Λ →+ Lbar r' S := fun j => x₀ + ∑ a in A, Lbar.mkTensor a (y' a j)
  have hxy : x = ∑ i, y i :=
    by
    apply lem98_aux' N A x x₀ x₁ x' x₀' x₁' hx₀' _ _ _ hx₁ y' hy'1 y
    all_goals intros; rfl
  use y, hxy
  intro j
  rw [hl.add_monoid_hom_mem_filtration_iff] at hx ⊢
  intro i
  specialize hx i
  simp only [Lbar.mem_filtration_iff] at hx hy'2 ⊢
  have Hx :
    «expr∥ ∥₊» (x (l i)) =
      N • «expr∥ ∥₊» (x₀ (l i)) + ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a) :=
    by
    apply lem98_crux N hN.1 A x x₀ x₁ x' x₀' x₁' xₐ
    all_goals intros;
      first
      | rfl
      | apply_assumption
  calc
    «expr∥ ∥₊» (y j (l i)) ≤
        «expr∥ ∥₊» (x₀ (l i)) + ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a) / N +
          d * «expr∥ ∥₊» (l i) :=
      _
    _ =
        (N • «expr∥ ∥₊» (x₀ (l i)) + ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a)) / N +
          d * «expr∥ ∥₊» (l i) :=
      _
    _ = «expr∥ ∥₊» (x (l i)) / N + d * «expr∥ ∥₊» (l i) := by rw [Hx]
    _ ≤ _ := _
  · simp only [AddMonoidHom.add_apply, add_assoc, AddMonoidHom.finset_sum_apply,
      Lbar.mkTensor_apply]
    refine' (Lbar.nnnorm_add_le _ _).trans (add_le_add le_rfl _)
    refine' (Lbar.nnnorm_sum_le _ _).trans _
    calc
      ∑ a in A, «expr∥ ∥₊» (a (l i) • y' a j) =
          ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (y' a j) :=
        Finset.sum_congr rfl _
      _ ≤ ∑ a in A, «expr∥ ∥₊» (a (l i)) * («expr∥ ∥₊» (xₐ a) / N + 1) := (Finset.sum_le_sum _)
      _ = ∑ a in A, («expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a) / N + «expr∥ ∥₊» (a (l i))) :=
        (Finset.sum_congr rfl _)
      _ = ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a) / N + ∑ a in A, «expr∥ ∥₊» (a (l i)) :=
        _
      _ ≤ ∑ a in A, «expr∥ ∥₊» (a (l i)) * «expr∥ ∥₊» (xₐ a) / N + d * «expr∥ ∥₊» (l i) :=
        add_le_add le_rfl _
    · intro a ha; rw [Lbar.nnnorm_zsmul]
    · intro a ha; exact mul_le_mul' le_rfl (hy'2 a j)
    · intro a ha; rw [mul_add, mul_one, mul_div_assoc]
    · rw [Finset.sum_add_distrib]
    · calc
        ∑ a in A, «expr∥ ∥₊» (a (l i)) =
            (∑ a in A, «expr∥ ∥₊» (a (l i)) / «expr∥ ∥₊» (l i)) * «expr∥ ∥₊» (l i) :=
          _
        _ ≤
            (finset.univ.sup fun i => ∑ a in A, «expr∥ ∥₊» (a (l i)) / «expr∥ ∥₊» (l i)) *
              «expr∥ ∥₊» (l i) :=
          _
      · have : «expr∥ ∥₊» (l i) ≠ 0 := by simp only [hl' i, nnnorm_eq_zero, Ne.def, not_false_iff]
        simp only [div_eq_mul_inv, ← Finset.sum_mul, inv_mul_cancel_right₀ this]
      · exact mul_le_mul' (Finset.le_sup (Finset.mem_univ i)) le_rfl
  · simp only [div_eq_mul_inv, add_mul, Finset.sum_mul, nsmul_eq_mul]
    congr 2
    rw [mul_comm, inv_mul_cancel_left₀]
    exact_mod_cast hN.1.ne'
  · simp only [add_mul, div_eq_mul_inv]
    refine' add_le_add _ le_rfl
    rw [mul_right_comm]
    exact mul_le_mul' hx le_rfl

#lint

