import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup2

#align_import for_mathlib.free_abelian_exact

noncomputable section

open CategoryTheory

open scoped BigOperators

variable (A : Type _) [AddCommGroup A]

namespace FreeAbelianGroup

def σπ : FreeAbelianGroup (A × A) →+ FreeAbelianGroup A :=
  FreeAbelianGroup.map Prod.fst + FreeAbelianGroup.map Prod.snd -
    FreeAbelianGroup.map (Function.uncurry (· + ·))

theorem σπ_of (x) : σπ A (of x) = of x.1 + of x.2 - of (x.1 + x.2) := by
  simp only [σπ, AddMonoidHom.sub_apply, AddMonoidHom.add_apply, map_of_apply, Function.uncurry]

theorem σπ_comp_zero : AddCommGroupCat.ofHom (σπ A) ≫ AddCommGroupCat.ofHom (lift id) = 0 :=
  by
  ext ⟨x, y⟩
  simp only [comp_apply, AddCommGroupCat.ofHom_apply, σπ_of, _root_.map_sub, _root_.map_add,
    lift.of, id.def, sub_self, AddCommGroupCat.zero_apply]

section Norm

open scoped NNReal

variable {X : Type _} (a b : FreeAbelianGroup X)

def norm : ℕ :=
  ∑ x in a.support, (coeff x a).natAbs

theorem tsum_norm : (a.norm : ℝ) = ∑' x, |(coeff x a : ℝ)| :=
  by
  rw [@tsum_eq_sum _ _ _ _ _ (fun x : X => |(coeff x a : ℝ)|) a.support _, norm, Nat.cast_sum]
  apply Finset.sum_congr (refl a.support)
  · exact fun x _ => Int.cast_natAbs _
  · intro x hx
    rw [abs_eq_zero, Int.cast_eq_zero]
    exact (not_mem_support_iff x a).mp hx

theorem summable_tsum_norm : Summable fun x => |(coeff x a : ℝ)| :=
  by
  apply summable_of_ne_finset_zero
  · intro x hx
    rw [abs_eq_zero, Int.cast_eq_zero]
    exact (not_mem_support_iff x a).mp hx

@[simp]
theorem norm_of (x : X) : (of x).norm = 1 := by
  simp only [norm, support_of, Finset.sum_singleton, coeff_of_self, Int.natAbs_one]

theorem norm_add : (a + b).norm ≤ a.norm + b.norm :=
  by
  rw [← @Nat.cast_le ℝ _ _, tsum_norm, Nat.cast_add, tsum_norm, tsum_norm, ←
    tsum_add (summable_tsum_norm a) (summable_tsum_norm b)]
  refine'
    tsum_le_tsum _ (summable_tsum_norm (a + b))
      (Summable.add (summable_tsum_norm _) (summable_tsum_norm _))
  intro
  rw [_root_.map_add, Int.cast_add]
  exact abs_add _ _

@[simp]
theorem norm_neg : (-a).norm = a.norm :=
  by
  apply_fun (coe : ℕ → ℝ)
  · rw [tsum_norm, tsum_norm, tsum_congr]
    intro x
    rw [_root_.map_neg, Int.cast_neg, abs_neg]
  exact Nat.cast_injective

theorem norm_sub : (a - b).norm ≤ a.norm + b.norm :=
  by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact norm_add _ _

@[simp]
theorem norm_eq_zero_iff : a.norm = 0 ↔ a = 0 :=
  by
  constructor
  · intro h
    rw [← @Nat.cast_eq_zero ℝ _ _ _, tsum_norm] at h 
    have H := (hasSum_zero_iff_of_nonneg _).mp ((summable_tsum_norm a).hasSum_iff.mpr h)
    have h_cz : ∀ x : X, coeff x a = 0 := by
      intro x
      have := Function.funext_iff.mp H x
      simp only [Pi.zero_apply, abs_eq_zero, Int.cast_eq_zero] at this 
      exact this
    apply_fun to_finsupp
    ext
    exacts [h_cz _, AddEquiv.injective (FreeAbelianGroup.equivFinsupp X), fun _ => abs_nonneg _]
  · intro h
    have h_cz : ∀ x : X, coeff x a = 0 := by
      intro x
      rw [h]
      simp only [_root_.map_zero, eq_self_iff_true]
    apply Finset.sum_eq_zero
    rintro x -
    exact int.natAbs_eq_zero.mpr (h_cz x)

theorem exists_of_norm_eq_succ_aux1 (n : ℤ) (H : 0 < n) : n.natAbs = (n - 1).natAbs + 1 :=
  by
  rcases n with ((_ | n) | n)
  · exfalso; revert H; decide
  · suffices Int.ofNat n.succ - 1 = Int.ofNat n by rw [this]; rfl
    simp only [Int.ofNat_eq_coe, Int.ofNat_succ, add_tsub_cancel_right]
  · exfalso; revert H; decide

theorem exists_of_norm_eq_succ_aux2 (n : ℤ) (H : n < 0) : n.natAbs = (n + 1).natAbs + 1 :=
  by
  rw [← Right.neg_pos_iff] at H 
  simpa only [Int.natAbs_neg, sub_eq_add_neg, ← neg_add] using exists_of_norm_eq_succ_aux1 (-n) H

theorem exists_of_norm_eq_succ (n : ℕ) (han : a.norm = n.succ) :
    ∃ b x, (a = b + of x ∨ a = b - of x) ∧ b.norm = n :=
  by
  have aux : a.norm ≠ 0 := by rw [han]; decide
  dsimp [norm] at aux 
  erw [not_iff_not.mpr Finset.sum_eq_zero_iff] at aux ; push_neg at aux 
  rcases aux with ⟨x, hxa, ha⟩
  rcases lt_trichotomy (coeff x a) 0 with (H | H | H); rotate_left
  · apply_fun Int.natAbs at H ; contradiction
  · refine' ⟨a - of x, x, Or.inl (sub_add_cancel _ _).symm, _⟩
    apply Nat.succ_injective; rw [← han]; symm
    dsimp only [norm, Nat.succ_eq_add_one]
    classical
    have : (a - of x).support ⊆ a.support :=
      by
      rw [sub_eq_add_neg]; refine' (support_add _ _).trans _
      simp only [support_neg, support_of, Finset.union_subset_iff, Finset.Subset.refl,
        Finset.singleton_subset_iff, true_and_iff, hxa]
    rw [Finset.sum_subset this]
    swap
    · intro y hy1 hy2; rwa [Int.natAbs_eq_zero, ← not_mem_support_iff]
    rw [← Finset.insert_erase hxa, Finset.sum_insert (Finset.not_mem_erase _ _),
      Finset.sum_insert (Finset.not_mem_erase _ _), add_right_comm]
    simp only [_root_.map_sub]
    congr 1
    · rw [coeff_of_self]; apply exists_of_norm_eq_succ_aux1 _ H
    · refine' Finset.sum_congr rfl _; intro y hy; rw [coeff_of_not_mem_support (of x), sub_zero]
      simp only [Finset.mem_erase, Ne.def] at hy 
      simpa only [support_of, Finset.mem_singleton] using hy.1
  · refine' ⟨a + of x, x, Or.inr (add_sub_cancel _ _).symm, _⟩
    apply Nat.succ_injective; rw [← han]; symm
    dsimp only [norm, Nat.succ_eq_add_one]
    classical
    have : (a + of x).support ⊆ a.support :=
      by
      refine' (support_add _ _).trans _
      simp only [support_neg, support_of, Finset.union_subset_iff, Finset.Subset.refl,
        Finset.singleton_subset_iff, true_and_iff, hxa]
    rw [Finset.sum_subset this]
    swap
    · intro y hy1 hy2; rwa [Int.natAbs_eq_zero, ← not_mem_support_iff]
    rw [← Finset.insert_erase hxa, Finset.sum_insert (Finset.not_mem_erase _ _),
      Finset.sum_insert (Finset.not_mem_erase _ _), add_right_comm]
    simp only [_root_.map_add]
    congr 1
    · rw [coeff_of_self]; apply exists_of_norm_eq_succ_aux2 _ H
    · refine' Finset.sum_congr rfl _; intro y hy; rw [coeff_of_not_mem_support (of x), add_zero]
      simp only [Finset.mem_erase, Ne.def] at hy 
      simpa only [support_of, Finset.mem_singleton] using hy.1

-- SELFCONTAINED
theorem norm_eq_one_iff : a.norm = 1 ↔ ∃ x, a = of x ∨ a = -of x :=
  by
  -- have := exists_of_norm_eq_succ a 0,
  constructor
  · intro h
    have := exists_of_norm_eq_succ a 0 h
    simp only [norm_eq_zero_iff, exists_and_right, exists_eq_right, zero_add, zero_sub] at this 
    exact this
  · intro h
    rcases h with ⟨x, hx | hx⟩
    all_goals rw [hx]
    any_goals rw [norm_neg]
    all_goals exact norm_of x

end Norm

theorem σπ_of_00 : σπ A (of (0, 0)) = of 0 := by simp only [σπ_of, add_zero, add_sub_cancel']

theorem exact_σπ_induction (a : FreeAbelianGroup A) (ha : FreeAbelianGroup.lift id a = 0) (n : ℕ)
    (hn : a.norm ≤ n) : ∃ x, FreeAbelianGroup.σπ A x = a :=
  by
  induction' n with n ih generalizing a
  · simp only [le_zero_iff, norm_eq_zero_iff] at hn ; subst a; exact ⟨0, _root_.map_zero _⟩
  erw [Nat.le_add_one_iff] at hn ; cases' hn with hn hn; · exact ih a ha hn
  cases n
  · rw [norm_eq_one_iff] at hn ; rcases hn with ⟨a, rfl | rfl⟩
    all_goals simp only [lift.of, _root_.map_neg, _root_.id, neg_eq_zero] at ha ; subst a
    · exact ⟨of (0, 0), σπ_of_00 _⟩
    · refine' ⟨-of (0, 0), _⟩; rw [_root_.map_neg, σπ_of_00]
  obtain ⟨b, y, H1, hbn⟩ := exists_of_norm_eq_succ _ _ hn
  obtain ⟨c, x, H2, hcn⟩ := exists_of_norm_eq_succ _ _ hbn
  rcases H1 with (rfl | rfl) <;> rcases H2 with (rfl | rfl)
  · obtain ⟨p, hp⟩ := ih (c + of (x + y)) _ _; rotate_left
    · simpa only [lift.of, _root_.map_add, id.def, add_assoc] using ha
    · refine' (norm_add _ _).trans _; rw [hcn, norm_of]
    refine' ⟨p + of (x, y), _⟩
    simp only [_root_.map_add, hp, σπ_of, add_assoc, add_right_inj]
    rw [add_comm (of (x + y)), sub_add_cancel]
  · obtain ⟨p, hp⟩ := ih (c + of (y - x)) _ _; rotate_left
    ·
      simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def, add_assoc, sub_eq_add_neg,
        add_comm y] using ha
    · refine' (norm_add _ _).trans _; rw [hcn, norm_of]
    refine' ⟨p - of (y - x, x), _⟩
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of, neg_add_cancel_right,
      neg_add_rev, neg_neg, add_assoc, add_left_neg, add_zero, add_right_inj]
    rw [add_comm (of (y + -x)), add_comm _ (of y)]
    simp only [add_assoc, add_left_neg, add_zero]
  · obtain ⟨p, hp⟩ := ih (c + of (x - y)) _ _; rotate_left
    ·
      simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def, add_assoc, sub_eq_add_neg] using
        ha
    · refine' (norm_add _ _).trans _; rw [hcn, norm_of]
    refine' ⟨p - of (x - y, y), _⟩
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of, neg_add_cancel_right,
      neg_add_rev, neg_neg, add_assoc, add_right_inj, add_left_neg, add_zero]
    rw [add_comm (of (x + -y))]
    simp only [add_assoc, add_left_neg, add_zero]
  · obtain ⟨p, hp⟩ := ih (c - of (x + y)) _ _; rotate_left
    ·
      simpa only [lift.of, _root_.map_add, _root_.map_neg, id.def, neg_add, add_assoc,
        sub_eq_add_neg] using ha
    · refine' (norm_sub _ _).trans _; rw [hcn, norm_of]
    refine' ⟨p - of (x, y), _⟩
    simp only [_root_.map_add, _root_.map_neg, sub_eq_add_neg, hp, σπ_of, neg_add_cancel_right,
      neg_add_rev, neg_neg, add_assoc, neg_add_cancel_left]
    rw [add_comm (-of x)]

theorem exact_σπ :
    Exact (AddCommGroupCat.ofHom <| FreeAbelianGroup.σπ A)
      (AddCommGroupCat.ofHom <| FreeAbelianGroup.lift id) :=
  by
  rw [AddCommGroupCat.exact_iff']
  refine' ⟨σπ_comp_zero _, _⟩
  intro a ha
  obtain ⟨p, hp⟩ := exact_σπ_induction A a ha a.norm le_rfl
  exact ⟨p, hp⟩

end FreeAbelianGroup

