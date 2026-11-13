import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.CharZero
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.InjSurj
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Finiteness
import LiquidTensorExperiment.ForMathlib.Gordan

#align_import combinatorial_lemma.lem97

/-!

# Lemma 9.7 of [Analytic]

In this file we state and prove 9.7 of [Analytic]. The proof in the pdf is short, but
combinatorics can be fiddly. However it is almost certain that this file could be
a lot shorter.

-/


open scoped NNReal BigOperators Classical

variable {Λ : Type _} [AddCommGroup Λ]

variable {ι : Type _}

noncomputable section

open Classical Subtype Function Embedding

/-- A technical auxiliary lemma used in the proof of `lem97_pos`. -/
theorem aux_1 {N : ℕ} {l : ι → Λ} {S₀ : Finset (Λ →+ ℤ)}
    (hS₀ : Submodule.span ℕ ↑S₀ = explicitDualSet l) :
    let ψ : ({ x // x ∈ S₀ } → Fin N) → Λ →+ ℤ := fun y : { x // x ∈ S₀ } → Fin N =>
      ∑ s : { x // x ∈ S₀ } in S₀.attach, (y s).val • s.val
    let B : Finset (Λ →+ ℤ) := Finset.image ψ Finset.univ
    ∀ b : Λ →+ ℤ, b ∈ B → b ∈ explicitDualSet l :=
  by
  intro ψ B b hb
  rcases finset.mem_image.mp hb with ⟨y, ⟨hy₁, rfl⟩⟩
  rw [← hS₀]
  apply mem_span_finset.mpr
  refine' ⟨fun x : Λ →+ ℤ => if H : x ∈ S₀ then (y ⟨x, H⟩ : ℕ) else 0, _⟩
  rw [← Finset.sum_attach]
  refine' Finset.sum_congr rfl fun s hs => _
  simp only [Finset.coe_mem, Finset.mk_coe, dite_eq_ite, if_true, Fin.val_eq_coe, val_eq_coe]

/-- A technical auxiliary lemma used in the proof of `lem97_pos`. -/
theorem aux_2 {N : ℕ} (hN : 0 < N) {l : ι → Λ} {S₀ : Finset (Λ →+ ℤ)}
    (hS₀ : Submodule.span ℕ ↑S₀ = explicitDualSet l) {f r : (Λ →+ ℤ) → ℕ} :
    let Y : Type u_1 := { x // x ∈ S₀ } → Fin N
    let ψ : Y → Λ →+ ℤ := fun y : Y => ∑ s : { x // x ∈ S₀ } in S₀.attach, (y s).val • s.val
    let B : Finset (Λ →+ ℤ) := Finset.image ψ Finset.univ
    let g : (Λ →+ ℤ) → Fin N := fun i : Λ →+ ℤ => ⟨f i % N, Nat.mod_lt _ hN⟩
    let x' : Λ →+ ℤ := ∑ i : Λ →+ ℤ in S₀, (g i).val • i
    f = ↑g + N • r →
      x' = ∑ i : Λ →+ ℤ in S₀, (g i).val • i →
        x' ∈ B → ∀ i : ι, x' (l i) ≤ (⇑(∑ i : Λ →+ ℤ in S₀, f i • i)) (l i) :=
  by
  intro Y ψ B g x' hr hx' H i
  dsimp [x']
  rw [sub_nonpos.symm, sub_eq_add_neg, ← AddMonoidHom.neg_apply, ← Finset.sum_neg_distrib,
    AddMonoidHom.finset_sum_apply, AddMonoidHom.finset_sum_apply, ← Finset.sum_add_distrib]
  swap; infer_instance
  simp only [← AddMonoidHom.add_apply, ← nsmul_eq_smul, ← coe_nat_zsmul, ← neg_zsmul, zsmul_eq_smul,
    ← add_smul]
  simp only [AddMonoidHom.add_apply, AddMonoidHom.smul_apply, Pi.add_apply, Pi.neg_apply,
    Int.coe_nat_mod, Pi.smul_apply, AddMonoidHom.neg_apply]
  apply Finset.sum_nonpos
  intro z hz
  replace hz : z ∈ explicitDualSet l
  · rw [← Submodule.span_singleton_le_iff_mem, ← hS₀]
    exact Submodule.span_mono (set.singleton_subset_iff.mpr hz)
  replace hz : 0 ≤ z (l i) := rfl.mpr hz i
  simp only [-add_neg_le_iff_le_add', Tactic.Ring.add_neg_eq_sub, smul_sub]
  rw [sub_smul]
  rw [← Int.coe_nat_mod, sub_le_iff_le_add, zero_add]
  simp only [SMul.smul, zsmul_int_int]
  exact mul_le_mul_of_nonneg_right (int.coe_nat_le.mpr (Nat.mod_le (f z) N)) hz

/-- A technical auxiliary lemma used in the proof of `lem97_pos`. -/
theorem aux_3 {N : ℕ} (hN : 0 < N) {l : ι → Λ} {S₀ : Finset (Λ →+ ℤ)}
    (hS₀ : Submodule.span ℕ ↑S₀ = explicitDualSet l) :
    let Y : Type u_1 := { x // x ∈ S₀ } → Fin N
    let ψ : Y → Λ →+ ℤ := fun y : Y => ∑ s : { x // x ∈ S₀ } in S₀.attach, (y s).val • s.val
    let B : Finset (Λ →+ ℤ) := Finset.image ψ Finset.univ
    ∀ x : Λ →+ ℤ,
      x ∈ explicitDualSet l →
        ∃ (x' : Λ →+ ℤ) (H : x' ∈ B) (y : Λ →+ ℤ), x = N • y + x' ∧ ∀ i : ι, x' (l i) ≤ x (l i) :=
  by
  intro Y ψ B x hx
  rw [← hS₀, mem_span_finset] at hx 
  rcases hx with ⟨f, rfl⟩
  let g : (Λ →+ ℤ) → Fin N := fun i => ⟨f i % N, Nat.mod_lt (f i) hN⟩
  obtain ⟨r, hr⟩ : ∃ r : (Λ →+ ℤ) → ℕ, f = ↑g + N • r :=
    by
    use fun x => (f x - g x) / N
    refine' funext fun z => (_ : f z = g z + N * ((f z - f z % N) / N))
    rw [Nat.mul_div_cancel' (Nat.dvd_sub_mod _)]
    exact (add_tsub_cancel_of_le (Nat.mod_le _ _)).symm
  set x' := ∑ i : Λ →+ ℤ in S₀, (g i).val • i with hx'
  have H : x' ∈ B :=
    by
    refine' finset.mem_image.mpr ⟨g ∘ val, Finset.mem_univ _, _⟩
    convert Finset.sum_attach
    rfl
  refine' ⟨x', _, ∑ i : Λ →+ ℤ in S₀, r i • i, _, _⟩
  · refine' finset.mem_image.mpr ⟨g ∘ val, Finset.mem_univ _, _⟩
    convert Finset.sum_attach
    rfl
  · rw [hr, Finset.smul_sum, ← Finset.sum_add_distrib]
    simp_rw [← smul_assoc, ← add_smul, add_comm (N • _) _]
    rfl
  exact aux_2 hN hS₀ hr hx' H

/-- The proof of Lemma 9.7 of `Analytic.pdf` under the additional assumption
that (in the notation of the paper) λᵢ(x)≥0 for all i. -/
theorem lem97_pos [Module.Finite ℤ Λ] [Module.Free ℤ Λ] [Fintype ι] (N : ℕ) (hN : 0 < N)
    (l : ι → Λ) :
    ∃ B : Finset (Λ →+ ℤ),
      (∀ b ∈ B, b ∈ explicitDualSet l) ∧
        ∀ x : Λ →+ ℤ,
          x ∈ explicitDualSet l →
            ∃ x' ∈ B, ∃ y : Λ →+ ℤ, x = N • y + x' ∧ ∀ i, x' (l i) ≤ x (l i) :=
  by
  obtain ⟨S₀, hS₀⟩ := explicit_gordan l
  let Y : Type _ := { x // x ∈ S₀ } → Fin N
  let ψ : Y → Λ →+ ℤ := fun y : Y => ∑ s in Finset.attach S₀, (y s).1 • s.val
  exact ⟨Finset.image ψ Finset.univ, aux_1 hS₀, aux_3 hN hS₀⟩

section SignVectors

def nonzeroSign : ℤ → Units ℤ := fun n => if 0 ≤ n then 1 else -1

def SignVectors (ι : Type _) :=
  ι → Units ℤ

instance signVectorsInhabited : Inhabited (SignVectors ι) :=
  ⟨fun i => 1⟩

def fintypeSignVectors [Fintype ι] : Fintype (SignVectors ι) :=
  Pi.fintype

/-- Given a list l of elements of Λ and a functional x, (pos_vector l x) is the sign-vector of
the values of x (l i). -/
def posVector (l : ι → Λ) (x : Λ →+ ℤ) : SignVectors ι := fun i => nonzeroSign (x (l i))

instance smulSigns : SMul (SignVectors ι) (ι → Λ) where smul ε l i := (ε i : ℤ) • l i

theorem posVector_nonneg (l : ι → Λ) (x : Λ →+ ℤ) (j : ι) : 0 ≤ x ((posVector l x • l) j) :=
  by
  rw [posVector, nonzeroSign]
  simp only [SMul.smul, AddMonoidHom.map_zsmul, zsmul_int_int]
  split_ifs
  · convert h; simp
  · simp; linarith

theorem smul_to_explicitDualSet (l : ι → Λ) (x : Λ →+ ℤ) :
    x ∈ explicitDualSet (posVector l x • l) := fun j => posVector_nonneg l x j

theorem posVector_id_if_nonneg (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) :
    0 ≤ x (l i) → (posVector l x • l) i = l i :=
  by
  intro hx
  simp only [posVector, nonzeroSign, SMul.smul, id.def]
  rw [if_pos hx]
  -- units.coe_one, one_zsmul],
  simp

theorem posVector_neg_if_neg (l : ι → Λ) (x : Λ →+ ℤ) (i : ι) :
    x (l i) < 0 → (posVector l x • l) i = -l i :=
  by
  intro hx
  simp only [posVector, nonzeroSign, SMul.smul, id.def]
  rw [if_neg (not_le.mpr hx)]; simp

end SignVectors

/-- Given a list l, a vector of signs ε (and a positive integer N), (pos_A l ε) is a finite set of
functionals satisfying the requirements of Lemma 9.7 of [Analytic] with respect to all functionals
which are positive on all ((ε • l) i)'s. Its existence was established in lem97_pos above.
-/
def posA [Fintype ι] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (N : ℕ) (hN : 0 < N) (l : ι → Λ)
    (ε : SignVectors ι) : Finset (Λ →+ ℤ) :=
  choose (lem97_pos N hN (ε • l))

theorem posA_to_explicit [Fintype ι] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (N : ℕ) (hN : 0 < N)
    (l : ι → Λ) (ε : SignVectors ι) (x' : Λ →+ ℤ) (H : x' ∈ posA N hN l ε) :
    x' ∈ explicitDualSet (ε • l) :=
  (choose_spec (lem97_pos N hN (ε • l))).1 x' H

theorem exists_good_pair [Fintype ι] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (N : ℕ) (hN : 0 < N)
    (l : ι → Λ) (ε : SignVectors ι) (x : Λ →+ ℤ) (H : x ∈ explicitDualSet (ε • l)) :
    ∃ x' y : Λ →+ ℤ, x' ∈ posA N hN l ε ∧ x = N • y + x' ∧ ∀ i, x' ((ε • l) i) ≤ x ((ε • l) i) :=
  by
  obtain ⟨x', hx', ⟨y, hy⟩⟩ := (some_spec (lem97_pos N hN (ε • l))).2 x H
  exact ⟨x', y, hx', hy⟩

/-

The remainder of this file is proofs of two versions of Lemma 9.7, namely
`lem97` and `lem97'`.

-/
/-- Lemma 9.7 of [Analytic]. See also the (mathematically indistinguishable) variant `lem97'`. -/
theorem lem97 [Fintype ι] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
    ∃ A : Finset (Λ →+ ℤ),
      ∀ x : Λ →+ ℤ,
        ∃ x' ∈ A,
          ∃ y : Λ →+ ℤ,
            x = N • y + x' ∧
              ∀ i, 0 ≤ x' (l i) ∧ 0 ≤ (x - x') (l i) ∨ x' (l i) ≤ 0 ∧ (x - x') (l i) ≤ 0 :=
  by
  refine' ⟨(@Finset.univ (SignVectors ι) fintypeSignVectors).biUnion (posA N hN l), fun x => _⟩
  have hx : x ∈ explicitDualSet (posVector l x • l) := smul_to_explicitDualSet l x
  obtain ⟨x', y, mem_x', hy, hx'⟩ := exists_good_pair N hN l (posVector l x) x hx
  refine' ⟨x', _, _⟩
  · refine' finset.mem_bUnion.mpr ⟨posVector l x, _, mem_x'⟩
    simp only [Finset.mem_univ]
  · refine' ⟨y, hy, fun i => _⟩
    have h_pos' : x' ∈ explicitDualSet (posVector l x • l) :=
      posA_to_explicit N hN l (posVector l x) x' mem_x'
    replace h_pos' : 0 ≤ x' ((posVector l x • l) i) := h_pos' _
    by_cases h_pos : 0 ≤ x (l i)
    · have h_posvect_id : (posVector l x • l) i = l i := posVector_id_if_nonneg l x i h_pos
      replace h_pos' : 0 ≤ x' (l i) := h_pos'.trans (le_of_eq (congr_arg x' h_posvect_id))
      refine' Or.inl ⟨h_pos', _⟩
      rw [← h_posvect_id]
      simp only [sub_nonneg, AddMonoidHom.sub_apply, hx']
    · specialize hx' i
      have h_posvect_neg : (posVector l x • l) i = -l i :=
        posVector_neg_if_neg l x i (not_le.mp h_pos)
      rw [h_posvect_neg] at *
      replace h_pos' : x' (l i) ≤ 0
      · rw [x'.map_neg] at h_pos' 
        exact neg_nonneg.mp h_pos'
      refine' Or.inr ⟨h_pos', _⟩
      simpa only [neg_le_neg_iff, AddMonoidHom.sub_apply, AddMonoidHom.map_neg, sub_nonpos] using
        hx'

theorem Os.monotone_pow {R : Type _} [OrderedSemiring R] (k : ℕ) (R0 : ∀ r : R, 0 ≤ r) :
    Monotone fun n : R => n ^ k := fun x y xy => pow_le_pow_of_le_left (R0 _) xy k

theorem Nat.monotone_pow (k : ℕ) : Monotone fun n : ℕ => n ^ k :=
  Os.monotone_pow k Nat.zero_le

--λ x y xy, pow_le_pow_of_le_left x.zero_le xy k
theorem Nat.strictMono_pow {k : ℕ} (k0 : 0 < k) : StrictMono fun n : ℕ => n ^ k := fun x y xy =>
  pow_lt_pow_of_lt_left xy x.zero_le k0

theorem Nat.injective_pow {k : ℕ} (k0 : 0 < k) : Function.Injective fun n : ℕ => n ^ k :=
  injective_of_increasing (· < ·) (· < ·) _ (Nat.strictMono_pow k0)

theorem Int.natAbs_eq_self (a : ℤ) : (a.natAbs : ℤ) = a ↔ 0 ≤ a :=
  ⟨fun h => by rw [← h]; exact Int.ofNat_zero_le a.nat_abs, fun h => Int.natAbs_of_nonneg h⟩

theorem abs_add_eq_iff_abs_hMul_eq {R : Type _} [LinearOrderedCommRing R] {a b : R} :
    abs (a + b) = abs a + abs b ↔ abs (a * b) = a * b :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  ·
    simpa only [abs_mul, add_pow_two, mul_assoc, pow_bit0_abs, add_left_inj, mul_eq_mul_left_iff,
      or_false_iff, bit0_eq_zero, one_ne_zero, add_right_inj] using
      congr_arg (fun x : R => x ^ 2) h.symm
  · rcases mul_nonneg_iff.mp (abs_eq_self.mp h) with (⟨a0, b0⟩ | ⟨a0, b0⟩)
    · rw [abs_of_nonneg a0, abs_of_nonneg b0, abs_of_nonneg (add_nonneg a0 b0)]
    · rw [abs_of_nonpos a0, abs_of_nonpos b0, abs_of_nonpos (add_nonpos a0 b0), neg_add]

theorem natAbs_add_eq_iff_natAbs_hMul_eq {a b : ℤ} :
    Int.natAbs (a + b) = a.natAbs + b.natAbs ↔ ((a * b).natAbs : ℤ) = a * b :=
  by
  rw [← Int.abs_eq_natAbs, ← abs_add_eq_iff_abs_hMul_eq, Int.abs_eq_natAbs, Int.abs_eq_natAbs,
    Int.abs_eq_natAbs]
  norm_cast

theorem natAbs_add_eq_iff (a b : ℤ) :
    Int.natAbs (a + b) = Int.natAbs a + Int.natAbs b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  natAbs_add_eq_iff_natAbs_hMul_eq.trans ((Int.natAbs_eq_self _).trans mul_nonneg_iff)

theorem nat_smul_natAbs (a : ℕ) (b : ℤ) : a • b.natAbs = (a • b).natAbs :=
  by
  nth_rw 1 [← Int.natAbs_ofNat a]
  rw [smul_eq_mul, ← Int.natAbs_mul, ← smul_eq_mul]
  apply congr_arg
  rw [Algebra.id.smul_eq_mul, nsmul_eq_mul]

/-- Lemma 9.7 of [Analytic]. See also the (mathematically indistinguishable) variant `lem97`. -/
theorem lem97' [Fintype ι] [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (N : ℕ) (hN : 0 < N) (l : ι → Λ) :
    ∃ A : Finset (Λ →+ ℤ),
      ∀ x : Λ →+ ℤ,
        ∃ x' ∈ A,
          ∃ y : Λ →+ ℤ,
            x = N • y + x' ∧ ∀ i, (x (l i)).natAbs = N * (y (l i)).natAbs + (x' (l i)).natAbs :=
  by
  obtain ⟨A, hA⟩ := lem97 N hN l
  refine' ⟨A, fun x => _⟩
  rcases hA x with ⟨x', mem_x', y, rfl, hx'⟩
  refine' ⟨x', mem_x', y, rfl, fun i => _⟩
  specialize hx' i
  rw [← natAbs_add_eq_iff, add_sub_cancel, AddMonoidHom.coe_smul, Pi.smul_apply] at hx' 
  rw [AddMonoidHom.add_apply, AddMonoidHom.coe_smul, Pi.smul_apply, add_comm, hx', add_comm,
    add_left_inj, ← nat_smul_natAbs, smul_eq_mul]

-- TODO
-- #lint-
-- /- The `doc_blame` linter reports: -/
-- /- DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/
-- #print nonzero_sign /- def missing doc string -/
-- #print sign_vectors /- def missing doc string -/
-- #print fintype_sign_vectors /- def missing doc string -/
