import Mathlib.Data.Real.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Algebra.Monoid

#align_import combinatorial_lemma.partition

open scoped NNReal BigOperators

open Finset

/-!

# A technical lemma on the way to `lem98`

The purpose of this file is to prove the following lemma:
```
lemma exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (hf' : summable f) :
  ∃ (mask : fin N → set ℕ),
    (∀ n, ∃! i, n ∈ mask i) ∧ (∀ i, ∑' n, set.indicator (mask i) f n ≤ (∑' n, f n) / N + 1) :=
```
In disguise, this is `lem98` (`combinatorial_lemma/default.lean`) specialized to `Λ = ℤ`.
The proof of the general case makes a reduction to this special case.

## Informal explanation of the statement

The lemma `exists_partition` informally says the following:

Suppose we have a sequence of real numbers `f 0`, `f 1`, …, all between `0` and `1`,
and suppose that `c = ∑ (f i)` exists.
Then, for every positive natural number `N`, we can split `f` into `N` subsequences `g 1`, …, `g N`,
such that `∑ (g j i) ≤ c/N + 1`.

The informal proof is easy: consider `N` buckets, that are initially empty.
Now view the numbers `f i` as an incoming stream of numbers,
and place each of these in the buckets with the smallest total sum.

The formal proof is a bit trickier: we need to make sure that every number ends up in a bucket,
we need to show that the final subsequences have a converging sum, etc…
We model the subsqeuences by using indicator functions to mask parts of `f`
using `N` subsets of `ℕ` (`mask` in the statement).

In `recursion_data` below, we setup the `N` buckets,
and define the recursion step in `recursion_data_succ`.
The rest of the file consists of assembling the pieces.

-/


namespace CombinatorialLemma

/-- A data structure for recording partial sums of subsequences of a sequence of real numbers,
such that all the partial sums are rougly the same size.
The field `m` records to which partial sum the next entry in the sequence will be added. -/
structure RecursionData (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (k : ℕ) where
  M : Fin N → Prop
  hm : ∃! i, m i
  partialSums : Fin N → ℝ≥0
  h₁ : ∑ i, partial_sums i = ∑ n in range (k + 1), f n
  h₂ : ∀ i, partial_sums i ≤ (∑ n in range (k + 1), f n) / N + 1
  [decInst : ∀ i, Decidable (m i)]

attribute [instance] CombinatorialLemma.RecursionData.decInst

/-- The starting point for recursively constructing subsequences of a sequence of real numbers
such that all the subsequences sum to be roughly the same size:
we start by placing the first element of the sequence into the subsequence `0`. -/
def recursionDataZero (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
    RecursionData N hN f hf 0 where
  M j := j = ⟨0, hN⟩
  hm := ⟨_, rfl, fun _ => id⟩
  partialSums j := if j = ⟨0, hN⟩ then f 0 else 0
  h₁ := by simp only [sum_ite_eq', if_true, mem_univ, sum_singleton, range_one]
  h₂ := by
    intro i
    split_ifs
    · simp only [sum_singleton, range_one]
      refine' (hf 0).trans _
      exact self_le_add_left 1 (f 0 / ↑N)
    · exact zero_le'

instance (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
    Inhabited (RecursionData N hN f hf 0) :=
  ⟨recursionDataZero N hN f hf⟩

/-- Given partial sums of subsequences up to the `k`-th element in a sequence of real numbers,
add the `k+1`st element to the smallest partial sum so far. -/
noncomputable def recursionDataSucc (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (k : ℕ)
    (dat : RecursionData N hN f hf k) : RecursionData N hN f hf (k + 1) :=
  let I :=
    (Finset.univ : Finset (Fin N)).exists_min_image dat.partialSums ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  { M := fun j => j = I.some
    hm := ⟨I.some, rfl, fun _ => id⟩
    partialSums := fun i => dat.partialSums i + if i = I.some then f (k + 1) else 0
    h₁ := by
      rw [sum_range_succ _ (k + 1)]
      simp [Finset.sum_add_distrib, dat.h₁, add_comm]
    h₂ := by
      intro i
      split_ifs
      · rw [h]
        have : dat.partial_sums I.some * N ≤ ∑ n in range (k + 1 + 1), f n :=
          by
          calc
            dat.partial_sums I.some * N = ∑ i : Fin N, dat.partial_sums I.some := _
            _ ≤ ∑ i, dat.partial_sums i := _
            -- follows from I
                _ =
                ∑ n in range (k + 1), f n :=
              dat.h₁
            _ ≤ ∑ n in range (k + 1 + 1), f n := _
          · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_comm]
          · obtain ⟨-, HI⟩ := I.some_spec
            apply Finset.sum_le_sum
            intro j hj; exact HI j hj
          · rw [sum_range_succ _ (k + 1)]
            simp
        have : dat.partial_sums I.some ≤ (∑ n in range (k + 1 + 1), f n) / ↑N := by
          rwa [NNReal.le_div_iff_mul_le]; exact_mod_cast hN.ne'
        exact add_le_add this (hf (k + 1))
      · calc
          dat.partial_sums i + 0 ≤ (∑ n in range (k + 1), f n) / ↑N + 1 := by simpa using dat.h₂ i
          _ ≤ (∑ n in range (k + 1 + 1), f n) / ↑N + 1 := add_le_add _ le_rfl
        simp only [div_eq_mul_inv, Fin.sum_univ_eq_sum_range]
        refine' mul_le_mul' _ le_rfl
        simp only [Finset.sum_range_succ]
        exact self_le_add_right _ _ }

/-- Recursively construct subsequences of a given sequence of real numbers,
in such a way that the sums of the subsequences are all roughly of the same size. -/
noncomputable def partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
    ∀ i : ℕ, RecursionData N hN f hf i
  | 0 => recursionDataZero N hN f hf
  | k + 1 => recursionDataSucc N hN f hf k (partition k)

theorem partition_sums_aux (k : ℕ) (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1)
    (i : Fin N) :
    (partition N hN f hf (k + 1)).partialSums i =
      (partition N hN f hf k).partialSums i +
        if (partition N hN f hf (k + 1)).M i then f (k + 1) else 0 :=
  by simp [partition, CombinatorialLemma.recursionDataSucc]

theorem partition_sums (k : ℕ) (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (i : Fin N) :
    (partition N hN f hf k).partialSums i =
      ∑ n in range (k + 1), Set.indicator {k | (partition N hN f hf k).M i} f n :=
  by
  induction' k with k IH
  · dsimp [partition]; simp; dsimp [partition, CombinatorialLemma.recursionDataZero]; congr
  rw [partition_sums_aux, IH, sum_range_succ _ k.succ, Set.indicator, add_right_inj]
  congr 1

theorem exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) (hf' : Summable f) :
    ∃ mask : Fin N → Set ℕ,
      (∀ n, ∃! i, n ∈ mask i) ∧ ∀ i, ∑' n, Set.indicator (mask i) f n ≤ (∑' n, f n) / N + 1 :=
  by
  let mask : Fin N → ℕ → Prop := fun i => {n | (partition N hN f hf n).M i}
  have h_sum : ∀ k i, ∑ n in range k, Set.indicator (mask i) f n ≤ (∑ n in range k, f n) / N + 1 :=
    by
    rintro ⟨k⟩ i
    · simp [mask]
    rw [← partition_sums Thm95.UniversalConstants.k N hN f hf i]
    exact (partition N hN f hf k).h₂ i
  refine' ⟨mask, _, _⟩
  · intro n; exact (partition N hN f hf n).hm
  · intro i
    set S₁ : ℝ≥0 := ∑' n : ℕ, f n
    have hf'' : HasSum f S₁ := hf'.hasSum
    have hf''' : HasSum _ (S₁ / N) := hf''.mul_right (N : ℝ≥0)⁻¹
    have : Set.indicator (mask i) f ≤ f := by
      intro n
      dsimp [Set.indicator]
      split_ifs; exacts [le_rfl, zero_le']
    obtain ⟨S₂, -, h_mask⟩ := NNReal.exists_le_hasSum_of_le this hf''
    rw [h_mask.tsum_eq]
    rw [NNReal.hasSum_iff_tendsto_nat] at hf''' h_mask 
    have := Filter.Tendsto.add_const 1 hf'''
    apply le_of_tendsto_of_tendsto' h_mask this
    intro n
    simp only [div_eq_mul_inv, Finset.sum_mul] at h_sum ⊢
    exact h_sum n i

end CombinatorialLemma

#lint

