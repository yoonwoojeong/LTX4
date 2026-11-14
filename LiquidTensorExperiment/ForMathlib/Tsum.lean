import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.NNReal

#align_import for_mathlib.tsum

open scoped BigOperators NNReal

theorem tsum_abs_eq_coe_tsum_nnabs {α : Type _} (f : α → ℝ) :
    -- Porting note: the coercion to `ℝ` must sit inside the binder, as in Lean 3
    ∑' i, abs (f i) = ∑' i, (Real.nnabs (f i) : ℝ) := by simp only [Real.coe_nnabs]

open NNReal Finset

theorem hasSum_nat_add_iff'' {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) :=
  by
  unfold HasSum
  rw [← tendsto_coe]
  rw [← tendsto_coe]
  simp only [NNReal.coe_sum]
  -- Porting note: the Lean 4 `hasSum_nat_add_iff` is stated for topological
  -- add groups, so we apply it in `ℝ` and transfer back.
  have h := (_root_.hasSum_nat_add_iff (f := fun n => (f n : ℝ)) k (a := (a : ℝ)))
  unfold HasSum at h
  simp only [NNReal.coe_add, NNReal.coe_sum]
  exact h

-- Porting note: mathlib later added an unrelated, more general `sum_add_tsum_nat_add'` at the
-- root; LTE's lemma (same statement as in Lean 3) lives in the `NNReal` namespace instead.
theorem NNReal.sum_add_tsum_nat_add' {f : ℕ → ℝ≥0} (k : ℕ) (h : Summable f) :
    ∑ i in range k, f i + ∑' i, f (i + k) = ∑' i, f i := by
  simpa [add_comm] using
    ((_root_.hasSum_nat_add_iff'' k).1 ((NNReal.summable_nat_add_iff k).2 h).hasSum).unique h.hasSum

theorem tsum_eq_zero {ι} (f : ι → ℝ≥0) (h : ∀ b, f b = 0) : ∑' b, f b = 0 := by
  simp only [h, tsum_zero]

#lint

