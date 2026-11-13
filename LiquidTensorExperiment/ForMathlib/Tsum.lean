import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.NNReal

#align_import for_mathlib.tsum

open scoped BigOperators NNReal

theorem tsum_abs_eq_coe_tsum_nnabs {α : Type _} (f : α → ℝ) :
    ∑' i, abs (f i) = ∑' i, Real.nnabs (f i) := by simp only [Real.coe_nnabs]

open NNReal Finset

theorem hasSum_nat_add_iff'' {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
    HasSum (fun n => f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) :=
  by
  unfold HasSum
  rw [← tendsto_coe]
  rw [← tendsto_coe]
  simp only [coe_sum]
  convert _root_.has_sum_nat_add_iff k
  rfl
  classical
  rw [NNReal.coe_add]
  simp only [coe_sum]
  infer_instance

theorem sum_add_tsum_nat_add' {f : ℕ → ℝ≥0} (k : ℕ) (h : Summable f) :
    ∑ i in range k, f i + ∑' i, f (i + k) = ∑' i, f i := by
  simpa [add_comm] using
    ((hasSum_nat_add_iff'' k).1 ((NNReal.summable_nat_add_iff k).2 h).HasSum).unique h.hasSum

theorem tsum_eq_zero {ι} (f : ι → ℝ≥0) (h : ∀ b, f b = 0) : ∑' b, f b = 0 := by
  simp only [h, tsum_zero]

#lint

