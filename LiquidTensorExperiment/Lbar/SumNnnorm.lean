import LiquidTensorExperiment.Lbar.FinsuppInstance

#align_import Lbar.sum_nnnorm

--  The lemmas in this file are likely no longer needed
--  The lemmas in this file are likely no longer needed
open Finset Finsupp

open scoped BigOperators

section FamiliesOfAddCommGroups

variable {S : FintypeCat} {α β : Type _}

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
--  Not needed anymore: the `seminormed_add_comm_group` instance has been removed
theorem sumNnnorm_add_le [SeminormedAddCommGroup α] (F G : S → α) :
    «expr∥ ∥₊» (F + G) ≤ «expr∥ ∥₊» F + «expr∥ ∥₊» G :=
  show ∑ s, «expr∥ ∥₊» (F s + G s) ≤ ∑ s, «expr∥ ∥₊» (F s) + ∑ s, «expr∥ ∥₊» (G s) from
    le_trans (sum_le_sum fun i hi => nnnorm_add_le _ _) sum_add_distrib.le

--  Not needed anymore: this was a helper lemma for the triangle inequality
theorem add_zero_dists [DecidableEq α] [AddZeroClass β] {l : α} {x y z : α →₀ β}
    (h : x l + y l + z l = 0) (hl : l ∈ x.support) : l ∈ y.support ∪ z.support :=
  by
  simp only [mem_support_iff, Ne.def, mem_union] at hl ⊢
  contrapose! hl
  simpa only [hl, add_zero] using h

--  Not needed anymore: this was a helper lemma for the triangle inequality
theorem dists [DecidableEq α] [AddGroup β] {l : α} {x y z : α →₀ β} (hl : l ∈ (x - z).support) :
    l ∈ (x - y).support ∪ (y - z).support :=
  have xz : l ∈ (-(x - z)).support := by rwa [support_neg]
  add_zero_dists
    (by simp only [neg_sub, Finsupp.coe_sub, Pi.sub_apply, sub_add_sub_cancel, sub_self]) xz

end FamiliesOfAddCommGroups

