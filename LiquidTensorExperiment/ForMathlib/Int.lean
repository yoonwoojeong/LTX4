import Mathlib.Data.Sign

#align_import for_mathlib.int

namespace Int

@[elab_as_elim]
protected theorem induction_on_iff {p : ℤ → Prop} (i : ℤ) (hz : p 0)
    (h : ∀ i : ℤ, p i ↔ p (i + 1)) : p i :=
  by
  induction' i using Int.induction_on with i IH i IH
  · exact hz
  · rwa [← h]
  · rwa [h, sub_add_cancel]

end Int

