import LiquidTensorExperiment.PseudoNormedGroup.Basic

#align_import pseudo_normed_group.splittable

attribute [local instance] typePow

open scoped NNReal BigOperators

namespace PseudoNormedGroup

section Splittable

class Splittable (M : Type _) [PseudoNormedGroup M] (N : ℕ) (d : ℝ≥0) : Prop where
  exists_sum :
    ∀ (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c),
      ∃ y : Fin N → M, x = ∑ i, y i ∧ ∀ i, y i ∈ filtration M (c / N + d)

variable {M : Type _} [PseudoNormedGroup M] (N : ℕ) (d : ℝ≥0) [Splittable M N d]

theorem exists_sum (c : ℝ≥0) (x : M) (hx : x ∈ filtration M c) :
    ∃ y : Fin N → M, x = ∑ i, y i ∧ y ∈ filtration (M ^ N) (c / N + d) :=
  Splittable.exists_sum c x hx

instance splittablePi {ι : Type _} (M : ι → Type _) [∀ i, PseudoNormedGroup (M i)] (N : ℕ) (d : ℝ≥0)
    [∀ i, Splittable (M i) N d] : Splittable (∀ i, M i) N d
    where exists_sum c x hx :=
    by
    have := fun i => exists_sum N d c (x i) (hx i)
    choose y hy1 hy2 using this
    refine' ⟨Function.swap y, _, Function.swap hy2⟩
    ext i; rw [hy1]; symm; convert Finset.sum_apply i _ _

end Splittable

end PseudoNormedGroup

