import Mathlib.Data.Int.Basic
import Mathlib.Algebra.GroupPower.Order

#align_import facts.int

theorem fact_le_of_add_one_le (q : ℤ) (m : ℤ) [h : Fact (q + 1 ≤ m)] : Fact (q ≤ m) :=
  ⟨(Int.le_add_one le_rfl).trans h.out⟩

instance fact_two_pow_pos (N : ℕ) : Fact (0 < 2 ^ N) :=
  ⟨pow_pos (zero_lt_two (α := ℕ)) _⟩

