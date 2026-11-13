import Mathlib.Analysis.NormedSpace.Basic

#align_import facts.normedGroup

variable {V : Type _} [SeminormedAddCommGroup V]

instance fact_nnnorm_add_le (v w : V) : Fact (‖v + w‖₊ ≤ ‖v‖₊ + ‖w‖₊) :=
  ⟨nnnorm_add_le _ _⟩

