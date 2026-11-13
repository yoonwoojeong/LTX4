import Mathlib.Analysis.NormedSpace.Basic

#align_import facts.normed_group

variable {V : Type _} [SeminormedAddCommGroup V]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
instance fact_nnnorm_add_le (v w : V) : Fact («expr∥ ∥₊» (v + w) ≤ «expr∥ ∥₊» v + «expr∥ ∥₊» w) :=
  ⟨nnnorm_add_le _ _⟩

