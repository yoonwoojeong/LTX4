import LiquidTensorExperiment.PolyhedralLattice.Basic

#align_import rescale.basic

/-!

# rescaling the norm on a type

This file is little more than the definition of the type alias.

-/


noncomputable section

open scoped BigOperators Classical NNReal

/-- `rescale r M` is the pseudo-normed group `M` but with a new filtration,
where `(rescale r M)_c := M_{c*r⁻¹}`.
-/
@[nolint unused_arguments]
def Rescale (N : ℝ≥0) (V : Type _) :=
  V

namespace Rescale

variable {N : ℝ≥0} {V : Type _}

instance [i : AddCommMonoid V] : AddCommMonoid (Rescale N V) :=
  i

instance [i : AddCommGroup V] : AddCommGroup (Rescale N V) :=
  i

def of : V ≃ Rescale N V :=
  Equiv.refl _

end Rescale

