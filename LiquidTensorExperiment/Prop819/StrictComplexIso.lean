import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels
import Mathlib.Algebra.Homology.Additive

#align_import prop819.strict_complex_iso

namespace SemiNormedGroupCat

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
protected class StrictIso {A B : SemiNormedGroupCat} (f : A ≅ B) where
  strict_hom' : ∀ a : A, «expr∥ ∥₊» (f.hom a) = «expr∥ ∥₊» a

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
@[simp]
theorem strictIso_hom {A B : SemiNormedGroupCat} (f : A ≅ B) [StrictIso f] (a : A) :
    «expr∥ ∥₊» (f.hom a) = «expr∥ ∥₊» a :=
  StrictIso.strict_hom' _

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
@[simp]
theorem strictIso_inv {A B : SemiNormedGroupCat} (f : A ≅ B) [StrictIso f] (b : B) :
    «expr∥ ∥₊» (f.inv b) = «expr∥ ∥₊» b :=
  by
  have : b = f.hom (f.inv b) := by change b = (f.inv ≫ f.hom) b; simp
  conv_rhs => rw [this]
  rw [strict_iso_hom]

end SemiNormedGroupCat

structure StrictIso (C D : CochainComplex SemiNormedGroupCat ℕ) where
  Iso : C ≅ D
  [isStrict : ∀ i : ℕ, SemiNormedGroupCat.StrictIso <| (HomologicalComplex.eval _ _ i).mapIso iso]

instance (C D : CochainComplex SemiNormedGroupCat ℕ) (f : StrictIso C D) (n : ℕ) :
    SemiNormedGroupCat.StrictIso ((HomologicalComplex.eval _ _ n).mapIso f.Iso) :=
  f.isStrict _

