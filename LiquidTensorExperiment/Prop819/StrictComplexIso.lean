import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels
import Mathlib.Algebra.Homology.Additive

#align_import prop819.strict_complex_iso

namespace SemiNormedGroupCat

protected class StrictIso {A B : SemiNormedGroupCat} (f : A ≅ B) where
  strict_hom' : ∀ a : A, ‖f.hom a‖₊ = ‖a‖₊

@[simp]
theorem strictIso_hom {A B : SemiNormedGroupCat} (f : A ≅ B) [StrictIso f] (a : A) :
    ‖f.hom a‖₊ = ‖a‖₊ :=
  StrictIso.strict_hom' _

@[simp]
theorem strictIso_inv {A B : SemiNormedGroupCat} (f : A ≅ B) [StrictIso f] (b : B) :
    ‖f.inv b‖₊ = ‖b‖₊ :=
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

