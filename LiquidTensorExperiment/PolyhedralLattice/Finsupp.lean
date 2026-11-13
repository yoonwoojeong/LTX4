import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import LiquidTensorExperiment.PolyhedralLattice.Basic

#align_import polyhedral_lattice.finsupp

/-!

# Hom(ι, Λ) for Λ a polyhedral lattice

If Λ is a polyhedral lattice and ι is a finite type, then ι → Λ is a polyhedral lattice.

## Implementation issue

We use `ι →₀ Λ` rather than `ι → Λ` to make life easier with sums.

-/


noncomputable section

open scoped BigOperators Classical

variable (ι Λ : Type _)

namespace Finsupp

section NormedAddCommGroup

variable [NormedAddCommGroup Λ]

instance : Norm (ι →₀ Λ) :=
  ⟨fun x => x.Sum fun _ => norm⟩

variable {ι Λ}

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem norm_def (x : ι →₀ Λ) : «expr∥ ∥» x = x.Sum fun _ => norm :=
  rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
@[simp]
theorem norm_single (i : ι) (l : Λ) : «expr∥ ∥» (single i l) = «expr∥ ∥» l := by
  simp only [norm_def, sum_single_index, norm_zero]

variable (ι Λ)

instance [Fintype ι] : NormedAddCommGroup (ι →₀ Λ) :=
  normed_add_comm_group.of_core _ <|
    { norm_eq_zero_iff := fun x => by
        simp only [norm_def, Sum, ← coe_nnnorm, ← NNReal.coe_sum, NNReal.coe_eq_zero, coe_zero,
          Finset.sum_eq_zero_iff, nnnorm_eq_zero, mem_support_iff, ext_iff, Pi.zero_apply,
          not_imp_self]
      triangle := by
        intro x y
        have aux := fun z : ι →₀ Λ => @sum_fintype ι Λ _ _ _ _ z (fun i => norm) fun i => norm_zero
        simp only [norm_def, aux, ← Finset.sum_add_distrib, add_apply]
        apply Finset.sum_le_sum
        rintro i -
        apply norm_add_le
      norm_neg := fun x =>
        by
        have aux := fun z : ι →₀ Λ => @sum_fintype ι Λ _ _ _ _ z (fun i => norm) fun i => norm_zero
        simp only [norm_def, aux, norm_neg, neg_apply] }

variable {ι Λ}

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem nnnorm_def [Fintype ι] (x : ι →₀ Λ) : «expr∥ ∥₊» x = x.Sum fun _ => nnnorm :=
  by
  ext
  simpa only [coe_nnnorm, Finsupp.sum, NNReal.coe_sum] using norm_def x

end NormedAddCommGroup

end Finsupp

namespace GeneratesNorm

open Finsupp

variable [PolyhedralLattice Λ]

variable {J : Type _} (x : J → Λ)

def finsuppGenerators : ι × J → ι →₀ Λ := fun j => single j.1 (x j.2)

variable {Λ x} [Fintype J] (hx : GeneratesNorm x)

theorem finsupp [Fintype ι] : GeneratesNorm (finsuppGenerators ι Λ x) :=
  by
  dsimp only [finsupp_generators]
  intro l
  have := fun i => hx (l i)
  choose c H1 H2 using this
  have hl : l = ∑ i, single i (l i) :=
    by
    conv_lhs => rw [← sum_single l, Finsupp.sum]
    apply Finset.sum_subset (Finset.subset_univ _)
    rintro i - hi
    rw [not_mem_support_iff] at hi 
    rw [hi, single_zero]
  simp only [← single_add_hom_apply, ← AddMonoidHom.map_nsmul] at hl ⊢
  refine' ⟨fun j => c j.1 j.2, _, _⟩
  · simp only [H1, AddMonoidHom.map_sum] at hl 
    rw [hl, ← Finset.univ_product_univ, Finset.sum_product]
  · have aux := fun z : ι →₀ Λ => @sum_fintype ι Λ _ _ _ _ z (fun i => norm) fun i => norm_zero
    simp only [norm_def, aux, ← Finset.univ_product_univ, Finset.sum_product, H2,
      single_add_hom_apply, norm_single]

end GeneratesNorm

namespace Finsupp

variable [PolyhedralLattice Λ]

instance {ι : Type} [Fintype ι] : PolyhedralLattice (ι →₀ Λ)
    where
  Finite := Module.Finite.of_basis (Finsupp.basis fun i => Module.Free.chooseBasis ℤ Λ)
  Free := Module.Free.of_basis (Finsupp.basis fun i => Module.Free.chooseBasis ℤ Λ)
  polyhedral' := by
    obtain ⟨J, _instJ, x, hx⟩ := PolyhedralLattice.polyhedral' Λ; skip
    refine' ⟨ι × J, inferInstance, fun j => single j.1 (x j.2), _⟩
    exact hx.finsupp _

end Finsupp

