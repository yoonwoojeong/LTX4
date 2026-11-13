import Mathlib.Analysis.NormedSpace.Int
import LiquidTensorExperiment.PolyhedralLattice.Basic

#align_import polyhedral_lattice.int

/-!

# The integers are a polyhedral lattice.

The integers, with its usual norm, are a polyhedral lattice.

-/


noncomputable section

open scoped BigOperators

theorem Int.sum_units_toNat_smul (n : ℤ) : ∑ i : Units ℤ, Int.toNat (i * n) • (i : ℤ) = n :=
  by
  rw [UnitsInt.univ, Finset.sum_insert]; swap; decide
  simp only [neg_mul, mul_one, one_mul, nsmul_eq_mul, Units.val_one, Units.coe_neg_one, mul_neg,
    Finset.sum_singleton, ← sub_eq_add_neg, Int.toNat_sub_toNat_neg]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
instance Int.polyhedralLattice : PolyhedralLattice ℤ
    where polyhedral' := by
    refine' ⟨Units ℤ, inferInstance, coe, _⟩
    intro n
    refine' ⟨fun e => Int.toNat (e * n), (Int.sum_units_toNat_smul _).symm, _⟩
    simp only [Int.norm_coe_units, mul_one, Nat.cast_one, one_mul, UnitsInt.univ]
    show «expr∥ ∥» n = (1 * n).toNat + (↑(-1 * n).toNat + 0)
    simp only [neg_mul, add_zero, one_mul]
    exact (Int.toNat_add_toNat_neg_eq_norm _).symm

