import LiquidTensorExperiment.Rescale.NormedGroup
import LiquidTensorExperiment.PolyhedralLattice.Category

#align_import Rescale.polyhedralLattice

/-!

# Rescaling the norm on a polyhedral lattice.

Rescaling the norm on a polyhedral lattice by a positive real factor gives a
polyhedral lattice (at least for us -- Scholze seem to demand a rationality
condition which we are missing).

-/


noncomputable section

open scoped BigOperators Classical NNReal

namespace GeneratesNorm

open Rescale

variable (N : ℝ≥0) (Λ : Type _) [PolyhedralLattice Λ]

variable {J : Type _} [Fintype J] (x : J → Λ) (hx : GeneratesNorm x)

def rescaleGenerators : J → Rescale N Λ :=
  x

variable {Λ x}

theorem rescale [hN : Fact (0 < N)] : GeneratesNorm (rescaleGenerators N Λ x) :=
  by
  intro l
  obtain ⟨c, H1, H2⟩ := hx l
  refine' ⟨c, H1, _⟩
  simp only [norm_def, ← mul_div_assoc, ← Finset.sum_div]
  congr 1

end GeneratesNorm

namespace Rescale

variable {N : ℝ≥0} {V : Type _}

instance (Λ : Type _) [hN : Fact (0 < N)] [PolyhedralLattice Λ] : PolyhedralLattice (Rescale N Λ)
    where
  Finite := by delta Rescale; infer_instance
  Free := by delta Rescale; infer_instance
  polyhedral' := by
    obtain ⟨ι, _inst_ι, l, hl⟩ := PolyhedralLattice.polyhedral' Λ; skip
    refine' ⟨ι, _inst_ι, l, hl.rescale N⟩

end Rescale

namespace PolyhedralLatticeCat

@[simps]
protected def rescale (N : ℝ≥0) [hN : Fact (0 < N)] : PolyhedralLatticeCat ⥤ PolyhedralLatticeCat
    where
  obj Λ := of (Rescale N Λ)
  map Λ₁ Λ₂ f :=
    { toFun := fun l => @Rescale.of N Λ₂ (f ((@Rescale.of N Λ₁).symm l))
      map_add' := f.map_add
      -- defeq abuse
      strict' := fun l => by
        simp only [← coe_nnnorm, NNReal.coe_le_coe]
        erw [Rescale.nnnorm_def, Rescale.nnnorm_def]; simp only [div_eq_mul_inv]
        exact mul_le_mul' (f.strict l) le_rfl }

end PolyhedralLatticeCat

