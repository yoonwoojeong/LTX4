import LiquidTensorExperiment.PolyhedralLattice.Cosimplicial
import LiquidTensorExperiment.PolyhedralLattice.Hom

#align_import polyhedral_lattice.cosimplicial_extra

open scoped NNReal

namespace PolyhedralLatticeCat

open PseudoNormedGroup

open PolyhedralLattice.Conerve (L obj lift' lift'_w)

variable (r' : ℝ≥0) (Λ : PolyhedralLatticeCat)

variable (M : ProFiltPseuNormGrpWithTinv r') (N : ℕ) [Fact (0 < N)]

variable (m : ℕ) (g₀ : Λ →+ M)

variable (g : Fin (m + 1) → Λ.rescaledPower N →+ M)

variable (hg : ∀ i l, (g i) (Λ.diagonalEmbedding N l) = g₀ l)

theorem cosimplicialLift_mk (l) :
    Λ.cosimplicialLift N m g₀ g hg (QuotientAddGroup.mk l) = Finsupp.liftAddHom g l :=
  by
  dsimp only [cosimplicial_lift, lift']
  have :=
    QuotientAddGroup.lift_mk' (L (Λ.diagonal_embedding N) (m + 1))
      (lift'_w (Λ.diagonal_embedding N) m g₀ g hg _) l
  exact this

theorem cosimplicialLift_mem_filtration (c : ℝ≥0)
    (H : ∀ i, g i ∈ filtration (Λ.rescaledPower N →+ M) c) :
    cosimplicialLift Λ N m g₀ g hg ∈ filtration (Obj (Λ.diagonalEmbedding N) (m + 1) →+ M) c :=
  by
  intro c' l' hl'
  rw [SeminormedAddCommGroup.mem_filtration_iff] at hl' 
  obtain ⟨l, rfl, hl⟩ := PolyhedralLattice.norm_lift _ l'
  erw [cosimplicial_lift_mk]
  rw [Finsupp.liftAddHom_apply, Finsupp.sum_fintype]
  swap; · intro; rw [AddMonoidHom.map_zero]
  simp only [← coe_nnnorm, NNReal.eq_iff] at hl 
  erw [Finsupp.nnnorm_def, Finsupp.sum_fintype] at hl 
  swap; · intro; rw [nnnorm_zero]
  rw [← hl] at hl' 
  replace hl' := mul_le_mul' (le_refl c) hl'
  rw [Finset.mul_sum] at hl' 
  apply filtration_mono hl'
  apply sum_mem_filtration
  rintro i -
  apply H
  exact SeminormedAddCommGroup.mem_filtration_nnnorm (l i)

end PolyhedralLatticeCat

