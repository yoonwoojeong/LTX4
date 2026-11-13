import LiquidTensorExperiment.Rescale.PolyhedralLattice
import LiquidTensorExperiment.PolyhedralLattice.Cech
import LiquidTensorExperiment.Facts.Nnreal

#align_import polyhedral_lattice.cosimplicial

/-!
# The cosimplicial polyhedral lattice attached to `Λ → Λ'`

Let `Λ` be a polyhedral lattice, and let `0 < n` be a natural number.
Let `Λ' := rescale n (fin n →₀ Λ)` be the polyhedral lattice
that is the `n`-fold direct sum of `Λ` with itself,
endowed with the norm `∥(l₁, l₂, ..., lₙ)∥ = (∥l₁∥ + ∥l₂∥ + ... + ∥lₙ∥) / n`.

The diagonal embedding `Λ → Λ'` is a norm-nonincreasing map.
In this file we construct the Cech conerve of this map.
It is a cosimplicial object in the category `PolyhedralLattice`.

Concretely, but in pseudo-code:
it consists of the objects `Λ'^(m)` defined as `(Λ')^m/L`,
where `L` is the sublattice `Λ ⊗ {x : ℤ^m | ∑ x = 0}`.
-/


noncomputable section

universe u

open scoped NNReal BigOperators

open CategoryTheory Finsupp

namespace PolyhedralLatticeCat

variable (Λ : PolyhedralLatticeCat.{u}) (N : ℕ) [hN : Fact (0 < N)]

def rescaledPower : PolyhedralLatticeCat :=
  of (Rescale N <| Fin N →₀ Λ)

def diagonalEmbedding : Λ ⟶ rescaledPower Λ N
    where
  toFun l := @Rescale.of N (Fin N →₀ Λ) <| ∑ i, singleAddHom i l
  map_add' l₁ l₂ := by simp only [AddMonoidHom.map_add, Finset.sum_add_distrib]; rfl
  -- defeq abuse
  strict' l :=
    by
    rw [Rescale.norm_def, Equiv.symm_apply_apply, norm_def, NNReal.coe_nat_cast, sum_fintype]
    swap; · intro; exact norm_zero
    apply le_of_eq
    rw [div_eq_iff]; swap
    · norm_cast; exact hN.out.ne'
    simp only [← apply_add_hom_apply, AddMonoidHom.map_sum]
    simp only [apply_add_hom_apply, single_add_hom_apply, single_apply]
    convert Finset.sum_const (‖l‖ : ℝ)
    · ext i; simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]

theorem diagonalEmbedding_apply (l : Λ) (i : Fin N) :
    ((@Rescale.of N (Fin N →₀ Λ)).symm (Λ.diagonalEmbedding N l) : Fin N →₀ Λ) i = l := by
  simp only [diagonal_embedding, single_add_hom_apply, Finset.sum_apply',
    PolyhedralLatticeHom.coe_mk, Equiv.symm_apply_apply, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

def cosimplicialLift {M : Type _} [AddCommGroup M] (m : ℕ) (g₀ : Λ →+ M)
    (g : Fin (m + 1) → Λ.rescaledPower N →+ M)
    (hg : ∀ i l, (g i) (Λ.diagonalEmbedding N l) = g₀ l) :
    PolyhedralLattice.Conerve.Obj (Λ.diagonalEmbedding N) (m + 1) →+ M :=
  PolyhedralLattice.Conerve.lift' _ m g₀ g hg <|
    by
    intro l₁ l₂ h
    rw [Finsupp.ext_iff] at h 
    specialize h ⟨0, Fact.out _⟩
    erw [diagonal_embedding_apply, diagonal_embedding_apply] at h 
    exact h

theorem zsmul_rescaledPower (n : ℤ) (l : Λ.rescaledPower N) :
    n • (@Rescale.of N (Fin N →₀ Λ)).symm l = (@Rescale.of N (Fin N →₀ Λ)).symm (n • l) :=
  rfl

instance : Fact (PolyhedralLatticeHom.toAddMonoidHom (Λ.diagonalEmbedding N)).range.saturated :=
  by
  constructor
  rw [AddSubgroup.saturated_iff_zsmul]
  intro n l' h
  by_cases hn : n = 0; · exact Or.inl hn
  let l₀ : ↥Λ := ((@Rescale.of N (Fin N →₀ Λ)).symm l' : Fin N →₀ Λ) ⟨0, hN.1⟩
  refine' Or.inr ⟨l₀, _⟩
  simp only [PolyhedralLatticeHom.coe_toAddMonoidHom, AddMonoidHom.mem_range] at h ⊢
  obtain ⟨l, hl⟩ := h
  refine' @smul_right_injective ℤ _ _ _ _ _ n hn _ _ _
  rw [← hl, ← PolyhedralLatticeHom.map_zsmul]
  dsimp only [l₀]
  rw [← Finsupp.smul_apply, zsmul_rescaled_power _ _ n l', ← hl, diagonal_embedding_apply]

def cosimplicial : CosimplicialObject PolyhedralLatticeCat.{u} :=
  cechConerve <| diagonalEmbedding Λ N

open SimplexCategory

def cosimplicialAugmentationMap : Λ ⟶ (cosimplicial Λ N).obj (mk 0) :=
  cechAugmentationMap _

def augmentedCosimplicial : CosimplicialObject.Augmented PolyhedralLatticeCat.{u} :=
  augmentedCechConerve <| diagonalEmbedding Λ N

end PolyhedralLatticeCat

