import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import LiquidTensorExperiment.PolyhedralLattice.Topology

#align_import polyhedral_lattice.quotient

/-!
# Quotients of polyhedral lattices
-/


noncomputable section

open scoped BigOperators

namespace PolyhedralLattice

variable {Λ : Type _} [PolyhedralLattice Λ] (L : AddSubgroup Λ)

instance : IsClosed (L : Set Λ) :=
  isClosed_discrete _

instance : NormedAddCommGroup (Λ ⧸ L) :=
  AddSubgroup.normedAddCommGroupQuotient _

theorem π_apply_eq_zero_iff (x) : L.normedMk x = 0 ↔ x ∈ L :=
  QuotientAddGroup.eq_zero_iff _

theorem π_isQuotient : L.normedMk.IsQuotient :=
  NormedAddGroupHom.isQuotientQuotient _

instance [H : Fact L.saturated] : NoZeroSMulDivisors ℤ (Λ ⧸ L)
    where eq_zero_or_eq_zero_of_smul_eq_zero :=
    by
    intro n x h
    obtain ⟨x, rfl⟩ : ∃ y, L.normed_mk y = x := Quotient.surjective_Quotient_mk'' x
    have : L.normed_mk (n • x) = n • L.normed_mk x := L.normed_mk.toAddMonoidHom.map_zsmul x n
    simp only [← this, π_apply_eq_zero_iff] at h ⊢
    exact add_subgroup.saturated_iff_zsmul.mp H.1 _ _ h

instance quotient_finite : Module.Finite ℤ (Λ ⧸ L) :=
  by
  apply Module.Finite.of_surjective L.normed_mk.toAddMonoidHom.toIntLinearMap
  exact Quotient.surjective_Quotient_mk''

instance quotient_free [H : Fact L.saturated] : Module.Free ℤ (Λ ⧸ L) :=
  by
  let φ := L.normed_mk.toAddMonoidHom.toIntLinearMap
  suffices Submodule.span ℤ (Set.range (φ ∘ Module.Free.chooseBasis ℤ Λ)) = ⊤
    by
    obtain ⟨n, b⟩ := Module.free_of_finite_type_torsion_free this
    exact Module.Free.of_basis b
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top,
    LinearMap.range_eq_top]
  exact Quotient.surjective_Quotient_mk''

open PseudoNormedGroup

theorem norm_lift (y : Λ ⧸ L) : ∃ x, L.normedMk x = y ∧ ‖x‖ = ‖y‖ :=
  by
  have hq : L.normed_mk.IsQuotient := NormedAddGroupHom.isQuotientQuotient _
  let s ε := {x | L.normed_mk x = y ∧ ‖x‖₊ ≤ ‖y‖₊ + ε}
  have hs : ∀ ε, (s ε).Finite := by
    intro ε
    apply (filtration_finite Λ (‖y‖₊ + ε)).Subset
    rintro x ⟨h1, h2⟩
    simpa only [SeminormedAddCommGroup.mem_filtration_iff] using h2
  let t ε := (hs ε).toFinset
  have ht : ∀ ε, 0 < ε → (t ε).Nonempty := by
    intro ε hε
    obtain ⟨x, h1, h2⟩ := hq.norm_lift hε y
    refine' ⟨x, _⟩; simp only [Set.Finite.mem_toFinset]; exact ⟨h1, h2.le⟩
  let r := ((t 1).image nnnorm).min' ((ht _ zero_lt_one).image _)
  have aux := Finset.min'_mem ((t 1).image nnnorm) ((ht _ zero_lt_one).image _)
  simp only [Finset.mem_image] at aux 
  obtain ⟨x, hx, H⟩ := aux
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx 
  suffices hr : r = ‖y‖₊
  · refine' ⟨x, hx.1, _⟩
    simp only [← coe_nnnorm, nnreal.coe_injective.eq_iff]
    exact H.trans hr
  refine' ((lt_or_eq_of_le _).resolve_left _).symm
  · rw [← hx.1]; exact (hq.norm_le x).trans H.le
  · intro hyr
    let ε := (r - ‖y‖₊) / 2
    have hε' : (ε : ℝ) = (r - ‖y‖₊) / 2 := by dsimp only [ε];
      rw [NNReal.coe_div, NNReal.coe_sub hyr.le, NNReal.coe_bit0, NNReal.coe_one]
    have hε : 0 < ε := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_zero, hε']
      exact div_pos (sub_pos.mpr <| nnreal.coe_lt_coe.mpr hyr) zero_lt_two
    have key : ‖y‖₊ + ε < r :=
      by
      rw [← NNReal.coe_lt_coe, NNReal.coe_add, hε']
      exact add_sub_div_two_lt (nnreal.coe_lt_coe.mpr hyr)
    refine' not_le_of_lt key _
    obtain ⟨x₀, hx₀⟩ := ht ε hε
    simp only [exists_prop, Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq] at hx₀ 
    refine' (Finset.min'_le _ _ _).trans hx₀.2
    simp only [exists_prop, Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq]
    exact ⟨x₀, ⟨hx₀.1, (hx₀.2.trans key.le).trans (H.ge.trans hx.2)⟩, rfl⟩

instance [H : Fact L.saturated] : PolyhedralLattice (Λ ⧸ L)
    where polyhedral' :=
    by
    obtain ⟨ι, _inst_ι, l, hl, hl'⟩ := PolyhedralLattice.polyhedral Λ; skip
    refine' ⟨ι, _inst_ι, fun i => L.normed_mk (l i), _⟩
    intro y
    obtain ⟨x, rfl, hx⟩ := norm_lift _ y
    obtain ⟨c, H1, H2⟩ := hl x
    have key : _ := _
    refine' ⟨c, key, _⟩; swap
    · show L.normed_mk x = _
      rw [H1, map_sum, Fintype.sum_congr]
      intro; exact L.normed_mk.toAddMonoidHom.map_nsmul _ _
    · apply le_antisymm
      · rw [key]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => norm_nsmul_le _ _)
      · simp only [← hx, H2]
        apply Finset.sum_le_sum
        rintro i -
        have hq : L.normed_mk.IsQuotient := NormedAddGroupHom.isQuotientQuotient _
        exact mul_le_mul le_rfl (hq.norm_le _) (norm_nonneg _) (Nat.cast_nonneg _)

end PolyhedralLattice

