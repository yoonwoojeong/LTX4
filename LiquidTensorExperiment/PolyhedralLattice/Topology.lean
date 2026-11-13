import LiquidTensorExperiment.PolyhedralLattice.Basic
import LiquidTensorExperiment.NormedGroup.PseudoNormedGroup
import LiquidTensorExperiment.PseudoNormedGroup.ProfinitelyFiltered

#align_import polyhedral_lattice.topology

noncomputable section

open scoped NNReal BigOperators

namespace PolyhedralLattice

open PseudoNormedGroup NormedAddCommGroup

variable (Λ : Type _) [PolyhedralLattice Λ]

theorem filtration_finite (ε : ℝ≥0) : (filtration Λ ε).Finite := by
  classical
  obtain ⟨ι, _ι_inst, l, hl, hl'⟩ := PolyhedralLattice.polyhedral Λ
  skip
  let n : ι → ℕ := fun i => ⌈(ε / ‖l i‖₊ : ℝ)⌉.natAbs + 1
  let S := finset.univ.pi fun i => Finset.range (n i)
  let S' : Finset Λ := S.image fun x => ∑ i, x i (Finset.mem_univ _) • l i
  apply S'.finite_to_set.subset
  intro l₀ H
  obtain ⟨c, h1, h2⟩ := hl.generates_nnnorm l₀
  simp only [S', Set.mem_image, Finset.mem_univ, Finset.mem_pi, forall_true_left, Finset.mem_range,
    Finset.mem_coe, Finset.coe_image]
  refine' ⟨fun i _ => c i, _, h1.symm⟩
  intro i
  apply Nat.succ_le_succ
  contrapose! H
  simp only [not_le, SeminormedAddCommGroup.mem_filtration_iff, h2]
  have aux : 0 < ‖l i‖₊ := by rw [zero_lt_iff, Ne.def, nnnorm_eq_zero]; exact hl' i
  calc
    ε ≤ (⌈(ε / ‖l i‖₊ : ℝ)⌉.natAbs : ℝ≥0) * ‖l i‖₊ := _
    _ < ↑(c i) * ‖l i‖₊ := _
    _ ≤ ∑ i : ι, ↑(c i) * ‖l i‖₊ := _
  · rw [← NNReal.div_le_iff aux.ne', ← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_natAbs, NNReal.coe_div]
    refine' (Int.le_ceil _).trans (le_abs_self _)
  · rw [mul_lt_mul_right aux]
    · exact_mod_cast H
  · refine' @Finset.single_le_sum _ _ _ _ _ _ i (Finset.mem_univ _)
    exact fun _ _ => zero_le'

open Metric SeminormedAddCommGroup

instance : DiscreteTopology Λ :=
  discreteTopology_of_open_singleton_zero <| by
    classical
    have aux := filtration_finite Λ 1
    let s := aux.to_finset
    let s₀ := s.erase 0
    by_cases hs₀ : s₀.nonempty
    · let ε : ℝ≥0 := Finset.min' (s₀.image <| nnnorm) (hs₀.image _)
      obtain ⟨a, has₀, ha⟩ : ∃ a ∈ s₀, ‖a‖₊ = ε := by rw [← Finset.mem_image];
        apply Finset.min'_mem
      have H : 0 < ‖a‖ := by simpa only [norm_pos_iff] using Finset.ne_of_mem_erase has₀
      have h0ε : 0 < ε := by simpa only [← ha]
      have hε1 : ε ≤ 1 := by
        replace has₀ := Finset.mem_of_mem_erase has₀
        simp only [Set.Finite.mem_toFinset, mem_filtration_iff] at has₀ 
        rwa [← ha]
      suffices ({0} : Set Λ) = ball (0 : Λ) ε by rw [this]; apply is_open_ball
      ext
      simp only [Metric.mem_ball, Set.mem_singleton_iff, dist_zero_right]
      constructor
      · rintro rfl; rw [norm_zero]; exact_mod_cast h0ε
      intro h
      have hx : x ∈ s := by
        simp only [Set.Finite.mem_toFinset, mem_filtration_iff]
        exact le_of_lt (lt_of_lt_of_le h hε1)
      by_contra hx0
      replace hx := Finset.mem_erase_of_ne_of_mem hx0 hx
      have := Finset.min'_le (s₀.image <| nnnorm)
      refine' not_lt.2 (this (‖x‖₊) _) h
      simp only [exists_prop, Set.Finite.mem_toFinset, Finset.mem_image]
      use⟨x, ⟨hx, rfl⟩⟩
    · suffices ({0} : Set Λ) = ball (0 : Λ) 1 by rw [this]; apply is_open_ball
      ext
      simp only [Metric.mem_ball, Set.mem_singleton_iff, dist_zero_right]
      constructor
      · rintro rfl; rw [norm_zero]; exact zero_lt_one
      intro h
      contrapose! hs₀
      refine' ⟨x, _⟩
      simp only [Set.Finite.mem_toFinset, Finset.mem_erase, mem_filtration_iff, NNReal.coe_one]
      exact ⟨hs₀, h.le⟩

instance filtrationFintype (c : ℝ≥0) : Fintype (filtration Λ c) :=
  (filtration_finite Λ c).Fintype

-- we don't need this
instance : ProfinitelyFilteredPseudoNormedGroup Λ :=
  {-- compact of finite
    show PseudoNormedGroup Λ by
      infer_instance with
    compact := fun c => by infer_instance
    continuous_add' := fun _ _ => continuous_of_discreteTopology
    continuous_neg' := fun _ => continuous_of_discreteTopology
    continuous_castLe := fun _ _ _ => continuous_of_discreteTopology }

end PolyhedralLattice

