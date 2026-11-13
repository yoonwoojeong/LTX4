import LiquidTensorExperiment.PolyhedralLattice.Basic
import LiquidTensorExperiment.NormedGroup.PseudoNormedGroup
import LiquidTensorExperiment.PseudoNormedGroup.WithTinv
import Mathlib.Topology.Connected.Basic
import LiquidTensorExperiment.Facts.Default

#align_import polyhedral_lattice.pseudoNormedGroup

/-!

# If M is a profinitely filtered pseudo-normed group with T⁻¹ then so is Hom(Λ, M)

Here Λ is a polyhedral lattice, and the T⁻¹ is in the sense
of `pseudo_normed_group.with_Tinv`.

-/


noncomputable section

open scoped NNReal BigOperators

open PseudoNormedGroup SeminormedAddCommGroup

theorem Int.one_mem_filtration : (1 : ℤ) ∈ filtration ℤ 1 := by
  simp only [nnnorm_one, mem_filtration_iff]

section

variable {Λ : Type _} [PolyhedralLattice Λ]

variable {M : Type _} [PseudoNormedGroup M]

theorem GeneratesNorm.addMonoidHom_mem_filtration_iff {ι : Type} [Fintype ι] {l : ι → Λ}
    (hl : GeneratesNorm l) (x : Λ →+ M) (c : ℝ≥0) :
    x ∈ filtration (Λ →+ M) c ↔ ∀ i, x (l i) ∈ filtration M (c * ‖l i‖₊) :=
  by
  refine' ⟨fun H i => H (le_refl (‖l i‖₊)), _⟩
  intro H c' l' hl'
  obtain ⟨cᵢ, h1, h2⟩ := hl.generates_nnnorm l'
  rw [h1, x.map_sum]
  refine' filtration_mono _ (sum_mem_filtration _ (fun i => c * cᵢ i * ‖l i‖₊) _ _)
  ·
    calc
      ∑ i, c * cᵢ i * ‖l i‖₊ = c * ∑ i, cᵢ i * ‖l i‖₊ := by
        simp only [mul_assoc, ← Finset.mul_sum]
      _ = c * ‖l'‖₊ := by rw [h2]
      _ ≤ c * c' := mul_le_mul' le_rfl hl'
  rintro i -
  rw [mul_assoc, mul_left_comm, x.map_nsmul]
  exact PseudoNormedGroup.nat_smul_mem_filtration (cᵢ i) _ _ (H i)

end

namespace PolyhedralLattice

variable (Λ : Type _) (r' : ℝ≥0) (M : Type _) [PolyhedralLattice Λ]

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M]

namespace AddMonoidHom

variable {Λ r' M} (c : ℝ≥0)

def incl (c : ℝ≥0) : filtration (Λ →+ M) c → ∀ l : Λ, filtration M (c * ‖l‖₊) := fun f l =>
  ⟨f l, f.2 <| mem_filtration_nnnorm _⟩

@[simp]
theorem coe_incl_apply (f : filtration (Λ →+ M) c) (l : Λ) : (incl c f l : M) = f l :=
  rfl

variable (Λ r' M)

theorem incl_injective : Function.Injective (@incl Λ r' M _ _ c) :=
  by
  intro f g h
  ext l
  show (incl c f l : M) = incl c g l
  rw [h]

instance : TopologicalSpace (filtration (Λ →+ M) c) :=
  TopologicalSpace.induced (incl c) inferInstance

theorem incl_embedding : Embedding (@incl Λ r' M _ _ c) :=
  { induced := rfl
    inj := incl_injective Λ r' M c }

theorem incl_inducing : Inducing (@incl Λ r' M _ _ c) :=
  ⟨rfl⟩

theorem incl_continuous : Continuous (@incl Λ r' M _ _ c) :=
  (incl_inducing _ _ _ _).continuous

instance : T2Space (filtration (Λ →+ M) c) :=
  (incl_embedding Λ r' M c).T2Space

instance : TotallyDisconnectedSpace (filtration (Λ →+ M) c)
    where isTotallyDisconnected_univ :=
    (incl_embedding Λ r' M c).IsTotallyDisconnected <|
      isTotallyDisconnected_of_totallyDisconnectedSpace _

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (l₁ l₂) -/
theorem incl_range_eq :
    Set.range (@incl Λ r' M _ _ c) =
      ⋂ (l₁) (l₂),
        {f |
          (castLe (f (l₁ + l₂)) : filtration M (c * (‖l₁‖₊ + ‖l₂‖₊))) =
            castLe (add' (f l₁, f l₂))} :=
  by
  ext f
  simp only [Set.mem_range, Set.mem_iInter, coeFn_coeBase, coe_incl_apply, Set.mem_setOf_eq,
    Subtype.coe_mk, Subtype.ext_iff]
  constructor
  · rintro ⟨⟨f, hf⟩, rfl⟩ l₁ l₂
    exact f.map_add _ _
  · intro h
    refine' ⟨⟨AddMonoidHom.mk' (fun l => f l) h, _⟩, _⟩
    · intro c' l hl
      rw [mem_filtration_iff] at hl 
      exact filtration_mono (mul_le_mul' le_rfl hl) (f l).2
    · ext; rfl

open ProfinitelyFilteredPseudoNormedGroup ComphausFilteredPseudoNormedGroup

theorem incl_range_isClosed : IsClosed (Set.range (@incl Λ r' M _ _ c)) :=
  by
  rw [incl_range_eq]
  apply isClosed_iInter
  intro l₁
  apply isClosed_iInter
  intro l₂
  apply isClosed_eq
  · exact (continuous_cast_le _ _).comp (continuous_apply (l₁ + l₂))
  ·
    exact
      (continuous_cast_le _ _).comp
        ((continuous_add' _ _).comp ((continuous_apply l₁).prod_mk (continuous_apply l₂)))

instance : CompactSpace (filtration (Λ →+ M) c)
    where compact_univ := by
    rw [← (incl_inducing Λ r' M c).isCompact_iff]
    apply IsClosed.isCompact
    rw [Set.image_univ]
    exact PolyhedralLattice.AddMonoidHom.incl_range_isClosed _ _ _ _

theorem continuous_iff {X : Type _} [TopologicalSpace X] (ϕ : X → filtration (Λ →+ M) c) :
    Continuous ϕ ↔ ∀ l : Λ, Continuous fun x => incl c (ϕ x) l :=
  by
  rw [(incl_inducing Λ r' M c).continuous_iff]
  constructor
  · intro h l; exact (continuous_apply l).comp h
  · exact continuous_pi

instance profinitelyFilteredPseudoNormedGroup : ProfinitelyFilteredPseudoNormedGroup (Λ →+ M) :=
  {
    AddMonoidHom.pseudoNormedGroup with
    continuous_add' := by
      intro c₁ c₂
      rw [continuous_iff]
      intro l
      have step1 :=
        ((continuous_apply l).comp (incl_continuous Λ r' M c₁)).Prod_map
          ((continuous_apply l).comp (incl_continuous Λ r' M c₂))
      have step2 := continuous_add' (c₁ * ‖l‖₊) (c₂ * ‖l‖₊)
      have := step2.comp step1
      refine' (@continuous_cast_le _ _ _ _ (id _)).comp this
      rw [add_mul]; exact ⟨le_rfl⟩
    continuous_neg' := by
      intro c
      rw [continuous_iff]
      intro l
      exact (continuous_neg' _).comp ((continuous_apply l).comp (incl_continuous Λ r' M c))
    continuous_castLe := by
      intro c₁ c₂ h
      rw [continuous_iff]
      intro l
      exact (continuous_cast_le _ _).comp ((continuous_apply l).comp (incl_continuous Λ r' M c₁)) }

end AddMonoidHom

variable {Λ r' M}

open ProfinitelyFilteredPseudoNormedGroupWithTinv

def tinv' : (Λ →+ M) →+ Λ →+ M :=
  AddMonoidHom.compHom (@tinv r' M _).toAddMonoidHom

@[simp]
theorem tinv'_apply (f : Λ →+ M) (l : Λ) : tinv' f l = tinv (f l) :=
  rfl

theorem tinv'_mem_filtration (c : ℝ≥0) (f : Λ →+ M) (hf : f ∈ filtration (Λ →+ M) c) :
    tinv' f ∈ filtration (Λ →+ M) (r'⁻¹ * c) :=
  by
  intro x l hl
  rw [Tinv'_apply, mul_assoc]
  apply Tinv_mem_filtration
  exact hf hl

variable (Λ r' M)

open ProfinitelyFilteredPseudoNormedGroup

open ComphausFilteredPseudoNormedGroup

variable [Fact (0 < r')]

def tinv : ComphausFilteredPseudoNormedGroupHom (Λ →+ M) (Λ →+ M) :=
  ComphausFilteredPseudoNormedGroupHom.mk' tinv'
    (by
      refine' ⟨r'⁻¹, fun c => ⟨Tinv'_mem_filtration c, _⟩⟩
      rw [AddMonoidHom.continuous_iff]
      intro l
      haveI : ∀ a, Fact (a ≤ r' * (r'⁻¹ * a)) := fun a =>
        ⟨by simp [mul_inv_cancel_left₀ (ne_of_gt (Fact.out _ : 0 < r'))]⟩
      refine'
        (@continuous_cast_le _ _ _ _ (id _)).comp
          ((@Tinv₀_continuous r' M _ (c * ‖l‖₊) (r'⁻¹ * (c * ‖l‖₊)) _).comp
            ((continuous_apply l).comp (AddMonoidHom.incl_continuous Λ r' M c)))
      rw [mul_assoc]; exact ⟨le_rfl⟩)

instance : ProfinitelyFilteredPseudoNormedGroupWithTinv r' (Λ →+ M) :=
  {
    AddMonoidHom.profinitelyFilteredPseudoNormedGroup Λ r'
      M with
    tinv := tinv Λ r' M
    tinv_mem_filtration := tinv'_mem_filtration }

@[simp]
theorem tinv_apply (x : Λ →+ M) (l : Λ) :
    (ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv x) l =
      ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv (x l) :=
  rfl

end PolyhedralLattice

