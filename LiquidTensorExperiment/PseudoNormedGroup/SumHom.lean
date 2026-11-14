import LiquidTensorExperiment.Rescale.PseudoNormedGroup

#align_import pseudo_normed_group.sum_hom

noncomputable section

open scoped NNReal BigOperators

attribute [local instance] typePow

section

variable {r' : ℝ≥0} (M : Type _) (N : ℕ)

namespace ProfinitelyFilteredPseudoNormedGroup

variable [ProfinitelyFilteredPseudoNormedGroup M]

def unrescale (N : ℝ≥0) (M : Type _) [ProfinitelyFilteredPseudoNormedGroup M] :
    ComphausFilteredPseudoNormedGroupHom (Rescale N M) M :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBound (AddMonoidHom.id _) N⁻¹
    (by
      intro c
      refine' ⟨fun x hx => _, _⟩
      · rwa [mul_comm]
      · haveI : Fact (c * N⁻¹ ≤ N⁻¹ * c) := ⟨(mul_comm _ _).le⟩
        exact ComphausFilteredPseudoNormedGroup.continuous_castLe (c * N⁻¹) (N⁻¹ * c))

def rescaleProj (i : Fin N) : ComphausFilteredPseudoNormedGroupHom (Rescale N (M ^ N)) M :=
  (ComphausFilteredPseudoNormedGroup.piProj i).comp (unrescale N _)

theorem rescaleProjBoundBy (i : Fin N) : (rescaleProj M N i).BoundBy N⁻¹ := by intro c x hx;
  rw [Rescale.mem_filtration, mul_comm] at hx ; exact hx i

def sumHom (N : ℕ) : ComphausFilteredPseudoNormedGroupHom (Rescale N (M ^ N)) M :=
  ∑ i, rescaleProj M N i

theorem sumHom_apply (x) : sumHom M N x = ∑ i, x i :=
  ComphausFilteredPseudoNormedGroupHom.sum_apply _ _ _

theorem sumHomStrict [Fact (0 < N)] : (sumHom M N).Strict :=
  by
  rw [ComphausFilteredPseudoNormedGroupHom.strict_iff_boundBy_one]
  have :=
    ComphausFilteredPseudoNormedGroupHom.sumBoundBy Finset.univ (rescale_proj M N) (fun i => N⁻¹)
      fun i _ => rescale_proj_bound_by M N i
  dsimp at this 
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this 
  rwa [mul_inv_cancel] at this 
  apply ne_of_gt
  norm_cast
  exact Fact.out _

end ProfinitelyFilteredPseudoNormedGroup

namespace ProfinitelyFilteredPseudoNormedGroupWithTinv

open ProfinitelyFilteredPseudoNormedGroup

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] [Fact (0 < r')] [Fact (0 < N)]

def sumHom : ComphausFilteredPseudoNormedGroupWithTinvHom r' (Rescale N (M ^ N)) M :=
  ComphausFilteredPseudoNormedGroupWithTinvHom.mk' (sumHom M N) (sumHomStrict M N).boundByOne
    fun x =>
    by
    simp only [sum_hom, ComphausFilteredPseudoNormedGroupHom.sum_apply,
      ComphausFilteredPseudoNormedGroupHom.map_sum]
    rfl

theorem sumHom_apply (x) : sumHom M N x = ∑ i, x i :=
  sumHom_apply _ _ _

end ProfinitelyFilteredPseudoNormedGroupWithTinv

end

