import LiquidTensorExperiment.PseudoNormedGroup.CLC
import LiquidTensorExperiment.Prop92.Concrete

#align_import prop_92.prop_92

noncomputable section

open scoped NNReal

namespace cLCFP

variable (r r' : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] (c c₁ c₂ : ℝ≥0) (n : ℕ)

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r' ≤ 1)] [Fact (c₂ ≤ r' * c₁)] [Fact (c₂ ≤ c₁)]

variable (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ)

def tInvSubTinv :=
  cLCFP.res V r' c₁ c₂ n ≫ cLCFP.tInv r V r' c₂ n - cLCFP.tinv V r' c₁ c₂ n

theorem norm_tInvSubTinv_le : ‖((tInvSubTinv r r' V c₁ c₂ n).app M)‖ ≤ 1 + r⁻¹ :=
  by
  rw [T_inv_sub_Tinv, sub_eq_neg_add]
  refine' le_trans (norm_add_le _ _) (add_le_add _ _)
  · rw [CategoryTheory.NatTrans.app_neg, norm_neg]
    refine' le_trans (NormedAddGroupHom.norm_completion _).le _
    exact
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
        (SemiNormedGroupCat.locallyConstant_obj_map_normNoninc _ _ _ _)
  · refine' NormedAddGroupHom.norm_comp_le_of_le' 1 r⁻¹ r⁻¹ (mul_one _).symm _ _
    · exact cLC.norm_tInv_le r V _
    ·
      exact
        NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 (res_norm_noninc V r' c₁ c₂ n M)

variable {V c n M}

open ProfinitelyFilteredPseudoNormedGroup ProfinitelyFilteredPseudoNormedGroupWithTinv
  ComphausFilteredPseudoNormedGroup

open LocallyConstant CategoryTheory

/-- 9.2 of Analytic.pdf -/
theorem tInvSubTinv_exists_preimage [hr1 : Fact (r < 1)] (f : (cLCFP V r' (r' * c) n).obj M)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ g : (cLCFP V r' c n).obj M,
      (tInvSubTinv r r' V c (r' * c) n).app M g = f ∧
        ‖g‖ ≤ (r / (1 - r) + ε) * ‖f‖ :=
  by
  obtain ⟨g, hg1, hg2⟩ :=
    @concrete_92 _ _ _ _ _ _ _ _ ((filtrationPow.castLe _ _ _ _).app _) (ComphausFilteredPseudoNormedGroup.embedding_castLe _ _)
      ((filtrationPow.tinv r' (r' * c) c _).app _) r V _ (Tinv₀_continuous _ _) hr1 _ f ε hε
  refine' ⟨g, _, hg2⟩
  rw [← hg1]; clear hg1
  dsimp only [T_inv_sub_Tinv, cLC, T_inv, cLC.tInv, Tinv, cLCFP.res, CategoryTheory.whiskerLeft_app,
    NatTrans.app_sub, NatTrans.comp_app, CategoryTheory.whiskerRight_app, NormedAddGroupHom.sub_apply,
    CategoryTheory.whiskerRight_app, Functor.comp_map]
  rw [← SemiNormedGroup.Completion.map_comp, ← NormedAddGroupHom.sub_apply, ← Functor.map_sub]
  rfl

variable (V c n M)

theorem tInvSubTinv_surjective [Fact (r < 1)] :
    Function.Surjective ((tInvSubTinv r r' V c (r' * c) n).app M) :=
  by
  intro f
  obtain ⟨g, hg, -⟩ := T_inv_sub_Tinv_exists_preimage r r' f 1 zero_lt_one
  exact ⟨g, hg⟩

end cLCFP

