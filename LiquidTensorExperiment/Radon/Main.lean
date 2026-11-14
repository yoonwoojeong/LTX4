import LiquidTensorExperiment.Radon.LCLimit
import Mathlib.Analysis.NormedSpace.WeakDual

#align_import Radon.main

open scoped NNReal BigOperators Classical

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

namespace Profinite

/-- The weak dual of `C(X,ℝ)` is linearly equivalent to
the weak dual of `locally_constant X ℝ`. -/
def weakDualCEquivLC (X : Profinite.{0}) :
    WeakDual ℝ C(X, ℝ) ≃ₗ[ℝ] WeakDual ℝ (LocallyConstant X ℝ) :=
  {--  `dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C]` works instead of `show` but is slower
      --  `dsimp [weak_dual_C_to_LC, weak_dual_LC_to_C, weak_dual.comap]` works instead of `show`,
      --  but is slower,
      X.weakDualCToLC with
    invFun := X.weakDualLCToC
    left_inv := by
      intro f; ext t
      show (LocallyConstant.pkg X ℝ).extend _ _ = _
      apply (LocallyConstant.pkg X ℝ).inductionOn t
      · apply isClosed_eq
        refine' (LocallyConstant.pkg X ℝ).continuous_extend
        exact f.2
      · intro e
        rw [(LocallyConstant.pkg X ℝ).extend_coe]; rfl
        apply ContinuousLinearMap.uniformContinuous
        infer_instance
    right_inv := by
      intro f; ext t
      show (LocallyConstant.pkg X ℝ).extend _ _ = _
      erw [(LocallyConstant.pkg X ℝ).extend_coe]
      apply ContinuousLinearMap.uniformContinuous
      infer_instance }

/-- An auxiliary definition to be used in the constructions below. -/
def radonToRadonLC (X : Profinite.{0}) (p c : ℝ≥0) : X.radon p c ⟶ X.radonLC p c
    where
  toFun μ := ⟨weakDualCToLC _ μ.1, μ.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine' Continuous.comp _ continuous_subtype_val
    exact ContinuousLinearMap.continuous _

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCToRadon (X : Profinite.{0}) (p c : ℝ≥0) : X.radonLC p c → X.radon p c := fun μ =>
  ⟨weakDualLCToC _ μ.1,
    by
    change (weak_dual_C_to_LC _ (weak_dual_LC_to_C _ μ.1)).BddLC p c
    erw [X.weak_dual_C_equiv_LC.apply_symm_apply]
    exact μ.2⟩

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCToWeakDual (X : Profinite.{0}) (p c : ℝ≥0) :
    X.radonLC p c → WeakDual ℝ (LocallyConstant X ℝ) :=
  Subtype.val

/-- An auxiliary definition to be used in the constructions below. -/
def weakDualLCToFun (X : Profinite.{0}) :
    WeakDual ℝ (LocallyConstant X ℝ) → LocallyConstant X ℝ → ℝ := fun μ x => μ x

theorem continuous_weakDualLCToFun (X : Profinite.{0}) : Continuous X.weakDualLCToFun :=
  by
  apply continuous_pi; intro e
  exact WeakDual.eval_continuous _

instance t2Space_weakDual (X : Profinite.{0}) : T2Space (WeakDual ℝ (LocallyConstant X ℝ)) :=
  ⟨fun x y h =>
    separated_by_continuous X.continuous_weakDualLCToFun fun c =>
      h <| by ext t; apply_fun fun e => e t at c ; exact c⟩

theorem radonLC_closedEmbedding (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    ClosedEmbedding (X.radonLCToWeakDual p c) :=
  closedEmbedding_subtype_val
    (by
      apply IsCompact.isClosed
      let S := _; change IsCompact S
      have : S = Set.range (X.Radon_LC_to_weak_dual p c) := by erw [Subtype.range_val]; rfl
      rw [this]; clear this
      apply isCompact_range
      exact continuous_subtype_val)

/-- An auxiliary definition to be used in the constructions below. -/
def radonToWeakDual (X : Profinite.{0}) (p c : ℝ≥0) : X.radon p c → WeakDual ℝ C(X, ℝ) :=
  Subtype.val

theorem radon_closedEmbedding (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    ClosedEmbedding (X.radonToWeakDual p c) :=
  closedEmbedding_subtype_val
    (by
      let T : Set (WeakDual ℝ (LocallyConstant X ℝ)) := {f | f.BddLC p c}
      change IsClosed (X.weak_dual_C_to_LC ⁻¹' T)
      apply IsClosed.preimage
      exact (weak_dual_C_to_LC X).continuous
      convert (X.Radon_LC_closed_embedding p c).closed_range
      erw [Subtype.range_val]; rfl)

theorem radon_closed_embedding_range_bdd (X : Profinite) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    Bornology.IsBounded (NormedSpace.Dual.toWeakDual ⁻¹' Set.range (X.radonToWeakDual p c)) :=
  by
  -- Use c^(1/p)
  letI : UniformSpace (LocallyConstant.pkg X ℝ).Space := (LocallyConstant.pkg X ℝ).uniformStruct
  refine' (Metric.isBounded_iff_subset_closedBall 0).mpr _
  refine' ⟨c ^ (1 / (p : ℝ)), fun μ hμ => mem_closed_ball_zero_iff.mpr _⟩
  apply ContinuousLinearMap.op_norm_le_bound
  refine' (NNReal.coe_nonneg _).trans_eq (NNReal.coe_rpow _ _)
  intro f
  apply (LocallyConstant.pkg X ℝ).inductionOn f
  · apply isClosed_le
    refine' Continuous.comp continuous_norm _
    exact μ.continuous
    refine' Continuous.comp (continuous_mul_left _) continuous_norm
  · intro e
    let γ : WeakDual ℝ (LocallyConstant X ℝ) := X.weak_dual_C_to_LC μ
    dsimp [LocallyConstant.pkg]
    have : μ e = γ e; rfl; rw [this]; clear this
    have : ‖e.toContinuousMap‖ = ‖e‖ := by
      simp only [ContinuousMap.norm_eq_iSup_norm, LocallyConstant.norm_def,
        LocallyConstant.toContinuousMap_eq_coe, LocallyConstant.coe_continuousMap]
    erw [this]; clear this
    suffices ‖γ e‖₊ ≤ c ^ (1 / (p : ℝ)) * ‖e‖₊ by exact_mod_cast this
    have hp : 0 < (p : ℝ) := nnreal.coe_pos.mpr (Fact.out (0 < p))
    have hp' : (p : ℝ) ≠ 0 := ne_of_gt hp
    rw [← NNReal.rpow_le_rpow_iff hp, NNReal.mul_rpow, ← NNReal.rpow_mul]
    rw [show 1 / (p : ℝ) * p = 1 from (eq_div_iff hp').mp rfl, NNReal.rpow_one]
    obtain ⟨δ, hδ⟩ := hμ
    have H := δ.2 e.discreteQuotient
    replace H := mul_le_mul H (le_refl (‖e‖₊ ^ (p : ℝ))) (zero_le _) (zero_le _)
    refine' le_trans _ H; clear H
    rw [mul_comm, Finset.mul_sum]
    nth_rw 1 [e.eq_sum]
    simp_rw [γ.map_sum, γ.map_smul]
    refine' le_trans (Real.pow_nnnorm_sum_le _ _ _) _
    apply Finset.sum_le_sum; rintro x -
    rw [smul_eq_mul, nnnorm_mul, NNReal.mul_rpow]
    refine' mul_le_mul _ (le_of_eq _) (zero_le _) (zero_le _)
    apply NNReal.rpow_le_rpow _ (le_of_lt hp)
    obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ x
    change ‖e x‖₊ ≤ _
    apply LocallyConstant.nnnorm_apply_le_nnnorm
    congr 2
    change _ = X.Radon_to_weak_dual p c δ _; rw [hδ]; rfl

instance compactSpace_radon (X : Profinite) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    CompactSpace (X.radon p c) :=
  by
  let e : X.Radon p c ≃ₜ Set.range (X.Radon_to_weak_dual p c) :=
    Homeomorph.ofEmbedding _ (X.Radon_closed_embedding p c).toEmbedding
  suffices CompactSpace (Set.range (X.Radon_to_weak_dual p c)) by skip; apply e.symm.compactSpace
  rw [← isCompact_iff_compactSpace]
  apply WeakDual.isCompact_of_bounded_of_closed
  apply Radon_closed_embedding_range_bdd
  exact (X.Radon_closed_embedding p c).closed_range

/-- An auxiliary definition to be used in the constructions below. -/
def radonEquivRadonLC (X : Profinite.{0}) (p c : ℝ≥0) : X.radon p c ≃ X.radonLC p c
    where
  toFun := X.radonToRadonLC p c
  invFun := X.radonLCToRadon p c
  left_inv := by
    intro t; ext1
    apply X.weak_dual_C_equiv_LC.symm_apply_apply
  right_inv := by
    intro t; ext1
    apply X.weak_dual_C_equiv_LC.apply_symm_apply

theorem continuous_radonEquivRadonLC (X : Profinite.{0}) (p c : ℝ≥0) :
    Continuous (X.radonEquivRadonLC p c) :=
  ContinuousMap.continuous _

theorem continuous_radonEquivRadonLC_symm (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)]
    [Fact (p ≤ 1)] : Continuous (X.radonEquivRadonLC p c).symm :=
  by
  rw [continuous_iff_isClosed]
  intro T hT
  rw [← Equiv.image_eq_preimage]
  apply IsCompact.isClosed
  apply IsCompact.image
  exact IsClosed.isCompact hT
  exact ContinuousMap.continuous _

/-- An auxiliary definition to be used in the constructions below. -/
def radonHomeomorphRadonLC (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    X.radon p c ≃ₜ X.radonLC p c :=
  {
    X.radonEquivRadonLC p
      c with
    continuous_toFun := continuous_radonEquivRadonLC _ _ _
    continuous_invFun := continuous_radonEquivRadonLC_symm _ _ _ }

/-- An auxiliary definition to be used in the constructions below. -/
def radonIsoRadonLC (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    X.radon p c ≅ X.radonLC p c :=
  TopCat.isoOfHomeo (X.radonHomeomorphRadonLC p c)

/-- The functor `X ↦ X.Radon p c` is isomorphic to its locally constant variant. -/
def radonFunctorIsoRadonLCFunctor (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    radonFunctor p c ≅ radonLCFunctor p c :=
  NatIso.ofComponents (fun X => X.radonIsoRadonLC p c) (by intro X Y f; ext; rfl)

/-- A `CompHaus` variant of `Radon_functor`. -/
def radonCompHausFunctor (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] : Profinite.{0} ⥤ CompHaus.{0}
    where
  obj X := CompHaus.of <| X.radon p c
  map X Y f := (radonFunctor p c).map f
  map_id := (radonFunctor p c).map_id
  map_comp _ _ _ f g := (radonFunctor p c).map_comp f g

/-- The functor `X ↦ X.Radon p c` is isomorphic to its locally constant variant.
This is a variant taking values in `CompHaus` as opposed to `Top`. -/
def radonCompHausFunctorIsoRadonLCCompHausFunctor (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    radonCompHausFunctor p c ≅ radonLCCompHausFunctor p c :=
  NatIso.ofComponents
    (fun X =>
      { hom := (radonFunctorIsoRadonLCFunctor p c).hom.app X
        inv := (radonFunctorIsoRadonLCFunctor p c).inv.app X
        hom_inv_id := by erw [← NatTrans.comp_app, Iso.hom_inv_id]; rfl
        inv_hom_id := by erw [← NatTrans.comp_app, Iso.inv_hom_id]; rfl })
    (by intros; ext; rfl)

/-- The cone exhibiting `X.Radon p c` as the limit of `T.Radon p c` where
`T` varies over the discrete quotients of `X`. -/
def radonCompHausCone (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    Cone (X.diagram ⋙ radonCompHausFunctor p c) :=
  (radonCompHausFunctor p c).mapCone X.asLimitCone

/-- X.Radon_CompHaus_cone p c` is a limit cone, as promised. -/
def isLimitRadonCompHausCone (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    IsLimit (X.radonCompHausCone p c)
    where
  lift S :=
    (X.isLimitRadonLCCompHausCone p c).lift
        ⟨S.pt, S.π ≫ whiskerLeft _ (radonCompHausFunctorIsoRadonLCCompHausFunctor p c).hom⟩ ≫
      (radonCompHausFunctorIsoRadonLCCompHausFunctor p c).inv.app _
  fac := by
    intro S j
    erw [Category.assoc, ← NatTrans.naturality, (X.is_limit_Radon_LC_CompHaus_cone p c).fac_assoc,
      ← NatIso.app_inv, Iso.comp_inv_eq]
    rfl
  uniq := by
    intro S m hm
    rw [← NatIso.app_inv, Iso.eq_comp_inv]
    apply (X.is_limit_Radon_LC_CompHaus_cone p c).hom_ext; intro j
    erw [(X.is_limit_Radon_LC_CompHaus_cone p c).fac]
    dsimp; rw [← hm]
    simp only [Category.assoc]
    erw [← NatTrans.naturality]

/-- The comparison between `Radon_LC` and `real_measures p` taking
values in `CompHaus` instead of `Top`, and restricted to the discrete quotients of `X`. -/
def radonLCCompHausComparison (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    X.diagram ⋙ radonLCCompHausFunctor p c ≅
      X.fintypeDiagram ⋙ RealMeasures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c :=
  NatIso.ofComponents
    (fun T =>
      { hom := (X.radonLCComparison p c).hom.app _
        inv := (X.radonLCComparison p c).inv.app _
        hom_inv_id := by erw [← NatTrans.comp_app, Iso.hom_inv_id]; rfl
        inv_hom_id := by erw [← NatTrans.comp_app, Iso.inv_hom_id]; rfl })
    (by
      intro S T i; dsimp
      erw [(X.Radon_LC_comparison p c).hom.naturality]; rfl)

/-- The comparison between `Radon` and `real_measures p`
restricted to the discrete quotients of `X`. -/
def radonCompHausComparison (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    X.diagram ⋙ radonCompHausFunctor p c ≅
      X.fintypeDiagram ⋙ RealMeasures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c :=
  isoWhiskerLeft _ (radonCompHausFunctorIsoRadonLCCompHausFunctor _ _) ≪≫
    radonLCCompHausComparison _ _ _

/-- An auxiliary definition to be used in the constructions below. -/
def radonIsoLimit (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    CompHaus.of (X.radon p c) ≅
      limit (X.fintypeDiagram ⋙ RealMeasures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c) :=
  (X.isLimitRadonCompHausCone p c).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (radonCompHausComparison _ _ _)

/-- The compact Hausdorff space `X.Radon p c` is isomorphic to the limit of
`real_measures p T` as `T` varies over the discrete quotients of `X`.
-/
def radonIsoRealMeasures (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    CompHaus.of (X.radon p c) ≅
      (CompHausFiltPseuNormGrp₁.level.obj c).obj
        ((Profinite.extend (RealMeasures.functor p)).obj X) :=
  radonIsoLimit _ _ _ ≪≫
    HasLimit.isoOfNatIso (Functor.associator _ _ _).symm ≪≫
      (limit.isLimit _).conePointUniqueUpToIso
        (isLimitOfPreserves (CompHausFiltPseuNormGrp₁.level.obj c)
          (limit.isLimit (X.fintypeDiagram ⋙ RealMeasures.functor p)))

end Profinite

