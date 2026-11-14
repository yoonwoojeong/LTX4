import LiquidTensorExperiment.Radon.LCComparison

#align_import Radon.LC_limit

open scoped NNReal BigOperators Classical

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

namespace Profinite

/-- This is the cone which will exhibit `X.Radon_LC p c` as the limit of `T.Radon_LC p c`
where `T` varies over the discrete quotients of `X`.
-/
def radonLCCone (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] :
    Cone (X.diagram ⋙ radonLCFunctor p c) :=
  (radonLCFunctor p c).mapCone X.asLimitCone

namespace IsLimitRadonLCCone

variable (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)]

/-- An auxiliary definition to be used in the constructions below. -/
def linearMap (S : Cone (X.diagram ⋙ radonLCFunctor p c)) (t : S.pt) : LocallyConstant X ℝ →ₗ[ℝ] ℝ
    where
  toFun e := (S.π.app e.DiscreteQuotient t).1 e.locally_constant_lift
  map_add' := by
    intro e₁ e₂
    let W₁ := e₁.discreteQuotient
    let W₂ := e₂.discreteQuotient
    let W₁₂ := (e₁ + e₂).DiscreteQuotient
    let W := W₁ ⊓ W₂ ⊓ W₁₂
    let π₁ : W ⟶ W₁ := hom_of_le (le_trans inf_le_left inf_le_left)
    let π₂ : W ⟶ W₂ := hom_of_le (le_trans inf_le_left inf_le_right)
    let π₁₂ : W ⟶ W₁₂ := hom_of_le inf_le_right
    rw [← S.w π₁, ← S.w π₂, ← S.w π₁₂]
    dsimp [Radon_LC_functor, map_Radon_LC, WeakDual.comap, ContinuousMap.comapLC]
    erw [← ((S.π.app W) t).1.map_add]; congr 1
    ext ⟨⟩; rfl
  map_smul' := by
    intro r e
    let W₁ := e.discreteQuotient
    let W₂ := (r • e).DiscreteQuotient
    let W := W₁ ⊓ W₂
    let π₁ : W ⟶ W₁ := hom_of_le inf_le_left
    let π₂ : W ⟶ W₂ := hom_of_le inf_le_right
    rw [← S.w π₁, ← S.w π₂]
    dsimp [Radon_LC_functor, map_Radon_LC, WeakDual.comap, ContinuousMap.comapLC]
    rw [← smul_eq_mul]
    erw [← ((S.π.app W) t).1.map_smul]; congr 1
    ext ⟨⟩; rfl

variable [Fact (p ≤ 1)]

/-- An auxiliary definition to be used in the constructions below. -/
def weakDual (S : Cone (X.diagram ⋙ radonLCFunctor p c)) (t : S.pt) :
    WeakDual ℝ (LocallyConstant X ℝ) :=
  LinearMap.mkContinuousOfExistsBound (linearMap X p c S t)
    (by
      use c ^ (1 / (p : ℝ))
      intro e
      suffices ‖LinearMap X p c S t e‖₊ ≤ c ^ (1 / (p : ℝ)) * ‖e‖₊ by
        exact_mod_cast this
      have hp : 0 < (p : ℝ) := by exact_mod_cast Fact.out (0 < p)
      have hp' : (p : ℝ) ≠ 0 := ne_of_gt hp
      rw [← NNReal.rpow_le_rpow_iff hp, NNReal.mul_rpow, ← NNReal.rpow_mul]
      rw [show 1 / (p : ℝ) * p = 1 by field_simp, NNReal.rpow_one]
      have H := ((S.π.app e.discreteQuotient) t).2 ⊥
      replace H := mul_le_mul H (le_refl (‖e‖₊ ^ (p : ℝ))) (zero_le _) (zero_le _)
      refine' le_trans _ H
      rw [mul_comm, Finset.mul_sum]
      nth_rw 1 [e.eq_sum]
      simp_rw [map_sum, LinearMap.map_smul]
      refine' le_trans (Real.pow_nnnorm_sum_le _ _ _) _
      have :
        ∑ x : (⊥ : DiscreteQuotient e.discreteQuotient),
            ‖e‖₊ ^ (p : ℝ) *
              ‖(((S.π.app e.discreteQuotient) t).val
                    ((⊥ : DiscreteQuotient e.discreteQuotient).fibre x).indicatorLC)‖₊ ^
                (p : ℝ) =
          ∑ x : e.discreteQuotient,
            ‖e‖₊ ^ (p : ℝ) *
              ‖((LinearMap X p c S t) (e.discreteQuotient.fibre x).indicatorLC)‖₊ ^
                (p : ℝ) :=
        by
        fapply Finset.sum_bij'
        · intro a _; exact discrete_quotient.equivBot.symm a
        · intros; exact Finset.mem_univ _
        · intros; congr 3; dsimp [LinearMap]
          let T₁ := e.discreteQuotient
          let T₂ :=
            (e.discreteQuotient.fibre
                  (discrete_quotient.equivBot.symm a)).indicatorLC.DiscreteQuotient
          let T := T₁ ⊓ T₂
          let π₁ : T ⟶ T₁ := hom_of_le inf_le_left
          let π₂ : T ⟶ T₂ := hom_of_le inf_le_right
          rw [← S.w π₁, ← S.w π₂]
          dsimp [Radon_LC_functor, map_Radon_LC, WeakDual.comap]
          congr 1
          ext b; obtain ⟨b, rfl⟩ := DiscreteQuotient.proj_surjective _ b
          dsimp [ContinuousMap.comapLC]
          change _ = (e.discreteQuotient.fibre (discrete_quotient.equivBot.symm a)).indicatorLC b
          dsimp only [TopologicalSpace.Clopens.indicatorLC_apply]
          rw [show X.fintype_diagram.map π₁ (T.proj b) = T₁.proj b by rfl]
          erw [DiscreteQuotient.mem_fibre_iff']
        · intro a _; exact DiscreteQuotient.equivBot a
        · intros; exact Finset.mem_univ _
        · intros; apply Equiv.apply_symm_apply
        · intros; apply Equiv.symm_apply_apply
      rw [this]; clear this
      apply Finset.sum_le_sum; rintro x -
      rw [smul_eq_mul, nnnorm_mul, NNReal.mul_rpow]
      refine' mul_le_mul _ (le_refl _) (zero_le _) (zero_le _)
      apply NNReal.rpow_le_rpow _ (le_of_lt hp)
      obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ x
      change ‖e x‖₊ ≤ _
      apply LocallyConstant.nnnorm_apply_le_nnnorm)

/-- An auxiliary definition to be used in the constructions below. -/
def radonLC (S : Cone (X.diagram ⋙ radonLCFunctor p c)) (t : S.pt) : X.radonLC p c
    where
  val := weakDual X p c S t
  property := by
    intro T
    dsimp [WeakDual, LinearMap]
    convert (S.π.app T t).2 ⊥ using 1
    fapply Finset.sum_bij'
    · intro a _; exact DiscreteQuotient.equivBot a
    · intros; apply Finset.mem_univ
    · intro a ha; congr 2
      let W := (T.fibre a).indicatorLC.DiscreteQuotient
      let E := T ⊓ W
      let π₁ : E ⟶ T := hom_of_le inf_le_left
      let π₂ : E ⟶ W := hom_of_le inf_le_right
      rw [← S.w π₁, ← S.w π₂]
      dsimp [Radon_LC_functor, map_Radon_LC, WeakDual.comap, ContinuousMap.comapLC]
      congr 1; ext b; obtain ⟨b, rfl⟩ := DiscreteQuotient.proj_surjective _ b
      change (T.fibre a).indicatorLC b = _
      dsimp [TopologicalSpace.Clopens.indicatorLC_apply]
      erw [DiscreteQuotient.mem_fibre_iff]
    · intro a _; exact discrete_quotient.equivBot.symm a
    · intros; apply Finset.mem_univ
    · intros; apply Equiv.symm_apply_apply
    · intros; apply Equiv.apply_symm_apply

theorem continuous_radonLC (S : Cone (X.diagram ⋙ radonLCFunctor p c)) :
    Continuous (radonLC X p c S) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro e; dsimp [WeakDual, LinearMap]
  refine' Continuous.comp (WeakDual.eval_continuous _) _
  refine' Continuous.comp continuous_subtype_val (ContinuousMap.continuous _)

end IsLimitRadonLCCone

/-- `X.Radon_LC_cone p c` is a limit cone, as promised. -/
def isLimitRadonLCCone (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    IsLimit (X.radonLCCone p c)
    where
  lift S := ⟨IsLimitRadonLCCone.radonLC X p c S, IsLimitRadonLCCone.continuous_radonLC X p c S⟩
  fac := by
    intro S T; ext t e
    dsimp [Radon_LC_cone, Radon_LC_functor, map_Radon_LC, IsLimitRadonLCCone.weakDual,
      IsLimitRadonLCCone.radonLC, WeakDual.comap, IsLimitRadonLCCone.linearMap]
    let W₁ := ((ContinuousMap.comapLC (X.as_limit_cone.π.app T)) e).DiscreteQuotient
    let W := W₁ ⊓ T
    let π₁ : W ⟶ W₁ := hom_of_le inf_le_left
    let π₂ : W ⟶ T := hom_of_le inf_le_right
    rw [← S.w π₁, ← S.w π₂]
    dsimp [Radon_LC_functor, map_Radon_LC, WeakDual.comap]
    congr 1; ext ⟨⟩; rfl
  uniq := by
    intro S m hm
    ext t T
    specialize hm T.discrete_quotient
    apply_fun fun e => (e t).1 T.locally_constant_lift at hm 
    convert hm using 1
    dsimp [IsLimitRadonLCCone.radonLC, IsLimitRadonLCCone.weakDual, Radon_LC_cone,
      Radon_LC_functor, map_Radon_LC, WeakDual.comap]
    congr 1; ext; rfl

instance compactSpace_radonLC_of_discreteQuotient (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)]
    [Fact (p ≤ 1)] (T : DiscreteQuotient X) : CompactSpace (radonLC (X.diagram.obj T) p c) :=
  by
  change CompactSpace ((X.diagram ⋙ Radon_LC_functor p c).obj T)
  let e := TopCat.homeoOfIso ((Radon_LC_comparison X p c).app T)
  have :
    CompactSpace
      ((X.fintype_diagram ⋙
            RealMeasures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙ compHausToTop).obj
        T) :=
    by
    change
      CompactSpace
        ((X.fintype_diagram ⋙ RealMeasures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c).obj T)
    infer_instance
  exact e.symm.compactSpace

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCCompHausDiagram (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    DiscreteQuotient X ⥤ CompHaus.{0}
    where
  obj T := CompHaus.of <| (X.diagram.obj T).radonLC p c
  map S T e := (radonLCFunctor p c).map <| X.diagram.map e
  map_id := by
    intro T
    rw [X.diagram.map_id]
    rw [(Radon_LC_functor p c).map_id]
    rfl
  map_comp := by
    intro S T W f g
    rw [X.diagram.map_comp]
    rw [(Radon_LC_functor p c).map_comp]
    rfl

instance compactSpace_radonLC (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    CompactSpace (X.radonLC p c) :=
  by
  let e₁ : X.Radon_LC p c ≅ limit (X.diagram ⋙ Radon_LC_functor p c) :=
    (X.is_limit_Radon_LC_cone p c).conePointUniqueUpToIso (limit.isLimit _)
  let e₂ :
    CompHaus_to_Top.obj (limit <| X.Radon_LC_CompHaus_diagram p c) ≅
      limit (X.diagram ⋙ Radon_LC_functor p c) :=
    (CategoryTheory.Limits.isLimitOfPreserves compHausToTop (limit.isLimit _)).conePointUniqueUpToIso
      (limit.isLimit _)
  let e := TopCat.homeoOfIso (e₂ ≪≫ e₁.symm)
  have : CompactSpace (CompHaus_to_Top.obj (limit <| X.Radon_LC_CompHaus_diagram p c)) := by
    show CompactSpace ↥(limit <| X.Radon_LC_CompHaus_diagram p c); infer_instance
  exact e.compactSpace

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCCompHausFunctor (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] : Profinite.{0} ⥤ CompHaus.{0}
    where
  obj X := CompHaus.of <| X.radonLC p c
  map X Y f := (radonLCFunctor p c).map f
  map_id := (radonLCFunctor p c).map_id
  map_comp X Y Z f g := (radonLCFunctor p c).map_comp f g

/-- This is the cone which will exhibit `X.Radon_LC p c` as the limit of `T.Radon_LC p c`
where `T` varies over the discrete quotients of `X`.
This is a variant of `X.Radon_LC_cone` taking values in `CompHaus` as opposed to `Top`.
-/
def radonLCCompHausCone (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    Cone (X.diagram ⋙ radonLCCompHausFunctor p c) :=
  (radonLCCompHausFunctor p c).mapCone X.asLimitCone

/-- `X.Radon_LC_CompHaus_cone p c` is a limit cone, as promised.
This is another key construction which will be used in the main comparison between
Radon measures and `ℳ_p`.
-/
def isLimitRadonLCCompHausCone (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    IsLimit (X.radonLCCompHausCone p c) :=
  by
  apply CategoryTheory.Limits.isLimitOfReflects compHausToTop
  apply is_limit_Radon_LC_cone

end Profinite

