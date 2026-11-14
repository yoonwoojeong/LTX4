import LiquidTensorExperiment.Radon.Setup

#align_import Radon.defs

open scoped NNReal BigOperators Classical

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

namespace Profinite

/-- The space of signed `p`-Radon measures on `X`, bounded by `c`.
-/
def radon (X : Profinite.{0}) (p c : ℝ≥0) : TopCat.{0} :=
  TopCat.of { μ : WeakDual ℝ C(X, ℝ) // μ.bdd p c }
deriving TopologicalSpace

/-- The space of signed `p`-Radon measures on `X`, bounded by `c`.
This is a variant of `Radon` which uses the dual of locally constant functions
as opposed to continuous functions, to be used an an auxiliary declaration in the
constructions below.
-/
def radonLC (X : Profinite.{0}) (p c : ℝ≥0) : TopCat.{0} :=
  TopCat.of { μ : WeakDual ℝ (LocallyConstant X ℝ) // μ.BddLC p c }
deriving TopologicalSpace

/-- A continuous map `X → Y` induces a map between spaces of `p`-Radon measures
with a given bound.
-/
def mapRadon {X Y : Profinite.{0}} (f : X ⟶ Y) (p c : ℝ≥0) [Fact (0 < p)] :
    X.radon p c ⟶ Y.radon p c
    where
  toFun μ := ⟨WeakDual.comap f.comap μ.1, WeakDual.bddComap _ μ.2 _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine' Continuous.comp _ continuous_subtype_val
    exact ContinuousLinearMap.continuous _

/-- A continuous map `X → Y` induces a map between spaces of `p`-Radon measures
with a given bound. (This is the locally constant variant.)
-/
def mapRadonLC {X Y : Profinite.{0}} (f : X ⟶ Y) (p c : ℝ≥0) [Fact (0 < p)] :
    X.radonLC p c ⟶ Y.radonLC p c
    where
  toFun μ := ⟨WeakDual.comap f.comapLC μ.1, WeakDual.bddLCComap _ μ.2 _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine' Continuous.comp _ continuous_subtype_val
    exact ContinuousLinearMap.continuous _

/-- The functor sending a topological space to the space of `p`-Radon
measures bounded by `c`.
-/
def radonFunctor (p c : ℝ≥0) [Fact (0 < p)] : Profinite.{0} ⥤ TopCat.{0}
    where
  obj X := X.radon p c
  map X Y f := mapRadon f _ _
  map_id X := by
    ext; dsimp [map_Radon, WeakDual.comap]; congr 1
    ext; rfl
  map_comp X Y Z f g := by ext; rfl

/-- The functor sending a topological space to the space of `p`-Radon
measures bounded by `c`. This is the locally constant variant.
-/
def radonLCFunctor (p c : ℝ≥0) [Fact (0 < p)] : Profinite.{0} ⥤ TopCat.{0}
    where
  obj X := X.radonLC p c
  map X Y f := mapRadonLC f _ _
  map_id X := by ext; dsimp [map_Radon_LC, WeakDual.comap]; congr 1; ext; rfl
  map_comp X Y Z f g := by ext; rfl

/-- An auxiliary definition to be used in the constructions below.
-/
def weakDualCToLC (X : Profinite.{0}) : WeakDual ℝ C(X, ℝ) →L[ℝ] WeakDual ℝ (LocallyConstant X ℝ) :=
  WeakDual.comap <| lcToC _

theorem denseRange_coe₂ (X : Profinite.{0}) :
    DenseRange fun p : LocallyConstant X ℝ × LocallyConstant X ℝ => (lcToC X p.1, lcToC X p.2) :=
  letI : UniformSpace (LocallyConstant.pkg X ℝ).Space := (LocallyConstant.pkg X ℝ).uniformStruct
  (LocallyConstant.pkg X ℝ).dense.Prod_map (LocallyConstant.pkg X ℝ).dense

/-- An auxiliary definition to be used in the constructions below.
-/
def weakDualLCToC (X : Profinite.{0}) : WeakDual ℝ (LocallyConstant X ℝ) →ₗ[ℝ] WeakDual ℝ C(X, ℝ)
    where
  toFun f :=
    { toFun := (LocallyConstant.pkg X ℝ).extend f
      map_add' :=
        by
        letI : UniformSpace (LocallyConstant.pkg X ℝ).Space :=
          (LocallyConstant.pkg X ℝ).uniformStruct
        letI : AddGroup (LocallyConstant.pkg X ℝ).Space := ContinuousMap.addGroup
        letI : TopologicalAddGroup (LocallyConstant.pkg X ℝ).Space :=
          ContinuousMap.topological_add_group
        rw [← Prod.forall']
        refine' isClosed_property (dense_range_coe₂ X) _ _
        · apply isClosed_eq
          · refine' (LocallyConstant.pkg X ℝ).continuous_extend.comp continuous_add
          · refine' Continuous.add _ _ <;>
              refine' (LocallyConstant.pkg X ℝ).continuous_extend.comp _
            exact continuous_fst
            exact continuous_snd
        · rintro ⟨φ, ψ⟩; dsimp only
          have hf := ContinuousLinearMap.uniformContinuous f
          rw [← (lcToC X).map_add]
          erw [(LocallyConstant.pkg X ℝ).extend_coe hf, (LocallyConstant.pkg X ℝ).extend_coe hf,
            (LocallyConstant.pkg X ℝ).extend_coe hf, map_add]
      map_smul' :=
        by
        letI : UniformSpace (LocallyConstant.pkg X ℝ).Space :=
          (LocallyConstant.pkg X ℝ).uniformStruct
        letI : AddGroup (LocallyConstant.pkg X ℝ).Space := ContinuousMap.addGroup
        letI : TopologicalAddGroup (LocallyConstant.pkg X ℝ).Space :=
          ContinuousMap.topological_add_group
        letI : SMul ℝ (LocallyConstant.pkg X ℝ).Space := ContinuousMap.instSMul
        letI : ContinuousSMul ℝ (LocallyConstant.pkg X ℝ).Space := ContinuousMap.continuousSMul
        intro r φ
        apply (LocallyConstant.pkg X ℝ).inductionOn φ <;> clear φ
        · apply isClosed_eq
          ·
            refine'
              (LocallyConstant.pkg X ℝ).continuous_extend.comp (continuous_const.smul continuous_id)
          · refine' continuous_const.smul (LocallyConstant.pkg X ℝ).continuous_extend
        · intro φ
          have hf := ContinuousLinearMap.uniformContinuous f
          erw [← (lcToC X).map_smul, (LocallyConstant.pkg X ℝ).extend_coe hf,
            (LocallyConstant.pkg X ℝ).extend_coe hf, map_smul]
          rfl
      cont := (LocallyConstant.pkg X ℝ).continuous_extend }
  map_add' :=
    by
    letI : UniformSpace (LocallyConstant.pkg X ℝ).Space := (LocallyConstant.pkg X ℝ).uniformStruct
    intro f g; ext ff; dsimp
    apply (LocallyConstant.pkg X ℝ).inductionOn ff
    · apply isClosed_eq
      apply (LocallyConstant.pkg X ℝ).continuous_extend; infer_instance
      let G : C(X, ℝ) → ℝ × ℝ := fun ff =>
        ((LocallyConstant.pkg X ℝ).extend f ff, (LocallyConstant.pkg X ℝ).extend g ff)
      change Continuous ((fun a : ℝ × ℝ => a.1 + a.2) ∘ G)
      refine' Continuous.comp continuous_add _
      apply Continuous.prod_mk
      apply (LocallyConstant.pkg X ℝ).continuous_extend; infer_instance
      apply (LocallyConstant.pkg X ℝ).continuous_extend; infer_instance
    · intro a
      rw [(LocallyConstant.pkg X ℝ).extend_coe]
      rw [(LocallyConstant.pkg X ℝ).extend_coe]
      rw [(LocallyConstant.pkg X ℝ).extend_coe]
      rfl
      any_goals apply ContinuousLinearMap.uniformContinuous
      any_goals infer_instance
  map_smul' :=
    by
    letI : UniformSpace (LocallyConstant.pkg X ℝ).Space := (LocallyConstant.pkg X ℝ).uniformStruct
    intro r f; ext ff; dsimp
    apply (LocallyConstant.pkg X ℝ).inductionOn ff
    · apply isClosed_eq
      apply (LocallyConstant.pkg X ℝ).continuous_extend; infer_instance
      refine' Continuous.comp (continuous_mul_left r) _
      apply (LocallyConstant.pkg X ℝ).continuous_extend; infer_instance
    · intro a
      rw [(LocallyConstant.pkg X ℝ).extend_coe]
      rw [(LocallyConstant.pkg X ℝ).extend_coe]
      rfl
      any_goals infer_instance
      exact f.uniformContinuous
      exact (r • f).UniformContinuous

end Profinite

