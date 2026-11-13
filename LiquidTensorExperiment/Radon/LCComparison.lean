import LiquidTensorExperiment.Radon.Defs

#align_import Radon.LC_comparison

open scoped NNReal BigOperators Classical

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

namespace Profinite

/-- Consider an element of `X.Radon_LC p c` as a function on the
type of locally constant functions. -/
def radonLCToFun (X : Profinite.{0}) (p c : ℝ≥0) : X.radonLC p c → LocallyConstant X ℝ → ℝ :=
  fun μ => μ.1

/-- Consider an element of `X.Radon p c` as a function on the
type of continuous functions. -/
def radonToFun (X : Profinite.{0}) (p c : ℝ≥0) : X.radon p c → C(X, ℝ) → ℝ := fun μ => μ.1

theorem radonLCToFun_injective (X : Profinite.{0}) (p c : ℝ≥0) :
    Function.Injective (X.radonLCToFun p c) :=
  by
  intro a b h; ext x : 2
  exact congr_fun h x

theorem radonToFun_injective (X : Profinite.{0}) (p c : ℝ≥0) :
    Function.Injective (X.radonToFun p c) :=
  by
  intro a b h; ext x : 2
  exact congr_fun h x

theorem radonLCToFun_continuous (X : Profinite.{0}) (p c : ℝ≥0) : Continuous (X.radonLCToFun p c) :=
  by
  apply continuous_pi
  intro f
  refine' Continuous.comp (WeakDual.eval_continuous f) continuous_subtype_val

theorem radonToFun_continuous (X : Profinite.{0}) (p c : ℝ≥0) : Continuous (X.radonToFun p c) :=
  by
  apply continuous_pi
  intro f
  refine' Continuous.comp (WeakDual.eval_continuous f) continuous_subtype_val

--WHY!?!?!?
instance t2Space_fun_to_R (X : Type _) : T2Space (X → ℝ) :=
  @Pi.t2Space X (fun _ => ℝ) inferInstance
    (by
      intro a; dsimp
      infer_instance)

instance t2Space_radonLC (X : Profinite.{0}) (p c : ℝ≥0) : T2Space (X.radonLC p c) :=
  ⟨fun f g h =>
    separated_by_continuous (X.radonLCToFun_continuous p c) <| (X.radonLCToFun_injective p c).Ne h⟩

instance t2Space_radon (X : Profinite.{0}) (p c : ℝ≥0) : T2Space (X.radon p c) :=
  ⟨fun f g h =>
    separated_by_continuous (X.radonToFun_continuous p c) <| (X.radonToFun_injective p c).Ne h⟩

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCComparisonComponentEquivAux (X : Profinite.{0}) (p : ℝ≥0) (T : DiscreteQuotient X) :
    WeakDual ℝ (LocallyConstant (X.diagram.obj T) ℝ) ≃ RealMeasures p (X.fintypeDiagram.obj T)
    where
  toFun μ t := μ (Clopens.indicatorLC <| DiscreteQuotient.fibre ⊥ (DiscreteQuotient.equivBot t))
  invFun μ :=
    { toFun := fun e => ∑ t : T, μ t * e t
      map_add' := by
        intro x y
        dsimp
        simp only [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r e; dsimp
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, mul_comm r]
      cont := by
        apply continuous_finset_sum; intro t ht
        refine' Continuous.comp (continuous_mul_left (μ t)) _
        apply LocallyConstant.continuous_eval }
  left_inv := by
    intro μ; ext t; dsimp
    have : Fintype (X.diagram.obj T) := by show Fintype T; · infer_instance
    conv_rhs => rw [t.eq_sum_of_fintype]
    rw [μ.map_sum]
    apply Finset.sum_congr; convert rfl
    intro t ht
    rw [μ.map_smul, mul_comm]; change _ = _ * _
    congr 3; ext w; change _ = _ ↔ _ = _
    constructor
    · intro h; apply_fun discrete_quotient.equiv_bot.symm at h 
      erw [discrete_quotient.equiv_bot.symm_apply_apply] at h 
      rw [discrete_quotient.equiv_bot.symm_apply_apply] at h 
      exact h
    · intro h; rw [h]; rfl
  right_inv := by
    intro μ; ext (t : T); dsimp
    rw [Finset.sum_eq_single t]
    · change _ * ite _ _ _ = _; rw [if_pos]; erw [mul_one]
      change _ = _; rfl
    · intro s _ hs; change _ * ite _ _ _ = _; rw [if_neg, MulZeroClass.mul_zero]
      change _ ≠ _; contrapose! hs
      apply_fun discrete_quotient.equiv_bot.symm at hs 
      erw [discrete_quotient.equiv_bot.symm_apply_apply] at hs 
      rw [discrete_quotient.equiv_bot.symm_apply_apply] at hs 
      exact hs
    · intro h; exact False.elim (h (Finset.mem_univ _))

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem bddLC_iff_comparison (X : Profinite.{0}) (T : DiscreteQuotient X) (p c : ℝ≥0) [Fact (0 < p)]
    [Fact (p ≤ 1)] (f : WeakDual ℝ (LocallyConstant (X.diagram.obj T) ℝ)) :
    f.BddLC p c ↔
      X.radonLCComparisonComponentEquivAux p T f ∈
        PseudoNormedGroup.filtration (RealMeasures p (X.fintypeDiagram.obj T)) c :=
  by
  constructor
  · intro h; change ∑ t : T, _ ≤ _; specialize h ⊥
    convert h using 1
    fapply Finset.sum_bij'
    · intro t _; exact DiscreteQuotient.equivBot t
    · intros; exact Finset.mem_univ _
    · intro t _; congr
    · intro t _; exact discrete_quotient.equiv_bot.symm t
    · intros; exact Finset.mem_univ _
    · intros; apply Equiv.apply_symm_apply
    · intros; exact discrete_quotient.equiv_bot.apply_symm_apply _
  · intro h E; change ∑ e : E, _ ≤ _
    change ∑ t : T, _ ≤ _ at h 
    dsimp [Radon_LC_comparison_component_equiv_aux] at h 
    refine' le_trans _ h
    have :
      ∀ e : E,
        (E.fibre e).indicatorLC =
          ∑ t in finset.univ.filter fun t : T => E.proj t = e,
            ((⊥ : DiscreteQuotient T).fibre (DiscreteQuotient.equivBot t)).indicatorLC :=
      by
      intro e
      ext (q : T); rw [LocallyConstant.sum_apply]
      change ite (_ = _) (1 : ℝ) 0 = _; split_ifs with hh hh
      · rw [Finset.sum_eq_single q]
        change _ = ite (_ = _) (1 : ℝ) _; erw [if_pos rfl]
        · intro t ht hh
          change ite (_ = _) _ (0 : ℝ) = 0; rw [if_neg]
          contrapose! hh
          rw [Finset.mem_filter] at ht 
          apply_fun discrete_quotient.equiv_bot.symm at hh 
          erw [discrete_quotient.equiv_bot.symm_apply_apply] at hh 
          rw [discrete_quotient.equiv_bot.symm_apply_apply] at hh 
          exact hh.symm
        · intro h; refine' False.elim (h _); rw [Finset.mem_filter]
          refine' ⟨Finset.mem_univ _, hh⟩
      · symm; apply Finset.sum_eq_zero
        intro t ht; rw [Finset.mem_filter] at ht 
        change ite (_ = _) _ (0 : ℝ) = 0; rw [if_neg]
        contrapose! hh
        apply_fun discrete_quotient.equiv_bot.symm at hh 
        erw [discrete_quotient.equiv_bot.symm_apply_apply] at hh 
        rw [discrete_quotient.equiv_bot.symm_apply_apply] at hh 
        rw [hh]
        exact ht.2
    simp_rw [this, f.map_sum]; clear this
    have :
      ∑ x : ↥E,
          «expr∥ ∥₊»
              (∑ i : ↥T in Finset.filter (fun t : ↥T => E.proj t = x) Finset.univ,
                f ((⊥ : DiscreteQuotient T).fibre (DiscreteQuotient.equivBot i)).indicatorLC) ^
            (p : ℝ) ≤
        ∑ x : E,
          ∑ i : T in Finset.filter (fun t : ↥T => E.proj t = x) Finset.univ,
            «expr∥ ∥₊»
                (f ((⊥ : DiscreteQuotient T).fibre (DiscreteQuotient.equivBot i)).indicatorLC) ^
              (p : ℝ) :=
      by
      apply Finset.sum_le_sum
      intro e _
      apply Real.pow_nnnorm_sum_le
    refine' le_trans this _; clear this
    erw [← Finset.sum_biUnion]
    have :
      (finset.univ.bUnion fun x : ↥E => Finset.filter (fun t : ↥T => E.proj t = x) Finset.univ) =
        Finset.univ :=
      by
      rw [Finset.eq_univ_iff_forall]
      intro t
      rw [Finset.mem_biUnion]
      refine' ⟨E.proj t, Finset.mem_univ _, _⟩
      rw [Finset.mem_filter]
      refine' ⟨Finset.mem_univ _, rfl⟩
    rw [this]
    intro a ha b hb hh q; dsimp; rw [Finset.mem_inter]; rintro ⟨h1, h2⟩
    simp only [Finset.not_mem_empty]; apply hh
    rw [Finset.mem_filter] at h1 h2 
    rw [← h1.2, h2.2]

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCComparisonComponentEquiv (X : Profinite.{0}) (T : DiscreteQuotient X) (p c : ℝ≥0)
    [Fact (0 < p)] [Fact (p ≤ 1)] :
    radonLC (X.diagram.obj T) p c ≃
      PseudoNormedGroup.filtration (RealMeasures p (X.fintypeDiagram.obj T)) c
    where
  toFun μ :=
    ⟨X.radonLCComparisonComponentEquivAux p T μ.1, by rw [← bdd_LC_iff_comparison]; exact μ.2⟩
  invFun μ :=
    ⟨(X.radonLCComparisonComponentEquivAux p T).symm μ.1,
      by
      have := μ.2
      rw [← (X.Radon_LC_comparison_component_equiv_aux p T).apply_symm_apply μ.val] at this 
      rw [← bdd_LC_iff_comparison] at this 
      exact this⟩
  left_inv := by
    intro μ; ext1
    apply (X.Radon_LC_comparison_component_equiv_aux p T).symm_apply_apply
  right_inv := by
    intro μ; ext1
    apply (X.Radon_LC_comparison_component_equiv_aux p T).apply_symm_apply

theorem continuous_radonLCComparisonComponentEquiv_symm (X : Profinite.{0}) (T : DiscreteQuotient X)
    (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    Continuous (X.radonLCComparisonComponentEquiv T p c).symm :=
  by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro y
  apply continuous_finset_sum
  rintro t -
  refine' Continuous.comp (continuous_mul_right (y t)) _
  refine' Continuous.comp (continuous_apply t) continuous_subtype_val

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCComparisonComponentHomeo (X : Profinite.{0}) (T : DiscreteQuotient X) (p c : ℝ≥0)
    [Fact (0 < p)] [Fact (p ≤ 1)] :
    radonLC (X.diagram.obj T) p c ≃ₜ
      PseudoNormedGroup.filtration (RealMeasures p (X.fintypeDiagram.obj T)) c :=
  {
    X.radonLCComparisonComponentEquiv T p
      c with
    continuous_toFun := by
      rw [continuous_iff_isClosed]; intro S hS
      erw [← (Radon_LC_comparison_component_equiv _ _ _ _).symm.image_eq_preimage]
      apply IsCompact.isClosed
      apply hS.is_compact.image
      apply continuous_Radon_LC_comparison_component_equiv_symm
    continuous_invFun := continuous_radonLCComparisonComponentEquiv_symm _ _ _ _ }

/-- An auxiliary definition to be used in the constructions below. -/
def radonLCComparisonComponentIso (X : Profinite.{0}) (T : DiscreteQuotient X) (p c : ℝ≥0)
    [Fact (0 < p)] [Fact (p ≤ 1)] :
    radonLC (X.diagram.obj T) p c ≅
      TopCat.of (PseudoNormedGroup.filtration (RealMeasures p (X.fintypeDiagram.obj T)) c) :=
  TopCat.isoOfHomeo <| radonLCComparisonComponentHomeo _ _ _ _

theorem Radon_LC_comparison_naturality_aux (X : Profinite.{0}) (S T : DiscreteQuotient X)
    (f : S ⟶ T) (t : T) (q : S) :
    ((⊥ : DiscreteQuotient T).fibre (DiscreteQuotient.equivBot t)).indicatorLC
        (X.fintypeDiagram.map f q) =
      ∑ i : S in Finset.univ.filterₓ fun j => X.fintypeDiagram.map f j = t,
        ((⊥ : DiscreteQuotient S).fibre (DiscreteQuotient.equivBot i)).indicatorLC q :=
  by
  by_cases H : X.fintype_diagram.map f q = t
  · rw [@Finset.sum_eq_single ℝ S _
        (Finset.filter (fun j : (X.fintype_diagram.obj S).α => X.fintype_diagram.map f j = t)
          Finset.univ)
        (fun i => ((⊥ : DiscreteQuotient S).fibre (DiscreteQuotient.equivBot i)).indicatorLC q) q _
        _]
    · dsimp [clopens.indicator_LC, Set.indicator, DiscreteQuotient.fibre]
      erw [if_pos rfl]
      rw [if_pos]; congr 1
    · intro s hs hsq; rw [Finset.mem_filter] at hs 
      dsimp [clopens.indicator_LC, Set.indicator, DiscreteQuotient.fibre]
      rw [if_neg]
      contrapose! hsq
      apply_fun discrete_quotient.equiv_bot.symm at hsq 
      rw [Equiv.symm_apply_apply] at hsq 
      erw [Equiv.symm_apply_apply] at hsq 
      exact hsq.symm
    · intro hq
      erw [Finset.mem_filter] at hq 
      push_neg at hq ; specialize hq (Finset.mem_univ _)
      exact False.elim (hq H)
  · change ite _ _ _ = _; rw [if_neg]
    · symm; apply Finset.sum_eq_zero
      intro s hs; rw [Finset.mem_filter] at hs ; replace hs := hs.2
      change ite _ _ _ = _; rw [if_neg]
      contrapose! H
      dsimp [DiscreteQuotient.fibre] at H 
      apply_fun discrete_quotient.equiv_bot.symm at H 
      rw [Equiv.symm_apply_apply] at H 
      erw [Equiv.symm_apply_apply] at H 
      rw [H]; exact hs
    · contrapose! H
      dsimp [DiscreteQuotient.fibre] at H 
      apply_fun discrete_quotient.equiv_bot.symm at H 
      rw [Equiv.symm_apply_apply] at H 
      erw [Equiv.symm_apply_apply] at H 
      exact H

/-- The restriction of `Radon_LC_functor` to the discrete quotients of a profinite set `X`
is isomorphic to the `c`-th level of the restriction of `real_measures.functor p`.
This is one of the key isomorphisms used in the comparison between Radon measures and `ℳ_p`.
 -/
def radonLCComparison (X : Profinite.{0}) (p c : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] :
    X.diagram ⋙ radonLCFunctor p c ≅
      X.fintypeDiagram ⋙
        RealMeasures.functor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ⋙ compHausToTop :=
  NatIso.ofComponents (fun T => radonLCComparisonComponentIso _ _ _ _)
    (by
      intro S T f
      ext a t
      dsimp [Radon_functor, Radon_LC_comparison_component_iso, Radon_LC_comparison_component_homeo,
        Radon_LC_comparison_component_equiv, Radon_LC_comparison_component_equiv_aux,
        Radon_LC_functor, RealMeasures.mapHom, CompHausFiltPseuNormGrp₁.level, map_Radon_LC,
        WeakDual.comap]
      let aa : WeakDual ℝ (LocallyConstant S ℝ) := a.1
      erw [← aa.map_sum]
      congr 1
      ext q
      rw [LocallyConstant.sum_apply]
      dsimp [ContinuousMap.comapLC]
      convert Radon_LC_comparison_naturality_aux X S T f t q)

end Profinite

