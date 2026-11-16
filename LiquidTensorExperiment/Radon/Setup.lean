import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.ContinuousFunction.Algebra
import LiquidTensorExperiment.LocallyConstant.SemiNormedGroup
import LiquidTensorExperiment.LocallyConstant.Completion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.MeanInequalitiesPow
import LiquidTensorExperiment.RealMeasures.Condensed
import LiquidTensorExperiment.ForMathlib.IsLocallyConstant

#align_import Radon.setup

open scoped NNReal BigOperators Classical

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

theorem Real.pow_nnnorm_sum_le {ι : Type _} (S : Finset ι) (r : ι → ℝ) (p : ℝ≥0) [Fact (0 < p)]
    [Fact (p ≤ 1)] : ‖∑ i in S, r i‖₊ ^ (p : ℝ) ≤ ∑ i in S, ‖r i‖₊ ^ (p : ℝ) :=
  by
  refine' Finset.le_sum_of_subadditive (fun x : ℝ => ‖x‖₊ ^ (p : ℝ)) _ _ S r
  · simp only [nnnorm_zero, NNReal.rpow_eq_zero_iff, eq_self_iff_true, Ne.def, NNReal.coe_eq_zero,
      true_and_iff]
    exact ne_of_gt (Fact.out _)
  · intro x y
    dsimp
    refine' le_trans _ (NNReal.rpow_add_le_add_rpow _ _ (nnreal.coe_pos.mpr (Fact.out _)).le _)
    rw [NNReal.rpow_le_rpow_iff (nnreal.coe_pos.mpr (Fact.out _) : 0 < ↑p)]
    apply nnnorm_add_le
    exact (nnreal.coe_le_coe.mpr (Fact.out _)).trans nnreal.coe_one.le

namespace LocallyConstant

instance normedSpace (X : Type _) [TopologicalSpace X] [CompactSpace X] :
    NormedSpace ℝ (LocallyConstant X ℝ) :=
  { (inferInstance : Module ℝ _) with
    norm_smul_le := fun a f => by
      simpa only [norm_def, coe_smul, Pi.smul_apply, Algebra.id.smul_eq_mul, Real.norm_eq_abs,
        abs_mul, mul_comm (abs a)] using (Real.iSup_mul_of_nonneg (abs_nonneg _) _).symm.le }

theorem nnnorm_apply_le_nnnorm (X : Type _) [TopologicalSpace X] [CompactSpace X]
    (e : LocallyConstant X ℝ) (x : X) : ‖e x‖₊ ≤ ‖e‖₊ :=
  by
  change _ ≤ Sup _
  apply le_csSup
  let S := _; change BddAbove S; suffices : IsCompact S; apply IsCompact.bddAbove this
  apply isCompact_range; refine' Continuous.comp _ e.continuous; exact continuous_norm
  use x; rfl

/-- The evaluation map at a point of a topological space, bundled as a linear map from
locally constant functions to the real numbers. -/
def linearEval (X : Type _) [TopologicalSpace X] (x : X) : LocallyConstant X ℝ →ₗ[ℝ] ℝ
    where
  toFun e := e x
  map_add' f g := rfl
  map_smul' r f := rfl

theorem continuous_eval (X : Type _) [TopologicalSpace X] [CompactSpace X] (x : X) :
    Continuous fun e : LocallyConstant X ℝ => e x :=
  by
  change Continuous (LocallyConstant.linearEval X x)
  let E := LinearMap.mkContinuousOfExistsBound (LocallyConstant.linearEval X x) _
  swap
  use 1; intro e; rw [one_mul]; apply nnnorm_apply_le_nnnorm
  exact E.continuous

end LocallyConstant

namespace TopologicalSpace.Clopens

theorem indicator_continuous {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (U : Clopens X) (f : X → Y) (hf : Continuous f) : Continuous (Set.indicator (U : Set X) f) :=
  by
  constructor; intro V hV
  set W : Set X := (U : Set X).indicator f ⁻¹' V
  by_cases h0 : (0 : Y) ∈ V
  · suffices W = f ⁻¹' V ∪ Uᶜ by rw [this]; exact (hV.preimage hf).union U.clopen.compl.isOpen
    classical
    ext x
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, SetLike.mem_coe,
      Set.indicator_apply]
    split_ifs with hxU
    · simp only [hxU, not_true, or_false_iff]
    · simp only [h0, hxU, true_iff_iff, not_false_iff, or_true_iff]
  · suffices W = f ⁻¹' V ∩ U by rw [this]; exact (hV.preimage hf).inter U.clopen.isOpen
    classical
    ext x
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, SetLike.mem_coe,
      Set.indicator_apply]
    split_ifs with hxU
    · simp only [hxU, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, and_true_iff]
    · simp only [h0, false_iff_iff, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, not_and]
      intro; assumption

/-- The indicator function on clopen sets are continuous functions. -/
def indicator {X : Type _} [TopologicalSpace X] (U : Clopens X) : C(X, ℝ)
    where
  toFun := Set.indicator U 1
  continuous_toFun := indicator_continuous _ _ continuous_one

theorem indicator_one_inverse_image {X : Type _} (U : Set X) (s : Set ℝ) :
    U.indicator 1 ⁻¹' s = Set.univ ∨
      U.indicator 1 ⁻¹' s = U ∨ U.indicator 1 ⁻¹' s = Uᶜ ∨ U.indicator 1 ⁻¹' s = ∅ :=
  by
  by_cases s1 : (1 : ℝ) ∈ s <;> by_cases s0 : (0 : ℝ) ∈ s
  on_goal 1 => refine' Or.inl _
  on_goal 2 => refine' Or.inr (Or.inl _)
  on_goal 3 => refine' Or.inr (Or.inr (Or.inl _))
  on_goal 4 => refine' Or.inr (Or.inr (Or.inr _))
  all_goals
    ext x
    by_cases xU : x ∈ U
    ·
      simp only [xU, s1, Set.mem_preimage, Set.indicator_of_mem, Pi.one_apply, Set.mem_compl_iff,
        not_true, Set.mem_univ, Set.mem_empty_iff_false]
    ·
      simp only [xU, s0, Set.mem_preimage, Set.indicator_of_not_mem, not_false_iff,
        Set.mem_compl_iff, Set.mem_univ, Set.mem_empty_iff_false]

/-- The indicator function of a clopen set, bundled as a locally constant function. -/
def indicatorLC {X : Type _} [TopologicalSpace X] (U : Clopens X) : LocallyConstant X ℝ
    where
  toFun := Set.indicator U 1
  IsLocallyConstant s :=
    by
    rcases indicator_one_inverse_image (↑U) s with (h | h | h | h) <;> rw [h]
    exacts [isOpen_univ, U.clopen.isOpen, Uᶜ.clopen.IsOpen, isOpen_empty]

theorem indicator_apply {X : Type _} [TopologicalSpace X] (U : Clopens X) (x) :
    U.indicator x = if x ∈ U then 1 else 0 :=
  rfl

theorem indicatorLC_apply {X : Type _} [TopologicalSpace X] (U : Clopens X) (x) :
    U.indicatorLC x = if x ∈ U then 1 else 0 :=
  rfl

end TopologicalSpace.Clopens

namespace DiscreteQuotient

/-- Given a discrete topological space `T` that is a quotient of a topological space `X`, and
an element `t : T`, `fiber T t` is the clopen subset of `X` that is the inverse image of `t` under
the quotient map `X → T`. -/
def fibre {X : Type _} [TopologicalSpace X] (T : DiscreteQuotient X) (t : T) : Clopens X
    where
  carrier := T.proj ⁻¹' {t}
  clopen' := fiber_clopen T {t}

/-- When the topological space `X` is discrete, `equiv_bot` is the equivalence between `X` and the
bottom element of the discrete quotients of `X`.  In other words, the identity map from `X` to
itself *is*  a discrete quotient and `equiv_bot` is this bijection. -/
def equivBot {X : Type _} [TopologicalSpace X] [DiscreteTopology X] :
    X ≃ (⊥ : DiscreteQuotient X) :=
  Equiv.ofBijective (DiscreteQuotient.proj _)
    ⟨fun x y h => Quotient.exact' h, DiscreteQuotient.proj_surjective _⟩

theorem mem_fibre_iff {X : Type _} [TopologicalSpace X] (T : DiscreteQuotient X) (a : T) (b : X) :
    T.proj b ∈ DiscreteQuotient.fibre _ (equivBot a) ↔ b ∈ DiscreteQuotient.fibre T a :=
  by
  obtain ⟨a, rfl⟩ := DiscreteQuotient.proj_surjective _ a
  dsimp [fibre, DiscreteQuotient.equivBot]
  let TT : DiscreteQuotient T := ⊥
  change T.proj b ∈ DiscreteQuotient.equivBot ⁻¹' {DiscreteQuotient.equivBot (T.proj a)} ↔ T.proj b ∈ {T.proj a}
  simp

theorem mem_fibre_iff' {X : Type _} [TopologicalSpace X] (T : DiscreteQuotient X)
    (a : (⊥ : DiscreteQuotient T)) (b : X) :
    T.proj b ∈ DiscreteQuotient.fibre _ a ↔ b ∈ DiscreteQuotient.fibre T (equivBot.symm a) :=
  by
  rw [← equiv_bot.apply_symm_apply a, mem_fibre_iff]
  simp

/-- Given a continuous (`hf`), surjective (`hf'`) function `f : X → Y` between topological spaces
`X` and `Y`, and a discrete quotient `T` of `Y`, `comap_equiv f hf hf' T` is the bijection between
between the  comap of `T` along `f` and `T` itself.
-/
def comapEquiv {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) (hf' : Function.Surjective f) (T : DiscreteQuotient Y) : T.comap hf ≃ T :=
  Equiv.ofBijective (DiscreteQuotient.map <| le_refl _)
    (by
      constructor
      · rintro ⟨x⟩ ⟨y⟩ h
        apply Quotient.sound'
        apply Quotient.exact' h
      · rintro ⟨x⟩
        obtain ⟨x, rfl⟩ := hf' x
        use DiscreteQuotient.proj _ x; rfl)

theorem comap_mem_fibre_iff {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) (T : DiscreteQuotient Y) (a : T.comap hf) (b : X) :
    b ∈ DiscreteQuotient.fibre (T.comap hf) a ↔
      f b ∈ DiscreteQuotient.fibre T (DiscreteQuotient.map (le_refl _) a) :=
  by
  dsimp [fibre]
  change b ∈ (T.comap hf).proj ⁻¹' {a} ↔ f b ∈ T.proj ⁻¹' {_}
  obtain ⟨a, rfl⟩ := DiscreteQuotient.proj_surjective _ a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, map_proj_apply]
  constructor
  · intro h; apply Quotient.sound'; apply Quotient.exact' h
  · intro h; apply Quotient.sound'; apply Quotient.exact' h

end DiscreteQuotient

theorem LocallyConstant.sum_apply {ι X Y : Type _} [TopologicalSpace X] [AddCommMonoid Y]
    (f : ι → LocallyConstant X Y) (S : Finset ι) (t : X) : (∑ i in S, f i) t = ∑ i in S, f i t :=
  by
  let ee : LocallyConstant X Y →+ X → Y := LocallyConstant.coeFnAddMonoidHom
  change (ee (∑ i in S, f i)) t = ∑ i in S, ee (f i) t
  rw [ee.map_sum, Finset.sum_apply]

theorem LocallyConstant.eq_sum {X : Type _} [TopologicalSpace X] [CompactSpace X]
    (e : LocallyConstant X ℝ) :
    e =
      ∑ t : e.DiscreteQuotient,
        e.locally_constant_lift t • (e.DiscreteQuotient.fibre t).indicatorLC :=
  by
  ext t
  simp_rw [LocallyConstant.sum_apply, LocallyConstant.smul_apply]
  suffices
    ∑ x : ↥e.discreteQuotient,
        e.locally_constant_lift x • (e.discreteQuotient.fibre x).indicatorLC t =
      ∑ x in {e.discreteQuotient.proj t},
        e.locally_constant_lift x • (e.discreteQuotient.fibre x).indicatorLC t
    by
    simp_rw [this, Algebra.id.smul_eq_mul, Finset.sum_singleton]
    convert (mul_one _).symm
    rw [TopologicalSpace.Clopens.indicatorLC_apply, if_pos]
    change e.discreteQuotient.proj t ∈ _; simp
  -- clopens is missing some `mem_mk` lemma...
  symm
  apply Finset.sum_subset; simp only [Finset.subset_univ]
  intro s _ ht
  convert smul_zero _
  rw [TopologicalSpace.Clopens.indicatorLC_apply, if_neg]
  contrapose! ht
  change e.discreteQuotient.proj t ∈ _ at ht 
  exact finset.mem_singleton.mpr (set.mem_singleton_iff.mp ht).symm

/-- Given a point `x : X` is a discrete topological space `X`,
`topological_space.clopens.singleton x` is the point `x`, bundled as a clopen subset of `X`. -/
def TopologicalSpace.Clopens.singleton {X : Type _} [TopologicalSpace X] [DiscreteTopology X]
    (x : X) : Clopens X where
  carrier := {x}
  clopen' := isClopen_discrete {x}

theorem LocallyConstant.eq_sum_of_fintype {X : Type _} [Fintype X] [TopologicalSpace X]
    [DiscreteTopology X] (e : LocallyConstant X ℝ) :
    e = ∑ t : X, e t • (TopologicalSpace.Clopens.singleton t).indicatorLC :=
  by
  ext t
  rw [LocallyConstant.sum_apply]
  rw [Finset.sum_eq_single t]
  · change _ = _ • ite _ _ _
    rw [if_pos, smul_eq_mul]; erw [mul_one]
    change _ = _; rfl
  · intro x _ hx
    change _ • ite _ _ _ = _
    rw [if_neg, smul_zero]; change _ ≠ _; exact hx.symm
  · intro h; exfalso; apply h; exact Finset.mem_univ _

/-- Given a continuous function `f : X → Y` between topological spaces `X` and `Y`,
`continuous_map.comap f` is the `ℝ`-linear pre-composition with `f` as a function from
the `ℝ`-valued continuous functions on `Y` to the `ℝ`-valued continuous functions on `X`. -/
def ContinuousMap.comap {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    C(Y, ℝ) →L[ℝ] C(X, ℝ) where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by refine' ContinuousMap.continuous_comp_left f

/-- Given a continuous function `f : X → Y` between topological spaces `X` and `Y`,
`continuous_map.comap_LC_linear_map f` is the `ℝ`-linear pre-composition with `f` as a function from
the locally constant `ℝ`-valued continuous functions on `Y` to the locally constant `ℝ`-valued
continuous functions on `X`.

`continuous_map.comap_LC` is similar, except that it also bundles continuity of the resulting
function among spaces of continuous maps. -/
def ContinuousMap.comapLCLinearMap {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : LocallyConstant Y ℝ →ₗ[ℝ] LocallyConstant X ℝ
    where
  toFun g :=
    { toFun := g ∘ f
      IsLocallyConstant := fun S => by rw [Set.preimage_comp]; apply IsOpen.preimage f.2;
        apply g.2 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Given a continuous function `f : X → Y` between topological spaces `X` and `Y`,
`continuous_map.comap_LC_linear_map f` is the `ℝ`-linear pre-composition with `f` as a *continuous*
function from the locally constant `ℝ`-valued continuous functions on `Y` to the locally constant
`ℝ`-valued continuous functions on `X`.

`continuous_map.comap_LC_linear_map` is similar, but does not bundle continuity of the resulting
function among spaces of continuous maps. -/
def ContinuousMap.comapLC {X Y : Type _} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (f : C(X, Y)) : LocallyConstant Y ℝ →L[ℝ] LocallyConstant X ℝ
    where
  toFun g :=
    { toFun := g ∘ f
      IsLocallyConstant := fun S => by rw [Set.preimage_comp]; apply IsOpen.preimage f.2;
        apply g.2 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply (f.comapLCLinearMap.mkContinuousOfExistsBound _).continuous
    use 1; intro e; rw [one_mul]
    by_cases IsEmpty X
    · have : f.comapLCLinearMap e = 0; ext x; exact h.elim x; rw [this]
      simp
    change Sup _ ≤ _
    apply csSup_le
    simp only [not_isEmpty_iff] at h ; obtain ⟨x⟩ := h
    use‖(e (f x))‖; use x; rfl
    rintro b ⟨x, rfl⟩; dsimp
    exact_mod_cast LocallyConstant.nnnorm_apply_le_nnnorm _ e (f x)

/-- Given a compact topological space `X`, the inclusion of locally constant functions on `X` into
the space of all continuous functions is a continuous `ℝ`-linear map. -/
def lcToC (X : Type _) [TopologicalSpace X] [CompactSpace X] : LocallyConstant X ℝ →L[ℝ] C(X, ℝ)
    where
  toFun f := f.toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply Isometry.continuous
    intro f g
    simp only [edist_dist, dist_eq_norm, ContinuousMap.norm_eq_iSup_norm, LocallyConstant.norm_def,
      LocallyConstant.toContinuousMap_eq_coe, ContinuousMap.coe_sub,
      LocallyConstant.coe_continuousMap, Pi.sub_apply]
    rfl

namespace WeakDual

/-- Given topological `ℝ`-vector spaces `A` and `B` and a continuous, `ℝ`-linear map `f : A → B`
between them, `comap f` is the pre-composition with `f` as a continuous, `ℝ`-linear map between
the weak `ℝ`-linear dual of `B` to the weak `ℝ`-linear dual of `A`. -/
def comap {A B : Type _} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A] [AddCommGroup B]
    [Module ℝ B] [TopologicalSpace B] (f : A →L[ℝ] B) : WeakDual ℝ B →L[ℝ] WeakDual ℝ A
    where
  toFun g := g.comp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply WeakDual.continuous_of_continuous_eval
    intro a
    apply WeakDual.eval_continuous

/-- Given a compact topological space `X`, an element `μ` in the weak, `ℝ`-linear dual of the
continuous functions on `X`, and two non-negative real numbers `p` and `c`, `bdd μ p c` is the
statement that the sum of the `p`-th powers of the absolute values of the measures of all the
clopen subsets of `X` is bounded above by `c`.

See the actual definition for what "all the clopen subsets" really means!

`bdd_LC` is similar, but uses the dual of locally constant functions.  -/
def Bdd {X : Type _} [TopologicalSpace X] [CompactSpace X] (μ : WeakDual ℝ C(X, ℝ)) (p c : ℝ≥0) :
    Prop :=
  ∀ T : DiscreteQuotient X, ∑ t : T, ‖(μ (T.fibre t).indicator)‖₊ ^ (p : ℝ) ≤ c

/-- Given a compact topological space `X`, an element `μ` in the weak, `ℝ`-linear dual of the
locally constant functions on `X`, and two non-negative real numbers `p` and `c`, `bdd μ p c` is the
statement that the sum of the `p`-th powers of the absolute values of the measures of all the
clopen subsets of `X` is bounded above by `c`.

See the actual definition for what "all the clopen subsets" really means!

`bdd` is similar, but uses the dual of continuous functions.  -/
def BddLC {X : Type _} [TopologicalSpace X] [CompactSpace X] (μ : WeakDual ℝ (LocallyConstant X ℝ))
    (p c : ℝ≥0) : Prop :=
  ∀ T : DiscreteQuotient X, ∑ t : T, ‖(μ (T.fibre t).indicatorLC)‖₊ ^ (p : ℝ) ≤ c

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ^ »(‖μ ⟨λ t, ite _ _ _, _⟩‖₊, «expr↑ »(p))]] -/
theorem bddLCComap {X Y : Type _} {p c : ℝ≥0} [Fact (0 < p)] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (μ : WeakDual ℝ (LocallyConstant X ℝ)) (hμ : μ.BddLC p c)
    (f : C(X, Y)) : (WeakDual.comap f.comapLC μ).BddLC p c :=
  by
  intro T
  convert hμ (T.comap f.2) using 1
  let ι : T.comap f.2 → T := DiscreteQuotient.map (le_refl _)
  have hι : Function.Injective ι := by
    rintro ⟨⟩ ⟨⟩ h
    apply Quotient.sound'
    apply Quotient.exact' h
  let S₁ := _; change S₁ = _
  have :
    S₁ =
      ∑ t in finset.univ.image ι,
        ‖(((comap f.comapLC) μ) (T.fibre t).indicatorLC)‖₊ ^ (p : ℝ) :=
    by
    symm; apply Finset.sum_subset; simp only [Finset.subset_univ]
    intro x _ hx
    --simp only [finset.mem_image, finset.mem_univ, exists_true_left, not_exists] at hx,
    suffices ((comap f.comapLC) μ) (T.fibre x).indicatorLC = 0
      by
      simp only [this, nnnorm_zero, NNReal.rpow_eq_zero_iff, eq_self_iff_true, Ne.def,
        NNReal.coe_eq_zero, true_and_iff]
      exact ne_of_gt (Fact.out (0 < p))
    -- the `change` below is faster than `dsimp [comap]`
    change μ (f.comapLC (T.fibre x).indicatorLC) = 0
    convert μ.map_zero
    refine' LocallyConstant.ext fun t => _
    dsimp only [ContinuousMap.comapLC, TopologicalSpace.Clopens.indicatorLC_apply]
    apply if_neg
    contrapose! hx
    rw [Finset.mem_image]
    refine' ⟨DiscreteQuotient.proj _ t, Finset.mem_univ _, hx⟩
  rw [this]; clear this; symm
  fapply Finset.sum_bij
  · intro a _; exact ι a
  · intros; dsimp; erw [Finset.mem_image]; refine' ⟨a, Finset.mem_univ _, rfl⟩
  · intro a ha
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ^ »(‖μ ⟨λ t, ite _ _ _, _⟩‖₊, «expr↑ »(p))]]"
    rw [SetLike.mem_coe, SetLike.mem_coe, ← DiscreteQuotient.comap_mem_fibre_iff]
  · intro a₁ a₂ h₁ h₂ hh; apply hι; exact hh
  · rintro b hb
    rw [Finset.mem_image] at hb 
    obtain ⟨b, hh, hb⟩ := hb
    use b, hh, hb.symm

theorem bddComap {X Y : Type _} {p c : ℝ≥0} [Fact (0 < p)] [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (μ : WeakDual ℝ C(X, ℝ)) (hμ : μ.bdd p c) (f : C(X, Y)) :
    (WeakDual.comap f.comap μ).bdd p c := fun t => by apply bdd_LC_comap (comap (lcToC X) μ) hμ f t

theorem bdd_iff_indexed_parition (S : Profinite.{0}) (μ : WeakDual ℝ C(S, ℝ)) (p c : ℝ≥0) :
    μ.bdd p c ↔
      ∀ (ι : FintypeCat.{0}) (e : ι → Set S) (I : IndexedPartition e) (he : ∀ i, IsClopen (e i)),
        ∑ i : ι, ‖(μ.1 (TopologicalSpace.Clopens.indicator ⟨e i, he i⟩))‖₊ ^ (p : ℝ) ≤ c :=
  by
  constructor
  · intro hμ ι e I he
    let T : DiscreteQuotient S := IndexedPartition.discreteQuotient I he
    let ee : ι ≃ T := IndexedPartition.discreteQuotientEquiv he I
    specialize hμ T
    convert hμ using 1
    fapply Finset.sum_bij'
    · intro i _; exact ee i
    · intros; exact Finset.mem_univ _
    · intro a ha; congr 4
      ext1; change _ = T.proj ⁻¹' _
      rw [IndexedPartition.discreteQuotient_fiber]
      erw [ee.symm_apply_apply]
      rfl
    · intro t ht; exact ee.symm t
    · intros; exact Finset.mem_univ _
    · intros; exact ee.symm_apply_apply _
    · intros; exact ee.apply_symm_apply _
  · intro hμ T
    refine' hμ (FintypeCat.of T) (fun t => T.proj ⁻¹' {t}) _ fun t => (T.fibre t).2
    fapply IndexedPartition.mk'
    · intro i j hij a ha; simp only [Set.bot_eq_empty, Set.mem_empty_iff_false]; apply hij
      simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at ha 
      rw [← ha.1, ha.2]
    · rintro (t : T); obtain ⟨t, rfl⟩ := T.proj_surjective t; use t; change _ = _; rfl
    · intro s; use T.proj s; change _ = _; rfl

end WeakDual

