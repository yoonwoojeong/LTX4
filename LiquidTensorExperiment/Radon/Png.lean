import LiquidTensorExperiment.Radon.Main
import LiquidTensorExperiment.Radon.PngReflectsLimits

#align_import Radon.png

open scoped NNReal BigOperators Classical

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open TopologicalSpace

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

namespace Profinite

variable (X : Profinite.{0}) (p : ℝ≥0)

instance whyDoINeedThis : AddCommGroup (WeakDual ℝ C(X, ℝ)) :=
  show AddCommGroup (C(X, ℝ) →L[ℝ] ℝ) by infer_instance

theorem bddNeg {c} (a : WeakDual ℝ C(X, ℝ)) (ha : a.bdd p c) : (-a).bdd p c := fun e => by
  simpa only [ContinuousLinearMap.neg_apply, nnnorm_neg] using ha e

section PPos

variable [Fact (0 < p)]

theorem bddZero : (0 : WeakDual ℝ C(X, ℝ)).bdd p 0 := fun e =>
  by
  refine' (Finset.sum_eq_zero fun x hx => _).le
  rw [ContinuousLinearMap.zero_apply, nnnorm_zero]
  exact nnreal.rpow_eq_zero_iff.mpr ⟨rfl, (nnreal.coe_pos.mpr (Fact.out _)).ne'⟩

section PLeOne

variable [Fact (p ≤ 1)]

theorem bddAdd {ca cb} (a b : WeakDual ℝ C(X, ℝ)) (ha : a.bdd p ca) (hb : b.bdd p cb) :
    (a + b).bdd p (ca + cb) := by
  intro e
  --  `dsimp` is unneeded and slowly changes the goal to
  -- `∑ (t : ↥e), ∥⇑a (e.fibre t).indicator + ⇑b (e.fibre t).indicator∥₊ ^ ↑p ≤ ca + cb`,
  refine' le_trans _ (add_le_add (ha e) (hb e))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; rintro i -
  refine'
    le_trans _
      (NNReal.rpow_add_le_add_rpow _ _ _ <|
        (nnreal.coe_le_coe.mpr (Fact.out _)).trans nnreal.coe_one.le)
  refine' NNReal.rpow_le_rpow _ _
  · apply nnnorm_add_le
  repeat' exact (nnreal.coe_pos.mpr (Fact.out _)).le

/-- An auxiliary definition to be used in the constructions below. -/
def bddWeakDual : AddSubgroup (WeakDual ℝ C(X, ℝ))
    where
  carrier := {μ | ∃ c, μ.bdd p c}
  add_mem' a b ha hb := by
    obtain ⟨ca, ha⟩ := ha
    obtain ⟨cb, hb⟩ := hb
    use ca + cb
    apply Profinite.bddAdd _ _ _ _ ha hb
  zero_mem' := ⟨0, bddZero _ _⟩
  neg_mem' a ha := by
    obtain ⟨c, ha⟩ := ha
    use c
    apply Profinite.bddNeg _ _ _ ha

instance : PseudoNormedGroup (X.bddWeakDual p)
    where
  filtration' c := {μ | μ.1.bdd p c}
  filtration_mono' c₁ c₂ h μ hμ e := by apply le_trans (hμ e) h
  zero_mem_filtration' c e := le_trans (bddZero _ _ _) (zero_le _)
  neg_mem_filtration' c μ hμ e := bddNeg _ _ _ hμ _
  add_mem_filtration' c₁ c₂ a b ha hb := bddAdd _ _ _ _ ha hb

instance topologicalSpaceBddWeakDualFiltration (c : ℝ≥0) :
    TopologicalSpace (PseudoNormedGroup.filtration (X.bddWeakDual p) c) :=
  TopologicalSpace.induced (fun μ => μ.1.1) inferInstance

/-- An auxiliary definition to be used in the constructions below. -/
def bddWeakDualFiltrationHomeo (c : ℝ≥0) :
    PseudoNormedGroup.filtration (X.bddWeakDual p) c ≃ₜ X.radon p c
    where
  toFun μ := ⟨μ.1.1, μ.2⟩
  invFun μ := ⟨⟨μ.1, ⟨c, μ.2⟩⟩, μ.2⟩
  left_inv μ := by ext; rfl
  right_inv μ := by ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_subtype_val

instance : ComphausFilteredPseudoNormedGroup (X.bddWeakDual p) :=
  {
    (inferInstance :
      PseudoNormedGroup
        (X.bddWeakDual
          p)) with
    t2 := fun c => (X.bddWeakDualFiltrationHomeo p c).symm.T2Space
    compact := fun c => (X.bddWeakDualFiltrationHomeo p c).symm.CompactSpace
    continuous_add' := by
      intro c₁ c₂
      rw [continuous_induced_rng]
      let i1 :
        PseudoNormedGroup.filtration (↥(X.bdd_weak_dual p)) c₁ ×
            PseudoNormedGroup.filtration (↥(X.bdd_weak_dual p)) c₂ →
          WeakDual ℝ C(X, ℝ) × WeakDual ℝ C(X, ℝ) :=
        Prod.map (fun μ => μ.1.1) fun μ => μ.1.1
      let i2 : WeakDual ℝ C(X, ℝ) × WeakDual ℝ C(X, ℝ) → WeakDual ℝ C(X, ℝ) := fun a => a.1 + a.2
      change Continuous (i2 ∘ i1)
      apply Continuous.comp
      exact continuous_add
      refine' Continuous.prod_map _ _
      exact continuous_induced_dom
      exact continuous_induced_dom
    continuous_neg' := by
      intro c
      rw [continuous_induced_rng]
      let i1 : PseudoNormedGroup.filtration (↥(X.bdd_weak_dual p)) c → WeakDual ℝ C(X, ℝ) :=
        fun μ => μ.1.1
      let i2 : WeakDual ℝ C(X, ℝ) → WeakDual ℝ C(X, ℝ) := fun μ => -μ
      change Continuous (i2 ∘ i1)
      apply Continuous.comp
      apply WeakDual.continuous_of_continuous_eval
      intro f
      dsimp [i2]
      have : (fun a : WeakDual ℝ C(↥X, ℝ) => -a f) = fun a : WeakDual ℝ C(↥X, ℝ) => a (-f) := by
        ext; simp
      rw [this]; apply WeakDual.eval_continuous
      exact continuous_induced_dom
    continuous_castLe := by
      intro c₁ c₂ h
      rw [continuous_induced_rng]
      exact continuous_induced_dom }

/-- The space of `p`-Radon measures on `X`, as a CompHaus-ly filtered pseudo normed group`. -/
def radonPng : CompHausFiltPseuNormGrp₁
    where
  M := X.bddWeakDual p
  exhaustive' μ := μ.2

/-- A continuous map of profinite spaces induces a morphism between `Radon_png p`. -/
def mapRadonPng {X Y : Profinite.{0}} (f : X ⟶ Y) : X.radonPng p ⟶ Y.radonPng p
    where
  toFun μ :=
    ⟨WeakDual.comap f.comap μ.1, by
      obtain ⟨c, hc⟩ := μ.2
      use c
      apply WeakDual.bddComap _ hc⟩
  map_zero' := by ext; rfl
  map_add' a b := by ext; rfl
  strict' c μ hμ := WeakDual.bddComap _ hμ _
  continuous' := by
    intro c
    rw [continuous_induced_rng]
    let i1 : PseudoNormedGroup.filtration (↥(X.Radon_png p)) c → WeakDual _ _ := fun μ => μ.1.1
    let i2 : WeakDual ℝ C(↥X, ℝ) → WeakDual ℝ C(↥Y, ℝ) := WeakDual.comap f.comap
    change Continuous (i2 ∘ i1)
    refine' Continuous.comp _ continuous_induced_dom
    refine' ContinuousLinearMap.continuous _

/-- A functorial version of `Radon_png`. -/
def radonPngFunctor : Profinite.{0} ⥤ CompHausFiltPseuNormGrp₁
    where
  obj X := X.radonPng p
  map X Y := mapRadonPng _
  map_id X := by
    ext; dsimp [map_Radon_png, WeakDual.comap]; congr 1
    ext; rfl
  map_comp X Y Z f g := by ext; rfl

/-- The cone exhibiting `X.Radon_png p` as a limit of `T.Radon_png p` as
`T` varies over the discrete quotients of `X`. -/
def radonPngCone : Cone (X.diagram ⋙ radonPngFunctor p) :=
  (radonPngFunctor p).mapCone X.asLimitCone

/-- An auxiliary definition to be used in the constructions below. -/
def radonPngFunctorLevelIsoComponent (c : ℝ≥0) (X : Profinite.{0}) :
    (CompHausFiltPseuNormGrp₁.level.obj c).obj (X.radonPng p) ≅ (radonCompHausFunctor p c).obj X :=
  let e := bddWeakDualFiltrationHomeo X p c
  { hom := e.toContinuousMap
    inv := e.symm.toContinuousMap
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl }

/-- An auxiliary definition to be used in the constructions below. -/
def radonPngFunctorLevelIso (c : ℝ≥0) :
    radonPngFunctor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c ≅ radonCompHausFunctor p c :=
  NatIso.ofComponents (fun X => radonPngFunctorLevelIsoComponent _ _ _) fun X Y f => by ext; rfl

/-- An auxiliary definition to be used in the constructions below. -/
def isLimitRadonPngConeMapLevel (c : ℝ≥0) :
    IsLimit ((radonPngFunctor p ⋙ CompHausFiltPseuNormGrp₁.level.obj c).mapCone X.asLimitCone)
    where
  lift S :=
    (X.isLimitRadonCompHausCone p c).lift
        ⟨_, S.π ≫ whiskerLeft _ (radonPngFunctorLevelIso p c).hom⟩ ≫
      (radonPngFunctorLevelIso p c).inv.app _
  fac := by
    intro S j
    erw [Category.assoc, ← NatTrans.naturality, (X.is_limit_Radon_CompHaus_cone p c).fac_assoc]
    dsimp; simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  uniq := by
    intro S m hm
    rw [← NatIso.app_inv, Iso.eq_comp_inv]
    apply (X.is_limit_Radon_CompHaus_cone p c).hom_ext; intro j
    erw [(X.is_limit_Radon_CompHaus_cone p c).fac]
    dsimp; rw [← hm]; dsimp; simp only [Category.assoc]
    erw [← NatTrans.naturality]

/-- As promised, `X.Radon_png p` is a limit cone. -/
def isLimitRadonPngCone : IsLimit (X.radonPngCone p) :=
  CompHausFiltPseuNormGrp₁.levelJointlyReflectsLimits _ fun c => isLimitRadonPngConeMapLevel _ _ _

/-- An auxiliary definition to be used in the constructions below. -/
def radonPngComparisonComponent (T : DiscreteQuotient X) :
    (X.diagram ⋙ radonPngFunctor p).obj T ≅ (X.fintypeDiagram ⋙ RealMeasures.functor p).obj T :=
  CompHausFiltPseuNormGrp₁.createIsoFromLevel.{0}
    (fun c => radonPngFunctorLevelIsoComponent _ _ _ ≪≫ (radonCompHausComparison _ _ _).app _)
    (by ext; rfl)
    (by
      intro a b
      ext; rfl)
    (by
      intro c₁ c₂ i
      ext; rfl)

-- ;-D
/-- An auxiliary definition to be used in the constructions below. -/
def radonPngComparison :
    X.diagram ⋙ radonPngFunctor p ≅ X.fintypeDiagram ⋙ RealMeasures.functor p :=
  NatIso.ofComponents (fun T => radonPngComparisonComponent _ _ _)
    (by
      intro S T f
      dsimp only [Radon_png_comparison_component, Iso.trans_hom]
      apply CompHausFiltPseuNormGrp₁.level_jointly_faithful
      intro c
      simp only [Functor.map_comp]
      simp_rw [CompHausFiltPseuNormGrp₁.level_createIsoFromLevel.{0}, Iso.trans_hom,
        NatIso.app_hom, Category.assoc]
      erw [← (X.Radon_CompHaus_comparison p c).hom.naturality f]
      rfl)

/-- The CompHaus-ly filtered pseudno normed group of signed `p`-Radon measures on `X`
is isomorphic to the limit of `real_measures p T` as `T` varies over
the discrete quotients of `X`.

This is the final key isomorphism needed for the comparison of Raon measures and
`ℳ_p(X)`. -/
def radonPngIso : X.radonPng p ≅ (Profinite.extend (RealMeasures.functor p)).obj X :=
  (X.isLimitRadonPngCone p).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (X.radonPngComparison p)

end PLeOne

end PPos

end Profinite

