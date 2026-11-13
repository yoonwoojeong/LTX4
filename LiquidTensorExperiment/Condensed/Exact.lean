import Mathlib.CategoryTheory.Limits.Fubini
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import LiquidTensorExperiment.ForMathlib.LimitFlipCompIso
import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.PseudoNormedGroup.BoundedLimits
import LiquidTensorExperiment.Condensed.Extr.LiftComphaus
import LiquidTensorExperiment.Condensed.ProjectiveResolution
import LiquidTensorExperiment.Condensed.KernelComparison

#align_import condensed.exact

universe u v

noncomputable section

open scoped NNReal

open CategoryTheory CategoryTheory.Limits Opposite PseudoNormedGroup

-- move me
namespace CompHaus

variable {J : Type u} [SmallCategory J] (F G : J ⥤ CompHaus.{u}) (α : F ⟶ G)

variable (cF : Cone F) (cG : Cone G) (hcF : IsLimit cF) (hcG : IsLimit cG)

def pt {X : CompHaus.{u}} (x : X) : ⊤_ CompHaus ⟶ X :=
  ⟨fun _ => x, continuous_const⟩

@[simps]
def diagramOfPt (y : cG.pt) : J ⥤ CompHaus.{u}
    where
  obj j := pullback (α.app j) (pt y ≫ cG.π.app j)
  map i j f :=
    pullback.lift (pullback.fst ≫ F.map f) pullback.snd
      (by rw [Category.assoc, α.naturality, pullback.condition_assoc, Category.assoc, cG.w])
  map_id j := by apply pullback.hom_ext <;> dsimp <;> simp
  map_comp i j k f g := by apply pullback.hom_ext <;> dsimp <;> simp

@[simps]
def coneOfPt (y : cG.pt) : Cone (diagramOfPt F G α cG y)
    where
  pt := pullback (hcG.map cF α) (pt y)
  π :=
    { app := fun j =>
        pullback.lift (pullback.fst ≫ cF.π.app _) pullback.snd
          (by rw [Category.assoc, ← pullback.condition_assoc, IsLimit.map_π])
      naturality := fun i j f => by apply pullback.hom_ext <;> dsimp <;> simp }

def isLimitConeOfPt (y : cG.pt) : IsLimit (coneOfPt F G α cF cG hcG y)
    where
  lift S :=
    pullback.lift
      (hcF.lift
        ⟨S.pt,
          { app := fun j => S.π.app j ≫ pullback.fst
            naturality := by
              intro i j f
              dsimp
              rw [← S.w f]; dsimp [CompHaus.diagramOfPt]
              simp only [Category.id_comp, Category.assoc, pullback.lift_fst] }⟩)
      (terminal.from _)
      (by
        apply hcG.hom_ext; intro j; dsimp
        simp only [Category.assoc, IsLimit.map_π, IsLimit.fac_assoc, pullback.condition]
        ext; rfl)
  fac := by
    intro s j; dsimp; apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsLimit.fac]
    · simp only [eq_iff_true_of_subsingleton]
  uniq := by
    intro s m hm
    dsimp at m hm 
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply hcF.hom_ext; intro j
      simp only [Category.assoc, IsLimit.fac, ← hm j, pullback.lift_fst]
    · simp only [eq_iff_true_of_subsingleton]

theorem IsLimit.surjective_of_surjective [IsCofiltered J]
    (hα : ∀ j, Function.Surjective (α.app j)) : Function.Surjective (hcG.map cF α) := fun y =>
  by
  let E := coneOfPt F G α cF cG hcG y
  let hE : IsLimit E := isLimitConeOfPt F G α cF cG hcF hcG y
  suffices ∃ e : ⊤_ CompHaus.{u} ⟶ E.X, e ≫ (pullback.fst : E.X ⟶ cF.X) ≫ hcG.map cF α = pt y
    by
    obtain ⟨e, he⟩ := this
    use(terminal.from (CompHaus.of PUnit) ≫ e ≫ pullback.fst) PUnit.unit
    rw [← comp_apply]
    have : y = (terminal.from (CompHaus.of PUnit) ≫ pt y) PUnit.unit := rfl
    conv_rhs => rw [this]; clear this; congr 1
    apply hcG.hom_ext
    intro j
    simp only [← he, Category.assoc]
  let E' := CompHaus_to_Top.map_cone E
  let hE' : is_limit E' := CategoryTheory.Limits.isLimitOfPreserves compHausToTop hE
  let ee : E' ≅ TopCat.limitCone.{u, u} _ := hE'.uniqueUpToIso (TopCat.limitConeIsLimit _)
  let e : E'.X ≅ (TopCat.limitCone.{u, u} _).pt :=
    hE'.conePointUniqueUpToIso (TopCat.limitConeIsLimit _)
  have : ∀ j : J, T2Space ((CompHaus.diagramOfPt F G α cG y ⋙ compHausToTop).obj j) := by intro j;
    change T2Space ((CompHaus.diagramOfPt F G α cG y).obj j); infer_instance
  have : ∀ j : J, CompactSpace ((CompHaus.diagramOfPt F G α cG y ⋙ compHausToTop).obj j) := by intro j;
    change CompactSpace ((CompHaus.diagramOfPt F G α cG y).obj j); infer_instance
  have : ∀ j : J, Nonempty ((CompHaus.diagramOfPt F G α cG y ⋙ compHausToTop).obj j) :=
    by
    intro j; change Nonempty ((CompHaus.diagramOfPt F G α cG y).obj j)
    dsimp only [CompHaus.diagramOfPt_obj]
    let y' := (terminal.from (CompHaus.of PUnit) ≫ pt y ≫ cG.π.app j) PUnit.unit
    obtain ⟨x', hx'⟩ := hα j y'
    refine' ⟨(terminal.from (CompHaus.of PUnit) ≫ pullback.lift (pt x') (𝟙 _) _) PUnit.unit⟩
    ext z; exact hx'
  have :=
    TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system
      (CompHaus.diagramOfPt F G α cG y ⋙ compHausToTop)
  obtain ⟨a⟩ := this
  let b := e.inv a
  use pt b
  rw [pullback.condition]
  rfl

-- Scott: perhaps life is easier if we use this version? I'm not too sure.
theorem IsLimit.surjective_of_surjective' [IsCofiltered J]
    (hα : ∀ j, Function.Surjective (α.app j)) : Function.Surjective (limMap α) :=
  IsLimit.surjective_of_surjective _ _ _ _ _ (limit.isLimit _) _ hα

end CompHaus

namespace CompHausFiltPseuNormGrp₁

-- move this
instance : HasZeroMorphisms CompHausFiltPseuNormGrp₁.{u}
    where
  Zero M₁ M₂ := ⟨0⟩
  comp_zero _ _ f _ := rfl
  zero_comp _ _ _ f := by ext; exact f.map_zero

variable {A B C : CompHausFiltPseuNormGrp₁.{u}}

structure StronglyExact (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0) : Prop where
  comp_eq_zero : f ≫ g = 0
  cond : ∀ c : ℝ≥0, g ⁻¹' {0} ∩ filtration B c ⊆ f '' filtration A (r c)
  large : id ≤ r

theorem StronglyExact.exact {f : A ⟶ B} {g : B ⟶ C} {r : ℝ≥0 → ℝ≥0} (h : StronglyExact f g r) :
    Exact ((toPNG₁ ⋙ PseuNormGrp₁.toAb).map f) ((toPNG₁ ⋙ PseuNormGrp₁.toAb).map g) :=
  by
  rw [AddCommGroupCat.exact_iff']
  constructor
  · ext x; have := h.comp_eq_zero; apply_fun fun φ => φ.toFun at this ; exact congr_fun this x
  · intro y hy
    obtain ⟨c, hc⟩ := B.exhaustive y
    obtain ⟨a, ha, rfl⟩ := h.cond c ⟨_, hc⟩
    · exact ⟨a, rfl⟩
    · simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hy

-- TODO remove this; it's a redundant alias
@[simps (config := { fullyApplied := false }) obj_obj obj_map_apply map_app]
def filtration : ℝ≥0 ⥤ CompHausFiltPseuNormGrp₁.{u} ⥤ CompHaus.{u} :=
  CompHausFiltPseuNormGrp₁.level

instance mono_filtration_map_app (c₁ c₂ : ℝ≥0) (h : c₁ ⟶ c₂) (M) :
    Mono ((filtration.map h).app M) := by rw [CompHaus.mono_iff_injective];
  convert injective_cast_le _ _

namespace StronglyExact

noncomputable section

variable (f : A ⟶ B) (g : B ⟶ C) (r : ℝ≥0 → ℝ≥0) (c : ℝ≥0) (hrc : c ≤ r c)

variable {r c}

def cLeRc : c ⟶ r c :=
  homOfLE <| hrc

/-- Given `f : A ⟶ B`, `P1` is the pullback `B_c ×_{B_{rc}} A_{rc}`. -/
def p1 : CompHaus :=
  pullback ((filtration.map (cLeRc hrc)).app B) ((filtration.obj (r c)).map f)

@[simps]
def pt {X : CompHaus} (x : X) : ⊤_ CompHaus ⟶ X :=
  ⟨fun _ => x, continuous_const⟩

/-- Given `g : B ⟶ C`, `P2` is the pullback `B_c ×_{C_c} {pt}`. -/
def p2 (c : ℝ≥0) : CompHaus :=
  pullback ((filtration.obj c).map g) (pt (0 : PseudoNormedGroup.filtration C c))

def p1ToP2 (hfg : f ≫ g = 0) : p1 f hrc ⟶ p2 g c :=
  pullback.lift pullback.fst (terminal.from _)
    (by
      rw [← cancel_mono ((Filtration.map (CompHausFiltPseuNormGrp₁.StronglyExact.cLeRc hrc)).app C), Category.assoc,
        NatTrans.naturality, pullback.condition_assoc, ← Functor.map_comp, hfg]
      rfl)

theorem p1ToP2_comp_fst (hfg : f ≫ g = 0) : p1ToP2 f g hrc hfg ≫ pullback.fst = pullback.fst :=
  pullback.lift_fst _ _ _

theorem surjective (h : StronglyExact f g r) :
    ∃ hfg : f ≫ g = 0, ∀ c, Function.Surjective (p1ToP2 f g (h.large c) hfg) :=
  by
  have hfg : f ≫ g = 0 := by ext x; exact FunLike.congr_fun h.exact.w x
  refine' ⟨hfg, _⟩
  intro c y
  let π₁ : P2 g c ⟶ (Filtration.obj c).obj B := pullback.fst
  have hy : (π₁ y).val ∈ g ⁻¹' {0} ∩ filtration B c :=
    by
    refine' ⟨_, (π₁ y).2⟩
    simp only [Subtype.val_eq_coe, Set.mem_preimage, Set.mem_singleton_iff]
    have w :=
      @pullback.condition _ _ _ _ _ ((Filtration.obj c).map g)
        (pt (0 : PseudoNormedGroup.filtration C c)) _
    have := FunLike.congr_fun w y
    exact congr_arg Subtype.val this
  obtain ⟨x, hx, hfx⟩ := h.cond c hy
  let s : CompHaus.of PUnit ⟶ P1 f (h.large c) :=
    terminal.from _ ≫ pullback.lift (pt (π₁ y)) (pt ⟨x, hx⟩) _
  swap; · ext t; exact hfx.symm
  refine' ⟨s PUnit.unit, _⟩
  suffices s ≫ P1_to_P2 f g (h.large c) hfg = terminal.from _ ≫ pt y by
    exact FunLike.congr_fun this PUnit.unit
  delta P1_to_P2
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]; rfl
  · exact Subsingleton.elim _ _

theorem ofSurjective (hfg : f ≫ g = 0) (hr : id ≤ r)
    (h : ∀ c, Function.Surjective (p1ToP2 f g (hr c) hfg)) : StronglyExact f g r :=
  by
  suffices H : ∀ c : ℝ≥0, g ⁻¹' {0} ∩ filtration B c ⊆ f '' filtration A (r c)
  · refine' ⟨_, H, hr⟩
    ext x
    have := congr_arg (coeFn : (A ⟶ C) → A → C) hfg
    exact congr_fun this x
  rintro c y ⟨hy, hyc⟩
  let t : CompHaus.of PUnit ⟶ P2 g c :=
    pullback.lift (terminal.from _ ≫ pt ⟨y, hyc⟩) (terminal.from _) _
  swap; · ext; exact hy
  obtain ⟨s, hs⟩ := h c (t PUnit.unit)
  let π₂ : P1 f (hr c) ⟶ (Filtration.obj (r c)).obj A := pullback.snd
  refine' ⟨(π₂ s).val, _⟩
  let P := CompHaus.of PUnit
  suffices
    terminal.from P ≫ pt s ≫ π₂ ≫ (Filtration.obj (r c)).map f =
      terminal.from _ ≫ pt ⟨y, filtration_mono (hr c) hyc⟩
    by have hs := FunLike.congr_fun this PUnit.unit; exact ⟨(π₂ s).2, congr_arg Subtype.val hs⟩
  have H : terminal.from P ≫ pt s ≫ P1_to_P2 f g (hr c) hfg = t := by apply ContinuousMap.ext;
    rintro ⟨⟩; exact hs
  erw [← pullback.condition, ← P1_to_P2_comp_fst f g (hr c) hfg, Category.assoc, reassoc_of H,
    pullback.lift_fst_assoc]
  rfl

theorem iff_surjective :
    StronglyExact f g r ↔
      ∃ (hfg : f ≫ g = 0) (hr : ∀ c, c ≤ r c), ∀ c, Function.Surjective (p1ToP2 f g (hr c) hfg) :=
  by
  constructor
  · intro h; obtain ⟨hfg, H⟩ := surjective _ _ h; exact ⟨hfg, h.large, H⟩
  · rintro ⟨hfg, hr, h⟩; exact of_surjective f g hfg hr h

end StronglyExact

namespace StronglyExact

variable {J : Type u} [SmallCategory J]

variable {A' B' C' : J ⥤ CompHausFiltPseuNormGrp₁.{u}}

variable (f : A' ⟶ B') (g : B' ⟶ C') (r : ℝ≥0 → ℝ≥0) (c : ℝ≥0) (hrc : c ≤ r c)

variable {r c}

@[simps (config := { fullyApplied := false }) obj obj_obj obj_map map map_app]
def p1Functor : J ⥤ WalkingCospan ⥤ CompHaus.{u} :=
  Functor.flip <|
    cospan (whiskerLeft B' (filtration.map (cLeRc hrc))) (whiskerRight f (filtration.obj (r c)))

@[simps (config := { fullyApplied := false }) obj obj_obj obj_map map map_app]
def p2Functor (c : ℝ≥0) : J ⥤ WalkingCospan ⥤ CompHaus.{u} :=
  Functor.flip <|
    @cospan _ _ _ ((CategoryTheory.Functor.const _).obj (⊤_ _)) _
      (whiskerRight g (filtration.obj c))
      { app := fun j => pt (0 : PseudoNormedGroup.filtration (C'.obj j) c)
        naturality := by intros; ext; exact (C'.map f).map_zero.symm }

theorem p1ToP2_nat_trans_aux_1 (hfg : f ≫ g = 0) (X Y : J) (h : X ⟶ Y) (w w') :
    ((p1Functor f hrc ⋙ limUnder).map h ≫
          limMap (diagramIsoCospan ((p1Functor f hrc).obj Y)).hom ≫
            p1ToP2 (f.app Y) (g.app Y) hrc w ≫
              limMap
                (𝟙 (cospan ((filtration.obj c).map (g.app Y)) (pt 0)) ≫
                  (diagramIsoCospan ((p2Functor g c).obj Y)).inv)) ≫
        limit.π ((p2Functor g c).obj Y) none =
      ((limMap (diagramIsoCospan ((p1Functor f hrc).obj X)).hom ≫
            p1ToP2 (f.app X) (g.app X) hrc w' ≫
              limMap
                (𝟙 (cospan ((filtration.obj c).map (g.app X)) (pt 0)) ≫
                  (diagramIsoCospan ((p2Functor g c).obj X)).inv)) ≫
          (p2Functor g c ⋙ limUnder).map h) ≫
        limit.π ((p2Functor g c).obj Y) none :=
  by
  dsimp [P1_to_P2]
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app, eq_to_iso_refl, Category.id_comp,
    Category.assoc, Cones.postcompose_obj_π, lim_map_π_assoc, limit.lift_π,
    CategoryTheory.Limits.diagramIsoCospan_hom_app, CategoryTheory.Limits.diagramIsoCospan_inv_app, PullbackCone.mk_π_app_one,
    limit.lift_map]
  dsimp
  simp only [← (Filtration.obj c).map_comp, Category.comp_id, Category.id_comp,
    NatTrans.naturality]

theorem p1ToP2_nat_trans_aux_2 (hfg : f ≫ g = 0) (X Y : J) (h : X ⟶ Y) (w w') :
    ((p1Functor f hrc ⋙ limUnder).map h ≫
          limMap (diagramIsoCospan ((p1Functor f hrc).obj Y)).hom ≫
            p1ToP2 (f.app Y) (g.app Y) hrc w ≫
              limMap
                (𝟙 (cospan ((filtration.obj c).map (g.app Y)) (pt 0)) ≫
                  (diagramIsoCospan ((p2Functor g c).obj Y)).inv)) ≫
        limit.π ((p2Functor g c).obj Y) (some WalkingPair.left) =
      ((limMap (diagramIsoCospan ((p1Functor f hrc).obj X)).hom ≫
            p1ToP2 (f.app X) (g.app X) hrc w' ≫
              limMap
                (𝟙 (cospan ((filtration.obj c).map (g.app X)) (pt 0)) ≫
                  (diagramIsoCospan ((p2Functor g c).obj X)).inv)) ≫
          (p2Functor g c ⋙ limUnder).map h) ≫
        limit.π ((p2Functor g c).obj Y) (some WalkingPair.left) :=
  by
  dsimp [P1_to_P2]
  simp only [Iso.refl_hom, Iso.refl_inv, eq_to_iso_refl, NatTrans.comp_app, Category.id_comp,
    Category.assoc, PullbackCone.mk_π_app_left, Cones.postcompose_obj_π, lim_map_π_assoc,
    limit.lift_π, limit.lift_map, CategoryTheory.Limits.diagramIsoCospan_hom_app, CategoryTheory.Limits.diagramIsoCospan_inv_app]
  dsimp
  simp only [Category.comp_id, Category.id_comp]

theorem p1ToP2_nat_trans_aux_3 (hfg : f ≫ g = 0) (X Y : J) (h : X ⟶ Y) (w w') :
    ((p1Functor f hrc ⋙ limUnder).map h ≫
          limMap (diagramIsoCospan ((p1Functor f hrc).obj Y)).hom ≫
            p1ToP2 (f.app Y) (g.app Y) hrc w ≫
              limMap
                (𝟙 (cospan ((filtration.obj c).map (g.app Y)) (pt 0)) ≫
                  (diagramIsoCospan ((p2Functor g c).obj Y)).inv)) ≫
        limit.π ((p2Functor g c).obj Y) (some WalkingPair.right) =
      ((limMap (diagramIsoCospan ((p1Functor f hrc).obj X)).hom ≫
            p1ToP2 (f.app X) (g.app X) hrc w' ≫
              limMap
                (𝟙 (cospan ((filtration.obj c).map (g.app X)) (pt 0)) ≫
                  (diagramIsoCospan ((p2Functor g c).obj X)).inv)) ≫
          (p2Functor g c ⋙ limUnder).map h) ≫
        limit.π ((p2Functor g c).obj Y) (some WalkingPair.right) :=
  by
  dsimp [P1_to_P2]
  simp only [Category.id_comp, Category.assoc, eq_to_iso_refl, Iso.refl_inv, NatTrans.comp_app,
    PullbackCone.mk_π_app_right, Cones.postcompose_obj_π, limit.lift_π, limit.lift_map,
    CategoryTheory.Limits.diagramIsoCospan_inv_app, eq_iff_true_of_subsingleton]

def p1ToP2NatTrans (hfg : f ≫ g = 0) : p1Functor f hrc ⋙ limUnder ⟶ p2Functor g c ⋙ limUnder
    where
  app j :=
    by
    refine' _ ≫ P1_to_P2 (f.app j) (g.app j) hrc (by rw [← NatTrans.comp_app, hfg]; rfl) ≫ _
    · refine' lim_map (CategoryTheory.Limits.diagramIsoCospan _).hom
    · refine' lim_map (_ ≫ (CategoryTheory.Limits.diagramIsoCospan _).inv); exact 𝟙 _
  naturality X Y h :=
    by
    -- It would be nicer to use `pullback.hom_ext` here, but it doesn't unify.
    -- Nevertheless, we can bash out the remaining goals with `simp`.
    apply limit.hom_ext;
    rintro (⟨⟩ | ⟨⟨⟩⟩)
    · apply P1_to_P2_nat_trans_aux_1 _ _ _ hfg
    · apply P1_to_P2_nat_trans_aux_2 _ _ _ hfg
    · apply P1_to_P2_nat_trans_aux_3 _ _ _ hfg

attribute [simps] P1_to_P2_nat_trans

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

/-
TODO:

jmc: below is a framework for setting up some canonical isomorphisms between limits.
It really boils down to saying that limits commute.
This shouldn't be so hard...
I'm not convinced that this is the best way to do it,
there should be a more ergonomic approach.

scott: I've replaced the definition of `P1_iso`
with one that uses the general theory for commuting limits.
-/
instance (c : ℝ≥0) : PreservesLimits (filtration.obj c) := by dsimp [Filtration]; infer_instance

def p1Iso {A B : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}} (f : A ⟶ B) {r : ℝ≥0 → ℝ≥0}
    {c : ℝ≥0} (hrc : c ≤ r c) (S : Profinite) :
    p1.{u} ((Profinite.extendNatTrans.{u, u + 1} f).app S) hrc ≅
      limit (p1Functor.{u} (whiskerLeft S.fintypeDiagram f) hrc ⋙ limUnder) :=
  by
  refine'
    HasLimit.isoOfNatIso (_ ≪≫ (CategoryTheory.Limits.cospanCompIso _ _ _).symm) ≪≫
      (CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim' _).symm
  -- This next line can be removed later if/when we generalize universe parameters in finite (co)limits
  refine' _ ≪≫ (CategoryTheory.Limits.diagramIsoCospan _).symm
  refine'
    CategoryTheory.Limits.cospanExt (CategoryTheory.preservesLimitIso _ _) (CategoryTheory.preservesLimitIso _ _) (CategoryTheory.preservesLimitIso _ _)
      (by apply limit.hom_ext; intros; ext; simp)
      (by
        apply limit.hom_ext
        intros
        simp [-CategoryTheory.Functor.map_comp, ← (Filtration.obj (r c)).map_comp])

open CategoryTheory.Limits

def p2Iso {B C : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}} (g : B ⟶ C) (c : ℝ≥0)
    (S : Profinite) :
    p2.{u} ((Profinite.extendNatTrans.{u, u + 1} g).app S) c ≅
      limit (p2Functor.{u} (whiskerLeft S.fintypeDiagram g) c ⋙ limUnder) :=
  by
  refine'
    HasLimit.isoOfNatIso (_ ≪≫ (CategoryTheory.Limits.cospanCompIso _ _ _).symm) ≪≫
      (CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim' _).symm
  -- This next line can be removed later if/when we generalize universe parameters in finite (co)limits
  refine' _ ≪≫ (CategoryTheory.Limits.diagramIsoCospan _).symm
  refine' CategoryTheory.Limits.cospanExt _ _ _ _ _
  exact CategoryTheory.preservesLimitIso _ _
  exact category_theory.limits.limitConstTerminal.symm
  exact CategoryTheory.preservesLimitIso _ _
  · apply limit.hom_ext; intros;
    simp [-CategoryTheory.Functor.map_comp, ← (Filtration.obj c).map_comp]
  · apply limit.hom_ext; intros; ext; simp

-- move me, generalize
theorem extend_aux {A₁ B₁ A₂ B₂ : CompHaus} (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (f : A₁ ⟶ A₂)
    (g : B₁ ⟶ B₂) (hf : Epi f) (H : e₁.inv ≫ f ≫ e₂.hom = g) : Epi g := by subst H;
  apply epi_comp _ _; infer_instance; apply epi_comp

-- move me, generalize
theorem extend_aux' {A₁ B₁ A₂ B₂ : CompHaus} (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (f : A₁ ⟶ A₂)
    (g : B₁ ⟶ B₂) (hf : Epi f) (H : f = e₁.hom ≫ g ≫ e₂.inv) : Epi g := by
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv, Category.assoc] at H ; apply extend_aux e₁ e₂ f g hf H

theorem extend_aux_1 {A B C : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}} {r : ℝ≥0 → ℝ≥0}
    {c : ℝ≥0} (S : Profinite.{u}) (f : A ⟶ B) (g : B ⟶ C) (hrc : c ≤ r c) (w w') :
    ((p1Iso.{u} f hrc S).symm.inv ≫
          limMap.{u, u, u, u + 1}
              (p1ToP2NatTrans.{u} (whiskerLeft.{u, u, u + 1, u, u + 1, u} S.fintypeDiagram f)
                (whiskerLeft.{u, u, u + 1, u, u + 1, u} S.fintypeDiagram g) hrc w) ≫
            (p2Iso.{u} g c S).symm.hom) ≫
        pullback.fst.{u, u + 1} =
      p1ToP2.{u} ((Profinite.extendNatTrans.{u, u + 1} f).app S)
          ((Profinite.extendNatTrans.{u, u + 1} g).app S) hrc w' ≫
        pullback.fst.{u, u + 1} :=
  by
  apply (cancel_mono (CategoryTheory.preservesLimitIso (Filtration.obj _) _).hom).1
  apply limit.hom_ext
  · -- TODO this is not the prettiest proof.
    -- We need some good simp lemmas for `P1_iso`, `P2_iso`, and `P1_to_P2`.
    intro j
    simp only [P1_to_P2_comp_fst, CategoryTheory.preservesLimitsIso_hom_π,
      CategoryTheory.Category.assoc]
    dsimp [P2_iso]
    simp only [CategoryTheory.Iso.symm_inv, CategoryTheory.Limits.cospanExt_inv_app_left,
      CategoryTheory.Iso.trans_inv, CategoryTheory.NatTrans.comp_app,
      CategoryTheory.Category.id_comp, CategoryTheory.preservesLimitsIso_inv_π,
      CategoryTheory.Limits.cospanCompIso_hom_app_left, CategoryTheory.Category.assoc,
      CategoryTheory.Limits.HasLimit.isoOfNatIso_inv_π_assoc]
    erw [limit_flip_comp_lim_iso_limit_comp_lim'_hom_π_π, lim_map_π_assoc]
    simp only [CategoryTheory.Category.id_comp,
      CompHausFiltPseuNormGrp₁.StronglyExact.p1ToP2NatTrans_app, CategoryTheory.Category.assoc]
    erw [lim_map_π]
    dsimp [P1_to_P2]
    simp only [CategoryTheory.Category.comp_id, CategoryTheory.Iso.refl_hom,
      CategoryTheory.eqToIso_refl, CategoryTheory.Limits.limMap_π,
      CategoryTheory.Limits.diagramIsoCospan_hom_app, CategoryTheory.Limits.pullback.lift_fst]
    dsimp [P1_iso]
    simp only [CategoryTheory.Category.assoc]
    erw [limit_flip_comp_lim_iso_limit_comp_lim'_inv_π_π]
    simp only [CategoryTheory.Limits.HasLimit.isoOfNatIso_hom_π_assoc,
      CategoryTheory.NatTrans.comp_app, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Limits.cospanCompIso_inv_app_left, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.trans_hom, CategoryTheory.Limits.cospanExt_hom_app_left]
    dsimp
    simp only [CategoryTheory.preservesLimitsIso_hom_π, CategoryTheory.Category.id_comp]
  all_goals infer_instance

theorem extend {A B C : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℝ≥0 → ℝ≥0) (hfg : ∀ S, StronglyExact (f.app S) (g.app S) r) (S : Profinite) :
    StronglyExact ((Profinite.extendNatTrans f).app S) ((Profinite.extendNatTrans g).app S) r :=
  by
  have hr : id ≤ r := (hfg <| FintypeCat.of PUnit).large
  rw [StronglyExact.iff_surjective]
  refine' ⟨_, hr, _⟩
  · rw [← NatTrans.comp_app, ← Profinite.extendNatTrans_comp]
    apply limit.hom_ext
    intro X
    specialize hfg (S.fintype_diagram.obj X)
    erw [zero_comp, limit.lift_π]
    simp only [Cones.postcompose_obj_π, whisker_left_comp, NatTrans.comp_app, limit.cone_π,
      CategoryTheory.whiskerLeft_app, hfg.comp_eq_zero, comp_zero]
  intro c
  have hfg' :
    whiskerLeft.{u, u, u + 1, u, u + 1, u} S.fintype_diagram f ≫
        whiskerLeft.{u, u, u + 1, u, u + 1, u} S.fintype_diagram g =
      0 :=
    by
    ext X : 2
    simp only [NatTrans.comp_app, CategoryTheory.whiskerLeft_app, (hfg (S.fintype_diagram.obj X)).comp_eq_zero]
    rfl
  have key :=
    CompHaus.IsLimit.surjective_of_surjective'
      (p1Functor.{u} (whisker_left S.fintype_diagram f) (hr c) ⋙ limUnder)
      (p2Functor.{u} (whisker_left S.fintype_diagram g) c ⋙ limUnder)
      (P1_to_P2_nat_trans _ _ _ hfg') _
  swap
  · intro X; specialize hfg (S.fintype_diagram.obj X); rw [iff_surjective] at hfg 
    rcases hfg with ⟨aux', hr, hfg⟩; specialize hfg c
    rw [← CompHaus.epi_iff_surjective] at hfg ⊢
    apply (config := { instances := false }) epi_comp
    · show epi ((@Limits.lim _ _ _ _ _).map _); infer_instance
    apply (config := { instances := false }) epi_comp
    · exact hfg
    · show epi ((@Limits.lim _ _ _ _ _).map _); infer_instance
  rw [← CompHaus.epi_iff_surjective] at key ⊢
  refine' extend_aux (P1_iso f (hr c) S).symm (P2_iso g c S).symm _ _ key _
  apply pullback.hom_ext
  apply extend_aux_1
  apply Subsingleton.elim

end StronglyExact

instance hasZeroNatTransCHFPNG₁ {𝒞 : Type _} [Category 𝒞] (A B : 𝒞 ⥤ CompHausFiltPseuNormGrp₁.{u}) :
    Zero (A ⟶ B) :=
  ⟨⟨0, fun S T f => by ext t; exact (B.map f).map_zero.symm⟩⟩

@[simp]
theorem zero_app {𝒞 : Type _} [Category 𝒞] (A B : 𝒞 ⥤ CompHausFiltPseuNormGrp₁.{u}) (S) :
    (0 : A ⟶ B).app S = 0 :=
  rfl

@[simp]
theorem Profinite.extendNatTrans_zero (A B : FintypeCat ⥤ CompHausFiltPseuNormGrp₁.{u}) :
    Profinite.extendNatTrans (0 : A ⟶ B) = 0 :=
  by
  apply Profinite.extend_nat_trans_ext
  rw [Profinite.extendNatTrans_whiskerLeft]
  ext S : 2
  simp only [NatTrans.comp_app, CategoryTheory.whiskerLeft_app, zero_app, zero_comp, comp_zero]

theorem stronglyExactExtendZeroLeft (A B C : FintypeCat ⥤ CompHausFiltPseuNormGrp₁.{u}) (g : B ⟶ C)
    (r : ℝ≥0 → ℝ≥0) (hfg : ∀ S, StronglyExact (0 : A.obj S ⟶ B.obj S) (g.app S) r) (S : Profinite) :
    StronglyExact (0 : (Profinite.extend A).obj S ⟶ (Profinite.extend B).obj S)
      ((Profinite.extendNatTrans g).app S) r :=
  by
  have := StronglyExact.extend (0 : A ⟶ B) g r hfg S
  simpa

theorem stronglyExactExtendZeroRight (A B C : FintypeCat ⥤ CompHausFiltPseuNormGrp₁.{u}) (f : A ⟶ B)
    (r : ℝ≥0 → ℝ≥0) (hfg : ∀ S, StronglyExact (f.app S) (0 : B.obj S ⟶ C.obj S) r) (S : Profinite) :
    StronglyExact ((Profinite.extendNatTrans f).app S)
      (0 : (Profinite.extend B).obj S ⟶ (Profinite.extend C).obj S) r :=
  by
  have := StronglyExact.extend f (0 : B ⟶ C) r hfg S
  simpa

variable (C)

theorem stronglyExactOfEpi (f : A ⟶ B) (r : ℝ≥0 → ℝ≥0) (hr : id ≤ r)
    (hf : ∀ c, filtration B c ⊆ f '' filtration A (r c)) : StronglyExact f (0 : B ⟶ C) r :=
  by
  refine' ⟨_, _, hr⟩
  · rw [comp_zero]
  · intro c; exact Set.Subset.trans (Set.inter_subset_right _ _) (hf c)

variable (A) {C}

theorem stronglyExactOfMono (g : B ⟶ C) [hg : Mono ((toPNG₁ ⋙ PseuNormGrp₁.toAb).map g)] :
    StronglyExact (0 : A ⟶ B) g id := by
  refine' ⟨_, _, le_rfl⟩
  · rw [zero_comp]
  · rintro c x ⟨hx, -⟩
    suffices x = 0 by subst x; refine' ⟨0, zero_mem_filtration _, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx 
    rw [AddCommGroupCat.mono_iff_injective, injective_iff_map_eq_zero] at hg 
    exact hg _ hx

end CompHausFiltPseuNormGrp₁

namespace Condensed

open CompHausFiltPseuNormGrp₁

theorem zero_iff_extrDisc {A B : Condensed.{u} Ab.{u + 1}} (f : A ⟶ B) :
    f = 0 ↔ ∀ S : ExtrDisc, f.val.app (op S.val) = 0 :=
  by
  constructor
  · rintro ⟨rfl⟩; simp
  · intro h
    apply (condensedExtrSheafProdEquiv Ab).Functor.map_injective
    apply (extrSheafProdToPresheaf Ab).map_injective
    ext : 2
    apply h

theorem exact_iff_extrDisc {A B C : Condensed.{u} Ab.{u + 1}} (f : A ⟶ B) (g : B ⟶ C) :
    Exact f g ↔
      ∀ S : ExtrDisc,
        Exact (f.1.app <| extrDiscToProfinite.op.obj (op S))
          (g.1.app <| extrDiscToProfinite.op.obj (op S)) :=
  by
  simp only [Abelian.exact_iff, zero_iff_ExtrDisc, forall_and]
  refine' and_congr Iff.rfl _
  apply forall_congr'
  intro S
  symm
  rw [← cancel_epi (kernel_iso g S).hom, ← cancel_mono (cokernel_iso f S).hom]
  dsimp only [Functor.op_obj, extrDiscToProfinite_obj]
  simp only [Category.assoc, zero_comp, comp_zero]
  erw [Condensed.kernelIso_hom_assoc, Condensed.cokernelIso_hom]
  exact Iff.rfl

open ComphausFilteredPseudoNormedGroup

open CompHausFiltPseuNormGrp₁.StronglyExact (p1 p2 p1ToP2 p1ToP2_comp_fst cLeRc)

theorem exact_of_stronglyExact {A B C : CompHausFiltPseuNormGrp₁.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (r : ℝ≥0 → ℝ≥0) (hfg : StronglyExact f g r) : Exact (toCondensed.map f) (toCondensed.map g) :=
  by
  rw [exact_iff_ExtrDisc]
  intro S
  rw [StronglyExact.iff_surjective] at hfg 
  rcases hfg with ⟨hfg, hr, H⟩
  simp only [Subtype.val_eq_coe, to_Condensed_map, CompHausFiltPseuNormGrp.presheaf.map_app,
    CategoryTheory.whiskerRight_app, Ab.exact_ulift_map]
  rw [AddCommGroupCat.exact_iff']
  constructor
  · show
      @CompHausFiltPseuNormGrp.Presheaf.map.{u} (CHFPNG₁_to_CHFPNGₑₗ.obj A)
          (CHFPNG₁_to_CHFPNGₑₗ.obj C)
          (@StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.{u, u} A C _ _ (f ≫ g))
          (unop.{u + 2} (extrDiscToProfinite.{u}.op.obj (op S))) =
        0
    rw [hfg]; ext x s; rfl
  · rintro ⟨_, c, y₀ : S.val → filtration B c, hy₀, rfl⟩ hy
    dsimp at hy ⊢
    let y : CompHaus.of S.val ⟶ (Filtration.obj c).obj B := ⟨y₀, hy₀⟩
    let t : CompHaus.of S.val ⟶ P2 g c := pullback.lift y (terminal.from _) _
    swap
    · apply ContinuousMap.ext; intro a; apply Subtype.ext
      simp only [AddMonoidHom.mem_ker, CompHausFiltPseuNormGrp.Presheaf.map_apply] at hy 
      have := congr_arg Subtype.val hy
      exact congr_fun this a
    let s := ExtrDisc.lift' _ (H c) t
    have hs : s ≫ P1_to_P2 f g (hr c) hfg = t := ExtrDisc.lift_lifts' _ _ _
    let π₂ : P1 f (hr c) ⟶ (Filtration.obj (r c)).obj A := pullback.snd
    let x₀ := (s ≫ π₂).1
    have hx₀ := (s ≫ π₂).2
    refine' ⟨⟨_, _, x₀, hx₀, rfl⟩, _⟩
    apply_fun fun φ => φ ≫ pullback.fst at hs 
    erw [pullback.lift_fst y (terminal.from _)] at hs 
    rw [Category.assoc, P1_to_P2_comp_fst, ← cancel_mono ((Filtration.map (CompHausFiltPseuNormGrp₁.StronglyExact.cLeRc (hr c))).app B),
      Category.assoc, pullback.condition] at hs 
    ext z
    have := FunLike.congr_fun hs z
    exact congr_arg Subtype.val this

@[simp]
theorem toCondensed_map_zero (A B : CompHausFiltPseuNormGrp₁.{u}) :
    toCondensed.map (0 : A ⟶ B) = 0 := by ext S s x; rfl

theorem mono_toCondensed_map {A B : CompHausFiltPseuNormGrp₁.{u}} (f : A ⟶ B)
    (hf : StronglyExact (0 : A ⟶ A) f id) : Mono (toCondensed.map f) :=
  by
  refine' ((Abelian.tfae_mono (to_Condensed.obj A) (to_Condensed.map f)).out 2 0).mp _
  have := Condensed.exact_of_stronglyExact (0 : A ⟶ A) f id hf
  simpa only [to_Condensed_map_zero]

theorem epi_toCondensed_map {A B : CompHausFiltPseuNormGrp₁.{u}} (f : A ⟶ B) (r : ℝ≥0 → ℝ≥0)
    (hf : StronglyExact f (0 : B ⟶ B) r) : Epi (toCondensed.map f) :=
  by
  refine' ((Abelian.tfae_epi (to_Condensed.obj B) (to_Condensed.map f)).out 2 0).mp _
  have := Condensed.exact_of_stronglyExact f (0 : B ⟶ B) r hf
  simpa only [to_Condensed_map_zero]

end Condensed

