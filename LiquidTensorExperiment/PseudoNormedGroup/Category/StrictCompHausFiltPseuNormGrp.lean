import LiquidTensorExperiment.PseudoNormedGroup.Category.CompHausFiltPseuNormGrp

#align_import pseudo_normed_group.category.strictCompHausFiltPseuNormGrp

universe u

open CategoryTheory

open scoped NNReal

attribute [local instance] typePow

noncomputable section

/-- The category of CompHaus-ly filtered pseudo-normed groups with exhaustive filtrations
and with strict morphisms. -/
structure CompHausFiltPseuNormGrp₁ : Type (u + 1) where
  M : Type u
  [str : ComphausFilteredPseudoNormedGroup M]
  exhaustive' : ∀ m : M, ∃ c, m ∈ PseudoNormedGroup.filtration M c

namespace CompHausFiltPseuNormGrp₁

instance : CoeSort CompHausFiltPseuNormGrp₁ (Type _) :=
  ⟨fun M => M.M⟩

instance (M : CompHausFiltPseuNormGrp₁) : ComphausFilteredPseudoNormedGroup M :=
  M.str

theorem exhaustive (M : CompHausFiltPseuNormGrp₁) (m : M) :
    ∃ c, m ∈ PseudoNormedGroup.filtration M c :=
  M.exhaustive' _

instance : LargeCategory CompHausFiltPseuNormGrp₁.{u}
    where
  Hom A B := StrictComphausFilteredPseudoNormedGroupHom A B
  id A := StrictComphausFilteredPseudoNormedGroupHom.id
  comp f g := StrictComphausFilteredPseudoNormedGroupHom.comp g f

-- Porting note: in Lean 3 morphisms unfolded to `StrictComphausFilteredPseudoNormedGroupHom` and used its
-- coercion; in Lean 4 it is declared (as for mathlib's `MonCat`)
instance {A B : CompHausFiltPseuNormGrp₁.{u}} : CoeFun (A ⟶ B) fun _ => A → B where
  coe (f : StrictComphausFilteredPseudoNormedGroupHom A B) := f

/-- The "forget ₁" functor from `CompHaus`-ly filtered normed groups with strict morphisms,
  to CompHaus-ly filtered pseudo-normed groups with bounded morphisms, which is the
  identity on objects. -/
@[simps]
def cHFPNG₁ToCHFPNGₑₗ : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp
    where
  obj M := CompHausFiltPseuNormGrp.of M
  map f := StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom f

instance : Faithful cHFPNG₁ToCHFPNGₑₗ.{u}
    where
  map_injective {M₁ M₂ f g} h := by
    apply StrictComphausFilteredPseudoNormedGroupHom.ext; intro x
    apply_fun fun φ => φ.toFun at h
    exact congr_fun h x

instance : ConcreteCategory CompHausFiltPseuNormGrp₁.{u}
    where
  forget :=
    { obj := fun M => M.M
      map := fun f => f }
  -- Porting note: Lean 3 proved this field automatically
  forget_faithful := ⟨fun h => StrictComphausFilteredPseudoNormedGroupHom.ext (congrFun h)⟩

def level : ℝ≥0 ⥤ CompHausFiltPseuNormGrp₁.{u} ⥤ CompHaus
    where
  obj c :=
    { obj := fun M => CompHaus.of <| PseudoNormedGroup.filtration M c
      map := fun f => ⟨_, StrictComphausFilteredPseudoNormedGroupHom.level_continuous f _⟩
      -- Porting note: Lean 3 proved the functor and naturality laws automatically
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  map {c₁ c₂} h :=
    { app := fun M =>
        letI : Fact (c₁ ≤ c₂) := ⟨leOfHom h⟩
        ⟨_, ComphausFilteredPseudoNormedGroup.continuous_castLe _ _⟩
      naturality := fun _ _ _ => rfl }
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

section Limits

/-!
In this section, we show (hopefully ;)) that `CompHausFiltPseuNormGrp₁` has limits.
-/


variable {J : Type u} [SmallCategory J] (G : J ⥤ CompHausFiltPseuNormGrp₁.{u})

open PseudoNormedGroup

open CategoryTheory.Limits

/-- This is a bifunctor which associates to each `c : ℝ≥0` and `j : J`,
  the `c`-th term of the filtration of `G.obj j`. -/
def conePointDiagram : AsSmall.{u} ℝ≥0 ⥤ J ⥤ CompHaus.{u} :=
  AsSmall.down ⋙ CompHausFiltPseuNormGrp₁.level ⋙ (whiskeringLeft _ _ _).obj G

def ConePointTypeFilt (c : ℝ≥0) : Type u :=
  {x : ∀ j : J, filtration (G.obj j) c | ∀ ⦃i j : J⦄ (e : i ⟶ j), StrictComphausFilteredPseudoNormedGroupHom.level (G.map e) (x _) = x _}

-- Porting note: Lean 3 derived these two instances (`@[derive]`)
instance (c : ℝ≥0) : TopologicalSpace (ConePointTypeFilt G c) := by
  unfold ConePointTypeFilt; infer_instance

instance (c : ℝ≥0) : T2Space (ConePointTypeFilt G c) := by
  unfold ConePointTypeFilt; infer_instance

-- Porting note: Lean 3 took this from `CompHaus.limitCone`, whose topology is not
-- definitionally the subspace topology in mathlib4; the cone points are a closed subset of a
-- compact product.
instance (c : ℝ≥0) : CompactSpace (ConePointTypeFilt G c) := by
  have : IsClosed {x : ∀ j : J, filtration (G.obj j) c |
      ∀ ⦃i j : J⦄ (e : i ⟶ j), StrictComphausFilteredPseudoNormedGroupHom.level (G.map e) (x _) = x _} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun e =>
      isClosed_eq ((StrictComphausFilteredPseudoNormedGroupHom.level_continuous (G.map e) c).comp (_root_.continuous_apply i))
        (_root_.continuous_apply j)
  exact isCompact_iff_compactSpace.mp this.isCompact

-- ;-)
namespace ConePointTypeFilt

variable {G}

instance (c : ℝ≥0) : CoeFun (ConePointTypeFilt G c) fun x => ∀ j : J, filtration (G.obj j) c :=
  ⟨fun x => x.1⟩

@[ext]
theorem ext {c} (x y : ConePointTypeFilt G c) :
    (⇑x : ∀ j : J, filtration (G.obj j) c) = y → x = y :=
  Subtype.ext

@[simp]
theorem level_apply {c : ℝ≥0} {i j : J} (x : ConePointTypeFilt G c) (e : i ⟶ j) :
    StrictComphausFilteredPseudoNormedGroupHom.level (G.map e) (x i) = x j :=
  x.2 e

@[simp]
theorem map_apply {c : ℝ≥0} {i j : J} (x : ConePointTypeFilt G c) (e : i ⟶ j) :
    (G.map e) (x i) = x j := by rw [← StrictComphausFilteredPseudoNormedGroupHom.coe_level (G.map e)]; simp

def trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : ConePointTypeFilt G c₁) : ConePointTypeFilt G c₂ :=
  ⟨fun j => castLe' h (x j), fun i j e => by ext; simp⟩

@[simp]
theorem trans_apply {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : ConePointTypeFilt G c₁) (j : J) :
    x.trans h j = castLe' h (x j) := by ext; rfl

theorem trans_injective {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
    Function.Injective (trans h : ConePointTypeFilt G c₁ → ConePointTypeFilt G c₂) :=
  by
  intro x y hh
  ext j
  apply_fun fun e => (e j : G.obj j) at hh 
  exact hh

theorem trans_continuous {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) :
    Continuous (trans h : ConePointTypeFilt G c₁ → ConePointTypeFilt G c₂) :=
  by
  -- Porting note: Lean 3 obtained this from the universal property of `CompHaus.limitCone`;
  -- here it is proved directly, coordinatewise
  haveI : Fact (c₁ ≤ c₂) := ⟨h⟩
  exact Continuous.subtype_mk (continuous_pi fun j =>
    (ComphausFilteredPseudoNormedGroup.continuous_castLe c₁ c₂).comp
      ((_root_.continuous_apply j).comp continuous_subtype_val)) _

theorem continuous_apply {c : ℝ≥0} (j : J) : Continuous fun t : ConePointTypeFilt G c => t j :=
  by
  change
    Continuous
      ((fun u : ∀ j, filtration (G.obj j) c => u j) ∘ fun u : CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c => ⇑u)
  apply Continuous.comp
  apply _root_.continuous_apply
  apply continuous_subtype_val

instance {c} : Zero (ConePointTypeFilt G c) :=
  Zero.mk <| ⟨fun j => 0, fun i j e => by ext; dsimp; simp⟩

instance {c} : Neg (ConePointTypeFilt G c) :=
  Neg.mk fun x => ⟨fun j => -x j, fun i j e => by ext; dsimp; simp⟩

def add' {c₁ c₂} (x : ConePointTypeFilt G c₁) (y : ConePointTypeFilt G c₂) :
    ConePointTypeFilt G (c₁ + c₂) :=
  ⟨fun j => PseudoNormedGroup.add' (x j, y j), fun i j e => by
    ext; dsimp; simp⟩

@[simp]
theorem zero_apply {c} (j : J) : (0 : ConePointTypeFilt G c) j = 0 :=
  rfl

@[simp]
theorem neg_apply {c} (j : J) (x : ConePointTypeFilt G c) : (-x) j = -x j :=
  rfl

@[simp]
theorem add'_apply_coe {c₁ c₂} (j : J) (x : ConePointTypeFilt G c₁) (y : ConePointTypeFilt G c₂) :
    ((x.add' y) j : G.obj j) = x j + y j :=
  rfl

theorem continuous_neg {c} : Continuous fun x : ConePointTypeFilt G c => -x :=
  by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous ((fun x => -x) ∘ fun a : CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c => a j)
  apply Continuous.comp
  apply ComphausFilteredPseudoNormedGroup.continuous_neg'
  apply continuous_apply

theorem continuous_add' {c1 c2} :
    Continuous fun t : ConePointTypeFilt G c1 × ConePointTypeFilt G c2 => t.1.add' t.2 :=
  by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  let A :
    CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c1 × CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c2 →
      (∀ j : J, filtration (G.obj j) c1) × ∀ j : J, filtration (G.obj j) c2 :=
    fun t => (t.1, t.2)
  let B :
    ((∀ j : J, filtration (G.obj j) c1) × ∀ j : J, filtration (G.obj j) c2) →
      filtration (G.obj j) c1 × filtration (G.obj j) c2 :=
    fun t => (t.1 j, t.2 j)
  let C : filtration (G.obj j) c1 × filtration (G.obj j) c2 → filtration (G.obj j) (c1 + c2) :=
    PseudoNormedGroup.add'
  change Continuous (C ∘ B ∘ A)
  apply Continuous.comp
  apply ComphausFilteredPseudoNormedGroup.continuous_add'
  apply Continuous.comp
  · apply Continuous.prod_mk
    · change Continuous ((fun t : ∀ j : J, filtration (G.obj j) c1 => t j) ∘ Prod.fst)
      apply Continuous.comp
      apply _root_.continuous_apply
      exact continuous_fst
    · change Continuous ((fun t : ∀ j : J, filtration (G.obj j) c2 => t j) ∘ Prod.snd)
      apply Continuous.comp
      apply _root_.continuous_apply
      exact continuous_snd
  apply Continuous.prod_map
  apply continuous_subtype_val
  apply continuous_subtype_val

end ConePointTypeFilt

def conePointTypeSetoid : Setoid (Σ c : ℝ≥0, ConePointTypeFilt G c)
    where
  r x y := ∃ (d : ℝ≥0) (hx : x.1 ≤ d) (hy : y.1 ≤ d), x.2.trans hx = y.2.trans hy
  iseqv := by
    refine' ⟨_, _, _⟩
    · rintro ⟨c, x⟩
      use c, le_refl _, le_refl _
    · rintro ⟨c, x⟩ ⟨d, y⟩ ⟨e, h1, h2, h⟩
      dsimp at *
      refine' ⟨_, le_sup_left, le_sup_right, _⟩
      ext j : 3
      symm
      apply_fun fun e => (e j : G.obj j) at h 
      exact h
    · rintro ⟨c, x⟩ ⟨d, y⟩ ⟨e, z⟩ ⟨i, h1, hh1, hhh1⟩ ⟨j, h2, hh2, hhh2⟩
      dsimp at *
      refine' ⟨_, le_sup_left, le_sup_right, _⟩
      ext jj : 3
      apply_fun fun e => (e jj : G.obj jj) at hhh1 
      apply_fun fun e => (e jj : G.obj jj) at hhh2 
      erw [hhh1, hhh2]; rfl

def ConePointType : Type u :=
  Quotient (conePointTypeSetoid G)

namespace ConePointType

variable {G}

def incl (c : ℝ≥0) : ConePointTypeFilt G c → ConePointType G :=
  Quotient.mk'' ∘ Sigma.mk c

theorem incl_injective (c : ℝ≥0) :
    Function.Injective (incl c : ConePointTypeFilt G c → ConePointType G) :=
  by
  intro x y h
  replace h := Quotient.exact' h
  obtain ⟨d, h1, h2, h⟩ := h
  dsimp at h1 h2 h 
  rw [show h1 = h2 by rfl] at h 
  apply ConePointTypeFilt.trans_injective h2
  exact h

@[simp]
theorem incl_trans {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : ConePointTypeFilt G c₁) :
    incl _ (x.trans h) = incl _ x := by
  apply Quotient.sound'
  refine' ⟨c₁ ⊔ c₂, by simp, by simp, _⟩
  ext
  rfl

theorem incl_jointly_surjective (x : ConePointType G) :
    ∃ (c : ℝ≥0) (y : ConePointTypeFilt G c), incl c y = x :=
  by
  obtain ⟨⟨c, y⟩⟩ := x
  exact ⟨c, y, rfl⟩

def index (x : ConePointType G) : ℝ≥0 :=
  (incl_jointly_surjective x).choose

def preimage (x : ConePointType G) : ConePointTypeFilt G x.index :=
  (incl_jointly_surjective x).choose_spec.choose

@[simp]
theorem preimage_spec (x : ConePointType G) : incl _ x.preimage = x :=
  (incl_jointly_surjective x).choose_spec.choose_spec

@[simp]
theorem coe_incl_preimage_apply {c} (x : ConePointTypeFilt G c) (j : J) :
    ((incl c x).preimage j : G.obj j) = x j :=
  by
  let e := c ⊔ (incl c x).index
  change _ = (PseudoNormedGroup.castLe' (le_sup_left : c ≤ e) (x j) : G.obj j)
  rw [← ConePointTypeFilt.trans_apply (le_sup_left : _ ≤ e) x j]
  rw [← PseudoNormedGroup.coe_castLe' (le_sup_right : _ ≤ e)]
  rw [← ConePointTypeFilt.trans_apply]
  -- Porting note: Lean 4's `congr 2` does not reach this equation, so it is stated
  have : ConePointTypeFilt.trans (le_sup_right : _ ≤ e) (incl c x).preimage =
      ConePointTypeFilt.trans (le_sup_left : c ≤ e) x := by
    apply incl_injective; simp
  rw [this]

instance : Zero (ConePointType G) :=
  ⟨incl 0 0⟩

theorem zero_def : (0 : ConePointType G) = incl 0 0 :=
  rfl

instance : Neg (ConePointType G) :=
  Neg.mk fun x => incl _ (-x.preimage)

theorem neg_def (x : ConePointType G) : -x = incl _ (-x.preimage) :=
  rfl

instance : Add (ConePointType G) :=
  Add.mk fun x y => incl _ (x.preimage.add' y.preimage)

theorem add_def (x y : ConePointType G) : x + y = incl _ (x.preimage.add' y.preimage) :=
  rfl

theorem incl_add_incl (c₁ c₂ : ℝ≥0) (x₁ : ConePointTypeFilt G c₁) (x₂ : ConePointTypeFilt G c₂) :
    incl c₁ x₁ + incl c₂ x₂ = incl (c₁ + c₂) (x₁.add' x₂) :=
  by
  rw [add_def]
  apply Quotient.sound'
  refine' ⟨max _ _, le_max_left _ _, le_max_right _ _, _⟩
  ext
  simp only [ConePointTypeFilt.trans_apply, ConePointTypeFilt.add'_apply_coe, coe_castLe,
    coe_incl_preimage_apply, PseudoNormedGroup.coe_castLe']

theorem zero_add (x : ConePointType G) : 0 + x = x :=
  by
  conv_rhs => rw [← x.preimage_spec]
  apply Quotient.sound'
  refine' ⟨(0 : CompHausFiltPseuNormGrp₁.ConePointType G).index + x.index, by simp, by simp, _⟩
  dsimp
  ext j : 3
  simp only [ConePointTypeFilt.trans_apply, ConePointTypeFilt.add'_apply_coe, PseudoNormedGroup.coe_castLe']
  simp only [add_left_eq_self]
  apply coe_incl_preimage_apply

theorem add_comm (x y : ConePointType G) : x + y = y + x :=
  by
  apply Quotient.sound'
  refine' ⟨x.index + y.index, le_refl _, le_of_eq (by dsimp; rw [_root_.add_comm]), _⟩
  dsimp
  ext j : 3
  simp only [ConePointTypeFilt.trans_apply, ConePointTypeFilt.add'_apply_coe, coe_castLe,
    PseudoNormedGroup.coe_castLe']
  rw [_root_.add_comm]

theorem add_zero (x : ConePointType G) : x + 0 = x := by rw [add_comm]; apply zero_add

theorem add_assoc (x y z : ConePointType G) : x + y + z = x + (y + z) :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j : 3
  simp only [ConePointTypeFilt.trans_apply, ConePointTypeFilt.add'_apply_coe, coe_castLe,
    PseudoNormedGroup.coe_castLe']
  erw [coe_incl_preimage_apply, coe_incl_preimage_apply]
  simp [_root_.add_assoc]

theorem add_left_neg (x : ConePointType G) : -x + x = 0 :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j : 3
  simp only [ConePointTypeFilt.trans_apply, ConePointTypeFilt.zero_apply,
    ConePointTypeFilt.add'_apply_coe, coe_castLe, filtration.coe_zero, PseudoNormedGroup.coe_castLe']
  erw [coe_incl_preimage_apply]
  simp

instance : AddCommGroup (ConePointType G) :=
  { (inferInstance : Add _), (inferInstance : Zero _),
    (inferInstance : Neg _) with
    add_assoc := add_assoc
    zero_add := zero_add
    add_zero := add_zero
    add_left_neg := add_left_neg
    add_comm := add_comm }

variable (G)

def filt (c : ℝ≥0) : Set (ConePointType G) :=
  Set.range (incl c)

def filtEquiv (c : ℝ≥0) : ConePointTypeFilt G c ≃ filt G c :=
  Equiv.ofBijective (fun x => ⟨_, x, rfl⟩)
    (by
      constructor
      · intro x y h
        apply_fun fun e => e.val at h 
        apply incl_injective
        exact h
      · rintro ⟨_, x, rfl⟩; use x)

instance {c} : TopologicalSpace (filt G c) :=
  TopologicalSpace.induced (filtEquiv G c).symm inferInstance

def filtHomeo (c : ℝ≥0) : filt G c ≃ₜ ConePointTypeFilt G c :=
  Homeomorph.homeomorphOfContinuousOpen (filtEquiv G c).symm continuous_induced_dom
    (by
      intro U hU
      have : Inducing (CompHausFiltPseuNormGrp₁.ConePointType.filtEquiv G c).symm := ⟨rfl⟩
      rw [this.isOpen_iff] at hU 
      obtain ⟨U, hU, rfl⟩ := hU
      simpa)

instance {c} : CompactSpace (filt G c) :=
  (filtHomeo G c).symm.compactSpace

instance {c} : T2Space (filt G c) :=
  (filtHomeo G c).symm.t2Space

def filtIso (c : ℝ≥0) :
    CompHaus.of (filt G c) ≅
      (CompHaus.limitCone.{_, u} ((conePointDiagram G).obj (AsSmall.up.obj c))).pt
    where
  hom := (filtHomeo G c).toContinuousMap
  inv := (filtHomeo G c).symm.toContinuousMap
  hom_inv_id := by ext1; exact (filtHomeo G c).symm_apply_apply _
  inv_hom_id := by ext1; exact (filtHomeo G c).apply_symm_apply _

variable {G}

@[simp]
theorem incl_neg {c} (x : ConePointTypeFilt G c) : incl c (-x) = -incl c x :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j : 3
  simp

@[simp]
theorem incl_add' {c1 c2} (x1 : ConePointTypeFilt G c1) (x2 : ConePointTypeFilt G c2) :
    incl (c1 + c2) (x1.add' x2) = incl c1 x1 + incl c2 x2 :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j : 3
  simp

@[simp]
theorem incl_zero {c} : incl c (0 : ConePointTypeFilt G c) = 0 :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j : 3
  simp

instance : PseudoNormedGroup (ConePointType G)
    where
  filtration' := filt G
  filtration_mono' := by
    rintro c1 c2 h x ⟨x, rfl⟩
    dsimp [filt]
    use x.trans h
    simp
  zero_mem_filtration' := by
    intro c
    use 0
    simp
  neg_mem_filtration' := by
    rintro c x ⟨x, rfl⟩
    use-x
    simp
  add_mem_filtration' := by
    rintro c1 c2 x1 x2 ⟨x1, rfl⟩ ⟨x2, rfl⟩
    use x1.add' x2
    simp

instance : ComphausFilteredPseudoNormedGroup (ConePointType G)
    where
  topology := by infer_instance
  t2 := by infer_instance
  compact := by infer_instance
  continuous_add' := by
    intro c1 c2
    let E :
      filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c1 × filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c2 →
        CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c1 × CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c2 :=
      fun t => ⟨(filtHomeo G c1) t.1, (filtHomeo G c2) t.2⟩
    let E' :
      CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c1 × CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c2 →
        filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c1 × filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c2 :=
      fun t => ⟨(filtHomeo G c1).symm t.1, (filtHomeo G c2).symm t.2⟩
    have hE'E : E' ∘ E = id := by dsimp [E, E']; ext; simp; simp
    have :
      (filtHomeo G (c1 + c2)).symm ∘
          (fun t : CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c1 × CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c2 => t.1.add' t.2) ∘ E =
        add' :=
      by
      suffices
        add' ∘ E' =
          (filtHomeo G (c1 + c2)).toEquiv.symm ∘
            fun t : CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c1 × CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c2 => t.1.add' t.2
        by
        erw [← Function.comp.assoc, ← this, Function.comp.assoc, hE'E]
        simp
      dsimp only [filtHomeo, Homeomorph.homeomorphOfContinuousOpen, E']
      ext
      dsimp [filtHomeo, CompHausFiltPseuNormGrp₁.ConePointType.filtEquiv, E, E']
      simp
    rw [← this]; clear this
    apply Continuous.comp (Homeomorph.continuous _)
    apply Continuous.comp
    apply ConePointTypeFilt.continuous_add'
    dsimp [E]
    continuity
  continuous_neg' := by
    intro c
    have :
      (neg' : filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c → filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c) =
        (filtHomeo G c).symm ∘ (fun x => -x) ∘ filtHomeo G c :=
      by
      suffices
        (neg' : filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c → filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c) ∘
            (filtHomeo G c).toEquiv.symm =
          (filtHomeo G c).toEquiv.symm ∘ fun x => -x
        by
        erw [← Function.comp.assoc, ← this, Function.comp.assoc, Equiv.symm_comp_self]
        rfl
      dsimp only [filtHomeo, Homeomorph.homeomorphOfContinuousOpen]
      simp only [Equiv.symm_symm]
      ext
      dsimp [CompHausFiltPseuNormGrp₁.ConePointType.filtEquiv]
      simp
    rw [this]
    exact (filtHomeo G c).symm.continuous.comp
      (ConePointTypeFilt.continuous_neg.comp (filtHomeo G c).continuous)
  continuous_castLe := by
    rintro c₁ c₂ ⟨h⟩
    change Continuous (PseudoNormedGroup.castLe' h)
    have : PseudoNormedGroup.castLe' h = (filtHomeo G c₂).symm ∘ ConePointTypeFilt.trans h ∘ filtHomeo G c₁ :=
      by
      suffices
        PseudoNormedGroup.castLe' h ∘ (filtHomeo G c₁).toEquiv.symm =
          (filtHomeo G c₂).toEquiv.symm ∘ ConePointTypeFilt.trans h
        by
        erw [← Function.comp.assoc, ← this, Function.comp.assoc, Equiv.symm_comp_self]
        simp
      dsimp only [filtHomeo, Homeomorph.homeomorphOfContinuousOpen]
      simp only [Equiv.symm_symm]
      ext
      dsimp [CompHausFiltPseuNormGrp₁.ConePointType.filtEquiv]
      simp
    rw [this]
    exact (filtHomeo G c₂).symm.continuous.comp
      ((ConePointTypeFilt.trans_continuous h).comp (filtHomeo G c₁).continuous)

end ConePointType

def conePoint : CompHausFiltPseuNormGrp₁
    where
  M := ConePointType G
  exhaustive' := ConePointType.incl_jointly_surjective

def proj (j : J) : conePoint G ⟶ G.obj j
    where
  toFun x := x.preimage j
  map_zero' := by
    rw [ConePointType.zero_def]
    simp only [ConePointType.coe_incl_preimage_apply, ConePointTypeFilt.zero_apply,
      filtration.coe_zero]
  map_add' := by
    intro x y
    rw [ConePointType.add_def x y]
    simp only [ConePointType.coe_incl_preimage_apply, ConePointTypeFilt.add'_apply_coe]
  strict' := by
    rintro c x ⟨x, rfl⟩
    simp only [ConePointType.coe_incl_preimage_apply, Subtype.coe_prop]
  continuous' := by
    intro c
    dsimp
    let E : filtration (CompHausFiltPseuNormGrp₁.ConePointType G) c → filtration (G.obj j) c := fun t =>
      ((ConePointType.filtHomeo G c) t) j
    suffices Continuous E by
      convert this
      ext ⟨t, t, rfl⟩
      dsimp [E]
      simp only [ConePointType.coe_incl_preimage_apply]
      congr 2
      -- Porting note: `filtHomeo` is `filtEquiv.symm`, so this is `symm_apply_apply`
      exact congrArg (fun u : ConePointTypeFilt G c => u j)
        ((ConePointType.filtEquiv G c).symm_apply_apply t).symm
    dsimp [E]
    change Continuous ((fun u : CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c => u j) ∘ ConePointType.filtHomeo G c)
    simp only [Homeomorph.comp_continuous_iff']
    apply ConePointTypeFilt.continuous_apply

def limitCone : Cone G where
  pt := conePoint G
  π :=
    { app := fun j => proj G j
      naturality := by
        intro i j e
        ext x
        dsimp
        simp only [comp_apply, Category.id_comp]
        have := (ConePointType.preimage x).2 e
        apply_fun fun e => (e : G.obj j) at this 
        exact this.symm }

def index {M : CompHausFiltPseuNormGrp₁} (x : M) : ℝ≥0 :=
  (M.exhaustive x).choose

def preimage {M : CompHausFiltPseuNormGrp₁} (x : M) : filtration M (index x) :=
  ⟨x, (M.exhaustive x).choose_spec⟩

def limitConeLiftMap (D : Cone G) : D.pt → conePoint G := fun x =>
  ConePointType.incl (index x)
    ⟨fun j => (D.π.app j).level (preimage x), by
      intro i j e
      ext
      dsimp
      simp⟩

theorem limitConeLiftMap_map_zero {D : Cone G} : limitConeLiftMap G D 0 = 0 :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j
  simp only [ConePointTypeFilt.trans_apply, ConePointTypeFilt.zero_apply, coe_castLe,
    filtration.coe_zero, PseudoNormedGroup.coe_castLe']
  apply (D.π.app j).map_zero

theorem limitConeLiftMap_map_add {D : Cone G} (a b : D.pt) :
    limitConeLiftMap G D (a + b) = limitConeLiftMap G D a + limitConeLiftMap G D b :=
  by
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  dsimp
  ext j
  dsimp [CompHausFiltPseuNormGrp₁.limitConeLiftMap]
  simp only [ConePointTypeFilt.trans_apply, ConePointType.coe_incl_preimage_apply,
    ConePointTypeFilt.add'_apply_coe, coe_castLe, PseudoNormedGroup.coe_castLe']
  exact (D.π.app j).map_add a b

theorem limitConeLiftMap_strict {D : Cone G} {x : D.pt} (c : ℝ≥0) (hx : x ∈ filtration D.pt c) :
    limitConeLiftMap G D x ∈ filtration (ConePointType G) c :=
  by
  dsimp [CompHausFiltPseuNormGrp₁.limitConeLiftMap]
  change _ ∈ Set.range _
  refine' ⟨⟨fun j => (D.π.app j).level ⟨x, hx⟩, _⟩, _⟩
  · intro i j e
    ext
    dsimp
    simp
  · dsimp
    apply Quotient.sound'
    refine' ⟨_, le_sup_left, le_sup_right, _⟩
    dsimp
    ext j
    simp; rfl

def limitConeLift (D : Cone G) : D.pt ⟶ conePoint G
    where
  toFun := limitConeLiftMap _ D
  map_zero' := limitConeLiftMap_map_zero _
  map_add' := limitConeLiftMap_map_add _
  strict' c x hx := limitConeLiftMap_strict G c hx
  continuous' := by
    intro c
    rw [(ConePointType.filtHomeo G c).inducing.continuous_iff]
    let E : filtration D.pt c → CompHausFiltPseuNormGrp₁.ConePointTypeFilt G c := fun t =>
      ⟨fun j => (D.π.app j).level t, _⟩
    swap;
    · intro i j e
      ext
      dsimp
      simp
    have :
      ConePointType.filtHomeo G c ∘
          PseudoNormedGroup.level (CompHausFiltPseuNormGrp₁.limitConeLiftMap G D)
            (fun c x hx => CompHausFiltPseuNormGrp₁.limitConeLiftMap_strict G c hx) c =
        E :=
      by
      ext1
      apply_fun (ConePointType.filtHomeo G c).symm
      dsimp [E]
      simp only [Homeomorph.symm_apply_apply]
      ext
      apply Quotient.sound'
      refine' ⟨_, le_sup_left, le_sup_right, _⟩
      ext
      dsimp
      simp only [ConePointTypeFilt.trans_apply, coe_castLe, PseudoNormedGroup.coe_castLe']
      rfl
    rw [this]
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    dsimp
    apply (D.π.app j).level_continuous

def limitConeIsLimit : IsLimit (limitCone G)
    where
  lift S := limitConeLift _ _
  fac := by
    intro S j
    ext
    change (limitCone G).π.app j _ = _
    dsimp [limitConeLift, limitCone, CompHausFiltPseuNormGrp₁.limitConeLiftMap, proj]
    simp; rfl
  uniq := by
    intro S m h
    ext x
    dsimp [limitConeLift, CompHausFiltPseuNormGrp₁.limitConeLiftMap]
    rw [← (m x).preimage_spec]
    apply Quotient.sound'
    refine' ⟨_, le_sup_left, le_sup_right, _⟩
    ext j
    dsimp
    simp only [ConePointTypeFilt.trans_apply, coe_castLe, PseudoNormedGroup.coe_castLe']
    specialize h j
    apply_fun fun e => e x at h 
    exact h

-- This is the goal of this section...
instance : HasLimit G :=
  HasLimit.mk ⟨limitCone _, limitConeIsLimit _⟩

instance : HasLimits CompHausFiltPseuNormGrp₁ :=
  ⟨fun J _ => { has_limit := fun G => inferInstance }⟩

instance (c : ℝ≥0) : PreservesLimit G (level.obj c) :=
  preservesLimitOfPreservesLimitCone (limitConeIsLimit _)
    { lift := fun S =>
        (CompHaus.limitConeIsLimit.{_, u} ((conePointDiagram G).obj (AsSmall.up.obj c))).lift _ ≫
          (ConePointType.filtIso _ _).inv
      fac := by
        intro S j
        dsimp
        rw [Category.assoc]
        convert
          (CompHaus.limitConeIsLimit.{_, u} ((CompHausFiltPseuNormGrp₁.conePointDiagram G).obj (AsSmall.up.obj c))).fac S
            j
        ext ⟨t, ht⟩
        dsimp [limitCone, ConePointType.filtIso, ConePointType.filtHomeo,
          Homeomorph.homeomorphOfContinuousOpen, ConePointType.filtEquiv, level, proj,
          CompHaus.limitCone, TopCat.limitCone]
        simpa
      uniq := by
        intro S m hm
        rw [Iso.eq_comp_inv]
        apply
          (CompHaus.limitConeIsLimit.{_, u} ((CompHausFiltPseuNormGrp₁.conePointDiagram G).obj (AsSmall.up.obj c))).uniq
        intro j
        rw [← hm, Category.assoc]
        congr 1
        rw [← Iso.eq_inv_comp]
        ext ⟨t, ht⟩
        dsimp [limitCone, ConePointType.filtIso, ConePointType.filtHomeo,
          Homeomorph.homeomorphOfContinuousOpen, ConePointType.filtEquiv, level, proj,
          CompHaus.limitCone, TopCat.limitCone]
        simpa }

instance (c : ℝ≥0) : PreservesLimits (level.obj c)
    where preservesLimitsOfShape := { preservesLimit := inferInstance }

theorem mem_filtration_iff_of_isLimit (C : Cone G) (hC : IsLimit C) (c : ℝ≥0) (x : C.pt) :
    x ∈ PseudoNormedGroup.filtration C.pt c ↔
      ∀ j : J, C.π.app j x ∈ PseudoNormedGroup.filtration (G.obj j) c :=
  by
  constructor
  · intro h j
    apply StrictComphausFilteredPseudoNormedGroupHom.strict (C.π.app j) h
  · intro h
    let E := limitCone G
    let e : C ≅ E := hC.uniqueUpToIso (limitConeIsLimit _)
    let eX : C.pt ≅ E.pt := (Cones.forget _).mapIso e
    let w := eX.hom x
    have hw : ∀ j, E.π.app j w ∈ filtration (G.obj j) c :=
      by
      intro j
      dsimp only [w]
      change (eX.hom ≫ E.π.app _) _ ∈ _
      dsimp only [eX, Functor.mapIso, Cones.forget]
      convert h j
      simp
    suffices w ∈ filtration (limitCone G).pt c
      by
      convert eX.inv.strict this
      change _ = (eX.hom ≫ eX.inv) x
      rw [Iso.hom_inv_id]
      rfl
    change ∃ z, _
    refine' ⟨⟨fun j => ⟨_, hw _⟩, _⟩, _⟩
    · intro i j f
      ext1
      dsimp
      change (E.π.app i ≫ G.map f) _ = _
      rw [E.w]
    · obtain ⟨i, z, hz⟩ := ConePointType.incl_jointly_surjective w
      let d : ℝ≥0 := i ⊔ c
      conv_rhs => rw [← hz]
      rw [← ConePointType.incl_trans (le_sup_left : i ≤ d)]
      rw [← ConePointType.incl_trans (le_sup_right : c ≤ d)]
      congr 1
      dsimp [ConePointTypeFilt.trans]
      ext j
      dsimp
      change E.π.app j _ = _
      rw [← hz]
      dsimp [E, limitCone, proj]
      simp

theorem isLimit_ext (C : Cone G) (hC : IsLimit C) (x y : C.pt)
    (h : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
  by
  let E := limitCone G
  let e : C ≅ E := hC.uniqueUpToIso (limitConeIsLimit _)
  let eX : C.pt ≅ E.pt := (Cones.forget _).mapIso e
  apply_fun eX.hom
  swap
  · intro a b hh
    apply_fun fun e => eX.inv e at hh 
    change (eX.hom ≫ eX.inv) _ = (eX.hom ≫ eX.inv) _ at hh 
    simpa only [Iso.hom_inv_id] using hh
  have hh : ∀ j, (E.π.app j) (eX.hom x) = (E.π.app j) (eX.hom y) :=
    by
    intro j
    change (eX.hom ≫ E.π.app j) x = (eX.hom ≫ E.π.app j) y
    convert h j using 2
    all_goals simp
  obtain ⟨ca, a, ha⟩ := ConePointType.incl_jointly_surjective (eX.hom x)
  obtain ⟨cb, b, hb⟩ := ConePointType.incl_jointly_surjective (eX.hom y)
  rw [← ha, ← hb] at hh ⊢
  let d : ℝ≥0 := ca ⊔ cb
  rw [← ConePointType.incl_trans (le_sup_left : ca ≤ d)] at hh ⊢
  rw [← ConePointType.incl_trans (le_sup_right : cb ≤ d)] at hh ⊢
  congr 1
  ext j
  specialize hh j
  convert hh using 1
  all_goals
    dsimp [E, limitCone, proj]
    simp

end Limits

section Products

/-!
In this section, we construct explicit finite products.
-/


def product {α : Type u} [Fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u}) :
    CompHausFiltPseuNormGrp₁.{u} where
  M := ∀ i, X i
  exhaustive' := by
    intro m
    choose cs hcs using fun i => (X i).exhaustive (m i)
    have : ∃ c : ℝ≥0, ∀ i, cs i ≤ c := by
      use Finset.univ.sup cs
      intro i
      apply Finset.le_sup (Finset.mem_univ i)
    obtain ⟨c, hc⟩ := this
    refine' ⟨c, fun i => PseudoNormedGroup.filtration_mono (hc i) (hcs i)⟩

@[simps]
def product.π {α : Type u} [Fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u}) (i : α) :
    product X ⟶ X i where
  toFun m := m i
  map_zero' := rfl
  map_add' x y := rfl
  strict' c x hx := hx i
  continuous' :=
    by
    -- This can be golfed.
    intro c
    have h : Inducing (PseudoNormedGroup.filtrationPiEquiv (fun i => X i) c) := ⟨rfl⟩
    let e :
      ↥(PseudoNormedGroup.filtration (↥(product X)) c) →
        ↥(PseudoNormedGroup.filtration (↥(X i)) c) :=
      PseudoNormedGroup.level (fun m : ↥(product X) => m i) _ c
    swap
    · intro c x hx
      apply hx
    change Continuous e
    have : e = _ ∘ PseudoNormedGroup.filtrationPiEquiv (fun i => X i) c
    rotate_left 2
    · intro x; exact x i
    · ext; rfl
    erw [this]
    apply Continuous.comp
    apply continuous_apply
    refine' Inducing.continuous h

@[simps]
def product.lift {α : Type u} [Fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
    (M : CompHausFiltPseuNormGrp₁.{u}) (f : ∀ i, M ⟶ X i) : M ⟶ product X
    where
  toFun m i := f _ m
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp
  strict' c x hx i := (f i).Strict hx
  continuous' := by
    intro c
    have h : Inducing (PseudoNormedGroup.filtrationPiEquiv (fun i => X i) c) := ⟨rfl⟩
    rw [h.continuous_iff, continuous_pi_iff]
    intro i
    exact (f i).continuous' c

@[reassoc (attr := simp)]
theorem product.lift_π {α : Type u} [Fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
    (M : CompHausFiltPseuNormGrp₁.{u}) (f : ∀ i, M ⟶ X i) (i) :
    product.lift X M f ≫ product.π X i = f i := by ext; simp

theorem product.lift_unique {α : Type u} [Fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
    (M : CompHausFiltPseuNormGrp₁.{u}) (f : ∀ i, M ⟶ X i) (g : M ⟶ product X)
    (hg : ∀ i, g ≫ product.π X i = f i) : g = product.lift X M f := by ext; simp [← hg]

theorem product.hom_ext {α : Type u} [Fintype α] (X : α → CompHausFiltPseuNormGrp₁.{u})
    (M : CompHausFiltPseuNormGrp₁.{u}) (g₁ g₂ : M ⟶ product X)
    (h : ∀ i, g₁ ≫ product.π X i = g₂ ≫ product.π X i) : g₁ = g₂ :=
  by
  rw [product.lift_unique X M _ g₁ fun i => rfl, product.lift_unique X M _ g₂ fun i => rfl]
  simp [h]

end Products

end CompHausFiltPseuNormGrp₁

