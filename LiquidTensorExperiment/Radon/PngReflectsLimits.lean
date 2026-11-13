import LiquidTensorExperiment.PseudoNormedGroup.BoundedLimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory

#align_import Radon.png_reflects_limits

open CategoryTheory

open CategoryTheory.Limits

open scoped NNReal

universe u

variable {J : Type u} [SmallCategory J] {F : J ⥤ CompHausFiltPseuNormGrp₁.{u}} (C : Cone F)

namespace CompHaus

theorem comp_apply {X Y Z : CompHaus} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  rfl

theorem id_apply (X : CompHaus) (x : X) : (𝟙 X : X ⟶ X) x = x :=
  rfl

theorem continuous_of_isLimit (F : J ⥤ CompHaus.{u}) (C : Cone F) (hC : IsLimit C) (Y : Type u)
    [TopologicalSpace Y] (t : Y → C.pt) (h : ∀ j, Continuous (C.π.app j ∘ t)) : Continuous t :=
  by
  let CC := CompHaus_to_Top.map_cone C
  let hCC : is_limit CC := is_limit_of_preserves compHausToTop hC
  let E : cone (F ⋙ compHausToTop) := ⟨TopCat.of Y, fun j => ⟨_, h j⟩, _⟩
  · convert (hCC.lift E).Continuous
    ext1 a
    apply concrete.is_limit_ext _ hCC; intro j
    change _ = (hCC.lift E ≫ CC.π.app j) _
    rw [hCC.fac]; rfl
  · intro i j f; ext
    change _ = (C.π.app _ ≫ F.map _) _
    rw [C.w]
    rfl

theorem injective_of_isIso {X Y : CompHaus} (f : X ⟶ Y) [IsIso f] : Function.Injective f :=
  by
  intro x y h
  apply_fun inv f at h 
  simp only [← CompHaus.comp_apply, is_iso.hom_inv_id] at h 
  exact h

end CompHaus

namespace CompHausFiltPseuNormGrp₁

noncomputable section

/-- A choice of level for some element of an exhaustive
CompHausly filtered pseudo normed group. -/
def lvl (X : CompHausFiltPseuNormGrp₁) (x : X) : ℝ≥0 :=
  (X.exhaustive x).some

theorem lvl_spec (X : CompHausFiltPseuNormGrp₁) (x : X) :
    x ∈ PseudoNormedGroup.filtration X (X.lvl x) :=
  (X.exhaustive x).choose_spec

/-- Consider an element of an exhaustive CompHausly filtered pseudo normed group
as an element of its chosen level. -/
def asLvl (X : CompHausFiltPseuNormGrp₁) (x : X) : (level.obj (X.lvl x)).obj X :=
  ⟨x, X.lvl_spec x⟩

@[reassoc]
theorem level_cone_compatible (c₁ c₂ : ℝ≥0) (e : c₁ ⟶ c₂) (j) :
    (level.map e).app _ ≫ ((level.obj _).mapCone C).π.app j =
      ((level.obj _).mapCone C).π.app j ≫ (level.map e).app _ :=
  rfl

namespace LevelJointlyReflectsLimits

variable (hC : ∀ c : ℝ≥0, IsLimit ((level.obj c).mapCone C))

variable (S : Cone F)

/-- An auxiliary definition to be used in the constructions below. -/
def liftFun : S.pt → C.pt := fun s =>
  ((hC (S.pt.lvl s)).lift ((level.obj _).mapCone S) (S.pt.asLvl s)).1

theorem liftFun_map_zero : liftFun C hC S 0 = 0 :=
  by
  --dsimp [lift_fun],  -- slows down the proof.  changes to goal to
  -- ⊢ ((hC (S.X.lvl 0)).lift ((level.obj (S.X.lvl 0)).map_cone S)) (S.X.as_lvl 0) = 0
  let a := ((hC (S.X.lvl 0)).lift ((level.obj (S.X.lvl 0)).mapCone S)) (S.X.as_lvl 0)
  let b := C.X.as_lvl 0
  let c₁ := S.X.lvl 0
  let c₂ := C.X.lvl 0
  let c := c₁ ⊔ c₂
  let i1 : c₁ ⟶ c := hom_of_le le_sup_left
  let i2 : c₂ ⟶ c := hom_of_le le_sup_right
  let e1 := (level.map i1).app C.X
  let e2 := (level.map i2).app C.X
  change (e1 a).1 = (e2 b).1; congr 1
  apply concrete.is_limit_ext _ (hC c)
  intro j; dsimp only [e1, e2, a, b, ← CompHaus.comp_apply]
  simp only [category.assoc, level_cone_compatible, (hC (S.X.lvl 0)).fac_assoc]
  ext1
  change (S.π.app j) 0 = (C.π.app j) 0
  -- was `dsimp [CompHaus.comp_apply, level, as_lvl],`
  rw [(S.π.app j).map_zero, (C.π.app j).map_zero]

theorem fac_aux (c) (x) (j) :
    C.π.app j ((hC c).lift ((level.obj c).mapCone S) x).1 = S.π.app j x.1 :=
  by
  change (((hC c).lift ((level.obj c).mapCone S) ≫ (level.obj c).map (C.π.app j)) x).1 = _
  erw [(hC c).fac]
  rfl

theorem liftFun_map_add (x y) : liftFun C hC S (x + y) = liftFun C hC S x + liftFun C hC S y :=
  by
  --dsimp [lift_fun],  -- slows down the proof.  changes the goal to
  -- ⊢ ((hC (S.X.lvl 0)).lift ((level.obj (S.X.lvl 0)).map_cone S)) (S.X.as_lvl 0) = 0
  let Axy :=
    ((hC (S.X.lvl (x + y))).lift ((level.obj (S.X.lvl (x + y))).mapCone S)) (S.X.as_lvl (x + y))
  let Ax := ((hC (S.X.lvl x)).lift ((level.obj (S.X.lvl x)).mapCone S)) (S.X.as_lvl x)
  let Ay := ((hC (S.X.lvl y)).lift ((level.obj (S.X.lvl y)).mapCone S)) (S.X.as_lvl y)
  let cxy := S.X.lvl (x + y)
  let cx := S.X.lvl x
  let cy := S.X.lvl y
  let cc := cxy ⊔ (cx + cy)
  let AA : (level.obj (cx + cy)).obj C.X :=
    ⟨Ax.1 + Ay.1, PseudoNormedGroup.add_mem_filtration Ax.2 Ay.2⟩
  let i1 : cxy ⟶ cc := hom_of_le le_sup_left
  let i2 : cx + cy ⟶ cc := hom_of_le le_sup_right
  let e1 := (level.map i1).app C.X
  let e2 := (level.map i2).app C.X
  change (e1 Axy).1 = (e2 AA).1; congr 1
  apply concrete.is_limit_ext _ (hC cc); intro j
  --  dsimp only [e1, e2, Axy, ← CompHaus.comp_apply],
  simp only [e1, e2, Axy, ← CompHaus.comp_apply, category.assoc, level_cone_compatible,
    (hC (S.X.lvl (x + y))).fac_assoc]
  ext1
  dsimp [CompHaus.comp_apply, level, as_lvl, AA]
  rw [(S.π.app j).map_add, (C.π.app j).map_add]
  congr 1
  · dsimp only [Ax]
    erw [fac_aux]; rfl
  · dsimp only [Ay]
    erw [fac_aux]; rfl

/- Lemmas `lift_strict` and `lift_continuous` separately compile *much* faster than when they are
embedded in `CompHausFiltPseuNormGrp₁.level_jointly_reflects_limits.lift`. -/
theorem lift_strict (c : ℝ≥0) (x : S.pt) (hx : x ∈ PseudoNormedGroup.filtration S.pt c) :
    liftFun C hC S x ∈ PseudoNormedGroup.filtration C.pt c :=
  by
  let y : (level.obj c).obj S.X := ⟨x, hx⟩
  let z := (hC c).lift ((level.obj c).mapCone S) y
  let a := ((hC (S.X.lvl x)).lift ((level.obj (S.X.lvl x)).mapCone S)) (S.X.as_lvl x)
  suffices a.1 = z.1 by dsimp only [lift_fun]; rw [this]; exact z.2
  let cc := c ⊔ S.X.lvl x
  let i1 : c ⟶ cc := hom_of_le le_sup_left
  let i2 : S.X.lvl x ⟶ cc := hom_of_le le_sup_right
  suffices (level.map i1).app _ z = (level.map i2).app _ a by apply_fun fun e => e.1 at this ;
    exact this.symm
  dsimp [a, z]
  apply concrete.is_limit_ext _ (hC cc)
  intro j
  simp only [← CompHaus.comp_apply, category.assoc, level_cone_compatible, (hC c).fac_assoc,
    (hC (S.X.lvl x)).fac_assoc]
  ext; rfl

/- Lemmas `lift_strict` and `lift_continuous` separately compile *much* faster than when they are
embedded in `CompHausFiltPseuNormGrp₁.level_jointly_reflects_limits.lift`. -/
theorem lift_continuous (c : ℝ≥0) :
    Continuous (PseudoNormedGroup.level (liftFun C hC S) (lift_strict C hC S) c) :=
  by
  let t : _ → (level.obj c).obj C.X := _; change Continuous t
  suffices ∀ j, Continuous ((level.obj c).map (C.π.app j) ∘ t) by
    exact CompHaus.continuous_of_isLimit (F ⋙ level.obj c) ((level.obj c).mapCone C) (hC c) _ _ this
  intro j
  convert ((level.obj c).map (S.π.app j)).Continuous
  ext1 a
  let cc : ℝ≥0 := c ⊔ S.X.lvl a
  let i1 : c ⟶ cc := hom_of_le le_sup_left
  let i2 : S.X.lvl a ⟶ cc := hom_of_le le_sup_right
  apply_fun (level.map i1).app _; swap
  · intro x y h; ext1; apply_fun fun e => e.1 at h ; exact h
  simp only [← CompHaus.comp_apply]
  simp only [nat_trans.naturality]
  dsimp [t]
  generalize_proofs hh
  let q := ((level.map i1).app C.X) (PseudoNormedGroup.level (lift_fun C hC S) hh c a)
  have :
    q =
      ((level.map i2).app C.X)
        (((hC (S.X.lvl a)).lift ((level.obj (S.X.lvl a)).mapCone S)) (S.X.as_lvl a))
  rfl
  dsimp only [q] at this 
  simp only [this, ← CompHaus.comp_apply, category.assoc]
  erw [level_cone_compatible]
  rw [(hC (S.X.lvl a)).fac_assoc]
  ext; rfl

/-- An auxiliary definition to be used in the constructions below. -/
def lift : S.pt ⟶ C.pt where
  toFun := liftFun _ hC _
  map_zero' := liftFun_map_zero _ _ _
  map_add' := liftFun_map_add _ _ _
  strict' := lift_strict _ _ _
  continuous' := lift_continuous _ _ _

end LevelJointlyReflectsLimits

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr subtype.val _]] -/
/-- If `C` is a cone taking values in `CompHausFiltPseuNormGrp₁` such that
the restriction to all the levels is a limit cone, then `C` is a limit cone.
-/
def levelJointlyReflectsLimits (hC : ∀ c : ℝ≥0, IsLimit ((level.obj c).mapCone C)) : IsLimit C
    where
  lift S := LevelJointlyReflectsLimits.lift _ hC _
  fac := by
    intro S j
    ext1 t
    -- `show` replaces the slower
    -- `dsimp [level_jointly_reflects_limits.lift, level_jointly_reflects_limits.lift_fun],`
    show (C.π.app j) _ = _
    erw [level_jointly_reflects_limits.fac_aux]; rfl
  uniq := by
    intro S m hm
    ext1 t
    --  `dsimp [level_jointly_reflects_limits.lift, level_jointly_reflects_limits.lift_fun],`
    --  commented as it slows down the proof.  changes the goal to
    -- ⊢ m t = ((hC (S.X.lvl t)).lift ((level.obj (S.X.lvl t)).map_cone S)) (S.X.as_lvl t)
    let a := ((hC (S.X.lvl t)).lift ((level.obj (S.X.lvl t)).mapCone S)) (S.X.as_lvl t)
    let c := C.X.lvl (m t)
    let d := c ⊔ S.X.lvl t
    let i1 : c ⟶ d := hom_of_le le_sup_left
    let i2 : S.X.lvl t ⟶ d := hom_of_le le_sup_right
    change ((level.map i1).app C.X (C.X.as_lvl (m t))).1 = ((level.map i2).app C.X a).1
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr subtype.val _]]"
    apply concrete.is_limit_ext _ (hC d); intro j
    specialize hm j
    ext1
    show (C.π.app j) (m t) = (C.π.app j) _
    --  `show` replaces a slow `dsimp [level, as_lvl, a]`
    erw [level_jointly_reflects_limits.fac_aux]
    rw [← hm]; rfl

/-- Create a moprhism in `CompHausFiltPseuNormGrp₁` levelwise. -/
@[simps]
def createHomFromLevel {X Y : CompHausFiltPseuNormGrp₁}
    (E : ∀ c, (level.obj c).obj X ⟶ (level.obj c).obj Y) (hE0 : (E (X.lvl 0) (X.asLvl 0)).1 = 0)
    (hEa : ∀ a b : X, (E _ (X.asLvl (a + b))).1 = (E _ (X.asLvl a)).1 + (E _ (X.asLvl b)).1)
    (hE : ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂), E _ ≫ (level.map i).app _ = (level.map i).app _ ≫ E _) :
    X ⟶ Y where
  toFun x := (E _ <| X.asLvl x).1
  map_zero' := hE0
  map_add' := hEa
  strict' := by
    intro c x hx
    let y : (level.obj c).obj X := ⟨x, hx⟩
    suffices ((E (X.lvl x)) (X.as_lvl x)).val = (E _ y).1 by rw [this]; exact (E _ y).2
    let d := c ⊔ X.lvl x
    let i1 : c ⟶ d := hom_of_le le_sup_left
    let i2 : X.lvl x ⟶ d := hom_of_le le_sup_right
    change ((level.map i2).app Y ((E (X.lvl x)) (X.as_lvl x))).1 = ((level.map i1).app _ _).1
    congr 1
    simp only [← CompHaus.comp_apply, hE]
    rfl
  continuous' := by
    intro c
    let t := _; change Continuous t
    convert (E c).Continuous
    ext a
    let d := X.lvl a ⊔ c
    let i1 : X.lvl a ⟶ d := hom_of_le le_sup_left
    let i2 : c ⟶ d := hom_of_le le_sup_right
    change ((level.map i1).app _ (E _ (X.as_lvl a))).1 = ((level.map i2).app _ (E _ a)).1
    simp only [← CompHaus.comp_apply, hE]; rfl

theorem create_iso_from_level_compat_aux {X Y : CompHausFiltPseuNormGrp₁}
    (E : ∀ c, (level.obj c).obj X ≅ (level.obj c).obj Y)
    (hE :
      ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
        (E _).Hom ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).Hom) :
    ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
      (E _).inv ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).inv :=
  by intro c₁ c₂ i; rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, hE]

theorem create_iso_from_level_zero_aux {X Y : CompHausFiltPseuNormGrp₁}
    (E : ∀ c, (level.obj c).obj X ≅ (level.obj c).obj Y)
    (hE0 : ((E (X.lvl 0)).Hom (X.asLvl 0)).1 = 0)
    (hE :
      ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
        (E _).Hom ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).Hom) :
    ((E (Y.lvl 0)).inv (Y.asLvl 0)).1 = 0 :=
  by
  let x := (E (Y.lvl 0)).inv (Y.as_lvl 0)
  let c := Y.lvl 0 ⊔ X.lvl 0
  let i1 : Y.lvl 0 ⟶ c := hom_of_le le_sup_left
  let i2 : X.lvl 0 ⟶ c := hom_of_le le_sup_right
  change ((level.map i2).app _ _).val = ((level.map i1).app _ (Y.as_lvl 0)).val at hE0 
  have hE0' := hE0
  replace hE0 :
    ((level.map i2).app Y) ((E (X.lvl 0)).Hom (X.as_lvl 0)) = ((level.map i1).app Y) (Y.as_lvl 0)
  · ext1; exact hE0
  apply_fun (E c).inv at hE0 
  simp only [← CompHaus.comp_apply, hE, category.assoc, iso.hom_inv_id] at hE0 
  apply_fun fun e => e.val at hE0 
  change ((level.map i1).app _ x).val = ((level.map i2).app _ (X.as_lvl 0)).val
  dsimp only [x, ← CompHaus.comp_apply]
  rw [create_iso_from_level_compat_aux, CompHaus.comp_apply]
  exact hE0.symm
  assumption

/-- An auxiliary definition to be used in the constructions below. -/
def asLvlAdd (X : CompHausFiltPseuNormGrp₁) (a b : X) : (level.obj (X.lvl a + X.lvl b)).obj X :=
  ⟨a + b, PseudoNormedGroup.add_mem_filtration (X.lvl_spec a) (X.lvl_spec b)⟩

theorem create_iso_from_level_add_aux_aux {X Y : CompHausFiltPseuNormGrp₁}
    (E : ∀ c, (level.obj c).obj X ≅ (level.obj c).obj Y) :
    ∀ (a b : X) (c : ℝ≥0) (h1 : X.lvl (a + b) ⟶ c) (h2 : X.lvl a + X.lvl b ⟶ c),
      (E c).Hom ((level.map h1).app _ <| X.asLvl _) =
        (E c).Hom ((level.map h2).app _ <| X.asLvlAdd _ _) :=
  by intros; congr

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr + »(_, _)]] -/
theorem create_iso_from_level_add_aux {X Y : CompHausFiltPseuNormGrp₁}
    (E : ∀ c, (level.obj c).obj X ≅ (level.obj c).obj Y)
    (hEa :
      ∀ a b : X,
        ((E _).Hom (X.asLvl (a + b))).1 = ((E _).Hom (X.asLvl a)).1 + ((E _).Hom (X.asLvl b)).1)
    (hE :
      ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
        (E _).Hom ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).Hom) :
    ∀ a b : Y,
      ((E _).inv (Y.asLvl (a + b))).1 = ((E _).inv (Y.asLvl a)).1 + ((E _).inv (Y.asLvl b)).1 :=
  by
  intro a b
  let a' := ((E (Y.lvl a)).inv (Y.as_lvl a)).val
  let b' := ((E (Y.lvl b)).inv (Y.as_lvl b)).val
  let ab' := ((E (Y.lvl (a + b))).inv (Y.as_lvl (a + b))).val
  let c₁ := Y.lvl (a + b)
  let c₂ := X.lvl a' + X.lvl b'
  let c := c₁ ⊔ c₂
  let i1 : c₁ ⟶ c := hom_of_le le_sup_left
  let i2 : c₂ ⟶ c := hom_of_le le_sup_right
  change ((level.map i1).app _ _).val = ((level.map i2).app _ <| X.as_lvl_add a' b').val
  congr 1
  rw [← CompHaus.comp_apply, create_iso_from_level_compat_aux _ hE]
  apply_fun (E _).Hom
  swap; · apply CompHaus.injective_of_isIso
  simp only [← CompHaus.comp_apply, category.assoc, iso.inv_hom_id]
  simp only [CompHaus.comp_apply, CompHaus.id_apply]
  let d := X.lvl (a' + b') ⊔ c
  let j1 : X.lvl (a' + b') ⟶ d := hom_of_le le_sup_left
  let j2 : c ⟶ d := hom_of_le le_sup_right
  apply_fun (level.map j2).app _
  swap; · intro x y h; ext1; apply_fun fun e => e.val at h ; exact h
  simp only [← CompHaus.comp_apply, category.assoc, hE, ← nat_trans.comp_app]
  rw [← category.assoc, ← nat_trans.comp_app, ← functor.map_comp, ← functor.map_comp,
    CompHaus.comp_apply]
  erw [create_iso_from_level_add_aux_aux]
  any_goals assumption
  swap; refine' i2 ≫ j2
  simp only [functor.map_comp, nat_trans.comp_app, CompHaus.comp_apply]
  let s := _; change _ = (E d).Hom s
  have : s = (level.map j1).app _ (X.as_lvl (a' + b')) := by ext; rfl
  rw [this]; clear this
  simp_rw [← CompHaus.comp_apply, ← hE, CompHaus.comp_apply]
  ext1
  --  `show` replaces the `slower `dsimp [level]`
  show ↑(Y.as_lvl _) = ↑((E (X.lvl (a' + b'))).Hom (X.as_lvl (a' + b')))
  --  show replaces the slower `conv_lhs { dsimp [as_lvl] }`
  show a + b = _
  rw [← Subtype.val_eq_coe, hEa a' b']
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr + »(_, _)]]"
  · let d₁ := Y.lvl a
    let d₂ := X.lvl a'
    let d := d₁ ⊔ d₂
    let e₁ : d₁ ⟶ d := hom_of_le le_sup_left
    let e₂ : d₂ ⟶ d := hom_of_le le_sup_right
    change
      ((level.map e₁).app _ (Y.as_lvl a)).val =
        ((level.map e₂).app _ ((E (X.lvl a')).Hom (X.as_lvl a'))).val
    rw [← CompHaus.comp_apply, hE]
    congr 1
    apply_fun (E d).inv
    swap; · apply CompHaus.injective_of_isIso
    simp_rw [← CompHaus.comp_apply, category.assoc, iso.hom_inv_id]
    rw [← create_iso_from_level_compat_aux]
    ext; rfl
    assumption
  · let d₁ := Y.lvl b
    let d₂ := X.lvl b'
    let d := d₁ ⊔ d₂
    let e₁ : d₁ ⟶ d := hom_of_le le_sup_left
    let e₂ : d₂ ⟶ d := hom_of_le le_sup_right
    change
      ((level.map e₁).app _ (Y.as_lvl b)).val =
        ((level.map e₂).app _ ((E (X.lvl b')).Hom (X.as_lvl b'))).val
    rw [← CompHaus.comp_apply, hE]
    congr 1
    apply_fun (E d).inv
    swap; · apply CompHaus.injective_of_isIso
    simp_rw [← CompHaus.comp_apply, category.assoc, iso.hom_inv_id]
    rw [← create_iso_from_level_compat_aux]
    ext; rfl
    assumption

/-- Create an isomoprhism in `CompHausFiltPseuNormGrp₁` levelwise. -/
def createIsoFromLevel {X Y : CompHausFiltPseuNormGrp₁.{u}}
    (E : ∀ c, (level.obj c).obj X ≅ (level.obj c).obj Y)
    (hE0 : ((E (X.lvl 0)).Hom (X.asLvl 0)).1 = 0)
    (hEa :
      ∀ a b : X,
        ((E _).Hom (X.asLvl (a + b))).1 = ((E _).Hom (X.asLvl a)).1 + ((E _).Hom (X.asLvl b)).1)
    (hE :
      ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
        (E _).Hom ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).Hom) :
    X ≅ Y where
  Hom := createHomFromLevel (fun c => (E c).Hom) hE0 hEa hE
  inv :=
    createHomFromLevel (fun c => (E c).inv) (create_iso_from_level_zero_aux _ hE0 hE)
      (create_iso_from_level_add_aux _ hEa hE) (create_iso_from_level_compat_aux _ hE)
  hom_inv_id' := by
    ext1 t
    simp only [comp_apply, create_hom_from_level_to_fun, Subtype.val_eq_coe, id_apply]
    let s := ((E (X.lvl t)).Hom (X.as_lvl t)).val
    let c₁ := Y.lvl s
    let c₂ := X.lvl t
    let c := c₁ ⊔ c₂
    let i1 : c₁ ⟶ c := hom_of_le le_sup_left
    let i2 : c₂ ⟶ c := hom_of_le le_sup_right
    change ((level.map i1).app _ _).val = ((level.map i2).app _ (X.as_lvl t)).val
    simp only [← CompHaus.comp_apply]
    rw [create_iso_from_level_compat_aux]
    any_goals assumption
    simp only [CompHaus.comp_apply]
    congr 1
    apply_fun (E c).Hom
    swap
    · intro x y h
      apply_fun (E c).inv at h 
      simp only [← CompHaus.comp_apply, iso.hom_inv_id] at h 
      exact h
    rw [← CompHaus.comp_apply, iso.inv_hom_id, CompHaus.id_apply]
    rw [← CompHaus.comp_apply, ← hE]
    rfl
  inv_hom_id' := by
    ext1 t
    simp only [comp_apply, create_hom_from_level_to_fun, Subtype.val_eq_coe, id_apply]
    let s := ((E (Y.lvl t)).inv (Y.as_lvl t)).val
    let c₁ := X.lvl s
    let c₂ := Y.lvl t
    let c := c₁ ⊔ c₂
    let i1 : c₁ ⟶ c := hom_of_le le_sup_left
    let i2 : c₂ ⟶ c := hom_of_le le_sup_right
    change ((level.map i1).app _ _).val = ((level.map i2).app _ (Y.as_lvl t)).val
    simp only [← CompHaus.comp_apply]
    rw [hE]
    simp only [CompHaus.comp_apply]
    congr 1
    apply_fun (E c).inv
    swap
    · intro x y h
      apply_fun (E c).Hom at h 
      simp only [← CompHaus.comp_apply, iso.inv_hom_id] at h 
      exact h
    rw [← CompHaus.comp_apply, iso.hom_inv_id, CompHaus.id_apply]
    rw [← CompHaus.comp_apply, ← create_iso_from_level_compat_aux]
    any_goals assumption
    rfl

theorem level_createIsoFromLevel {X Y : CompHausFiltPseuNormGrp₁}
    (E : ∀ c, (level.obj c).obj X ≅ (level.obj c).obj Y)
    (hE0 : ((E (X.lvl 0)).Hom (X.asLvl 0)).1 = 0)
    (hEa :
      ∀ a b : X,
        ((E _).Hom (X.asLvl (a + b))).1 = ((E _).Hom (X.asLvl a)).1 + ((E _).Hom (X.asLvl b)).1)
    (hE :
      ∀ (c₁ c₂ : ℝ≥0) (i : c₁ ⟶ c₂),
        (E _).Hom ≫ (level.map i).app _ = (level.map i).app _ ≫ (E _).Hom)
    (c) : (level.obj c).map (createIsoFromLevel E hE0 hEa hE).Hom = (E _).Hom :=
  by
  ext t
  --  `dsimp [create_iso_from_level, create_hom_from_level, level],` -- changes the goal to
  -- ⊢ ↑(⇑((E (X.lvl ↑t)).hom) (X.as_lvl ↑t)) = ↑(⇑((E c).hom) t)
  -- but is not needed and slows down the proof.
  let d := X.lvl t.1 ⊔ c
  let i1 : X.lvl t.1 ⟶ d := hom_of_le le_sup_left
  let i2 : c ⟶ d := hom_of_le le_sup_right
  change ((level.map i1).app _ _).val = ((level.map i2).app _ _).val
  congr 1
  simp only [← CompHaus.comp_apply, hE]; ext; rfl

theorem level_jointly_faithful {X Y : CompHausFiltPseuNormGrp₁} (f g : X ⟶ Y)
    (h : ∀ c, (level.obj c).map f = (level.obj c).map g) : f = g :=
  by
  ext t
  specialize h (X.lvl t)
  apply_fun fun e => (e (X.as_lvl t)).1 at h 
  exact h

end CompHausFiltPseuNormGrp₁

