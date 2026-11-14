import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitLimits
import Mathlib.Topology.Category.Compactum

#align_import pseudo_normed_group.bounded_limits

open CategoryTheory

open CategoryTheory.Limits

universe u

variable {J : Type u} [SmallCategory J]

structure PseuNormGrp₁ where
  carrier : Type u
  [str : PseudoNormedGroup carrier]
  exhaustive' : ∀ x : carrier, ∃ c : NNReal, x ∈ PseudoNormedGroup.filtration carrier c

namespace PseuNormGrp₁

instance : CoeSort PseuNormGrp₁.{u} (Type u) :=
  ⟨Carrier⟩

instance (M : PseuNormGrp₁.{u}) : PseudoNormedGroup M :=
  M.str

theorem exhaustive (M : PseuNormGrp₁) (x : M) : ∃ c, x ∈ PseudoNormedGroup.filtration M c :=
  M.exhaustive' x

instance : Category PseuNormGrp₁.{u}
    where
  Hom A B := StrictPseudoNormedGroupHom A B
  id A := StrictPseudoNormedGroupHom.id A
  comp A B C f g := f.comp g

@[simp]
theorem id_apply (M : PseuNormGrp₁) (x : M) : (𝟙 M : M ⟶ M) x = x :=
  rfl

@[simp]
theorem comp_apply {A B C : PseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) :=
  rfl

def toAb : PseuNormGrp₁.{u} ⥤ Ab.{u}
    where
  obj M := AddCommGroupCat.of M
  map M N f := f.toAddMonoidHom

variable {K : J ⥤ PseuNormGrp₁.{u}}

variable (C : Limits.LimitCone (K ⋙ toAb))

def boundedElements : AddSubgroup C.Cone.pt
    where
  carrier := {x | ∃ c, ∀ j, C.Cone.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c}
  zero_mem' := ⟨0, fun j => by simp; apply PseudoNormedGroup.zero_mem_filtration⟩
  add_mem' a b ha hb := by
    obtain ⟨c, hc⟩ := ha
    obtain ⟨d, hd⟩ := hb
    use c + d
    intro j
    simp
    apply PseudoNormedGroup.add_mem_filtration
    apply hc
    apply hd
  neg_mem' a ha := by
    obtain ⟨c, hc⟩ := ha
    use c
    intro j
    simp
    apply PseudoNormedGroup.neg_mem_filtration
    apply hc

def boundedElements.filt (c : NNReal) : Set C.Cone.pt :=
  {x | ∀ j, C.Cone.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c}

def boundedElements.filtIncl (c : NNReal) : boundedElements.filt C c → boundedElements C := fun x =>
  ⟨x, c, x.2⟩

def boundedElements.filtration (c : NNReal) : Set (boundedElements C) :=
  Set.range (boundedElements.filtIncl _ c)

def boundedConePoint : PseuNormGrp₁
    where
  carrier := boundedElements C
  str :=
    { filtration' := boundedElements.filtration _
      filtration_mono' := by
        intro c₁ c₂ h x hx
        obtain ⟨t, rfl⟩ := hx; refine' ⟨⟨t, _⟩, rfl⟩; intro i
        apply PseudoNormedGroup.filtration_mono h; apply t.2
      zero_mem_filtration' := by
        intro c; refine' ⟨⟨0, fun i => _⟩, rfl⟩; simp
        apply PseudoNormedGroup.zero_mem_filtration
      neg_mem_filtration' := by
        intro c x hx
        obtain ⟨t, rfl⟩ := hx; refine' ⟨⟨-t, fun i => _⟩, rfl⟩; simp
        apply PseudoNormedGroup.neg_mem_filtration; apply t.2
      add_mem_filtration' := by
        intro c₁ c₂ x₁ x₂ h₁ h₂
        obtain ⟨t₁, rfl⟩ := h₁; obtain ⟨t₂, rfl⟩ := h₂
        refine' ⟨⟨t₁ + t₂, fun i => _⟩, rfl⟩; simp
        apply PseudoNormedGroup.add_mem_filtration; apply t₁.2; apply t₂.2 }
  exhaustive' := by
    intro m
    obtain ⟨c, hc⟩ := m.2
    refine' ⟨c, ⟨m.1, hc⟩, by ext; rfl⟩

def boundedCone : Cone K where
  pt := boundedConePoint C
  π :=
    { app := fun j =>
        { toFun := fun x => C.Cone.π.app _ x.1
          map_zero' := by simp
          map_add' := fun x y => by simp
          strict' := by
            rintro c x ⟨x, rfl⟩
            apply x.2 }
      naturality := by
        intro i j f
        ext
        dsimp
        rw [← C.cone.w f]
        rfl }

def boundedConeLift (S : Cone K) : S.pt ⟶ boundedConePoint C
    where
  toFun x :=
    ⟨C.2.lift (toAb.mapCone S) x, by
      obtain ⟨c, hc⟩ := S.X.exhaustive x
      use c
      intro j
      rw [← Ab.comp_apply, C.2.fac]
      apply (S.π.app j).Strict
      exact hc⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  strict' := by
    intro c x hx
    refine' ⟨⟨_, fun j => _⟩, rfl⟩
    erw [← Ab.comp_apply, C.2.fac]
    apply (S.π.app j).Strict
    exact hx

def boundedConeIsLimit : IsLimit (boundedCone C)
    where
  lift S := boundedConeLift C S
  fac := by
    intro S j
    ext
    dsimp [PseuNormGrp₁.boundedConeLift, bounded_cone]
    rw [← Ab.comp_apply, C.2.fac]
    rfl
  uniq := by
    intro S m hm
    ext
    dsimp [PseuNormGrp₁.boundedConeLift, bounded_cone]
    apply Ab.is_limit_ext
    intro j
    rw [← Ab.comp_apply, C.2.fac]
    dsimp
    rw [← hm]
    rfl

instance : HasLimits PseuNormGrp₁ := by
  constructor; intro J hJ; constructor; intro K
  exact HasLimit.mk ⟨_, bounded_cone_is_limit ⟨_, limit.isLimit _⟩⟩

open PseudoNormedGroup

theorem mem_filtration_iff_of_isLimit (C : Cone K) (hC : IsLimit C) (x : C.pt) (c : NNReal) :
    x ∈ PseudoNormedGroup.filtration C.pt c ↔
      ∀ j : J, C.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c :=
  by
  constructor
  · intro h j
    exact (C.π.app j).Strict h
  · intro h
    let E := bounded_cone ⟨_, Ab.explicitLimitConeIsLimit.{u, u} _⟩
    let e : C ≅ E := hC.uniqueUpToIso (bounded_cone_is_limit _)
    let eX : C.X ≅ E.X := (Cones.forget _).mapIso e
    let w := eX.hom x
    have hw : ∀ j, E.π.app j w ∈ filtration (K.obj j) c :=
      by
      intro j
      dsimp only [w]
      change (eX.hom ≫ E.π.app _) _ ∈ _
      dsimp only [eX, Functor.mapIso, Cones.forget]
      convert h j
      simp
    suffices w ∈ filtration E.X c by
      convert eX.inv.strict this
      change _ = (eX.hom ≫ eX.inv) x
      rw [Iso.hom_inv_id]
      rfl
    refine' ⟨⟨_, hw⟩, rfl⟩

@[simps]
def StrictPseudoNormedGroupHom.level {M N : Type _} [PseudoNormedGroup M] [PseudoNormedGroup N]
    (f : StrictPseudoNormedGroupHom M N) (c) : filtration M c → filtration N c := fun x =>
  ⟨f x, f.Strict x.2⟩

@[simp]
theorem StrictPseudoNormedGroupHom.level_id (M : Type _) [PseudoNormedGroup M] (c) :
    (StrictPseudoNormedGroupHom.id M).level c = id := by ext; rfl

@[simp]
theorem StrictPseudoNormedGroupHom.level_comp {M N L : Type _} [PseudoNormedGroup M]
    [PseudoNormedGroup N] [PseudoNormedGroup L] (f : StrictPseudoNormedGroupHom M N)
    (g : StrictPseudoNormedGroupHom N L) (c) : (f.comp g).level c = g.level c ∘ f.level c := by ext;
  rfl

@[simps]
def level : NNReal ⥤ PseuNormGrp₁.{u} ⥤ Type u
    where
  obj c :=
    { obj := fun M => filtration M c
      map := fun X Y f => f.level _
      map_id := fun M => StrictPseudoNormedGroupHom.level_id M _
      map_comp := fun M N L f g => f.level_comp g c }
  map c₁ c₂ h := { app := fun M => PseudoNormedGroup.castLe' h.le }

theorem level_map {X Y : PseuNormGrp₁} (f : X ⟶ Y) (c) : (level.obj c).map f = f.level _ :=
  rfl

theorem level_map' {X Y : PseuNormGrp₁} (f : X ⟶ Y) (c) :
    (level.obj c).map f = PseudoNormedGroup.level f f.Strict c :=
  rfl

def levelConeIsoHom (c) (t : (level.obj c).obj (boundedConePoint C)) : (K ⋙ level.obj c).sections
    where
  val j :=
    { val := C.Cone.π.app j t.1.1
      property := by
        obtain ⟨w, hw⟩ := t.2
        apply_fun fun e => e.val at hw 
        rw [← hw]
        apply w.2 }
  property := by
    intro i j f
    ext
    dsimp
    rw [← C.cone.w f]
    rfl

def levelConeIsoInv (c) (t : (K ⋙ level.obj c).sections) : (level.obj c).obj (boundedConePoint C)
    where
  val :=
    { val :=
        C.2.lift (Ab.explicitLimitCone.{u, u} _)
          ⟨fun j => (t.1 j).1, by
            intro i j f
            dsimp
            change _ = (t.val _).val
            rw [← t.2 f]
            rfl⟩
      property := by
        use c
        intro j
        rw [← Ab.comp_apply, C.2.fac]
        dsimp [Ab.explicitLimitCone]
        apply (t.1 j).2 }
  property := by
    refine' ⟨⟨_, _⟩, rfl⟩
    intro j
    dsimp
    rw [← Ab.comp_apply, C.2.fac]
    dsimp [Ab.explicitLimitCone]
    apply (t.1 j).2

def levelConeIso (c) : (level.obj c).mapCone (boundedCone C) ≅ Types.limitCone.{u, u} _ :=
  Cones.ext
    { hom := levelConeIsoHom _ _
      inv := levelConeIsoInv _ _
      hom_inv_id := by
        ext
        dsimp [PseuNormGrp₁.levelConeIsoInv, PseuNormGrp₁.levelConeIsoHom]
        apply Ab.is_limit_ext
        intro j
        rw [← Ab.comp_apply, C.2.fac]
        rfl
      inv_hom_id := by
        ext
        dsimp [PseuNormGrp₁.levelConeIsoInv, PseuNormGrp₁.levelConeIsoHom]
        rw [← Ab.comp_apply, C.2.fac]
        rfl }
    (by
      intro j
      ext
      rfl)

instance preservesLimitsLevelObj (c) : PreservesLimits (level.obj c) :=
  by
  constructor; intro J hJ; constructor; intro K
  apply
    CategoryTheory.Limits.preservesLimitOfPreservesLimitCone
      (bounded_cone_is_limit ⟨_, Ab.explicitLimitConeIsLimit _⟩)
  apply IsLimit.ofIsoLimit (Types.limitConeIsLimit _) (PseuNormGrp₁.levelConeIso _ _).symm

def negNatTrans (c) : level.obj c ⟶ level.obj c
    where
  app X := PseudoNormedGroup.neg'
  naturality := by
    intro A B f
    ext
    dsimp [level, neg']
    simp

end PseuNormGrp₁

namespace CompHausFiltPseuNormGrp₁

@[simp]
theorem id_apply {A : CompHausFiltPseuNormGrp₁} (a : A) : (𝟙 A : A ⟶ A) a = a :=
  rfl

@[simp]
theorem comp_apply {A B C : CompHausFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) :=
  rfl

def toPNG₁ : CompHausFiltPseuNormGrp₁.{u} ⥤ PseuNormGrp₁.{u}
    where
  obj M :=
    { carrier := M
      exhaustive' := M.exhaustive }
  map X Y f := { f.toAddMonoidHom with strict' := fun c x h => f.Strict h }

instance : Faithful toPNG₁.{u} :=
  Faithful.mk <| by
    intro X Y f g h
    ext
    apply_fun fun e => e x at h 
    exact h

variable {K : J ⥤ CompHausFiltPseuNormGrp₁.{u}}

variable (C : Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb))

def filtrationEquiv (c : NNReal) :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c ≃
      (CompHaus.limitCone.{u, u} (K ⋙ level.obj c)).pt :=
  ((Cones.forget _).mapIso (PseuNormGrp₁.levelConeIso C c)).toEquiv

instance (c) :
    TopologicalSpace (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  TopologicalSpace.induced (filtrationEquiv C c) inferInstance

def filtrationHomeo (c : NNReal) :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c ≃ₜ
      (CompHaus.limitCone.{u, u} (K ⋙ level.obj c)).pt :=
  Homeomorph.homeomorphOfContinuousOpen (filtrationEquiv _ _) continuous_induced_dom
    (by
      intro U hU
      have : Inducing (filtration_equiv C c) := ⟨rfl⟩
      rw [this.isOpen_iff] at hU 
      obtain ⟨U, hU, rfl⟩ := hU
      simpa)

instance (c) : T2Space (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  (filtrationHomeo C c).symm.T2Space

instance (c) : CompactSpace (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  (filtrationHomeo C c).symm.CompactSpace

/-
instance (c) : totally_disconnected_space
  (pseudo_normed_group.filtration (PseuNormGrp₁.bounded_cone_point C) c) :=
(filtration_homeo C c).symm.totally_disconnected_space
-/
def levelπ (j c) :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c →
      PseudoNormedGroup.filtration (K.obj j) c :=
  (PseuNormGrp₁.level.obj c).map ((PseuNormGrp₁.boundedCone C).π.app j)

theorem levelπ_continuous (j c) : Continuous (levelπ C j c) :=
  by
  have : level_π C j c ∘ (filtration_homeo C c).symm = (CompHaus.limitCone.{u, u} _).π.app j :=
    by
    ext
    change (C.is_limit.lift _ ≫ C.cone.π.app j) _ = _
    rw [C.is_limit.fac]
    rfl
  suffices Continuous (level_π C j c ∘ (filtration_homeo C c).symm) by simpa using this
  rw [this]
  continuity

theorem boundedConePoint_continuous_add'_aux {J : Type u} [SmallCategory J]
    {K : J ⥤ CompHausFiltPseuNormGrp₁}
    (C : CategoryTheory.Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb)) :
    ∀ c₁ c₂ : NNReal,
      Continuous
        (PseudoNormedGroup.add' :
          PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ ×
              PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂ →
            PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) (c₁ + c₂)) :=
  by
  intro c₁ c₂
  let g :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ ×
        PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂ →
      PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) (c₁ + c₂) :=
    PseudoNormedGroup.add'
  change Continuous g
  suffices Continuous (filtration_homeo C _ ∘ g) by simpa using this
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  let e := PseudoNormedGroup.add' ∘ Prod.map (level_π C j c₁) (level_π C j c₂)
  have he : Continuous e := by
    apply Continuous.comp
    apply ComphausFilteredPseudoNormedGroup.continuous_add'
    apply Continuous.prod_map
    apply level_π_continuous
    apply level_π_continuous
  convert he
  ext
  dsimp
  simpa

theorem boundedConePoint_continuous_neg'_aux {J : Type u} [SmallCategory J]
    {K : J ⥤ CompHausFiltPseuNormGrp₁}
    (C : CategoryTheory.Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb)) :
    ∀ c : NNReal,
      Continuous
        (PseudoNormedGroup.neg' :
          PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c →
            PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  by
  intro c
  let g :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c →
      PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c :=
    PseudoNormedGroup.neg'
  change Continuous g
  suffices Continuous (filtration_homeo C c ∘ g) by simpa using this
  apply Continuous.subtype_mk
  apply continuous_pi
  dsimp [g]
  intro j
  let e := PseudoNormedGroup.neg' ∘ level_π C j c
  have he : Continuous e := by
    apply Continuous.comp
    apply ComphausFilteredPseudoNormedGroup.continuous_neg'
    apply level_π_continuous
  convert he
  ext
  dsimp
  simpa

theorem boundedConePoint_continuous_cast_le_aux {J : Type u} [SmallCategory J]
    {K : J ⥤ CompHausFiltPseuNormGrp₁}
    (C : CategoryTheory.Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb)) :
    ∀ (c₁ c₂ : NNReal) (h : c₁ ≤ c₂),
      Continuous
        (PseudoNormedGroup.castLe' h :
          PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ →
            PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂) :=
  by
  intro c₁ c₂ h
  let g :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ →
      PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂ :=
    PseudoNormedGroup.castLe' h
  change Continuous g
  suffices Continuous (filtration_homeo C _ ∘ g) by simpa using this
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  dsimp [g]
  let e := PseudoNormedGroup.castLe' h ∘ level_π C j c₁
  have he : Continuous e := by
    apply Continuous.comp
    haveI : Fact (c₁ ≤ c₂) := ⟨h⟩
    apply ComphausFilteredPseudoNormedGroup.continuous_castLe
    apply level_π_continuous
  exact he

def boundedConePoint : CompHausFiltPseuNormGrp₁
    where
  M := PseuNormGrp₁.boundedConePoint C
  str :=
    {
      (inferInstance :
        PseudoNormedGroup
          (PseuNormGrp₁.boundedConePoint
            C)) with
      continuous_add' := boundedConePoint_continuous_add'_aux _
      continuous_neg' := boundedConePoint_continuous_neg'_aux _
      continuous_castLe := fun _ _ h => boundedConePoint_continuous_cast_le_aux _ _ _ h.out }
  exhaustive' := (PseuNormGrp₁.boundedConePoint C).exhaustive

def boundedCone : Cone K where
  pt := boundedConePoint C
  π :=
    { app := fun j =>
        { (PseuNormGrp₁.boundedCone C).π.app j with
          continuous' := fun c => levelπ_continuous _ _ _ }
      naturality := by
        intro i j f
        ext
        dsimp
        rw [← (PseuNormGrp₁.boundedCone C).w f]
        rfl }

def boundedConeIsLimit : IsLimit (boundedCone C)
    where
  lift S :=
    { (PseuNormGrp₁.boundedConeIsLimit C).lift (toPNG₁.mapCone S) with
      continuous' := by
        intro c
        let t :
          PseudoNormedGroup.filtration S.X c → PseudoNormedGroup.filtration (bounded_cone C).pt c :=
          ((PseuNormGrp₁.boundedConeIsLimit C).lift (to_PNG₁.mapCone S)).level _
        change Continuous t
        suffices Continuous (filtration_homeo C c ∘ t) by simpa using this
        have :
          ⇑(filtration_homeo C c) ∘ t =
            (CompHaus.limitConeIsLimit.{u, u} _).lift ((level.obj c).mapCone S) :=
          by
          ext
          change (C.is_limit.lift _ ≫ C.cone.π.app _) _ = _
          rw [C.is_limit.fac]; rfl
        rw [this]
        continuity }
  fac := by
    intro S j
    ext
    dsimp [bounded_cone]
    change
      ((PseuNormGrp₁.boundedConeIsLimit C).lift (to_PNG₁.mapCone S) ≫
            (PseuNormGrp₁.boundedCone C).π.app j)
          _ =
        _
    rw [(PseuNormGrp₁.boundedConeIsLimit C).fac]
    rfl
  uniq := by
    intro S m hm
    ext
    dsimp
    have : to_PNG₁.map m = (PseuNormGrp₁.boundedConeIsLimit C).lift (to_PNG₁.mapCone S) :=
      by
      apply (PseuNormGrp₁.boundedConeIsLimit C).uniq (to_PNG₁.mapCone S)
      intro j
      ext t
      specialize hm j
      apply_fun fun e => e t at hm 
      exact hm
    rw [← this]
    rfl

instance : PreservesLimit K toPNG₁ :=
  by
  apply CategoryTheory.Limits.preservesLimitOfPreservesLimitCone
  rotate_left 2
  exact bounded_cone ⟨_, Ab.explicitLimitConeIsLimit.{u, u} _⟩
  exact bounded_cone_is_limit _
  exact PseuNormGrp₁.boundedConeIsLimit _

/-
Remark: This functor even creates limits, as can be shown using the fact that the forgetful
functor from `Profinite` to `Type*` creates limits.
I don't think we actually need that strong statement, so we only prove the following.
-/
instance : PreservesLimits toPNG₁ := by constructor; intro J hJ; constructor

end CompHausFiltPseuNormGrp₁

namespace ProFiltPseuNormGrp₁

@[simp]
theorem id_apply {A : ProFiltPseuNormGrp₁} (a : A) : (𝟙 A : A ⟶ A) a = a :=
  rfl

@[simp]
theorem comp_apply {A B C : ProFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) :=
  rfl

def toPNG₁ : ProFiltPseuNormGrp₁.{u} ⥤ PseuNormGrp₁.{u}
    where
  obj M :=
    { carrier := M
      exhaustive' := M.exhaustive }
  map X Y f := { f.toAddMonoidHom with strict' := fun c x h => f.Strict h }

instance : Faithful toPNG₁.{u} :=
  Faithful.mk <| by
    intro X Y f g h
    ext
    apply_fun fun e => e x at h 
    exact h

variable {K : J ⥤ ProFiltPseuNormGrp₁.{u}}

variable (C : Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb))

def filtrationEquiv (c : NNReal) :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c ≃
      (Profinite.limitCone (K ⋙ level.obj c)).pt :=
  ((Cones.forget _).mapIso (PseuNormGrp₁.levelConeIso C c)).toEquiv

instance (c) :
    TopologicalSpace (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  TopologicalSpace.induced (filtrationEquiv C c) inferInstance

def filtrationHomeo (c : NNReal) :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c ≃ₜ
      (Profinite.limitCone (K ⋙ level.obj c)).pt :=
  Homeomorph.homeomorphOfContinuousOpen (filtrationEquiv _ _) continuous_induced_dom
    (by
      intro U hU
      have : Inducing (filtration_equiv C c) := ⟨rfl⟩
      rw [this.isOpen_iff] at hU 
      obtain ⟨U, hU, rfl⟩ := hU
      simpa)

instance (c) : T2Space (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  (filtrationHomeo C c).symm.T2Space

instance (c) : CompactSpace (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  (filtrationHomeo C c).symm.CompactSpace

instance (c) :
    TotallyDisconnectedSpace (PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  (filtrationHomeo C c).symm.TotallyDisconnectedSpace

def levelπ (j c) :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c →
      PseudoNormedGroup.filtration (K.obj j) c :=
  (PseuNormGrp₁.level.obj c).map ((PseuNormGrp₁.boundedCone C).π.app j)

theorem levelπ_continuous (j c) : Continuous (levelπ C j c) :=
  by
  have : level_π C j c ∘ (filtration_homeo C c).symm = (Profinite.limitCone _).π.app j :=
    by
    ext
    change (C.is_limit.lift _ ≫ C.cone.π.app j) _ = _
    rw [C.is_limit.fac]
    rfl
  suffices Continuous (level_π C j c ∘ (filtration_homeo C c).symm) by simpa using this
  rw [this]
  continuity

theorem boundedConePoint_continuous_add'_aux {J : Type u} [SmallCategory J]
    {K : J ⥤ ProFiltPseuNormGrp₁}
    (C : CategoryTheory.Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb)) :
    ∀ c₁ c₂ : NNReal,
      Continuous
        (PseudoNormedGroup.add' :
          PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ ×
              PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂ →
            PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) (c₁ + c₂)) :=
  by
  intro c₁ c₂
  let g :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ ×
        PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂ →
      PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) (c₁ + c₂) :=
    PseudoNormedGroup.add'
  change Continuous g
  suffices Continuous (filtration_homeo C _ ∘ g) by simpa using this
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  let e := PseudoNormedGroup.add' ∘ Prod.map (level_π C j c₁) (level_π C j c₂)
  have he : Continuous e := by
    apply Continuous.comp
    apply ComphausFilteredPseudoNormedGroup.continuous_add'
    apply Continuous.prod_map
    apply level_π_continuous
    apply level_π_continuous
  convert he
  ext
  dsimp
  simpa

theorem boundedConePoint_continuous_neg'_aux {J : Type u} [SmallCategory J]
    {K : J ⥤ ProFiltPseuNormGrp₁}
    (C : CategoryTheory.Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb)) :
    ∀ c : NNReal,
      Continuous
        (PseudoNormedGroup.neg' :
          PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c →
            PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c) :=
  by
  intro c
  let g :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c →
      PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c :=
    PseudoNormedGroup.neg'
  change Continuous g
  suffices Continuous (filtration_homeo C c ∘ g) by simpa using this
  apply Continuous.subtype_mk
  apply continuous_pi
  dsimp [g]
  intro j
  let e := PseudoNormedGroup.neg' ∘ level_π C j c
  have he : Continuous e := by
    apply Continuous.comp
    apply ComphausFilteredPseudoNormedGroup.continuous_neg'
    apply level_π_continuous
  convert he
  ext
  dsimp
  simpa

theorem boundedConePoint_continuous_cast_le_aux {J : Type u} [SmallCategory J]
    {K : J ⥤ ProFiltPseuNormGrp₁}
    (C : CategoryTheory.Limits.LimitCone ((K ⋙ toPNG₁) ⋙ PseuNormGrp₁.toAb)) :
    ∀ (c₁ c₂ : NNReal) (h : c₁ ≤ c₂),
      Continuous
        (PseudoNormedGroup.castLe' h :
          PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ →
            PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂) :=
  by
  intro c₁ c₂ h
  let g :
    PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₁ →
      PseudoNormedGroup.filtration (PseuNormGrp₁.boundedConePoint C) c₂ :=
    PseudoNormedGroup.castLe' h
  change Continuous g
  suffices Continuous (filtration_homeo C _ ∘ g) by simpa using this
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  dsimp [g]
  let e := PseudoNormedGroup.castLe' h ∘ level_π C j c₁
  have he : Continuous e := by
    apply Continuous.comp
    haveI : Fact (c₁ ≤ c₂) := ⟨h⟩
    apply ComphausFilteredPseudoNormedGroup.continuous_castLe
    apply level_π_continuous
  exact he

def boundedConePoint : ProFiltPseuNormGrp₁
    where
  M := PseuNormGrp₁.boundedConePoint C
  str :=
    {
      (inferInstance :
        PseudoNormedGroup
          (PseuNormGrp₁.boundedConePoint
            C)) with
      continuous_add' := boundedConePoint_continuous_add'_aux _
      continuous_neg' := boundedConePoint_continuous_neg'_aux _
      continuous_castLe := fun _ _ h => boundedConePoint_continuous_cast_le_aux _ _ _ h.out }
  exhaustive' := (PseuNormGrp₁.boundedConePoint C).exhaustive

def boundedCone : Cone K where
  pt := boundedConePoint C
  π :=
    { app := fun j =>
        { (PseuNormGrp₁.boundedCone C).π.app j with
          continuous' := fun c => levelπ_continuous _ _ _ }
      naturality := by
        intro i j f
        ext
        dsimp
        rw [← (PseuNormGrp₁.boundedCone C).w f]
        rfl }

def boundedConeIsLimit : IsLimit (boundedCone C)
    where
  lift S :=
    { (PseuNormGrp₁.boundedConeIsLimit C).lift (toPNG₁.mapCone S) with
      continuous' := by
        intro c
        let t :
          PseudoNormedGroup.filtration S.X c → PseudoNormedGroup.filtration (bounded_cone C).pt c :=
          ((PseuNormGrp₁.boundedConeIsLimit C).lift (to_PNG₁.mapCone S)).level _
        change Continuous t
        suffices Continuous (filtration_homeo C c ∘ t) by simpa using this
        have :
          ⇑(filtration_homeo C c) ∘ t =
            (Profinite.limitConeIsLimit _).lift ((level.obj c).mapCone S) :=
          by
          ext
          change (C.is_limit.lift _ ≫ C.cone.π.app _) _ = _
          rw [C.is_limit.fac]; rfl
        rw [this]
        continuity }
  fac := by
    intro S j
    ext
    dsimp [bounded_cone]
    change
      ((PseuNormGrp₁.boundedConeIsLimit C).lift (to_PNG₁.mapCone S) ≫
            (PseuNormGrp₁.boundedCone C).π.app j)
          _ =
        _
    rw [(PseuNormGrp₁.boundedConeIsLimit C).fac]
    rfl
  uniq := by
    intro S m hm
    ext
    dsimp
    have : to_PNG₁.map m = (PseuNormGrp₁.boundedConeIsLimit C).lift (to_PNG₁.mapCone S) :=
      by
      apply (PseuNormGrp₁.boundedConeIsLimit C).uniq (to_PNG₁.mapCone S)
      intro j
      ext t
      specialize hm j
      apply_fun fun e => e t at hm 
      exact hm
    rw [← this]
    rfl

instance : PreservesLimit K toPNG₁ :=
  by
  apply CategoryTheory.Limits.preservesLimitOfPreservesLimitCone
  rotate_left 2
  exact bounded_cone ⟨_, Ab.explicitLimitConeIsLimit.{u, u} _⟩
  exact bounded_cone_is_limit _
  exact PseuNormGrp₁.boundedConeIsLimit _

/-
Remark: This functor even creates limits, as can be shown using the fact that the forgetful
functor from `Profinite` to `Type*` creates limits.
I don't think we actually need that strong statement, so we only prove the following.
-/
instance : PreservesLimits toPNG₁ := by constructor; intro J hJ; constructor

end ProFiltPseuNormGrp₁

