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
  ⟨carrier⟩

instance (M : PseuNormGrp₁.{u}) : PseudoNormedGroup M :=
  M.str

theorem exhaustive (M : PseuNormGrp₁) (x : M) : ∃ c, x ∈ PseudoNormedGroup.filtration M c :=
  M.exhaustive' x

instance : Category PseuNormGrp₁.{u}
    where
  Hom A B := StrictPseudoNormedGroupHom A B
  id A := StrictPseudoNormedGroupHom.id A
  comp f g := f.comp g

-- Porting note: in Lean 3 morphisms unfolded to `StrictPseudoNormedGroupHom` and used its
-- coercion; in Lean 4 it is declared (as for mathlib's `MonCat`)
instance {A B : PseuNormGrp₁.{u}} : CoeFun (A ⟶ B) fun _ => A → B where
  coe (f : StrictPseudoNormedGroupHom A B) := f

-- Porting note: Lean 3's `ext` found the extensionality lemma of `strict_pseudo_normed_group_hom`
-- through the definition of `⟶`; in Lean 4 it has to be stated for `⟶`.
@[ext]
theorem hom_ext {A B : PseuNormGrp₁.{u}} (f g : A ⟶ B) (h : ∀ x, f x = g x) : f = g :=
  StrictPseudoNormedGroupHom.ext f g h

@[simp]
theorem id_apply (M : PseuNormGrp₁) (x : M) : (𝟙 M : M ⟶ M) x = x :=
  rfl

@[simp]
theorem comp_apply {A B C : PseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) :=
  rfl

def toAb : PseuNormGrp₁.{u} ⥤ Ab.{u}
    where
  obj M := AddCommGroupCat.of M
  map {M N} f := f.toAddMonoidHom

variable {K : J ⥤ PseuNormGrp₁.{u}}

variable (C : Limits.LimitCone (K ⋙ toAb))

def boundedElements : AddSubgroup C.cone.pt
    where
  carrier := {x | ∃ c, ∀ j, C.cone.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c}
  -- Porting note: the `simp` calls of the Lean 3 proofs are replaced by explicit rewrites, and
  -- the pseudo-normed group `K.obj j` is given explicitly (it is not found from `toAb.obj (K.obj j)`)
  zero_mem' := ⟨0, fun j => by
    rw [map_zero]
    exact PseudoNormedGroup.zero_mem_filtration (M := K.obj j) 0⟩
  add_mem' {a b} ha hb := by
    obtain ⟨c, hc⟩ := ha
    obtain ⟨d, hd⟩ := hb
    use c + d
    intro j
    rw [map_add]
    exact PseudoNormedGroup.add_mem_filtration (M := K.obj j) (hc j) (hd j)
  neg_mem' {a} ha := by
    obtain ⟨c, hc⟩ := ha
    use c
    intro j
    rw [map_neg]
    exact PseudoNormedGroup.neg_mem_filtration (M := K.obj j) (hc j)

def boundedElements.filt (c : NNReal) : Set C.cone.pt :=
  {x | ∀ j, C.cone.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c}

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
        exact PseudoNormedGroup.filtration_mono (M := K.obj i) h (t.2 i)
      zero_mem_filtration' := by
        intro c; refine' ⟨⟨0, fun i => _⟩, rfl⟩
        rw [map_zero]
        exact PseudoNormedGroup.zero_mem_filtration (M := K.obj i) c
      neg_mem_filtration' := by
        intro c x hx
        obtain ⟨t, rfl⟩ := hx; refine' ⟨⟨-t, fun i => _⟩, rfl⟩
        rw [map_neg]
        exact PseudoNormedGroup.neg_mem_filtration (M := K.obj i) (t.2 i)
      add_mem_filtration' := by
        intro c₁ c₂ x₁ x₂ h₁ h₂
        obtain ⟨t₁, rfl⟩ := h₁; obtain ⟨t₂, rfl⟩ := h₂
        refine' ⟨⟨t₁ + t₂, fun i => _⟩, rfl⟩
        rw [map_add]
        exact PseudoNormedGroup.add_mem_filtration (M := K.obj i) (t₁.2 i) (t₂.2 i) }
  exhaustive' := by
    intro m
    obtain ⟨c, hc⟩ := m.2
    refine' ⟨c, ⟨m.1, hc⟩, Subtype.ext rfl⟩

def boundedCone : Cone K where
  pt := boundedConePoint C
  π :=
    { app := fun j =>
        { toFun := fun x => C.cone.π.app _ x.1
          map_zero' := AddMonoidHom.map_zero (C.cone.π.app _)
          map_add' := fun x y => AddMonoidHom.map_add (C.cone.π.app _) x.1 y.1
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
      obtain ⟨c, hc⟩ := S.pt.exhaustive x
      use c
      intro j
      -- Porting note: `rw [← Ab.comp_apply, C.2.fac]` does not find its pattern in Lean 4
      have h : C.cone.π.app j (C.2.lift (toAb.mapCone S) x) = S.π.app j x :=
        FunLike.congr_fun (C.2.fac (toAb.mapCone S) j) x
      rw [h]
      exact StrictPseudoNormedGroupHom.strict (S.π.app j) hc⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)
  strict' := by
    intro c x hx
    refine' ⟨⟨_, fun j => _⟩, rfl⟩
    -- Porting note: `erw [← Ab.comp_apply, C.2.fac]` does not find its pattern in Lean 4
    have h : C.cone.π.app j (C.2.lift (toAb.mapCone S) x) = S.π.app j x :=
      FunLike.congr_fun (C.2.fac (toAb.mapCone S) j) x
    rw [h]
    exact StrictPseudoNormedGroupHom.strict (S.π.app j) hx

def boundedConeIsLimit : IsLimit (boundedCone C)
    where
  lift S := boundedConeLift C S
  fac := by
    intro S j
    ext x
    exact FunLike.congr_fun (C.2.fac (toAb.mapCone S) j) x
  uniq := by
    intro S m hm
    ext x
    apply Subtype.ext
    refine' Ab.is_limit_ext C _ _ fun j => _
    exact (congrArg (fun f : S.pt ⟶ K.obj j => f x) (hm j)).trans (FunLike.congr_fun (C.2.fac (toAb.mapCone S) j) x).symm

instance : HasLimits PseuNormGrp₁ := by
  constructor; intro J hJ; constructor; intro K
  exact HasLimit.mk ⟨_, boundedConeIsLimit ⟨_, limit.isLimit _⟩⟩

open PseudoNormedGroup

theorem mem_filtration_iff_of_isLimit (C : Cone K) (hC : IsLimit C) (x : C.pt) (c : NNReal) :
    x ∈ PseudoNormedGroup.filtration C.pt c ↔
      ∀ j : J, C.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c :=
  by
  constructor
  · intro h j
    exact StrictPseudoNormedGroupHom.strict (C.π.app j) h
  · intro h
    let E := boundedCone ⟨_, Ab.explicitLimitConeIsLimit.{u, u} (K ⋙ toAb)⟩
    let e : C ≅ E := hC.uniqueUpToIso (boundedConeIsLimit _)
    let eX : C.pt ≅ E.pt := (Cones.forget _).mapIso e
    let w := eX.hom x
    have hw : ∀ j, E.π.app j w ∈ filtration (K.obj j) c :=
      by
      intro j
      -- Porting note: the `simp`/`convert` of the Lean 3 proof is replaced by an explicit equation
      have hj : E.π.app j w = C.π.app j x :=
        congrArg (fun f : C.pt ⟶ K.obj j => f x) (e.hom.w j)
      rw [hj]
      exact h j
    suffices hwm : w ∈ filtration E.pt c by
      have hx : eX.inv w = x := congrArg (fun f : C.pt ⟶ C.pt => f x) eX.hom_inv_id
      have := StrictPseudoNormedGroupHom.strict eX.inv hwm
      rw [hx] at this
      exact this
    exact ⟨⟨w.1, hw⟩, rfl⟩

-- Porting note: `_root_` as in Lean 3 (mathport dropped it)
@[simps]
def _root_.StrictPseudoNormedGroupHom.level {M N : Type _} [PseudoNormedGroup M]
    [PseudoNormedGroup N] (f : StrictPseudoNormedGroupHom M N) (c) :
    filtration M c → filtration N c := fun x => ⟨f x, f.strict x.2⟩

@[simp]
theorem _root_.StrictPseudoNormedGroupHom.level_id (M : Type _) [PseudoNormedGroup M] (c) :
    (StrictPseudoNormedGroupHom.id M).level c = id := by ext; rfl

@[simp]
theorem _root_.StrictPseudoNormedGroupHom.level_comp {M N L : Type _} [PseudoNormedGroup M]
    [PseudoNormedGroup N] [PseudoNormedGroup L] (f : StrictPseudoNormedGroupHom M N)
    (g : StrictPseudoNormedGroupHom N L) (c) : (f.comp g).level c = g.level c ∘ f.level c := by
  ext; rfl

@[simps]
def level : NNReal ⥤ PseuNormGrp₁.{u} ⥤ Type u
    where
  obj c :=
    { obj := fun M => filtration M c
      map := fun f => StrictPseudoNormedGroupHom.level f _
      map_id := fun M => StrictPseudoNormedGroupHom.level_id M _
      map_comp := fun f g => StrictPseudoNormedGroupHom.level_comp f g c }
  map {c₁ c₂} h := { app := fun M => PseudoNormedGroup.castLe' (leOfHom h) }

theorem level_map {X Y : PseuNormGrp₁} (f : X ⟶ Y) (c) :
    (level.obj c).map f = StrictPseudoNormedGroupHom.level f _ :=
  rfl

theorem level_map' {X Y : PseuNormGrp₁} (f : X ⟶ Y) (c) :
    (level.obj c).map f = PseudoNormedGroup.level f (StrictPseudoNormedGroupHom.strict f) c :=
  rfl

def levelConeIsoHom (c) (t : (level.obj c).obj (boundedConePoint C)) : (K ⋙ level.obj c).sections
    where
  val j :=
    { val := C.cone.π.app j t.1.1
      property := by
        obtain ⟨w, hw⟩ := t.2
        have hw' : w.1 = t.1.1 := congrArg Subtype.val hw
        rw [← hw']
        exact w.2 j }
  property := by
    intro i j f
    -- Porting note: `ext; dsimp; rw [← C.cone.w f]; refl` replaced by an explicit term
    exact Subtype.ext (FunLike.congr_fun (C.cone.w f) t.1.1)

-- Porting note: `noncomputable` is needed in Lean 4 (it was not checked in Lean 3)
noncomputable def levelConeIsoInv (c) (t : (K ⋙ level.obj c).sections) :
    (level.obj c).obj (boundedConePoint C) :=
  -- Porting note: the element of the explicit limit is named so that it can be reused
  let y : ((K ⋙ toAb) ⋙ forget Ab).sections :=
    ⟨fun j => (t.1 j).1, fun {i j} f => congrArg Subtype.val (t.2 f)⟩
  have hy : ∀ j, C.cone.π.app j (C.2.lift (Ab.explicitLimitCone.{u, u} (K ⋙ toAb)) y) =
      (t.1 j).1 := fun j => FunLike.congr_fun (C.2.fac (Ab.explicitLimitCone.{u, u} (K ⋙ toAb)) j) y
  ⟨⟨C.2.lift (Ab.explicitLimitCone.{u, u} (K ⋙ toAb)) y, by
      use c
      intro j
      rw [hy j]
      exact (t.1 j).2⟩,
    ⟨⟨C.2.lift (Ab.explicitLimitCone.{u, u} (K ⋙ toAb)) y, fun j => by
      rw [hy j]
      exact (t.1 j).2⟩, rfl⟩⟩

-- Porting note: `noncomputable` is needed in Lean 4 (it was not checked in Lean 3)
noncomputable def levelConeIso (c) :
    (level.obj c).mapCone (boundedCone C) ≅ Types.limitCone.{u, u} _ :=
  Cones.ext
    { hom := levelConeIsoHom _ _
      inv := levelConeIsoInv _ _
      hom_inv_id := by
        funext t
        apply Subtype.ext
        apply Subtype.ext
        apply Ab.is_limit_ext C
        intro j
        exact FunLike.congr_fun (C.2.fac (Ab.explicitLimitCone.{u, u} (K ⋙ toAb)) j) _
      inv_hom_id := by
        funext t
        apply Subtype.ext
        funext j
        apply Subtype.ext
        exact FunLike.congr_fun (C.2.fac (Ab.explicitLimitCone.{u, u} (K ⋙ toAb)) j) _ }
    (by
      intro j
      funext t
      rfl)

-- Porting note: `noncomputable` is needed in Lean 4 (it was not checked in Lean 3)
noncomputable instance preservesLimitsLevelObj (c) : PreservesLimits (level.obj c) :=
  by
  constructor; intro J hJ; constructor; intro K
  apply
    CategoryTheory.Limits.preservesLimitOfPreservesLimitCone
      (boundedConeIsLimit ⟨_, Ab.explicitLimitConeIsLimit.{u, u} (K ⋙ toAb)⟩)
  apply IsLimit.ofIsoLimit (Types.limitConeIsLimit _) (PseuNormGrp₁.levelConeIso _ _).symm

def negNatTrans (c) : level.obj c ⟶ level.obj c
    where
  app X := PseudoNormedGroup.neg'
  naturality := by
    intro A B f
    funext x
    apply Subtype.ext
    exact (StrictPseudoNormedGroupHom.map_neg f x.1).symm

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
  map {X Y} f := { f.toAddMonoidHom with strict' := fun c x h => f.strict h }

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
  map {X Y} f := { f.toAddMonoidHom with strict' := fun c x h => f.strict h }

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

