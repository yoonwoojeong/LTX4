import LiquidTensorExperiment.PseudoNormedGroup.Category.ProFiltPseuNormGrp

#align_import pseudo_normed_group.category.strictProFiltPseuNormGrp

universe u

open CategoryTheory

open scoped NNReal

noncomputable section

attribute [local instance] typePow

/-- The bundled category whose objects are `profinitely_filtered_pseudo_normed_group`s
equipped (this is the `₁`) with exhaustive filtrations and strict morphisms. -/
structure ProFiltPseuNormGrp₁ : Type (u + 1) where
  M : Type u
  [str : ProfinitelyFilteredPseudoNormedGroup M]
  exhaustive' : ∀ m : M, ∃ c, m ∈ PseudoNormedGroup.filtration M c

namespace ProFiltPseuNormGrp₁

instance : CoeSort ProFiltPseuNormGrp₁ (Type _) :=
  ⟨fun M => M.M⟩

instance (M : ProFiltPseuNormGrp₁) : ProfinitelyFilteredPseudoNormedGroup M :=
  M.str

theorem exhaustive (M : ProFiltPseuNormGrp₁) (m : M) : ∃ c, m ∈ PseudoNormedGroup.filtration M c :=
  M.exhaustive' m

instance : LargeCategory ProFiltPseuNormGrp₁.{u}
    where
  Hom A B := StrictComphausFilteredPseudoNormedGroupHom A B
  id A := StrictComphausFilteredPseudoNormedGroupHom.id
  comp A B C f g := g.comp f

def pFPNG₁ToPFPNGₑₗ : ProFiltPseuNormGrp₁ ⥤ ProFiltPseuNormGrp
    where
  obj M := ProFiltPseuNormGrp.of M
  map M₁ M₂ f := f.toChfpsngHom

instance : ConcreteCategory ProFiltPseuNormGrp₁.{u}
    where
  forget :=
    { obj := fun M => M.M
      map := fun A B f => f }
  forget_faithful := ⟨⟩

/-- The forgetful functor from groups filtered by profinite spaces to
groups filtered by compact Hausdorff spaces. -/
def pFPNG₁ToCHFPNG₁ₑₗ : ProFiltPseuNormGrp₁.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}
    where
  obj M :=
    { M
      exhaustive' := M.exhaustive }
  map A B f := f

def limitCone {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) : Limits.Cone K
    where
  pt :=
    { M := (CompHausFiltPseuNormGrp₁.limitCone (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ)).pt
      str :=
        {
          (inferInstance :
            PseudoNormedGroup
              _) with
          continuous_add' := ComphausFilteredPseudoNormedGroup.continuous_add'
          continuous_neg' := ComphausFilteredPseudoNormedGroup.continuous_neg'
          continuous_castLe := ComphausFilteredPseudoNormedGroup.continuous_castLe
          td := by
            intro c
            let E := CompHausFiltPseuNormGrp₁.ConePointType.filtHomeo (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c
            haveI :
              TotallyDisconnectedSpace
                (CompHausFiltPseuNormGrp₁.ConePointTypeFilt (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c) :=
              by
              dsimp [CompHausFiltPseuNormGrp₁.ConePointTypeFilt]
              infer_instance
            apply E.symm.totallyDisconnectedSpace }
      exhaustive' := CompHausFiltPseuNormGrp₁.exhaustive _ }
  π :=
    { app := fun j => (CompHausFiltPseuNormGrp₁.limitCone (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ)).π.app j
      naturality := (CompHausFiltPseuNormGrp₁.limitCone (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ)).π.naturality }

instance {J : Type u} [SmallCategory J] : CreatesLimitsOfShape J pFPNG₁ToCHFPNG₁ₑₗ
    where CreatesLimit K :=
    { reflects := fun C hC =>
        { lift := fun S => hC.lift (pFPNG₁ToCHFPNG₁ₑₗ.mapCone S)
          fac := fun S j => hC.fac _ _
          uniq := fun S m h => hC.uniq (pFPNG₁ToCHFPNG₁ₑₗ.mapCone S) m h }
      lifts := fun C hC =>
        { liftedCone := limitCone _
          validLift :=
            (CompHausFiltPseuNormGrp₁.limitConeIsLimit (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ)).uniqueUpToIso hC } }

instance : CreatesLimits pFPNG₁ToCHFPNG₁ₑₗ :=
  ⟨⟩

def limitConeIsLimit {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) :
    Limits.IsLimit (limitCone K) :=
  Limits.isLimitOfReflects pFPNG₁ToCHFPNG₁ₑₗ (CompHausFiltPseuNormGrp₁.limitConeIsLimit _)

instance : Limits.HasLimits ProFiltPseuNormGrp₁.{u} :=
  hasLimits_of_hasLimits_createsLimits pFPNG₁ToCHFPNG₁ₑₗ

theorem eq_of_π_eq {J : Type u} [SmallCategory J] {K : J ⥤ ProFiltPseuNormGrp₁.{u}}
    (C : Limits.Cone K) (hC : Limits.IsLimit C) (x y : C.pt)
    (cond : ∀ j, C.π.app j x = C.π.app j y) : x = y :=
  by
  let D := limit_cone K
  let hD : Limits.IsLimit D := limit_cone_is_limit _
  let E : C.X ≅ D.X := hC.conePointUniqueUpToIso hD
  apply_fun E.hom
  swap;
  · intro a b h
    apply_fun E.inv at h 
    change (E.hom ≫ E.inv) _ = (E.hom ≫ E.inv) _ at h 
    simpa using h
  apply Quotient.sound'
  refine' ⟨_, le_sup_left, le_sup_right, _⟩
  simp
  ext j : 3
  dsimp; simp
  exact cond j

theorem coe_comp_apply {A B C : ProFiltPseuNormGrp₁} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) :=
  rfl

def level : ℝ≥0 ⥤ ProFiltPseuNormGrp₁.{u} ⥤ Profinite.{u}
    where
  obj c :=
    { obj := fun M => Profinite.of <| PseudoNormedGroup.filtration M c
      map := fun A B f => ⟨_, f.level_continuous _⟩ }
  map c₁ c₂ h :=
    {
      app := fun M =>
        letI : Fact (c₁ ≤ c₂) := ⟨h.le⟩
        ⟨_, ComphausFilteredPseudoNormedGroup.continuous_castLe _ _⟩ }

instance {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrp₁.{u}) (c : ℝ≥0) :
    Limits.PreservesLimit K (level.obj c) :=
  by
  constructor
  intro E hE
  apply Limits.isLimitOfReflects profiniteToCompHaus
  change
    Limits.IsLimit
      ((CompHausFiltPseuNormGrp₁.level.obj c).mapCone (PFPNG₁_to_CHFPNG₁ₑₗ.map_cone E))
  apply Limits.isLimitOfPreserves
  apply Limits.isLimitOfPreserves
  assumption

theorem mem_filtration_iff_of_isLimit {J : Type u} [SmallCategory J]
    (K : J ⥤ ProFiltPseuNormGrp₁.{u}) (C : Limits.Cone K) (hC : Limits.IsLimit C) (c : ℝ≥0)
    (x : C.pt) :
    x ∈ PseudoNormedGroup.filtration C.pt c ↔
      ∀ j : J, C.π.app j x ∈ PseudoNormedGroup.filtration (K.obj j) c :=
  CompHausFiltPseuNormGrp₁.mem_filtration_iff_of_isLimit (K ⋙ pFPNG₁ToCHFPNG₁ₑₗ)
    (pFPNG₁ToCHFPNG₁ₑₗ.mapCone C) (Limits.isLimitOfPreserves _ hC) _ _

theorem isLimit_ext {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrp₁.{u})
    (C : Limits.Cone K) (hC : Limits.IsLimit C) (x y : C.pt) (h : ∀ j, C.π.app j x = C.π.app j y) :
    x = y :=
  CompHausFiltPseuNormGrp₁.isLimit_ext _ _ (Limits.isLimitOfPreserves pFPNG₁ToCHFPNG₁ₑₗ hC) _ _ h

section ExplicitProduct

def product {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) : ProFiltPseuNormGrp₁.{u}
    where
  M := ∀ i, X i
  str := inferInstance
  exhaustive' := (CompHausFiltPseuNormGrp₁.product fun i => pFPNG₁ToCHFPNG₁ₑₗ.obj (X i)).exhaustive'

@[simps]
def product.π {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) (i) : product X ⟶ X i :=
  CompHausFiltPseuNormGrp₁.product.π (fun i => pFPNG₁ToCHFPNG₁ₑₗ.obj (X i)) i

@[simps]
def product.lift {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
    (M : ProFiltPseuNormGrp₁.{u}) (f : ∀ i, M ⟶ X i) : M ⟶ product X :=
  CompHausFiltPseuNormGrp₁.product.lift (fun i => pFPNG₁ToCHFPNG₁ₑₗ.obj (X i))
    (pFPNG₁ToCHFPNG₁ₑₗ.obj M) f

@[simp, reassoc]
theorem product.lift_π {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
    (M : ProFiltPseuNormGrp₁.{u}) (f : ∀ i, M ⟶ X i) (i) :
    product.lift X M f ≫ product.π X i = f i := by ext; simp

theorem product.lift_unique {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
    (M : ProFiltPseuNormGrp₁.{u}) (f : ∀ i, M ⟶ X i) (g : M ⟶ product X)
    (hg : ∀ i, g ≫ product.π X i = f i) : g = product.lift X M f := by ext; simp [← hg]

theorem product.hom_ext {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u})
    (M : ProFiltPseuNormGrp₁.{u}) (g₁ g₂ : M ⟶ product X)
    (h : ∀ i, g₁ ≫ product.π X i = g₂ ≫ product.π X i) : g₁ = g₂ :=
  by
  rw [product.lift_unique X M _ g₁ fun i => rfl, product.lift_unique X M _ g₂ fun i => rfl]
  simp [h]

end ExplicitProduct

end ProFiltPseuNormGrp₁

