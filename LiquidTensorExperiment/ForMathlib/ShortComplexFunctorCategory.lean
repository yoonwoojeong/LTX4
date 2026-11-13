import LiquidTensorExperiment.ForMathlib.ShortComplexProjections
import LiquidTensorExperiment.ForMathlib.HomologyMapDatum

#align_import for_mathlib.short_complex_functor_category

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

open scoped ZeroObject

variable {J C : Type _} [Category J] [Category C] [HasZeroMorphisms C]

namespace ShortComplex

namespace FunctorCategoryEquivalence

instance evaluation_preservesZeroMorphisms (j : J) :
    ((evaluation J C).obj j).PreservesZeroMorphisms :=
  ⟨fun F G => rfl⟩

-- deterministic timeouts may occur if we add @[simps] attributes -
def functor : ShortComplex (J ⥤ C) ⥤ J ⥤ ShortComplex C :=
  Functor.flip
    { obj := fun j => Functor.mapShortComplex ((evaluation J C).obj j)
      map := fun i j f => NatTrans.mapShortComplex ((evaluation J C).map f) }

@[simps]
def Inverse.obj (F : J ⥤ ShortComplex C) : ShortComplex (J ⥤ C) :=
  mk (𝟙 F ◫ φ₁₂) (𝟙 F ◫ φ₂₃)
    (by
      ext
      simp only [NatTrans.comp_app, NatTrans.hcomp_app, φ₁₂_app, NatTrans.id_app, π₂_map,
        φ₂₃_app, π₃_map, assoc, zero_app]
      erw [id_comp, comp_id]
      apply ShortComplex.zero)

@[simps]
def Inverse.map {F G : J ⥤ ShortComplex C} (φ : F ⟶ G) : Inverse.obj F ⟶ Inverse.obj G :=
  by
  refine' ⟨φ ◫ 𝟙 _, φ ◫ 𝟙 _, φ ◫ 𝟙 _, _, _⟩ <;> ext <;> dsimp <;>
    erw [comp_id, id_comp, id_comp, comp_id]
  exacts [(φ.app x).comm₁₂, (φ.app x).comm₂₃]

def inverse : (J ⥤ ShortComplex C) ⥤ ShortComplex (J ⥤ C)
    where
  obj := Inverse.obj
  map F G := Inverse.map
  map_id F := by ext <;> apply comp_id
  map_comp F₁ F₂ F₃ φ ψ := by ext <;> dsimp <;> erw [id_comp, id_comp, id_comp]

def UnitIso.obj (S : ShortComplex (J ⥤ C)) : S ≅ (functor ⋙ inverse).obj S :=
  by
  refine' iso_mk _ _ _ _ _ <;>
    try
      refine' NatIso.ofComponents (fun X => iso.refl _) _
      intro i j f; dsimp; erw [comp_id, id_comp]; rfl
  all_goals ext; dsimp [Functor, inverse]; erw [comp_id, id_comp]

def unitIso :
    𝟭 (ShortComplex (J ⥤ C)) ≅
      FunctorCategoryEquivalence.functor ⋙ FunctorCategoryEquivalence.inverse :=
  NatIso.ofComponents UnitIso.obj fun S₁ S₂ ψ => by
    ext <;> dsimp [iso_mk, NatIso.ofComponents, iso_mk, Functor, inverse, UnitIso.obj] <;>
      erw [comp_id, id_comp, id_comp]

def CounitIso.obj (F : J ⥤ ShortComplex C) : (inverse ⋙ functor).obj F ≅ F :=
  NatIso.ofComponents
    (fun j => by
      refine' iso_mk (iso.refl _) (iso.refl _) (iso.refl _) _ _
      all_goals dsimp [Functor, inverse]; erw [id_comp, comp_id, comp_id])
    fun i j f => by ext <;> dsimp <;> erw [comp_id, id_comp] <;> rfl

def counitIso :
    FunctorCategoryEquivalence.inverse ⋙ FunctorCategoryEquivalence.functor ≅
      𝟭 (J ⥤ ShortComplex C) :=
  NatIso.ofComponents CounitIso.obj fun F₁ F₂ φ => by
    ext <;> dsimp [Functor, inverse, CounitIso.obj] <;> erw [id_comp, comp_id]

theorem functor_unitIso_comp (F : ShortComplex (J ⥤ C)) :
    FunctorCategoryEquivalence.functor.map (FunctorCategoryEquivalence.unitIso.hom.app F) ≫
        FunctorCategoryEquivalence.counitIso.hom.app (FunctorCategoryEquivalence.functor.obj F) =
      𝟙 _ :=
  by
  dsimp [functor_category_equivalence.functor, functor_category_equivalence.unitIso,
    functor_category_equivalence.inverse, functor_category_equivalence.counitIso, evaluation,
    Functor.flip, Functor.mapShortComplex, FunctorCategoryEquivalence.CounitIso.obj,
    FunctorCategoryEquivalence.UnitIso.obj, NatIso.ofComponents]
  ext <;> apply id_comp

end FunctorCategoryEquivalence

@[simps]
def functorCategoryEquivalence : ShortComplex (J ⥤ C) ≌ J ⥤ ShortComplex C
    where
  Functor := FunctorCategoryEquivalence.functor
  inverse := FunctorCategoryEquivalence.inverse
  unitIso := FunctorCategoryEquivalence.unitIso
  counitIso := FunctorCategoryEquivalence.counitIso
  functor_unitIso_comp' := FunctorCategoryEquivalence.functor_unitIso_comp

@[simps]
def functorLift {X Y Z : J ⥤ C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) : J ⥤ ShortComplex C :=
  FunctorCategoryEquivalence.functor.obj (mk f g h)

@[simps]
def ιMiddle [HasZeroObject C] : C ⥤ ShortComplex C :=
  functorLift (0 : 0 ⟶ 𝟭 C) (0 : 𝟭 C ⟶ 0) zero_comp

def ιMiddleHomologyNatIso {A : Type _} [Category A] [Abelian A] : 𝟭 A ≅ ιMiddle ⋙ homologyFunctor :=
  NatIso.ofComponents (fun X => (HomologyIsoDatum.ofBothZeros _ _ rfl rfl).Iso) fun X Y f =>
    by
    erw [(HomologyMapDatum.ofBothAreZeros (ι_middle.map f) rfl rfl rfl rfl).homology'_map_eq]
    erw [Iso.hom_inv_id_assoc]
    rfl

theorem ιMiddle_π₁_isZero [HasZeroObject C] : IsZero ((ιMiddle : C ⥤ _) ⋙ ShortComplex.π₁) :=
  by
  rw [Functor.isZero_iff]
  intro X
  dsimp
  simp only [Functor.zero_obj]

theorem ιMiddle_π₃_isZero [HasZeroObject C] : IsZero ((ιMiddle : C ⥤ _) ⋙ ShortComplex.π₃) :=
  by
  rw [Functor.isZero_iff]
  intro X
  dsimp
  simp only [Functor.zero_obj]

@[simps]
def natTransHomMk {S₁ S₂ : J ⥤ ShortComplex C} (τ₁ : S₁ ⋙ π₁ ⟶ S₂ ⋙ π₁) (τ₂ : S₁ ⋙ π₂ ⟶ S₂ ⋙ π₂)
    (τ₃ : S₁ ⋙ π₃ ⟶ S₂ ⋙ π₃) (comm₁₂ : (𝟙 S₁ ◫ φ₁₂) ≫ τ₂ = τ₁ ≫ 𝟙 S₂ ◫ φ₁₂)
    (comm₂₃ : (𝟙 S₁ ◫ φ₂₃) ≫ τ₃ = τ₂ ≫ 𝟙 S₂ ◫ φ₂₃) : S₁ ⟶ S₂ :=
  FunctorCategoryEquivalence.counitIso.inv.app S₁ ≫
    FunctorCategoryEquivalence.functor.map (homMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃) ≫
      FunctorCategoryEquivalence.counitIso.hom.app S₂

theorem natTransHomMk_app_τ₂_eq {S₁ S₂ : J ⥤ ShortComplex C} (τ₁ : S₁ ⋙ π₁ ⟶ S₂ ⋙ π₁)
    (τ₂ : S₁ ⋙ π₂ ⟶ S₂ ⋙ π₂) (τ₃ : S₁ ⋙ π₃ ⟶ S₂ ⋙ π₃) (comm₁₂ : (𝟙 S₁ ◫ φ₁₂) ≫ τ₂ = τ₁ ≫ 𝟙 S₂ ◫ φ₁₂)
    (comm₂₃ : (𝟙 S₁ ◫ φ₂₃) ≫ τ₃ = τ₂ ≫ 𝟙 S₂ ◫ φ₂₃) (j : J) :
    ((natTransHomMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃).app j).τ₂ = τ₂.app j :=
  by
  dsimp [functor_category_equivalence.counitIso, FunctorCategoryEquivalence.CounitIso.obj,
    iso.refl]
  erw [id_comp, comp_id]
  rfl

@[simp, reassoc]
def natTransHomMk_comp {S₁ S₂ S₃ : J ⥤ ShortComplex C} (τ₁ : S₁ ⋙ π₁ ⟶ S₂ ⋙ π₁)
    (τ₂ : S₁ ⋙ π₂ ⟶ S₂ ⋙ π₂) (τ₃ : S₁ ⋙ π₃ ⟶ S₂ ⋙ π₃) (comm₁₂ : (𝟙 S₁ ◫ φ₁₂) ≫ τ₂ = τ₁ ≫ 𝟙 S₂ ◫ φ₁₂)
    (comm₂₃ : (𝟙 S₁ ◫ φ₂₃) ≫ τ₃ = τ₂ ≫ 𝟙 S₂ ◫ φ₂₃) (τ₁' : S₂ ⋙ π₁ ⟶ S₃ ⋙ π₁)
    (τ₂' : S₂ ⋙ π₂ ⟶ S₃ ⋙ π₂) (τ₃' : S₂ ⋙ π₃ ⟶ S₃ ⋙ π₃)
    (comm₁₂' : (𝟙 S₂ ◫ φ₁₂) ≫ τ₂' = τ₁' ≫ 𝟙 S₃ ◫ φ₁₂)
    (comm₂₃' : (𝟙 S₂ ◫ φ₂₃) ≫ τ₃' = τ₂' ≫ 𝟙 S₃ ◫ φ₂₃) :
    natTransHomMk τ₁ τ₂ τ₃ comm₁₂ comm₂₃ ≫ natTransHomMk τ₁' τ₂' τ₃' comm₁₂' comm₂₃' =
      natTransHomMk (τ₁ ≫ τ₁') (τ₂ ≫ τ₂') (τ₃ ≫ τ₃')
        (by rw [← assoc, comm₁₂, assoc, comm₁₂', assoc])
        (by rw [← assoc, comm₂₃, assoc, comm₂₃', assoc]) :=
  by
  ext
  all_goals
    dsimp [functor_category_equivalence.counitIso, NatIso.ofComponents,
      FunctorCategoryEquivalence.CounitIso.obj, functor_category_equivalence.functor]
    erw [id_comp, id_comp, id_comp, comp_id, comp_id, comp_id]

@[simp]
def natTransHomMk_id (S : J ⥤ ShortComplex C) :
    natTransHomMk (𝟙 (S ⋙ π₁)) (𝟙 (S ⋙ π₂)) (𝟙 (S ⋙ π₃)) (by simp only [id_comp, comp_id])
        (by simp only [id_comp, comp_id]) =
      𝟙 S :=
  by
  ext
  all_goals
    dsimp [functor_category_equivalence.counitIso, NatIso.ofComponents,
      FunctorCategoryEquivalence.CounitIso.obj, functor_category_equivalence.functor]
    erw [id_comp, comp_id]
    rfl

@[simps]
def functorNatIsoMk {S₁ S₂ : J ⥤ ShortComplex C} (τ₁ : S₁ ⋙ π₁ ≅ S₂ ⋙ π₁) (τ₂ : S₁ ⋙ π₂ ≅ S₂ ⋙ π₂)
    (τ₃ : S₁ ⋙ π₃ ≅ S₂ ⋙ π₃) (comm₁₂ : (𝟙 S₁ ◫ φ₁₂) ≫ τ₂.hom = τ₁.hom ≫ 𝟙 S₂ ◫ φ₁₂)
    (comm₂₃ : (𝟙 S₁ ◫ φ₂₃) ≫ τ₃.hom = τ₂.hom ≫ 𝟙 S₂ ◫ φ₂₃) : S₁ ≅ S₂ :=
  by
  have comm₁₂' : (𝟙 S₂ ◫ φ₁₂) ≫ τ₂.inv = τ₁.inv ≫ 𝟙 S₁ ◫ φ₁₂ := by
    simpa only [← cancel_epi τ₁.hom, ← cancel_mono τ₂.hom, assoc, τ₂.inv_hom_id, comp_id,
      τ₁.hom_inv_id_assoc] using comm₁₂.symm
  have comm₂₃' : (𝟙 S₂ ◫ φ₂₃) ≫ τ₃.inv = τ₂.inv ≫ 𝟙 S₁ ◫ φ₂₃ := by
    simpa only [← cancel_epi τ₂.hom, ← cancel_mono τ₃.hom, assoc, τ₃.inv_hom_id, comp_id,
      τ₂.hom_inv_id_assoc] using comm₂₃.symm
  exact
    { hom := ShortComplex.natTransHomMk τ₁.hom τ₂.hom τ₃.hom comm₁₂ comm₂₃
      inv := ShortComplex.natTransHomMk τ₁.inv τ₂.inv τ₃.inv comm₁₂' comm₂₃'
      hom_inv_id := by simp only [ShortComplex.natTransHomMk_comp, Iso.hom_inv_id, ShortComplex.natTransHomMk_id]
      inv_hom_id := by simp only [ShortComplex.natTransHomMk_comp, Iso.inv_hom_id, ShortComplex.natTransHomMk_id] }

end ShortComplex

