import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import LiquidTensorExperiment.Compat.AdditiveCategory
import Mathlib.CategoryTheory.Abelian.Exact

#align_import for_mathlib.abelian_sheaves.functor_category

-- This can be removed after #13686 is merged
-- This can be removed after #13686 is merged
namespace CategoryTheory

universe w v u

variable {C : Type max v u} [Category.{v} C]

variable {D : Type w} [Category.{max v u} D]

open CategoryTheory.Limits

example [HasZeroMorphisms D] : HasZeroMorphisms (C ⥤ D) :=
  inferInstance

example [Preadditive D] : Preadditive (C ⥤ D) :=
  inferInstance

noncomputable section

section Kernels

variable [HasZeroMorphisms D] [HasKernels D]

@[simps]
def NatTrans.kernelFunctor {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D
    where
  obj X := kernel (η.app X)
  map f := kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

@[simps]
def NatTrans.kernelι {F G : C ⥤ D} (η : F ⟶ G) : (NatTrans.kernelFunctor.{w, v, u} η) ⟶ F
    where
  app X := kernel.ι _
  naturality f := by simp

@[simps]
def NatTrans.kernelFork {F G : C ⥤ D} (η : F ⟶ G) : KernelFork η :=
  Limits.KernelFork.ofι (NatTrans.kernelι.{w, v, u} η) <| by ext; simp

@[simps]
def NatTrans.isLimitKernelFork {F G : C ⥤ D} (η : F ⟶ G) : IsLimit (NatTrans.kernelFork.{w, v, u} η) :=
  isLimitAux _
    (fun S =>
      { app := fun X => kernel.lift _ (S.ι.app X) <| by simp [← NatTrans.comp_app]
        naturality := fun X Y f => by
          apply equalizer.hom_ext
          dsimp
          simp })
    (by
      intro S
      ext
      delta Fork.ι
      dsimp
      simp only [kernel.lift_ι])
    (by
      intro S m hm
      ext X
      apply_fun fun e => e.app X at hm 
      delta Fork.ι at hm
      dsimp at hm ⊢
      exact (cancel_mono (kernel.ι (η.app X))).1 (by rw [hm, kernel.lift_ι]))

instance functor_category_hasKernels : HasKernels (C ⥤ D) :=
  ⟨fun η => ⟨⟨⟨_, (NatTrans.isLimitKernelFork.{w, v, u} η)⟩⟩⟩⟩

universe w₁ v₁ u₁ v₂

section General

-- Porting note: Lean 4 cannot solve the universe constraint `max v ?u =?= max u v` that arises
-- when synthesising `HasKernels (C ⥤ D)` (resp. `HasCokernels (C ⥤ D)`) for `C : Type (max v u)`
-- and `D : Type w` with `Category.{max v u} D`. We therefore also provide these instances with
-- independent universe parameters (the proofs are those of the Lean 3 file); they are found by
-- unification.
variable {C' : Type u₁} [Category.{v₁} C'] {D' : Type w₁} [Category.{v₂} D'] [HasZeroMorphisms D']

section

variable [HasKernels D']

/-- Auxiliary general version of `NatTrans.kernelFunctor`. -/
private def kernelFunctorGen {F G : C' ⥤ D'} (η : F ⟶ G) : C' ⥤ D'
    where
  obj X := kernel (η.app X)
  map f := kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

private def kernelιGen {F G : C' ⥤ D'} (η : F ⟶ G) : kernelFunctorGen η ⟶ F
    where
  app X := kernel.ι _
  naturality f := by simp [kernelFunctorGen]

private def isLimitKernelForkGen {F G : C' ⥤ D'} (η : F ⟶ G) :
    IsLimit (KernelFork.ofι (kernelιGen η) (by ext; simp [kernelιGen] : kernelιGen η ≫ η = 0)) :=
  isLimitAux _
    (fun S =>
      { app := fun X => kernel.lift _ (S.ι.app X) <| by simp [← NatTrans.comp_app]
        naturality := fun X Y f => by
          apply equalizer.hom_ext
          dsimp [kernelFunctorGen]
          simp })
    (by
      intro S
      ext
      simp [kernelιGen])
    (by
      intro S m hm
      ext X
      apply_fun fun e => e.app X at hm
      dsimp [kernelιGen] at hm ⊢
      exact (cancel_mono (kernel.ι (η.app X))).1 (by rw [hm, kernel.lift_ι]))

instance functor_category_hasKernels_general : HasKernels (C' ⥤ D') :=
  ⟨fun η => ⟨⟨⟨_, isLimitKernelForkGen η⟩⟩⟩⟩

end

end General

def NatTrans.kernelObjIso {F G : C ⥤ D} (η : F ⟶ G) (X : C) : (kernel η).obj X ≅ kernel (η.app X) :=
  ((limit.isLimit _).conePointUniqueUpToIso (NatTrans.isLimitKernelFork.{w, v, u} η)).app X

@[reassoc (attr := simp)]
theorem NatTrans.kernelObjIso_hom_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.kernelObjIso.{w, v, u} η X).hom ≫ kernel.ι (η.app X) = (NatTrans.app (kernel.ι η) X) :=
  by
  have h :=
    ((limit.isLimit _).uniqueUpToIso (NatTrans.isLimitKernelFork.{w, v, u} η)).hom.w WalkingParallelPair.zero
  apply_fun fun e => e.app X at h 
  exact h

@[reassoc (attr := simp)]
theorem NatTrans.kernelObjIso_inv_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.kernelObjIso.{w, v, u} η X).inv ≫ (NatTrans.app (kernel.ι η) X) = kernel.ι _ := by simp [Iso.inv_comp_eq]

@[simps]
def NatTrans.cokernelKernelιIso [HasCokernels D] {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    cokernel ((NatTrans.app (kernel.ι η) X)) ≅ cokernel (kernel.ι (η.app X))
    where
  hom := cokernel.map _ _ (NatTrans.kernelObjIso.{w, v, u} _ _).hom (𝟙 _) (by simp)
  inv := cokernel.map _ _ (NatTrans.kernelObjIso.{w, v, u} _ _).inv (𝟙 _) (by simp)
  hom_inv_id := by ext; dsimp; simp
  inv_hom_id := by ext; dsimp; simp

end Kernels

section Cokernels

variable [HasZeroMorphisms D] [HasCokernels D]

@[simps]
def NatTrans.cokernelFunctor {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D
    where
  obj X := cokernel (η.app X)
  map f := cokernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

@[simps]
def NatTrans.cokernelπ {F G : C ⥤ D} (η : F ⟶ G) : G ⟶ (NatTrans.cokernelFunctor.{w, v, u} η)
    where
  app X := cokernel.π _
  naturality f := by simp

@[simps]
def NatTrans.cokernelCofork {F G : C ⥤ D} (η : F ⟶ G) : CokernelCofork η :=
  Limits.CokernelCofork.ofπ (NatTrans.cokernelπ.{w, v, u} η) <| by ext; simp

@[simps]
def NatTrans.isColimitCokernelCofork {F G : C ⥤ D} (η : F ⟶ G) : IsColimit (NatTrans.cokernelCofork.{w, v, u} η) :=
  isColimitAux _
    (fun S =>
      { app := fun X => cokernel.desc _ (S.π.app X) <| by simp [← NatTrans.comp_app]
        naturality := fun X Y f => by
          apply coequalizer.hom_ext
          dsimp
          simp })
    (by
      intro S
      ext
      delta Cofork.π
      dsimp
      simp only [cokernel.π_desc])
    (by
      intro S m hm
      ext X
      apply_fun fun e => e.app X at hm 
      delta Cofork.π at hm
      dsimp at hm ⊢
      exact (cancel_epi (cokernel.π (η.app X))).1 (by rw [hm, cokernel.π_desc]))

instance functor_category_hasCokernels : HasCokernels (C ⥤ D) :=
  ⟨fun η => ⟨⟨⟨_, (NatTrans.isColimitCokernelCofork.{w, v, u} η)⟩⟩⟩⟩

section General

-- Porting note: see the note on `functor_category_hasKernels_general` above.
variable {C' : Type u₁} [Category.{v₁} C'] {D' : Type w₁} [Category.{v₂} D'] [HasZeroMorphisms D']

section

variable [HasCokernels D']

/-- Auxiliary general version of `NatTrans.cokernelFunctor`. -/
private def cokernelFunctorGen {F G : C' ⥤ D'} (η : F ⟶ G) : C' ⥤ D'
    where
  obj X := cokernel (η.app X)
  map f := cokernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

private def cokernelπGen {F G : C' ⥤ D'} (η : F ⟶ G) : G ⟶ cokernelFunctorGen η
    where
  app X := cokernel.π _
  naturality f := by simp [cokernelFunctorGen]

private def isColimitCokernelCoforkGen {F G : C' ⥤ D'} (η : F ⟶ G) :
    IsColimit
      (CokernelCofork.ofπ (cokernelπGen η) (by ext; simp [cokernelπGen] : η ≫ cokernelπGen η = 0)) :=
  isColimitAux _
    (fun S =>
      { app := fun X => cokernel.desc _ (S.π.app X) <| by simp [← NatTrans.comp_app]
        naturality := fun X Y f => by
          apply coequalizer.hom_ext
          dsimp [cokernelFunctorGen]
          simp })
    (by
      intro S
      ext
      simp [cokernelπGen])
    (by
      intro S m hm
      ext X
      apply_fun fun e => e.app X at hm
      dsimp [cokernelπGen] at hm ⊢
      exact (cancel_epi (cokernel.π (η.app X))).1 (by rw [hm, cokernel.π_desc]))

instance functor_category_hasCokernels_general : HasCokernels (C' ⥤ D') :=
  ⟨fun η => ⟨⟨⟨_, isColimitCokernelCoforkGen η⟩⟩⟩⟩

end

end General

def NatTrans.cokernelObjIso {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (cokernel η).obj X ≅ cokernel (η.app X) :=
  ((colimit.isColimit _).coconePointUniqueUpToIso (NatTrans.isColimitCokernelCofork.{w, v, u} η)).app X

@[reassoc (attr := simp)]
theorem NatTrans.cokernelObjIso_π_hom {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.app (cokernel.π η) X) ≫ (NatTrans.cokernelObjIso.{w, v, u} η X).hom = cokernel.π _ :=
  by
  have h :=
    ((colimit.isColimit _).uniqueUpToIso (NatTrans.isColimitCokernelCofork.{w, v, u} η)).hom.w
      WalkingParallelPair.one
  apply_fun fun e => e.app X at h 
  exact h

@[reassoc (attr := simp)]
theorem NatTrans.cokernelObjIso_π_inv {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    cokernel.π (η.app X) ≫ (NatTrans.cokernelObjIso.{w, v, u} η X).inv = (NatTrans.app (cokernel.π η) X) := by
  simp [Iso.comp_inv_eq]

@[simps]
def NatTrans.kernelCokernelπIso [HasKernels D] {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    kernel ((NatTrans.app (cokernel.π η) X)) ≅ kernel (cokernel.π (η.app X))
    where
  hom := kernel.map _ _ (𝟙 _) (NatTrans.cokernelObjIso.{w, v, u} η X).hom (by simp)
  inv := kernel.map _ _ (𝟙 _) (NatTrans.cokernelObjIso.{w, v, u} η X).inv (by simp)
  hom_inv_id := by ext; dsimp; simp
  inv_hom_id := by ext; dsimp; simp

end Cokernels

section CokernelsAndKernels

variable [HasZeroMorphisms D] [HasCokernels D] [HasKernels D]

theorem NatTrans.coimageImageComparison_app {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.cokernelKernelιIso.{w, v, u} _ _).inv ≫
        (NatTrans.cokernelObjIso.{w, v, u} _ _).inv ≫
          NatTrans.app (Abelian.coimageImageComparison.{max u v, max (max u v) w} η) X ≫
            (NatTrans.kernelObjIso.{w, v, u} _ _).hom ≫ (NatTrans.kernelCokernelπIso.{w, v, u} _ _).hom =
      Abelian.coimageImageComparison.{max v u, w} (η.app X) :=
  by
  dsimp [Abelian.coimageImageComparison]
  ext
  dsimp [NatTrans.cokernelObjIso, IsColimit.coconePointUniqueUpToIso]
  dsimp [NatTrans.kernelObjIso, IsLimit.conePointUniqueUpToIso]
  simp
  exact congrArg (fun e => NatTrans.app e X)
    (Abelian.coimage_image_factorisation.{max u v, max (max u v) w} η)

end CokernelsAndKernels

section Additivity

variable [AdditiveCategory D]

instance : AdditiveCategory (C ⥤ D) :=
  {-- without the infer instance, this becomes REALLY slow...
    (inferInstance : Preadditive (C ⥤ D)) with
    -- Porting note: the Lean 4 field of `HasFiniteBiproducts` is `out`
    out := by
      intro n
      constructor
      intro F
      apply Limits.HasBiproduct.of_hasProduct }

-- Porting note: general-universe version of the instance above, see the note on
-- `functor_category_hasKernels_general`.
instance functor_category_additiveCategory_general {C' : Type u₁} [Category.{v₁} C'] {D' : Type w₁}
    [Category.{v₂} D'] [AdditiveCategory D'] : AdditiveCategory (C' ⥤ D') :=
  { (functorCategoryPreadditive : Preadditive (C' ⥤ D')) with
    out := by
      intro n
      constructor
      intro F
      haveI : Preadditive (C' ⥤ D') := functorCategoryPreadditive
      haveI : HasLimitsOfShape (Discrete (Fin n)) (C' ⥤ D') := functorCategoryHasLimitsOfShape
      apply Limits.HasBiproduct.of_hasProduct }

end Additivity

section Abelian

variable [Abelian D]

instance additiveCategoryOfAbelian : AdditiveCategory D :=
  -- Porting note: `HasFiniteBiproducts D` is not an instance in mathlib 4 (it is the theorem
  -- `Abelian.hasFiniteBiproducts`), so it has to be given explicitly
  { (inferInstance : Preadditive D) with toHasFiniteBiproducts := Abelian.hasFiniteBiproducts }

-- Porting note: general-universe version of the instance above, see the note on
-- `functor_category_hasKernels_general`.
instance additiveCategoryOfAbelian_general {D' : Type w₁} [Category.{v₂} D'] [Abelian D'] :
    AdditiveCategory D' :=
  { (inferInstance : Preadditive D') with toHasFiniteBiproducts := Abelian.hasFiniteBiproducts }

-- without the infer instance, this becomes REALLY slow...
instance functor_category_isIso_coim_to_im_app {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    IsIso (NatTrans.app (Abelian.coimageImageComparison.{max u v, max (max u v) w} η) X) :=
  by
  have :
    NatTrans.app (Abelian.coimageImageComparison.{max u v, max (max u v) w} η) X =
      (NatTrans.cokernelObjIso.{w, v, u} _ _).hom ≫
        (NatTrans.cokernelKernelιIso.{w, v, u} _ _).hom ≫
          Abelian.coimageImageComparison.{max v u, w} (η.app X) ≫
            (NatTrans.kernelCokernelπIso.{w, v, u} _ _).inv ≫ (NatTrans.kernelObjIso.{w, v, u} _ _).inv :=
    by
    rw [← NatTrans.coimageImageComparison_app.{w, v, u} η X]
    simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc, Category.comp_id]
  rw [this]
  apply IsIso.comp_isIso

instance functor_category_isIso_coim_to_im {F G : C ⥤ D} (η : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison.{max u v, max (max u v) w} η) := by
  -- Porting note: the instance has to be provided explicitly because of universe unification
  haveI : ∀ X : C,
      IsIso (NatTrans.app (Abelian.coimageImageComparison.{max u v, max (max u v) w} η) X) :=
    fun X => functor_category_isIso_coim_to_im_app.{w, v, u} η X
  exact NatIso.isIso_of_isIso_app _

instance functorCategoryIsAbelian : Abelian (C ⥤ D) := by
  -- Porting note: the instance has to be provided explicitly because of universe unification
  haveI : ∀ {F G : C ⥤ D} (η : F ⟶ G),
      IsIso (Abelian.coimageImageComparison.{max u v, max (max u v) w} η) :=
    fun η => functor_category_isIso_coim_to_im.{w, v, u} η
  exact Abelian.ofCoimageImageComparisonIsIso

theorem NatTrans.exact_iff_forall {F G H : C ⥤ D} (η : F ⟶ G) (γ : G ⟶ H) :
    Exact η γ ↔ ∀ j, Exact (η.app j) (γ.app j) :=
  by
  simp_rw [Abelian.exact_iff]
  constructor
  · rintro ⟨h1, h2⟩ j
    constructor
    · apply_fun fun e => e.app j at h1 ; simpa using h1
    · apply_fun fun e => e.app j at h2 
      simp only [NatTrans.comp_app, NatTrans.app_zero] at h2 
      let eK : (kernel γ).obj j ≅ kernel (γ.app j) := NatTrans.kernelObjIso.{w, v, u} γ j
      let eQ : (cokernel η).obj j ≅ cokernel (η.app j) := NatTrans.cokernelObjIso.{w, v, u} η j
      have : kernel.ι (γ.app j) = eK.inv ≫ (NatTrans.app (kernel.ι γ) j) := by simp; rw [this]; clear this
      have : cokernel.π (η.app j) = (NatTrans.app (cokernel.π η) j) ≫ eQ.hom := by simp; rw [this]; clear this
      simp only [Category.assoc, reassoc_of h2, zero_comp, comp_zero]
  · intro h
    constructor
    · ext j
      exact (h j).1
    · ext j
      dsimp
      let eK : (kernel γ).obj j ≅ kernel (γ.app j) := NatTrans.kernelObjIso.{w, v, u} γ j
      let eQ : (cokernel η).obj j ≅ cokernel (η.app j) := NatTrans.cokernelObjIso.{w, v, u} η j
      have : (NatTrans.app (kernel.ι γ) j) = eK.hom ≫ kernel.ι _ := by simp; rw [this]; clear this
      have : (NatTrans.app (cokernel.π η) j) = cokernel.π _ ≫ eQ.inv := by simp; rw [this]; clear this
      simp only [Category.assoc, reassoc_of (h j).2, comp_zero, zero_comp]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

-- We need to help lean out a little bit because of the `max` in the universe parameters above.
instance functorCategoryIsAbelian' {A : Type u} [Category.{v} A] [Abelian A] {J : Type v}
    [SmallCategory J] : Abelian (J ⥤ A) :=
  @CategoryTheory.functorCategoryIsAbelian.{u, v, v} J _ A _ _

end Abelian

end CategoryTheory

