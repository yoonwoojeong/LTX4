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
  map X Y f := kernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := by ext; simp
  map_comp X Y Z f g := by ext; simp

@[simps]
def NatTrans.kernelι {F G : C ⥤ D} (η : F ⟶ G) : η.kernelFunctor ⟶ F
    where
  app X := kernel.ι _
  naturality X Y f := by simp

@[simps]
def NatTrans.kernelFork {F G : C ⥤ D} (η : F ⟶ G) : KernelFork η :=
  Limits.KernelFork.ofι η.kernelι <| by ext; simp

@[simps]
def NatTrans.isLimitKernelFork {F G : C ⥤ D} (η : F ⟶ G) : IsLimit η.kernelFork :=
  isLimitAux _
    (fun S =>
      { app := fun X => kernel.lift _ (S.ι.app X) <| by simp [← NatTrans.comp_app]
        naturality := fun X Y f => by ext; dsimp; simp })
    (by
      intro S
      ext
      delta fork.ι
      dsimp
      simp only [kernel.lift_ι])
    (by
      intro S m hm
      ext X
      apply_fun fun e => e.app X at hm 
      delta fork.ι at hm 
      dsimp at hm ⊢
      simp only [hm, kernel.lift_ι])

instance functor_category_hasKernels : HasKernels (C ⥤ D) :=
  ⟨fun F G η => ⟨⟨⟨_, η.isLimitKernelFork⟩⟩⟩⟩

def NatTrans.kernelObjIso {F G : C ⥤ D} (η : F ⟶ G) (X : C) : (kernel η).obj X ≅ kernel (η.app X) :=
  ((limit.isLimit _).conePointUniqueUpToIso η.isLimitKernelFork).app X

@[simp, reassoc]
theorem NatTrans.kernelObjIso_hom_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.kernelObjIso η X).hom ≫ kernel.ι (η.app X) = (kernel.ι η).app X :=
  by
  have h :=
    ((limit.isLimit _).uniqueUpToIso η.isLimitKernelFork).hom.w WalkingParallelPair.zero
  apply_fun fun e => e.app X at h 
  exact h

@[simp, reassoc]
theorem NatTrans.kernelObjIso_inv_ι {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.kernelObjIso η X).inv ≫ (kernel.ι η).app X = kernel.ι _ := by simp [Iso.inv_comp_eq]

@[simps]
def NatTrans.cokernelKernelιIso [HasCokernels D] {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    cokernel ((kernel.ι η).app X) ≅ cokernel (kernel.ι (η.app X))
    where
  hom := cokernel.map _ _ (NatTrans.kernelObjIso _ _).hom (𝟙 _) (by simp)
  inv := cokernel.map _ _ (NatTrans.kernelObjIso _ _).inv (𝟙 _) (by simp)
  hom_inv_id := by ext; dsimp; simp
  inv_hom_id := by ext; dsimp; simp

end Kernels

section Cokernels

variable [HasZeroMorphisms D] [HasCokernels D]

@[simps]
def NatTrans.cokernelFunctor {F G : C ⥤ D} (η : F ⟶ G) : C ⥤ D
    where
  obj X := cokernel (η.app X)
  map X Y f := cokernel.map _ _ (F.map f) (G.map f) (η.naturality f).symm
  map_id X := by ext; simp
  map_comp X Y Z f g := by ext; simp

@[simps]
def NatTrans.cokernelπ {F G : C ⥤ D} (η : F ⟶ G) : G ⟶ η.cokernelFunctor
    where
  app X := cokernel.π _
  naturality X Y f := by simp

@[simps]
def NatTrans.cokernelCofork {F G : C ⥤ D} (η : F ⟶ G) : CokernelCofork η :=
  Limits.CokernelCofork.ofπ η.cokernelπ <| by ext; simp

@[simps]
def NatTrans.isColimitCokernelCofork {F G : C ⥤ D} (η : F ⟶ G) : IsColimit η.cokernelCofork :=
  isColimitAux _
    (fun S =>
      { app := fun X => cokernel.desc _ (S.π.app X) <| by simp [← NatTrans.comp_app]
        naturality := fun X Y f => by ext; dsimp; simp })
    (by
      intro S
      ext
      delta cofork.π
      dsimp
      simp only [cokernel.π_desc])
    (by
      intro S m hm
      ext X
      apply_fun fun e => e.app X at hm 
      delta cofork.π at hm 
      dsimp at hm ⊢
      simp only [hm, cokernel.π_desc])

instance functor_category_hasCokernels : HasCokernels (C ⥤ D) :=
  ⟨fun F G η => ⟨⟨⟨_, η.isColimitCokernelCofork⟩⟩⟩⟩

def NatTrans.cokernelObjIso {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (cokernel η).obj X ≅ cokernel (η.app X) :=
  ((colimit.isColimit _).coconePointUniqueUpToIso η.isColimitCokernelCofork).app X

@[simp, reassoc]
theorem NatTrans.cokernelObjIso_π_hom {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (cokernel.π η).app X ≫ (NatTrans.cokernelObjIso η X).hom = cokernel.π _ :=
  by
  have h :=
    ((colimit.isColimit _).uniqueUpToIso η.isColimitCokernelCofork).hom.w
      WalkingParallelPair.one
  apply_fun fun e => e.app X at h 
  exact h

@[simp, reassoc]
theorem NatTrans.cokernelObjIso_π_inv {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    cokernel.π (η.app X) ≫ (NatTrans.cokernelObjIso η X).inv = (cokernel.π η).app X := by
  simp [Iso.comp_inv_eq]

@[simps]
def NatTrans.kernelCokernelπIso [HasKernels D] {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    kernel ((cokernel.π η).app X) ≅ kernel (cokernel.π (η.app X))
    where
  hom := kernel.map _ _ (𝟙 _) (NatTrans.cokernelObjIso η X).hom (by simp)
  inv := kernel.map _ _ (𝟙 _) (NatTrans.cokernelObjIso η X).inv (by simp)
  hom_inv_id := by ext; dsimp; simp
  inv_hom_id := by ext; dsimp; simp

end Cokernels

section CokernelsAndKernels

variable [HasZeroMorphisms D] [HasCokernels D] [HasKernels D]

theorem NatTrans.coimageImageComparison_app {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    (NatTrans.cokernelKernelιIso _ _).inv ≫
        (NatTrans.cokernelObjIso _ _).inv ≫
          (Abelian.coimageImageComparison η).app X ≫
            (NatTrans.kernelObjIso _ _).hom ≫ (NatTrans.kernelCokernelπIso _ _).hom =
      Abelian.coimageImageComparison (η.app X) :=
  by
  dsimp [Abelian.coimageImageComparison]
  ext
  dsimp [NatTrans.cokernelObjIso, IsColimit.coconePointUniqueUpToIso]
  dsimp [NatTrans.kernelObjIso, IsLimit.conePointUniqueUpToIso]
  simp

end CokernelsAndKernels

section Additivity

variable [AdditiveCategory D]

instance : AdditiveCategory (C ⥤ D) :=
  {-- without the infer instance, this becomes REALLY slow...
    (inferInstance : Preadditive (C ⥤ D)) with
    HasBiproductsOfShape := by
      intro J _
      constructor
      intro F
      apply Limits.HasBiproduct.of_hasProduct }

end Additivity

section Abelian

variable [Abelian D]

instance additiveCategoryOfAbelian : AdditiveCategory D :=
  { (inferInstance : Preadditive D) with }

-- without the infer instance, this becomes REALLY slow...
instance functor_category_isIso_coim_to_im_app {F G : C ⥤ D} (η : F ⟶ G) (X : C) :
    IsIso ((Abelian.coimageImageComparison η).app X) :=
  by
  have :
    (Abelian.coimageImageComparison η).app X =
      (NatTrans.cokernelObjIso _ _).hom ≫
        (NatTrans.cokernelKernelιIso _ _).hom ≫
          Abelian.coimageImageComparison _ ≫
            (NatTrans.kernelCokernelπIso _ _).inv ≫ (NatTrans.kernelObjIso _ _).inv :=
    by
    rw [← NatTrans.coimageImageComparison_app]
    simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Iso.hom_inv_id_assoc, Category.comp_id]
  rw [this]
  apply IsIso.comp_isIso

instance functor_category_isIso_coim_to_im {F G : C ⥤ D} (η : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison η) :=
  NatIso.isIso_of_isIso_app _

instance functorCategoryIsAbelian : Abelian (C ⥤ D) :=
  Abelian.ofCoimageImageComparisonIsIso

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
      let eK : (kernel γ).obj j ≅ kernel (γ.app j) := NatTrans.kernelObjIso γ j
      let eQ : (cokernel η).obj j ≅ cokernel (η.app j) := NatTrans.cokernelObjIso η j
      have : kernel.ι (γ.app j) = eK.inv ≫ (kernel.ι γ).app j := by simp; rw [this]; clear this
      have : cokernel.π (η.app j) = (cokernel.π η).app j ≫ eQ.hom := by simp; rw [this]; clear this
      simp only [Category.assoc, reassoc_of h2, zero_comp, comp_zero]
  · intro h
    constructor
    · ext j
      exact (h j).1
    · ext j
      dsimp
      let eK : (kernel γ).obj j ≅ kernel (γ.app j) := NatTrans.kernelObjIso γ j
      let eQ : (cokernel η).obj j ≅ cokernel (η.app j) := NatTrans.cokernelObjIso η j
      have : (kernel.ι γ).app j = eK.hom ≫ kernel.ι _ := by simp; rw [this]; clear this
      have : (cokernel.π η).app j = cokernel.π _ ≫ eQ.inv := by simp; rw [this]; clear this
      simp only [Category.assoc, reassoc_of (h j).2, comp_zero, zero_comp]

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

-- We need to help lean out a little bit because of the `max` in the universe parameters above.
instance functorCategoryIsAbelian' {A : Type u} [Category.{v} A] [Abelian A] {J : Type v}
    [SmallCategory J] : Abelian (J ⥤ A) :=
  @CategoryTheory.functorCategoryIsAbelian.{u, v, v} J _ A _ _

end Abelian

end CategoryTheory

