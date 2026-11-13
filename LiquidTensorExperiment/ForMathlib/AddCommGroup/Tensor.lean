import Mathlib.LinearAlgebra.TensorProduct
import LiquidTensorExperiment.ForMathlib.AddCommGroupInstances
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitProducts
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Ab4
import LiquidTensorExperiment.ForMathlib.AddCommGroup
import LiquidTensorExperiment.ForMathlib.ExactFilteredColimits
import LiquidTensorExperiment.ForMathlib.SplitExact
import LiquidTensorExperiment.ForMathlib.Ab4
import LiquidTensorExperiment.ForMathlib.Ab52
import Mathlib.CategoryTheory.Limits.Preserves.Limits

#align_import for_mathlib.AddCommGroup.tensor

noncomputable section

universe u

open scoped TensorProduct

open CategoryTheory

namespace AddCommGroupCat

def linearEquivToIso {A B : AddCommGroupCat.{u}} (e : A ≃ₗ[ℤ] B) : A ≅ B
    where
  hom := e.toLinearMap.toAddMonoidHom
  inv := e.symm.toLinearMap.toAddMonoidHom
  hom_inv_id' := by
    ext t
    simp
  inv_hom_id' := by
    ext t
    simp

def tensor (A B : AddCommGroupCat.{u}) : AddCommGroupCat.{u} :=
  AddCommGroupCat.of (A ⊗[ℤ] B)

theorem tensor_ext {A B C : AddCommGroupCat.{u}} (f g : A.tensor B ⟶ C)
    (h : ∀ x y, f (x ⊗ₜ y) = g (x ⊗ₜ y)) : f = g :=
  by
  ext1 x; show f.to_int_linear_map x = g.to_int_linear_map x; congr 1; clear x
  apply TensorProduct.ext'; exact h

def tensorUncurry {A B C : AddCommGroupCat.{u}} (e : A ⟶ AddCommGroupCat.of (B ⟶ C)) :
    tensor A B ⟶ C :=
  LinearMap.toAddMonoidHom <|
    TensorProduct.lift <|
      let e' := e.toIntLinearMap
      let e'' : (B ⟶ C) →ₗ[ℤ] B →ₗ[ℤ] C :=
        AddMonoidHom.toIntLinearMap
          { toFun := fun f => f.toIntLinearMap
            map_zero' := by ext; rfl
            map_add' := fun f g => by ext; rfl }
      e''.comp e'

def tensorCurry {A B C : AddCommGroupCat.{u}} (e : tensor A B ⟶ C) : A ⟶ AddCommGroupCat.of (B ⟶ C)
    where
  toFun a :=
    { toFun := fun b => e (a ⊗ₜ b)
      map_zero' := by rw [TensorProduct.tmul_zero, e.map_zero]
      map_add' := by
        intro b c
        rw [TensorProduct.tmul_add, e.map_add] }
  map_zero' := by
    ext t
    dsimp
    rw [TensorProduct.zero_tmul, e.map_zero]
  map_add' := by
    intro x y; ext t
    dsimp
    rw [TensorProduct.add_tmul, e.map_add]

@[simps]
def tensorCurryEquiv (A B C : AddCommGroupCat.{u}) :
    (tensor A B ⟶ C) ≃+ (A ⟶ AddCommGroupCat.of (B ⟶ C))
    where
  toFun := tensorCurry
  invFun := tensorUncurry
  left_inv := by
    intro f; apply tensor_ext; intro x y; dsimp only [tensor_uncurry, tensor_curry]
    erw [TensorProduct.lift.tmul]; rfl
  right_inv f := by
    ext; dsimp only [tensor_uncurry, tensor_curry]
    erw [TensorProduct.lift.tmul]; rfl
  map_add' x y := by ext; rfl

@[simp]
theorem tensorCurry_uncurry {A B C : AddCommGroupCat.{u}} (e : A ⟶ AddCommGroupCat.of (B ⟶ C)) :
    tensorCurry (tensorUncurry e) = e :=
  (tensorCurryEquiv A B C).apply_symm_apply e

@[simp]
theorem tensorUncurry_curry {A B C : AddCommGroupCat.{u}} (e : tensor A B ⟶ C) :
    tensorUncurry (tensorCurry e) = e :=
  (tensorCurryEquiv A B C).symm_apply_apply e

def mapTensor {A A' B B' : AddCommGroupCat.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    tensor A B ⟶ tensor A' B' :=
  (TensorProduct.map f.toIntLinearMap g.toIntLinearMap).toAddMonoidHom

theorem id_helper (A : AddCommGroupCat.{u}) : (𝟙 A : A ⟶ A).toIntLinearMap = LinearMap.id :=
  rfl

theorem comp_helper {A B C : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toIntLinearMap = g.toIntLinearMap.comp f.toIntLinearMap :=
  rfl

@[simp]
theorem zero_helper {A B : AddCommGroupCat.{u}} : (0 : A ⟶ B).toIntLinearMap = 0 :=
  rfl

@[simp]
theorem mapTensor_id {A B : AddCommGroupCat.{u}} : mapTensor (𝟙 A) (𝟙 B) = 𝟙 _ := by ext t;
  dsimp [map_tensor]; simp [id_helper]

@[simp]
theorem mapTensor_comp_left {A A' A'' B : AddCommGroupCat.{u}} (f : A ⟶ A') (g : A' ⟶ A'') :
    mapTensor (f ≫ g) (𝟙 B) = mapTensor f (𝟙 _) ≫ mapTensor g (𝟙 _) :=
  by
  ext t
  rw [← category.id_comp (𝟙 B)]
  dsimp [map_tensor]; simp only [comp_helper, id_helper, TensorProduct.map_comp]
  simp

@[simp]
theorem mapTensor_comp_right {A B B' B'' : AddCommGroupCat.{u}} (f : B ⟶ B') (g : B' ⟶ B'') :
    mapTensor (𝟙 A) (f ≫ g) = mapTensor (𝟙 _) f ≫ mapTensor (𝟙 _) g :=
  by
  ext t
  rw [← category.id_comp (𝟙 A)]
  dsimp [map_tensor]; simp only [comp_helper, id_helper, TensorProduct.map_comp]
  simp

@[simp]
theorem mapTensor_comp_comp {A A' A'' B B' B'' : AddCommGroupCat.{u}} (f : A ⟶ A') (f' : A' ⟶ A'')
    (g : B ⟶ B') (g' : B' ⟶ B'') : mapTensor (f ≫ f') (g ≫ g') = mapTensor f g ≫ mapTensor f' g' :=
  by
  ext t
  dsimp [map_tensor]; simp only [comp_helper, id_helper, TensorProduct.map_comp]
  simp

theorem mapTensor_eq_comp {A A' B B' : AddCommGroupCat.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    mapTensor f g = mapTensor f (𝟙 _) ≫ mapTensor (𝟙 _) g :=
  by
  nth_rw 1 [← category.id_comp g]
  nth_rw 1 [← category.comp_id f]
  rw [map_tensor_comp_comp]

theorem mapTensor_eq_comp' {A A' B B' : AddCommGroupCat.{u}} (f : A ⟶ A') (g : B ⟶ B') :
    mapTensor f g = mapTensor (𝟙 _) g ≫ mapTensor f (𝟙 _) :=
  by
  nth_rw 1 [← category.id_comp f]
  nth_rw 1 [← category.comp_id g]
  rw [map_tensor_comp_comp]

@[simp]
theorem mapTensor_zero_left {A A' B B' : AddCommGroupCat.{u}} (f : B ⟶ B') :
    mapTensor (0 : A ⟶ A') f = 0 :=
  by
  apply (tensor_curry_equiv _ _ _).Injective
  ext a b
  dsimp [tensor_curry, map_tensor]
  simp

@[simp]
theorem mapTensor_zero_right {A A' B B' : AddCommGroupCat.{u}} (f : A ⟶ A') :
    mapTensor f (0 : B ⟶ B') = 0 :=
  by
  apply (tensor_curry_equiv _ _ _).Injective
  ext a b
  dsimp [tensor_curry, map_tensor]
  simp

@[simp]
theorem mapTensor_add_right {A A' B B' : AddCommGroupCat.{u}} (f : A ⟶ A') (g₁ g₂ : B ⟶ B') :
    mapTensor f (g₁ + g₂) = mapTensor f g₁ + mapTensor f g₂ :=
  by
  apply (tensor_curry_equiv _ _ _).Injective
  ext a b
  dsimp [tensor_curry, map_tensor]
  apply TensorProduct.tmul_add

@[simp]
theorem mapTensor_add_left {A A' B B' : AddCommGroupCat.{u}} (f₁ f₂ : A ⟶ A') (g : B ⟶ B') :
    mapTensor (f₁ + f₂) g = mapTensor f₁ g + mapTensor f₂ g :=
  by
  apply (tensor_curry_equiv _ _ _).Injective
  ext a b
  dsimp [tensor_curry, map_tensor]
  apply TensorProduct.add_tmul

theorem tensorUncurry_comp_curry {A B C D : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B.tensor C ⟶ D) :
    tensorUncurry (f ≫ tensorCurry g) = mapTensor f (𝟙 _) ≫ g :=
  by
  apply (tensor_curry_equiv _ _ _).Injective
  erw [(tensor_curry_equiv _ _ _).apply_symm_apply]
  ext a c
  dsimp [tensor_curry, tensor_curry_equiv, map_tensor]
  simp

theorem tensorCurry_uncurry_comp {A B C D : AddCommGroupCat.{u}}
    (e : A ⟶ AddCommGroupCat.of (B ⟶ C)) (g : C ⟶ D) :
    tensorCurry (tensorUncurry e ≫ g) = e ≫ (preadditiveYoneda.flip.obj (Opposite.op B)).map g :=
  by
  ext a b
  dsimp [tensor_curry, tensor_uncurry, preadditive_yoneda]
  simp

@[simps]
def tensorFunctor : AddCommGroupCat.{u} ⥤ AddCommGroupCat.{u} ⥤ AddCommGroupCat.{u}
    where
  obj A :=
    { obj := fun B => tensor A B
      map := fun B B' f => mapTensor (𝟙 _) f
      map_id' := fun A => mapTensor_id
      map_comp' := fun A B C f g => mapTensor_comp_right _ _ }
  map A A' f :=
    { app := fun B => mapTensor f (𝟙 _)
      naturality' := fun B C g => by
        dsimp
        rw [← map_tensor_eq_comp, ← map_tensor_eq_comp'] }
  map_id' := by
    intro A
    ext B : 2
    dsimp; exact map_tensor_id
  map_comp' := by
    intro A B C f g
    ext B : 2
    dsimp; exact map_tensor_comp_left _ _

open Opposite

def tensorAdj (B : AddCommGroupCat.{u}) :
    tensorFunctor.flip.obj B ⊣ preadditiveCoyoneda.obj (op B) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A C => (tensorCurryEquiv A B C).toEquiv
      homEquiv_naturality_left_symm := fun A A' C f g =>
        by
        apply tensor_ext; intro x y
        erw [tensor_curry_equiv_symm_apply, comp_apply, tensor_curry_equiv_symm_apply]
        dsimp only [tensor_uncurry]
        simp only [LinearMap.comp_apply, TensorProduct.lift.tmul, TensorProduct.map_tmul,
          AddMonoidHom.coe_toIntLinearMap, id_apply, comp_apply]
        rfl
      homEquiv_naturality_right := fun A C C' f g => by ext x y : 2; rfl }

instance tensorFlipPreservesColimits (B : AddCommGroupCat.{u}) :
    Limits.PreservesColimits (tensorFunctor.flip.obj B) :=
  (tensorAdj B).leftAdjointPreservesColimits

def tensorExplicitPiComparison {α : Type u} [Fintype α] (X : α → AddCommGroupCat.{u + 1})
    (B : AddCommGroupCat.{u + 1}) :
    tensor (AddCommGroupCat.of (DirectSum α fun i => X i)) B ⟶
      AddCommGroupCat.of (DirectSum α fun i => tensor (X i) B) :=
  directSumLift.{u, u + 1} _ fun a => mapTensor (directSumπ.{u, u + 1} _ _) (𝟙 _)

def tensorPiComparison {α : Type u} (X : α → AddCommGroupCat.{u + 1})
    (B : AddCommGroupCat.{u + 1}) : tensor (∏ X) B ⟶ ∏ fun a => tensor (X a) B :=
  Limits.Pi.lift fun b => mapTensor (Limits.Pi.π _ _) (𝟙 _)

open scoped Classical

def tensorExplicitPiIso {α : Type u} (X : α → AddCommGroupCat.{u + 1})
    (B : AddCommGroupCat.{u + 1}) :
    (of (DirectSum α fun i : α => ↥(X i))).tensor B ≅
      of (DirectSum α fun i : α => ↥((X i).tensor B))
    where
  hom :=
    tensorUncurry <| directSumDesc.{u, u + 1} X fun i => tensorCurry <| directSumι.{u, u + 1} _ i
  inv := directSumDesc.{u, u + 1} _ fun i => mapTensor (directSumι.{u, u + 1} X i) (𝟙 _)
  hom_inv_id' := by
    apply (tensor_curry_equiv _ _ _).Injective
    ext a b
    dsimp [tensor_curry, tensor_uncurry, direct_sum_desc]
    simp only [comp_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.lift.tmul,
      LinearMap.coe_comp, AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_mk,
      DirectSum.toAddMonoid_of, id_apply]
    dsimp [direct_sum_ι]
    simp only [DirectSum.toAddMonoid_of]
    dsimp [map_tensor]
    simp only [id_apply]
  inv_hom_id' := by
    apply directSum_hom_ext'.{u, u + 1}
    intro i
    simp only [direct_sum_ι_desc_assoc, category.comp_id]
    apply (tensor_curry_equiv _ _ _).Injective
    ext a b k
    dsimp [tensor_curry, direct_sum_ι, DirectSum.of, map_tensor, tensor_uncurry, tensor_curry,
      direct_sum_desc]
    simp only [comp_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.map_tmul,
      AddMonoidHom.coe_toIntLinearMap, DFinsupp.singleAddHom_apply, id_apply,
      TensorProduct.lift.tmul, LinearMap.coe_comp, AddMonoidHom.coe_mk, DFinsupp.single_apply]
    dsimp [DirectSum.toAddMonoid]
    simp only [DFinsupp.sumAddHom_single, AddMonoidHom.coe_mk, DFinsupp.single_apply]

theorem tensorExplicitPiIso_hom_eq {α : Type u} [Fintype α] (X : α → AddCommGroupCat.{u + 1})
    (B : AddCommGroupCat.{u + 1}) :
    (tensorExplicitPiIso X B).hom = tensorExplicitPiComparison X B :=
  by
  symm
  apply directSum_hom_ext.{u, u + 1}; swap; infer_instance
  intro j
  apply (tensor_curry_equiv _ _ _).Injective
  apply directSum_hom_ext'.{u, u + 1}; intro i
  apply (tensor_curry_equiv _ _ _).symm.Injective
  dsimp
  simp_rw [tensor_uncurry_comp_curry]
  erw [direct_sum_lift_π, ← map_tensor_comp_comp, category.id_comp]
  dsimp only [tensor_explicit_pi_iso]
  erw [← category.assoc]; let t := _; change _ = t ≫ _
  have ht : t = directSumι.{u, u + 1} _ i := by
    dsimp [t]
    have :=
      directSumι_desc.{u, u + 1} (fun i => tensor (X i) B)
        (fun i => map_tensor (directSumι.{u, u + 1} _ i) (𝟙 _)) i
    dsimp at this ; rw [← this]; clear this
    rw [category.assoc]
    erw [(tensor_explicit_pi_iso X B).inv_hom_id, category.comp_id]
  rw [ht]; clear ht; clear t
  by_cases i = j
  · subst h
    simp [directSumι_π.{u, u + 1}]
  · simp [directSumι_π_of_ne.{u, u + 1} _ _ _ h]

instance isIso_tensorExplicitPiComparison {α : Type u} [Fintype α] (X : α → AddCommGroupCat.{u + 1})
    (B : AddCommGroupCat.{u + 1}) : IsIso (tensorExplicitPiComparison X B) :=
  by
  rw [← tensor_explicit_pi_iso_hom_eq]
  infer_instance

theorem tensorExplicitPiComparison_comparison {α : Type u} [Fintype α]
    (X : α → AddCommGroupCat.{u + 1}) (B : AddCommGroupCat.{u + 1}) :
    tensorPiComparison X B =
      mapTensor (directSumLift.{u, u + 1} _ <| Limits.Pi.π _) (𝟙 _) ≫
        tensorExplicitPiComparison X B ≫
          Limits.Pi.lift (directSumπ.{u, u + 1} fun i => tensor (X i) B) :=
  by
  ext1
  dsimp [tensor_pi_comparison]
  simp only [limits.limit.lift_π, limits.fan.mk_π_app, category.assoc]
  dsimp [tensor_explicit_pi_comparison]
  rw [direct_sum_lift_π, ← map_tensor_comp_left, direct_sum_lift_π]

instance isIso_tensorPiComparison {α : Type u} [Fintype α] (X : α → AddCommGroupCat.{u + 1})
    (B : AddCommGroupCat.{u + 1}) : IsIso (tensorPiComparison X B) :=
  by
  rw [tensor_explicit_pi_comparison_comparison]
  apply (config := { instances := false }) is_iso.comp_is_iso
  · change is_iso ((tensor_functor.flip.obj B).map _)
    apply (config := { instances := false }) functor.map_is_iso
    change
      is_iso
        ((limits.limit.is_limit _).conePointUniqueUpToIso (isLimitDirectSumFan.{u, u + 1} X)).hom
    infer_instance
  apply (config := { instances := false }) is_iso.comp_is_iso; infer_instance
  change
    is_iso ((isLimitDirectSumFan.{u, u + 1} _).conePointUniqueUpToIso (limits.limit.is_limit _)).hom
  infer_instance
  infer_instance

def tensorFlip (A B : AddCommGroupCat.{u}) : A.tensor B ≅ B.tensor A :=
  linearEquivToIso (TensorProduct.comm _ _ _)

def tensorFunctorIsoFlip : tensorFunctor.flip ≅ tensorFunctor :=
  NatIso.ofComponents
    (fun A =>
      NatIso.ofComponents (fun B => tensorFlip _ _)
        (by intro U B f; apply tensor_ext; intro a b; rfl))
    (by
      intro U V f; ext A : 2; apply tensor_ext; intro a b
      rfl)

instance preservesColimitsTensorObj (A : AddCommGroupCat.{u}) :
    Limits.PreservesColimits (tensorFunctor.obj A) :=
  Limits.preservesColimitsOfNatIso (tensorFunctorIsoFlip.app _)

section PreservesFiniteLimits

variable {X Y : AddCommGroupCat.{u}} (f : X ⟶ Y) [Mono f] (A : AddCommGroupCat.{u})

def tensorUnitIsoAux (t A : AddCommGroupCat.{u}) (ht : IsTensorUnit t) : t.tensor A ⟶ A :=
  tensorUncurry <| ht.asHom (𝟙 _)

instance isIso_tensorUnitIsoAux (t A : AddCommGroupCat.{u}) (ht : IsTensorUnit t) :
    IsIso (tensorUnitIsoAux t A ht) :=
  by
  let q : A ⟶ t.tensor A := ⟨fun a => ht.gen ⊗ₜ a, _, _⟩
  use q; constructor
  · apply_fun (tensor_curry_equiv _ _ _).toEquiv
    dsimp [tensor_unit_iso_aux]; rw [tensor_curry_uncurry_comp]; apply ht.ext
    simp; dsimp [tensor_curry]; simp
  · ext; dsimp [q, tensor_unit_iso_aux, tensor_uncurry]; simp
  · simp
  · intro x y; rw [TensorProduct.tmul_add]

def tensorUnitIso (t A : AddCommGroupCat.{u}) (ht : IsTensorUnit t) : t.tensor A ≅ A :=
  asIso (tensorUnitIsoAux t A ht)

theorem tensorUnitIso_naturality (t A B : AddCommGroupCat.{u}) (ht : IsTensorUnit t) (f : A ⟶ B) :
    (tensorUnitIso t A ht).hom ≫ f = mapTensor (𝟙 _) f ≫ (tensorUnitIso t B ht).hom :=
  by
  apply_fun (tensor_curry_equiv _ _ _).toEquiv
  dsimp [tensor_unit_iso, tensor_unit_iso_aux]
  rw [tensor_curry_uncurry_comp]
  apply ht.ext
  simp; dsimp; simp
  ext; dsimp [tensor_curry, map_tensor, tensor_uncurry]
  simp

instance tensor_obj_map_preserves_mono [NoZeroSMulDivisors ℤ A] :
    Mono ((tensorFunctor.obj A).map f) :=
  by
  let D := A.diagram
  let T := A.cocone
  let hT : limits.is_colimit T := A.is_colimit_cocone
  let FX : A.index_cat ⥤ AddCommGroupCat := D ⋙ tensor_functor.flip.obj X
  let FY : A.index_cat ⥤ AddCommGroupCat := D ⋙ tensor_functor.flip.obj Y
  let η : FX ⟶ FY := whisker_left _ (tensor_functor.flip.map f)
  let eX : tensor A X ≅ limits.colimit FX :=
    (limits.is_colimit_of_preserves (tensor_functor.flip.obj X) hT).coconePointUniqueUpToIso
      (limits.colimit.is_colimit _)
  let eY : tensor A Y ≅ limits.colimit FY :=
    (limits.is_colimit_of_preserves (tensor_functor.flip.obj Y) hT).coconePointUniqueUpToIso
      (limits.colimit.is_colimit _)
  let t := _; change mono t
  have ht : t = eX.hom ≫ limits.colim_map η ≫ eY.inv :=
    by
    dsimp [t, eX, eY]
    apply (limits.is_colimit_of_preserves (tensor_functor.flip.obj X) hT).hom_ext
    intro i
    erw [(limits.is_colimit_of_preserves (tensor_functor.flip.obj X) hT).fac_assoc]
    simp only [functor.map_cocone_ι_app, functor.flip_obj_map, tensor_functor_map_app,
      limits.colimit.cocone_ι, limits.ι_colim_map_assoc, whisker_left_app, functor.flip_map_app,
      tensor_functor_obj_map, limits.colimit.comp_cocone_point_unique_up_to_iso_inv]
    simp only [← map_tensor_comp_comp, category.id_comp, category.comp_id]
    dsimp; erw [category.comp_id]
  rw [ht]; clear ht t
  suffices mono (limits.colim_map η) by skip; infer_instance
  suffices ∀ i, mono (η.app i) by skip; apply mono_colim_map_of_mono
  intro i
  obtain ⟨α : Type u, _, e, -⟩ := exists_sigma_iso_of_index _ i; skip
  change mono ((tensor_functor.obj (of i.val)).map f)
  clear eX eY
  let eX :
    (tensor_functor.obj (of i.val)).obj X ≅ (tensor_functor.obj (∐ fun i : α => tunit)).obj X :=
    (tensor_functor.map_iso e.symm).app X
  let eY :
    (tensor_functor.obj (of i.val)).obj Y ≅ (tensor_functor.obj (∐ fun i : α => tunit)).obj Y :=
    (tensor_functor.map_iso e.symm).app Y
  have : (tensor_functor.obj (of ↥i.val)).map f = eX.hom ≫ (tensor_functor.obj _).map f ≫ eY.inv :=
    by
    dsimp [eX, eY]
    simpa only [← map_tensor_comp_comp, category.id_comp, category.comp_id, e.inv_hom_id]
  rw [this]; clear this
  suffices mono ((tensor_functor.obj (∐ fun i : α => tunit)).map f) by skip; infer_instance
  clear eX eY e i η FX FY D
  let eX : (tensor_functor.obj (∐ fun i : α => tunit)).obj X ≅ ∐ fun i : α => tensor tunit X :=
    preserves_colimit_iso (tensor_functor.flip.obj X) _ ≪≫
      limits.has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  let eY : (tensor_functor.obj (∐ fun i : α => tunit)).obj Y ≅ ∐ fun i : α => tensor tunit Y :=
    preserves_colimit_iso (tensor_functor.flip.obj Y) _ ≪≫
      limits.has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  have : (tensor_functor.obj (∐ fun i : α => tunit)).map f = eX.hom ≫ _ ≫ eY.inv
  rotate_left 2
  · apply limits.sigma.desc
    intro i; refine' _ ≫ limits.sigma.ι _ i
    exact map_tensor (𝟙 _) f
  · dsimp [eX, eY]
    apply (limits.is_colimit_of_preserves (tensor_functor.flip.obj X) _).hom_ext
    rotate_left
    · apply limits.colimit.is_colimit
    · infer_instance
    rintro ⟨j⟩
    slice_rhs 1 2 =>
      erw [(limits.is_colimit_of_preserves (tensor_functor.flip.obj X)
            (limits.colimit.is_colimit _)).fac]
    dsimp
    simp only [limits.has_colimit.iso_of_nat_iso_ι_hom, discrete.nat_iso_hom_app, category.assoc,
      limits.colimit.ι_desc, limits.cofan.mk_ι_app, limits.has_colimit.iso_of_nat_iso_ι_inv,
      discrete.nat_iso_inv_app, ι_preserves_colimits_iso_inv, functor.flip_obj_map,
      tensor_functor_map_app]
    dsimp; simp only [category.id_comp, ← map_tensor_comp_comp, category.comp_id]
  rw [this]; clear this
  let t := _; change mono (eX.hom ≫ t ≫ eY.inv)
  suffices mono t by skip; infer_instance
  suffices mono (map_tensor (𝟙 tunit) f) by apply AB4.cond; intro i; assumption
  clear eX eY
  let eX : tunit.tensor X ≅ X := tensor_unit_iso _ _ is_tensor_unit_tunit
  let eY : tunit.tensor Y ≅ Y := tensor_unit_iso _ _ is_tensor_unit_tunit
  have : map_tensor (𝟙 tunit) f = eX.hom ≫ f ≫ eY.inv := by
    simp [reassoc_of (tensor_unit_iso_naturality tunit X Y is_tensor_unit_tunit f)]
  rw [this]; infer_instance

end PreservesFiniteLimits

instance tensorFunctor_additive (A : AddCommGroupCat.{u}) : (tensorFunctor.obj A).Additive where

instance tensorFunctor_flip_additive (A : AddCommGroupCat.{u}) : (tensorFunctor.flip.obj A).Additive
    where

end AddCommGroupCat

