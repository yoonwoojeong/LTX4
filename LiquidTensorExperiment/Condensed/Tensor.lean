import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.Condensed.Extr.Equivalence
import LiquidTensorExperiment.Condensed.ShortExact
import LiquidTensorExperiment.Condensed.Acyclic
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Tensor

#align_import Condensed.tensor

noncomputable section

universe u

open scoped TensorProduct

open CategoryTheory

namespace ExtrSheafProd

@[simps obj map]
def tensorPresheaf (M : ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u + 1}) (A : Ab.{u + 1}) :
    ExtrDisc.{u}ᵒᵖ ⥤ Ab.{u + 1} :=
  M ⋙ AddCommGroupCat.tensorFunctor.flip.obj A

@[simps val]
def tensor (M : ExtrSheafProd.{u} Ab.{u + 1}) (A : Ab.{u + 1}) : ExtrSheafProd.{u} Ab.{u + 1}
    where
  val := tensorPresheaf M.val A
  cond := by
    intro α _ X; dsimp [ExtrSheafProd.tensorPresheaf, AddCommGroupCat.tensorFunctor]
    let e := _; change is_iso e
    have hq := M.cond _ X; dsimp at hq ; let q := _; change is_iso q at hq 
    have he : e = AddCommGroupCat.mapTensor q (𝟙 _) ≫ AddCommGroupCat.tensorPiComparison _ _ :=
      by
      ext1 j
      dsimp [AddCommGroupCat.tensorPiComparison]
      simp only [← AddCommGroupCat.mapTensor_comp_left, Limits.limit.lift_π, Limits.Fan.mk_π_app,
        Category.assoc]
    rw [he]; skip; apply (config := { instances := false }) IsIso.comp_isIso
    swap; infer_instance
    use AddCommGroupCat.mapTensor (inv q) (𝟙 _)
    constructor
    · rw [← AddCommGroupCat.mapTensor_comp_left, IsIso.hom_inv_id, AddCommGroupCat.mapTensor_id]
    · rw [← AddCommGroupCat.mapTensor_comp_left, IsIso.inv_hom_id, AddCommGroupCat.mapTensor_id]

-- tensor products commutes with direct sums.
@[simps val_app]
def mapTensor {M M' : ExtrSheafProd.{u} Ab.{u + 1}} {A A' : AddCommGroupCat.{u + 1}} (f : M ⟶ M')
    (g : A ⟶ A') : M.tensor A ⟶ M'.tensor A' :=
  ExtrSheafProd.Hom.mk <|
    { app := fun S => AddCommGroupCat.mapTensor (f.val.app _) g
      naturality := by
        intro X Y i
        dsimp [tensor, ExtrSheafProd.tensorPresheaf]
        simp only [← AddCommGroupCat.mapTensor_comp_comp, Category.id_comp, Category.comp_id,
          f.val.naturality] }

@[simp]
theorem mapTensor_id (M : ExtrSheafProd.{u} Ab.{u + 1}) (A : AddCommGroupCat.{u + 1}) :
    mapTensor (𝟙 M) (𝟙 A) = 𝟙 _ := by ext : 3; dsimp; simp

@[simp]
theorem mapTensor_comp {M M' M'' : ExtrSheafProd.{u} Ab.{u + 1}}
    {A A' A'' : AddCommGroupCat.{u + 1}} (f : M ⟶ M') (f' : M' ⟶ M'') (g : A ⟶ A') (g' : A' ⟶ A'') :
    mapTensor (f ≫ f') (g ≫ g') = mapTensor f g ≫ mapTensor f' g' := by ext : 3; dsimp; simp

-- Slow, so probably break into pieces
@[simps]
def tensorFunctor : ExtrSheafProd.{u} Ab.{u + 1} ⥤ Ab.{u + 1} ⥤ ExtrSheafProd.{u} Ab.{u + 1}
    where
  obj M :=
    { obj := fun A => M.tensor A
      map := fun A A' f => mapTensor (𝟙 _) f
      map_id := fun X => by simp
      map_comp := fun X Y Z f g =>
        by
        nth_rw 1 [← Category.id_comp (𝟙 M)]
        rw [map_tensor_comp] }
  map M N f :=
    { app := fun A => mapTensor f (𝟙 _)
      naturality := fun A B g => by
        dsimp
        simp only [← map_tensor_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    ext : 2
    simp
  map_comp M N L f g := by
    ext x : 2
    dsimp
    nth_rw 1 [← Category.comp_id (𝟙 x)]
    rw [map_tensor_comp]

@[simps]
instance homHasAdd {M N : ExtrSheafProd.{u} Ab.{u + 1}} : Add (M ⟶ N) :=
  ⟨fun f g => ⟨f.val + g.val⟩⟩

@[simps]
instance homHasZero {M N : ExtrSheafProd.{u} Ab.{u + 1}} : Zero (M ⟶ N) :=
  ⟨⟨0⟩⟩

@[simps]
instance homHasNeg {M N : ExtrSheafProd.{u} Ab.{u + 1}} : Neg (M ⟶ N) :=
  ⟨fun f => ⟨-f.val⟩⟩

@[simps]
instance homHasSub {M N : ExtrSheafProd.{u} Ab.{u + 1}} : Sub (M ⟶ N) :=
  ⟨fun f g => ⟨f.val - g.val⟩⟩

instance preadditive : Preadditive (ExtrSheafProd.{u} Ab.{u + 1})
    where
  homGroup P Q :=
    { (inferInstance : Add _), (inferInstance : Neg _), (inferInstance : Zero _),
      (inferInstance :
        Sub _) with
      add_assoc := fun f g h => by ext1; dsimp; rw [add_assoc]
      zero_add := fun f => by ext1; dsimp; rw [zero_add]
      add_zero := fun f => by ext1; dsimp; rw [add_zero]
      nsmul := fun n f => ⟨n • f.val⟩
      nsmul_zero := fun f => by ext1; dsimp; simp
      nsmul_succ := fun n f => by ext1; dsimp; exact succ_nsmul f.val n
      sub_eq_add_neg := fun f g => by ext1; dsimp; exact sub_eq_add_neg f.val g.val
      zsmul := fun n f => ⟨n • f.val⟩
      zsmul_zero' := fun f => by ext1; dsimp; simp
      zsmul_succ' := fun n f => by ext1; dsimp; rw [Nat.cast_succ, add_zsmul, one_zsmul, add_comm]
      zsmul_neg' := fun n f => by ext1; dsimp; simpa
      add_left_neg := fun f => by ext1; dsimp; simp
      add_comm := fun f g => by ext1; dsimp; rw [add_comm] }
  add_comp P Q R f f' g := by ext1; dsimp; simp
  comp_add P Q R f g g' := by ext1; dsimp; simp

def evaluation (S : ExtrDisc.{u}) : ExtrSheafProd.{u} Ab.{u + 1} ⥤ Ab.{u + 1} :=
  extrSheafProdToPresheaf _ ⋙ (evaluation _ _).obj (Opposite.op S)

instance evaluation_additive (S) : Functor.Additive (evaluation S) :=
  ⟨fun M N f g => rfl⟩

@[simps]
def halfInternalHom (A : AddCommGroupCat.{u + 1}) (M : ExtrSheafProd.{u} Ab.{u + 1}) :
    ExtrSheafProd.{u} Ab.{u + 1}
    where
  val :=
    { obj := fun S => AddCommGroupCat.of (A ⟶ M.val.obj S)
      map := fun X Y f => (preadditiveYoneda.flip.obj (Opposite.op A)).map <| M.val.map f
      map_id := by
        intro S
        dsimp; simpa
      map_comp := by
        intro R S T f g
        dsimp
        simp }
  cond := by
    intro α _ X; dsimp
    let t := _; change is_iso t
    have := M.cond α X; dsimp at this ; let e := _; change is_iso e at this ; skip
    let q :
      AddCommGroupCat.of (A ⟶ M.val.obj (Opposite.op (ExtrDisc.sigma X))) ≅
        AddCommGroupCat.of (A ⟶ ∏ fun i => M.val.obj (Opposite.op (X i))) :=
      (preadditive_yoneda.flip.obj (Opposite.op A)).mapIso (CategoryTheory.asIso e)
    let s :
      AddCommGroupCat.of (A ⟶ ∏ fun i => M.val.obj (Opposite.op (X i))) ⟶
        ∏ fun i => AddCommGroupCat.of (A ⟶ M.val.obj (Opposite.op (X i))) :=
      Limits.Pi.lift fun i => (preadditive_yoneda.flip.obj (Opposite.op A)).map (limits.pi.π _ i)
    have ht : t = q.hom ≫ s := by
      dsimp [t, q, s, e]; ext1
      simp only [Limits.limit.lift_π, Limits.Fan.mk_π_app, Category.assoc]
      rw [← NatTrans.comp_app, ← Functor.map_comp, Limits.limit.lift_π]
      rfl
    rw [ht]; clear ht
    suffices is_iso s by skip; apply IsIso.comp_isIso
    -- Now we need to show that `Hom(A,(Π i, X i)) = Π i, Hom(A,X i)`.
    apply AddCommGroupCat.isIso_homProductComparison.{u, u + 1}

def tensorUncurry {A : AddCommGroupCat.{u + 1}} {M N : ExtrSheafProd.{u} Ab.{u + 1}}
    (e : M ⟶ halfInternalHom A N) : tensor M A ⟶ N :=
  ExtrSheafProd.Hom.mk <|
    { app := fun S => AddCommGroupCat.tensorUncurry <| e.val.app _
      naturality := by
        intro X Y f
        erw [← AddCommGroupCat.tensorUncurry_comp_curry]
        apply (AddCommGroupCat.tensorCurryEquiv _ _ _).injective
        erw [(AddCommGroupCat.tensorCurryEquiv _ _ _).apply_symm_apply]
        dsimp [AddCommGroupCat.tensorCurryEquiv]
        erw [AddCommGroupCat.tensorCurry_uncurry_comp, ← NatTrans.naturality, ←
          AddCommGroupCat.tensorCurryEquiv_apply, ← AddCommGroupCat.tensorCurryEquiv_symm_apply,
          (AddCommGroupCat.tensorCurryEquiv _ _ _).apply_symm_apply] }

def tensorCurry {A : AddCommGroupCat.{u + 1}} {M N : ExtrSheafProd.{u} Ab.{u + 1}}
    (e : M.tensor A ⟶ N) : M ⟶ halfInternalHom A N :=
  ExtrSheafProd.Hom.mk <|
    { app := fun S => AddCommGroupCat.tensorCurry <| e.val.app _
      naturality := by
        intro X Y f
        dsimp [half_internal_hom]
        erw [← AddCommGroupCat.tensorCurry_uncurry_comp]
        apply (AddCommGroupCat.tensorCurryEquiv _ _ _).symm.injective
        simp_rw [← AddCommGroupCat.tensorCurryEquiv_apply]
        rw [(AddCommGroupCat.tensorCurryEquiv _ _ _).symm_apply_apply]
        rw [← AddCommGroupCat.tensorCurryEquiv_symm_apply]
        rw [(AddCommGroupCat.tensorCurryEquiv _ _ _).symm_apply_apply]
        dsimp
        rw [AddCommGroupCat.tensorUncurry_comp_curry, ← NatTrans.naturality]
        rfl }

theorem tensorCurry_uncurry {A : AddCommGroupCat.{u + 1}} {M N : ExtrSheafProd.{u} Ab.{u + 1}}
    (e : M ⟶ halfInternalHom A N) : tensorCurry (tensorUncurry e) = e :=
  by
  ext S : 3
  dsimp [tensor_curry, tensor_uncurry]
  simp

theorem tensorUncurry_curry {A : AddCommGroupCat.{u + 1}} {M N : ExtrSheafProd.{u} Ab.{u + 1}}
    (e : M.tensor A ⟶ N) : tensorUncurry (tensorCurry e) = e :=
  by
  ext S : 3
  dsimp [tensor_curry, tensor_uncurry]
  simp

instance tensorFunctor_additive (M : ExtrSheafProd.{u} Ab.{u + 1}) : (tensorFunctor.obj M).Additive
    where

instance tensorFunctor_flip_additive (A : Ab.{u + 1}) : (tensorFunctor.flip.obj A).Additive where

end ExtrSheafProd

namespace ExtrSheaf

def tensor (M : ExtrSheaf.{u} Ab.{u + 1}) (A : AddCommGroupCat.{u + 1}) :
    ExtrSheaf.{u} Ab.{u + 1} :=
  (extrSheafExtrSheafProdEquiv _).inverse.obj <|
    ((extrSheafExtrSheafProdEquiv _).Functor.obj M).tensor A

@[simp]
theorem tensor_val_obj (M : ExtrSheaf.{u} Ab.{u + 1}) (A : AddCommGroupCat.{u + 1}) (T) :
    (M.tensor A).val.obj T = (M.val.obj T).tensor A :=
  rfl

def halfInternalHom (A : AddCommGroupCat.{u + 1}) (M : ExtrSheaf.{u} Ab.{u + 1}) :
    ExtrSheaf.{u} Ab.{u + 1} :=
  (extrSheafExtrSheafProdEquiv _).inverse.obj <|
    ((extrSheafExtrSheafProdEquiv _).Functor.obj M).halfInternalHom A

@[simp]
theorem halfInternalHom_val_obj (A : AddCommGroupCat.{u + 1}) (M : ExtrSheaf.{u} Ab.{u + 1}) (T) :
    (M.halfInternalHom A).val.obj T = AddCommGroupCat.of (A ⟶ M.val.obj T) :=
  rfl

def tensorCurry {A : AddCommGroupCat.{u + 1}} {M N : ExtrSheaf.{u} Ab.{u + 1}}
    (e : M.tensor A ⟶ N) : M ⟶ N.halfInternalHom A :=
  ⟨(ExtrSheafProd.tensorCurry <| (extrSheafExtrSheafProdEquiv _).Functor.map e).val⟩

def tensorUncurry {A : AddCommGroupCat.{u + 1}} {M N : ExtrSheaf.{u} Ab.{u + 1}}
    (e : M ⟶ N.halfInternalHom A) : M.tensor A ⟶ N :=
  ⟨(ExtrSheafProd.tensorUncurry <| (extrSheafExtrSheafProdEquiv _).Functor.map e).val⟩

@[simps val]
def mapTensor {M M' : ExtrSheaf.{u} Ab.{u + 1}} {A A' : AddCommGroupCat.{u + 1}} (f : M ⟶ M')
    (g : A ⟶ A') : M.tensor A ⟶ M'.tensor A' :=
  ⟨((ExtrSheafProd.mapTensor <| (extrSheafExtrSheafProdEquiv _).Functor.map f) g).val⟩

@[simp]
theorem mapTensor_id (M : ExtrSheaf.{u} Ab.{u + 1}) (A : AddCommGroupCat.{u + 1}) :
    mapTensor (𝟙 M) (𝟙 A) = 𝟙 _ := by ext : 1; dsimp; simpa

@[simp]
theorem mapTensor_comp {M M' M'' : ExtrSheaf.{u} Ab.{u + 1}} {A A' A'' : AddCommGroupCat.{u + 1}}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : A ⟶ A') (g' : A' ⟶ A'') :
    mapTensor (f ≫ f') (g ≫ g') = mapTensor f g ≫ mapTensor f' g' := by ext : 1; dsimp; simp

@[simps]
def tensorFunctor : ExtrSheaf.{u} Ab.{u + 1} ⥤ Ab.{u + 1} ⥤ ExtrSheaf.{u} Ab.{u + 1}
    where
  obj M :=
    { obj := fun A => M.tensor A
      map := fun A A' f => mapTensor (𝟙 _) f
      map_id := fun X => by simp
      map_comp := fun X Y Z f g =>
        by
        nth_rw 1 [← Category.id_comp (𝟙 M)]
        rw [map_tensor_comp] }
  map M N f :=
    { app := fun A => mapTensor f (𝟙 _)
      naturality := fun A B g => by
        dsimp
        simp only [← map_tensor_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    ext : 2
    simp
  map_comp M N L f g := by
    ext x : 2
    dsimp
    nth_rw 1 [← Category.comp_id (𝟙 x)]
    rw [map_tensor_comp]

instance createsColimits :
    CreatesColimits (sheafToPresheaf ExtrDisc.proetaleTopology.{u} Ab.{u + 1}) :=
  show CreatesColimits ((extrSheafExtrSheafProdEquiv _).Functor ⋙ extrSheafProdToPresheaf _) from
    inferInstance

instance preservesColimitsTensorObj (M : ExtrSheaf.{u} Ab.{u + 1}) :
    Limits.PreservesColimits (tensorFunctor.obj M) :=
  by
  constructor; intro J _; constructor; intro F; constructor; intro S hS
  let T := _; change Limits.IsColimit T
  apply Limits.isColimitOfReflects (Sheaf_to_presheaf ExtrDisc.proetaleTopology.{u} Ab.{u + 1})
  apply Limits.evaluationJointlyReflectsColimits
  intro Q
  change Limits.IsColimit ((AddCommGroup.tensor_functor.obj (M.val.obj Q)).mapCocone S)
  apply Limits.isColimitOfPreserves
  exact hS

example (α : Type (u + 1)) (N : ExtrSheaf.{u} Ab.{u + 1}) :
    Limits.PreservesColimitsOfShape (Discrete α) (tensorFunctor.obj N) :=
  inferInstance

instance tensorFunctor_additive (M : ExtrSheaf.{u} Ab.{u + 1}) : (tensorFunctor.obj M).Additive
    where

end ExtrSheaf

namespace Condensed

def tensor (M : Condensed.{u} Ab.{u + 1}) (A : Ab.{u + 1}) : Condensed.{u} Ab.{u + 1} :=
  (condensedExtrSheafEquiv _).Functor.obj (((condensedExtrSheafEquiv _).inverse.obj M).tensor A)

def mapTensor {M M' : Condensed.{u} Ab.{u + 1}} {A A' : Ab.{u + 1}} (f : M ⟶ M') (g : A ⟶ A') :
    M.tensor A ⟶ M'.tensor A' :=
  (condensedExtrSheafEquiv _).Functor.map <|
    ExtrSheaf.mapTensor ((condensedExtrSheafEquiv _).inverse.map f) g

@[simp]
theorem mapTensor_id (M : Condensed.{u} Ab.{u + 1}) (A : AddCommGroupCat.{u + 1}) :
    mapTensor (𝟙 M) (𝟙 A) = 𝟙 _ := by dsimp [map_tensor]; simpa

@[simp]
theorem mapTensor_comp {M M' M'' : Condensed.{u} Ab.{u + 1}} {A A' A'' : AddCommGroupCat.{u + 1}}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : A ⟶ A') (g' : A' ⟶ A'') :
    mapTensor (f ≫ f') (g ≫ g') = mapTensor f g ≫ mapTensor f' g' := by dsimp [map_tensor]; simp

/-- This is the functor that sends `A : Ab` to `M ⊗ A`,
where `M` is a condensed abelian group, functorial in both `M` and `A`. -/
def tensorFunctor : Condensed.{u} Ab.{u + 1} ⥤ Ab.{u + 1} ⥤ Condensed.{u} Ab.{u + 1}
    where
  obj M :=
    { obj := fun A => M.tensor A
      map := fun A A' f => mapTensor (𝟙 _) f
      map_id := fun X => by simp
      map_comp := fun X Y Z f g =>
        by
        nth_rw 1 [← Category.id_comp (𝟙 M)]
        rw [map_tensor_comp] }
  map M N f :=
    { app := fun A => mapTensor f (𝟙 _)
      naturality := fun A B g => by
        dsimp
        simp only [← map_tensor_comp, Category.id_comp, Category.comp_id] }
  map_id M := by
    ext : 2
    simp
  map_comp M N L f g := by
    ext x : 2
    dsimp
    nth_rw 1 [← Category.comp_id (𝟙 x)]
    rw [map_tensor_comp]

/-
/-- Restrincting to `ExtrDisc` works as expeceted. -/
def tensor_functor_conj_iso :
  (Condensed_ExtrSheaf_equiv Ab.{u+1}).functor ⋙
  ((whiskering_right _ _ _).obj $ ((whiskering_right _ _ _).obj
    (Condensed_ExtrSheaf_equiv Ab.{u+1}).inverse)).obj tensor_functor ≅
  ExtrSheaf.tensor_functor :=
nat_iso.of_components
(λ X, begin
  dsimp [tensor_functor],
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp only [equivalence.fun_inv_map, equivalence.equivalence_mk'_counit,
    equivalence.equivalence_mk'_counit_inv, functor.map_comp, nat_trans.comp_app,
    category.assoc, iso.inv_hom_id_app_assoc, category.id_comp,
    nat_iso.cancel_nat_iso_hom_left],
  rw [← nat_trans.comp_app, ← functor.map_comp, ← nat_trans.comp_app],
  have : (Condensed_ExtrSheafProd_equiv Ab).counit_iso.inv.app Y ≫
    (Condensed_ExtrSheafProd_equiv Ab).counit_iso.hom.app Y = 𝟙 _,
  { rw [← nat_trans.comp_app, iso.inv_hom_id], refl },
  rw this,
  simp only [nat_trans.comp_app],
  dsimp,
  simp only [category_theory.functor.map_id, nat_trans.id_app, category.comp_id],
end

def tensor_functor_conj_iso' :
  tensor_functor ⋙ (whiskering_right _ _ _).obj
  (Condensed_ExtrSheafProd_equiv _).functor ≅
  (Condensed_ExtrSheafProd_equiv _).functor ⋙ ExtrSheafProd.tensor_functor :=
nat_iso.of_components
(λ X, begin
  dsimp [tensor_functor],
  refine functor.associator _ _ _ ≪≫ _,
  refine _ ≪≫ functor.right_unitor _,
  refine ((whiskering_left _ _ _).obj _).map_iso _,
  refine (Condensed_ExtrSheafProd_equiv _).counit_iso,
end)
begin
  intros X Y f, ext : 2,
  dsimp [tensor_functor],
  simp, dsimp, simp,
end
-/
def tensorIso (M : Condensed.{u} Ab.{u + 1}) (A : Ab.{u + 1}) :
    (condensedExtrSheafEquiv _).inverse.obj (M.tensor A) ≅
      ((condensedExtrSheafEquiv _).inverse.obj M).tensor A :=
  ((condensedExtrSheafEquiv _).unitIso.app _).symm

/-- The tensor product behaves in the naive way when evaluated
on extremally disconnected sets. -/
def tensorEvalIso (M : Condensed.{u} Ab.{u + 1}) (A : Ab.{u + 1}) (S : ExtrDisc.{u}) :
    (tensor M A).val.obj (Opposite.op S.val) ≅ (M.val.obj (Opposite.op S.val)).tensor A :=
  ((sheafToPresheaf _ _).mapIso (M.tensorIso A)).app (Opposite.op S)

def halfInternalHom (A : AddCommGroupCat.{u + 1}) (M : Condensed.{u} Ab.{u + 1}) :
    Condensed.{u} Ab.{u + 1} :=
  (condensedExtrSheafEquiv _).Functor.obj <|
    ExtrSheaf.halfInternalHom A ((condensedExtrSheafEquiv _).inverse.obj M)

def halfInternalHomIso (A : AddCommGroupCat.{u + 1}) (M : Condensed.{u} Ab.{u + 1}) :
    (condensedExtrSheafEquiv _).inverse.obj (halfInternalHom A M) ≅
      ExtrSheaf.halfInternalHom A ((condensedExtrSheafEquiv _).inverse.obj M) :=
  ((condensedExtrSheafEquiv _).unitIso.app _).symm

def halfInternalHomEvalIso (A : AddCommGroupCat.{u + 1}) (M : Condensed.{u} Ab.{u + 1})
    (S : ExtrDisc.{u}) :
    (halfInternalHom A M).val.obj (Opposite.op S.val) ≅
      AddCommGroupCat.of (A ⟶ M.val.obj (Opposite.op S.val)) :=
  ((sheafToPresheaf _ _).mapIso (halfInternalHomIso A M)).app (Opposite.op S)

def tensorUncurry {A : AddCommGroupCat.{u + 1}} {M N : Condensed.{u} Ab.{u + 1}}
    (e : M ⟶ halfInternalHom A N) : tensor M A ⟶ N :=
  (condensedExtrSheafEquiv _).Functor.map
      (ExtrSheaf.tensorUncurry <|
        (condensedExtrSheafEquiv Ab).inverse.map e ≫ (halfInternalHomIso _ _).hom) ≫
    ((condensedExtrSheafEquiv _).counitIso.app N).hom

theorem tensorUncurry_eq {A : AddCommGroupCat.{u + 1}} {M N : Condensed.{u} Ab.{u + 1}}
    (e : M ⟶ halfInternalHom A N) :
    (condensedExtrSheafEquiv _).inverse.map (tensorUncurry e) =
      (tensorIso _ _).hom ≫
        ExtrSheaf.tensorUncurry
          ((condensedExtrSheafEquiv _).inverse.map e ≫ (halfInternalHomIso _ _).hom) :=
  by
  dsimp [tensor_uncurry, Condensed.halfInternalHomIso, tensor_iso]
  simp

def tensorCurry {A : AddCommGroupCat.{u + 1}} {M N : Condensed.{u} Ab.{u + 1}}
    (e : M.tensor A ⟶ N) : M ⟶ halfInternalHom A N :=
  ((condensedExtrSheafEquiv _).counitIso.app _).inv ≫
    (condensedExtrSheafEquiv _).Functor.map
      (ExtrSheaf.tensorCurry <| (tensorIso M A).inv ≫ (condensedExtrSheafEquiv Ab).inverse.map e)

theorem tensorCurry_eq {A : AddCommGroupCat.{u + 1}} {M N : Condensed.{u} Ab.{u + 1}}
    (e : M.tensor A ⟶ N) :
    (condensedExtrSheafEquiv _).inverse.map (tensorCurry e) =
      ExtrSheaf.tensorCurry ((tensorIso _ _).inv ≫ (condensedExtrSheafEquiv Ab).inverse.map e) ≫
        (halfInternalHomIso _ _).inv :=
  by
  rw [Iso.eq_comp_inv]
  dsimp [tensor_curry, Condensed.halfInternalHomIso, tensor_iso]
  simp only [Functor.map_comp, Equivalence.fun_inv_map, Equivalence.Equivalence_mk'_counit,
    Category.assoc, Iso.inv_hom_id_app]
  simp; dsimp; simp
  --dsimp,
  --simp only [category.comp_id],
  suffices
    (condensedExtrSheafEquiv Ab).inverse.map ((condensedExtrSheafEquiv Ab).counitIso.inv.app M) ≫
        (condensedExtrSheafEquiv Ab).unitIso.inv.app ((condensedExtrSheafEquiv Ab).inverse.obj M) =
      𝟙 _
    by rw [reassoc_of this]
  simpa

def tensorFunctorIsoExtrSheafTensorFunctor (M : Condensed.{u} Ab.{u + 1}) :
    tensorFunctor.obj M ≅
      ExtrSheaf.tensorFunctor.obj ((condensedExtrSheafEquiv _).inverse.obj M) ⋙
        (condensedExtrSheafEquiv _).Functor :=
  by rfl

instance (M : Condensed.{u} Ab.{u + 1}) : Limits.PreservesColimits (tensorFunctor.obj M) :=
  Limits.preservesColimitsOfNatIso (tensorFunctorIsoExtrSheafTensorFunctor M).symm

example (α : Type (u + 1)) (M : Condensed.{u} Ab.{u + 1}) :
    Limits.PreservesColimitsOfShape (Discrete α) (tensorFunctor.obj M) :=
  inferInstance

/- this is an assumption in `main_lemma'` in `breen_deligne/main.lean` and it is
used in `condensed/bd_lemma.lean` -/
instance tensorFunctor_additive (A : Condensed.{u} Ab.{u + 1}) : (tensorFunctor.obj A).Additive
    where map_add' := by
    intro A B f g
    dsimp [tensor_functor, map_tensor]
    rw [← Functor.map_add]; congr 1; ext S : 3
    dsimp only [ExtrSheaf.mapTensor, ExtrSheafProd.mapTensor]
    simp only [CategoryTheory.Functor.map_id]
    erw [NatTrans.id_app]
    rw [← AddCommGroupCat.tensorFunctor_obj_map, Functor.map_add]
    rfl

end Condensed

