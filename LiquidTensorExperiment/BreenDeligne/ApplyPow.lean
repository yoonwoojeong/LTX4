import LiquidTensorExperiment.BreenDeligne.Eval1half
import LiquidTensorExperiment.ForMathlib.NatIsoMapHomologicalComplex

#align_import breen_deligne.applyPow

noncomputable section

universe v

namespace CategoryTheory

namespace Preadditive

open CategoryTheory CategoryTheory.Limits

variable {C D : Type _} [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] (F : C ⥤ D) [Functor.Additive F] (F' : C ⥤ D)
  [Functor.Additive F'] (τ : F ⟶ F') (n : ℕ)

@[simps]
def applyPow : pow n ⋙ F ≅ F ⋙ pow n :=
  NatIso.ofComponents
    (fun A =>
      { hom := biproduct.lift fun i => F.map (biproduct.π _ i)
        inv := biproduct.desc fun i => F.map (biproduct.ι _ i)
        hom_inv_id := by
          simpa only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum, biproduct.total] using
            F.map_id _
        inv_hom_id := by
          ext i j
          by_cases i = j
          · subst h
            dsimp
            simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
              biproduct.ι_π_self, ← F.map_comp, F.map_id]
          · dsimp
            simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id, ←
              F.map_comp, Limits.biproduct.ι_π_ne _ h, Functor.map_zero] })
    fun X Y f => by ext;
    simp only [Category.assoc, biproduct.lift_π, Functor.comp_map, Pow_map, biproduct.lift_map, ←
      F.map_comp, biproduct.map_π]

theorem applyPow_naturality (M : C) :
    τ.app ((pow n).obj M) ≫ (applyPow F' n).hom.app M =
      (applyPow F n).hom.app M ≫ (pow n).map (τ.app M) :=
  by
  rw [← cancel_epi ((apply_Pow F n).inv.app M)]
  slice_rhs 1 2 => rw [← NatTrans.comp_app, Iso.inv_hom_id]
  erw [Category.id_comp]
  apply Limits.biproduct.hom_ext
  intro j
  apply Limits.biproduct.hom_ext'
  intro i
  simp only [apply_Pow_inv_app, apply_Pow_hom_app, Category.assoc, biproduct.lift_π,
    biproduct.ι_desc_assoc, Pow_map, biproduct.map_π]
  erw [τ.naturality_assoc, ← F'.map_comp]
  by_cases i = j
  · subst h
    erw [biproduct.ι_π_self_assoc, biproduct.ι_π_self, F'.map_id, Category.comp_id]
  · erw [biproduct.ι_π_ne_assoc _ h, biproduct.ι_π_ne _ h, F'.map_zero, comp_zero, zero_comp]

open BreenDeligne BreenDeligne.UniversalMap

variable {A₁ A₂ : Type _} [Category.{v} A₁] [Category.{v} A₂] [Preadditive A₁] [Preadditive A₂]
  [HasFiniteBiproducts A₁] [HasFiniteBiproducts A₂] (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂) (G : A₁ ⥤ A₂)
  [Functor.Additive G]

def evalPowFunctorComp (e : F₁ ⋙ G ≅ G ⋙ F₂) :
    evalPowFunctor F₂ ⋙ (whiskeringLeft _ _ A₂).obj G ≅
      evalPowFunctor F₁ ⋙ (whiskeringRight A₁ _ _).obj G :=
  NatIso.ofComponents
    (fun n => by
      apply iso.symm
      refine' Functor.associator _ _ _ ≪≫ CategoryTheory.isoWhiskerLeft _ e ≪≫ _
      refine' (Functor.associator _ _ _).symm ≪≫ _ ≪≫ Functor.associator _ _ _
      refine' CategoryTheory.isoWhiskerRight (apply_Pow G n) _)
    fun n m f => by
    ext M
    dsimp only [whiskering_right, CategoryTheory.whiskeringLeft, Functor.associator, iso.symm, CategoryTheory.isoWhiskerLeft,
      CategoryTheory.isoWhiskerRight, Iso.trans, NatTrans.comp_app, Functor.mapIso, eval_Pow_functor,
      Functor.comp_map, whisker_right, whisker_left]
    repeat' erw [Category.id_comp]
    repeat' erw [Category.comp_id]
    rw [map_eval_Pow f F₁ G M, Category.assoc, ← congr_eval_Pow' f e.inv]
    simp only [← Category.assoc]
    congr 1
    revert f
    let φ₁ : BreenDeligne.UniversalMap n m →+ ((G ⋙ Pow n ⋙ F₂).obj M ⟶ F₂.obj ((Pow m ⋙ G).obj M)) :=
      { toFun := fun f => ((eval_Pow F₂) f).app (G.obj M) ≫ F₂.map ((apply_Pow G m).inv.app M)
        map_zero' := by simp only [eval_Pow_zero, NatTrans.app_zero, zero_comp]
        map_add' := fun f₁ f₂ => by simp only [map_add, NatTrans.app_add, add_comp] }
    let φ₂ : BreenDeligne.UniversalMap n m →+ ((G ⋙ Pow n ⋙ F₂).obj M ⟶ F₂.obj ((Pow m ⋙ G).obj M)) :=
      { toFun := fun f => F₂.map ((apply_Pow G n).inv.app M) ≫ ((eval_Pow' (G ⋙ F₂)) f).app M
        map_zero' := by simp only [map_zero, NatTrans.app_zero, comp_zero]
        map_add' := fun f₁ f₂ => by simp only [map_add, NatTrans.app_add, comp_add] }
    suffices φ₁ = φ₂ by
      intro f
      change φ₁ f = φ₂ f
      rw [this]
    ext f
    dsimp only [φ₁, φ₂]; clear φ₁ φ₂
    simp only [AddMonoidHom.coe_mk, eval_Pow'_of, eval_Pow_of, CategoryTheory.whiskerRight_app, ← F₂.map_comp,
      Functor.comp_map]
    congr 1
    erw [← cancel_mono ((apply_Pow G m).hom.app M), Category.assoc, ← NatTrans.comp_app,
      Iso.inv_hom_id, NatTrans.id_app, Category.comp_id]
    simp only [BasicUniversalMap.evalPow_app, apply_Pow_inv_app, apply_Pow_hom_app,
      Category.assoc]
    apply Limits.biproduct.hom_ext
    intro j
    apply Limits.biproduct.hom_ext'
    intro i
    simp only [biproduct.matrix_π, biproduct.ι_desc, Category.assoc, biproduct.lift_π,
      biproduct.ι_desc_assoc, ← G.map_comp, G.map_zsmul, G.map_id]

end Preadditive

end CategoryTheory

namespace BreenDeligne

namespace Data

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

open UniversalMap

variable {A₁ A₂ : Type _} [Category.{v} A₁] [Category.{v} A₂] (BD : Data) (F₁ : A₁ ⥤ A₁)
  (F₂ : A₂ ⥤ A₂) (G : A₁ ⥤ A₂) (e : F₁ ⋙ G ≅ G ⋙ F₂)

variable [Preadditive A₂]

instance additive_whiskeringLeft : Functor.Additive ((whiskeringLeft _ _ A₂).obj G) where

variable [Preadditive A₁] [Functor.Additive G]

instance additive_whiskeringRight : Functor.Additive ((whiskeringRight A₁ _ _).obj G) where

variable [HasFiniteBiproducts A₁] [HasFiniteBiproducts A₂]

def evalFunctor'Comp :
    evalFunctor' F₂ ⋙ ((whiskeringLeft _ _ A₂).obj G).mapHomologicalComplex _ ≅
      evalFunctor' F₁ ⋙ ((whiskeringRight A₁ _ _).obj G).mapHomologicalComplex _ :=
  CategoryTheory.NatIso.mapHomologicalComplex (evalPowFunctorComp F₁ F₂ G e) _

def evalFunctorComp :
    evalFunctor F₂ ⋙ (whiskeringLeft _ _ _).obj G ≅
      evalFunctor F₁ ⋙ (whiskeringRight A₁ _ _).obj (G.mapHomologicalComplex _) :=
  isoWhiskerRight (evalFunctor'Comp F₁ F₂ G e) HomologicalComplex.functorEval.flip

end Data

end BreenDeligne

