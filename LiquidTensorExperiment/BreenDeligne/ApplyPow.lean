import LiquidTensorExperiment.BreenDeligne.Eval1half
import LiquidTensorExperiment.ForMathlib.NatIsoMapHomologicalComplex

#align_import breen_deligne.apply_Pow

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
        hom_inv_id' := by
          simpa only [biproduct.lift_desc, ← F.map_comp, ← F.map_sum, biproduct.total] using
            F.map_id _
        inv_hom_id' := by
          ext i j
          by_cases i = j
          · subst h
            dsimp
            simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π, category.comp_id,
              biproduct.ι_π_self, ← F.map_comp, F.map_id]
          · dsimp
            simp only [biproduct.ι_desc_assoc, category.assoc, biproduct.lift_π, category.comp_id, ←
              F.map_comp, limits.biproduct.ι_π_ne _ h, functor.map_zero] })
    fun X Y f => by ext;
    simp only [category.assoc, biproduct.lift_π, functor.comp_map, Pow_map, biproduct.lift_map, ←
      F.map_comp, biproduct.map_π]

theorem applyPow_naturality (M : C) :
    τ.app ((pow n).obj M) ≫ (applyPow F' n).hom.app M =
      (applyPow F n).hom.app M ≫ (pow n).map (τ.app M) :=
  by
  rw [← cancel_epi ((apply_Pow F n).inv.app M)]
  slice_rhs 1 2 => rw [← nat_trans.comp_app, iso.inv_hom_id]
  erw [category.id_comp]
  apply limits.biproduct.hom_ext
  intro j
  apply limits.biproduct.hom_ext'
  intro i
  simp only [apply_Pow_inv_app, apply_Pow_hom_app, category.assoc, biproduct.lift_π,
    biproduct.ι_desc_assoc, Pow_map, biproduct.map_π]
  erw [τ.naturality_assoc, ← F'.map_comp]
  by_cases i = j
  · subst h
    erw [biproduct.ι_π_self_assoc, biproduct.ι_π_self, F'.map_id, category.comp_id]
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
      refine' functor.associator _ _ _ ≪≫ iso_whisker_left _ e ≪≫ _
      refine' (functor.associator _ _ _).symm ≪≫ _ ≪≫ functor.associator _ _ _
      refine' iso_whisker_right (apply_Pow G n) _)
    fun n m f => by
    ext M
    dsimp only [whiskering_right, whiskering_left, functor.associator, iso.symm, iso_whisker_left,
      iso_whisker_right, iso.trans, nat_trans.comp_app, functor.map_iso, eval_Pow_functor,
      functor.comp_map, whisker_right, whisker_left]
    repeat' erw [category.id_comp]
    repeat' erw [category.comp_id]
    rw [map_eval_Pow f F₁ G M, category.assoc, ← congr_eval_Pow' f e.inv]
    simp only [← category.assoc]
    congr 1
    revert f
    let φ₁ : universal_map n m →+ ((G ⋙ Pow n ⋙ F₂).obj M ⟶ F₂.obj ((Pow m ⋙ G).obj M)) :=
      { toFun := fun f => ((eval_Pow F₂) f).app (G.obj M) ≫ F₂.map ((apply_Pow G m).inv.app M)
        map_zero' := by simp only [eval_Pow_zero, nat_trans.app_zero, zero_comp]
        map_add' := fun f₁ f₂ => by simp only [map_add, nat_trans.app_add, add_comp] }
    let φ₂ : universal_map n m →+ ((G ⋙ Pow n ⋙ F₂).obj M ⟶ F₂.obj ((Pow m ⋙ G).obj M)) :=
      { toFun := fun f => F₂.map ((apply_Pow G n).inv.app M) ≫ ((eval_Pow' (G ⋙ F₂)) f).app M
        map_zero' := by simp only [map_zero, nat_trans.app_zero, comp_zero]
        map_add' := fun f₁ f₂ => by simp only [map_add, nat_trans.app_add, comp_add] }
    suffices φ₁ = φ₂ by
      intro f
      change φ₁ f = φ₂ f
      rw [this]
    ext f
    dsimp only [φ₁, φ₂]; clear φ₁ φ₂
    simp only [AddMonoidHom.coe_mk, eval_Pow'_of, eval_Pow_of, whisker_right_app, ← F₂.map_comp,
      functor.comp_map]
    congr 1
    erw [← cancel_mono ((apply_Pow G m).hom.app M), category.assoc, ← nat_trans.comp_app,
      iso.inv_hom_id, nat_trans.id_app, category.comp_id]
    simp only [basic_universal_map.eval_Pow_app, apply_Pow_inv_app, apply_Pow_hom_app,
      category.assoc]
    apply limits.biproduct.hom_ext
    intro j
    apply limits.biproduct.hom_ext'
    intro i
    simp only [biproduct.matrix_π, biproduct.ι_desc, category.assoc, biproduct.lift_π,
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

