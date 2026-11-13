import LiquidTensorExperiment.BreenDeligne.ApplyPow

#align_import breen_deligne.eval_Pow_functor_nat_trans_compatibility

noncomputable section

universe v

namespace BreenDeligne

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits UniversalMap
  CategoryTheory.Preadditive

variable {A₁ A₂ : Type _} [Category.{v} A₁] [Category.{v} A₂] [Preadditive A₁] [Preadditive A₂]
  [HasFiniteBiproducts A₁] [HasFiniteBiproducts A₂] (BD : Data) (F₁ : A₁ ⥤ A₁) (F₂ : A₂ ⥤ A₂)
  {G G' : A₁ ⥤ A₂} [Functor.Additive G] [Functor.Additive G'] (τ : G ⟶ G') (e : F₁ ⋙ G ≅ G ⋙ F₂)
  (e' : F₁ ⋙ G' ≅ G' ⋙ F₂)

theorem evalPowFunctor_nat_trans_compatibility
    (h : e.hom ≫ whiskerRight τ F₂ = whiskerLeft F₁ τ ≫ e'.hom) (M : A₁) (n : FreeMat) :
    τ.app (((evalPowFunctor F₁).obj n).obj M) ≫ e'.hom.app _ ≫ F₂.map ((applyPow G' n).hom.app M) =
      e.hom.app _ ≫ F₂.map ((applyPow G n).hom.app M) ≫ ((evalPowFunctor F₂).obj n).map (τ.app M) :=
  by
  dsimp only [eval_Pow_functor]
  have h₁ := nat_trans.congr_app h ((Pow n).obj M)
  simp only [nat_trans.comp_app, whisker_right_app, whisker_left] at h₁ 
  slice_lhs 1 2 => erw [← h₁]
  simp only [category.assoc]
  erw [← F₂.map_comp, ← F₂.map_comp]
  congr 2
  apply apply_Pow_naturality

end BreenDeligne

