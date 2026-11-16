import LiquidTensorExperiment.BreenDeligne.Eval

#align_import breen_deligne.eval1half

noncomputable section

namespace BreenDeligne

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive

variable {A₁ A₂ A₃ : Type _} [Category A₁] [Preadditive A₁] [HasFiniteBiproducts A₁] [Category A₂]
  [Preadditive A₂]
  --[has_finite_biproducts A₂]
  [Category A₃]
  [Preadditive A₃]

--[has_finite_biproducts A₃]
namespace UniversalMap

variable {m n : ℕ} (f : UniversalMap m n)

def evalPow' (F : A₁ ⥤ A₂) : UniversalMap m n →+ (pow m ⋙ F ⟶ pow n ⋙ F) :=
  FreeAbelianGroup.lift fun g : BasicUniversalMap m n => whiskerRight g.evalPow F

@[simp]
theorem evalPow'_of (F : A₁ ⥤ A₂) (f : BasicUniversalMap m n) :
    evalPow' F (FreeAbelianGroup.of f) = whiskerRight f.evalPow F :=
  FreeAbelianGroup.lift.of _ _

theorem evalPow'_hcomp (F : A₁ ⥤ A₂) (H : A₂ ⥤ A₃) [H.Additive] :
    evalPow' F f ◫ 𝟙 H = evalPow' (F ⋙ H) f :=
  by
  revert f
  let φ : BreenDeligne.UniversalMap m n →+ ((Pow m ⋙ F) ⋙ H ⟶ (Pow n ⋙ F) ⋙ H) :=
    { toFun := fun f => whisker_right (eval_Pow' F f) H
      map_zero' := by ext; dsimp; simp only [map_zero, NatTrans.app_zero, Functor.map_zero]
      map_add' := fun f₁ f₂ => by ext; dsimp;
        simp only [map_add, NatTrans.app_add, Functor.map_add] }
  suffices φ = eval_Pow' (F ⋙ H) by
    intro f
    change 𝟙 _ ≫ φ f = _
    rw [Category.id_comp, this]
  ext1 f
  simp only [AddMonoidHom.coe_mk, eval_Pow'_of, CategoryTheory.whiskerRight_twice]

theorem map_evalPow' (F : A₁ ⥤ A₂) (H : A₂ ⥤ A₃) [H.Additive] (M₁ : A₁) :
    H.map ((evalPow' F f).app M₁) = (evalPow' (F ⋙ H) f).app M₁ := by
  simpa only [NatTrans.hcomp_id_app] using NatTrans.congr_app (f.evalPow'_hcomp F H) M₁

theorem map_evalPow (F : A₁ ⥤ A₁) (H : A₁ ⥤ A₂) [H.Additive] (M₁ : A₁) :
    H.map ((evalPow F f).app M₁) = (evalPow' (F ⋙ H) f).app M₁ :=
  map_evalPow' f F H M₁

@[reassoc]
theorem congr_evalPow' {F F' : A₁ ⥤ A₂} (φ : F ⟶ F') (M₁ : A₁) :
    (evalPow' F f).app M₁ ≫ φ.app ((pow n).obj M₁) =
      φ.app ((pow m).obj M₁) ≫ (evalPow' F' f).app M₁ :=
  by
  revert f
  let φ₁ : BreenDeligne.UniversalMap m n →+ ((Pow m ⋙ F).obj M₁ ⟶ (Pow n ⋙ F').obj M₁) :=
    { toFun := fun f => (eval_Pow' F f).app M₁ ≫ φ.app ((Pow n).obj M₁)
      map_zero' := by simp only [map_zero, NatTrans.app_zero, zero_comp]
      map_add' := fun f₁ f₂ => by simp only [map_add, NatTrans.app_add, add_comp] }
  let φ₂ : BreenDeligne.UniversalMap m n →+ ((Pow m ⋙ F).obj M₁ ⟶ (Pow n ⋙ F').obj M₁) :=
    { toFun := fun f => φ.app ((Pow m).obj M₁) ≫ (eval_Pow' F' f).app M₁
      map_zero' := by simp only [map_zero, NatTrans.app_zero, comp_zero]
      map_add' := fun f₁ f₂ => by simp only [map_add, NatTrans.app_add, comp_add] }
  suffices φ₁ = φ₂ by
    intro f
    change φ₁ f = φ₂ f
    rw [this]
  ext
  dsimp only [φ₁, φ₂]
  simp only [AddMonoidHom.coe_mk, eval_Pow'_of, CategoryTheory.whiskerRight_app, NatTrans.naturality]

end UniversalMap

end BreenDeligne

