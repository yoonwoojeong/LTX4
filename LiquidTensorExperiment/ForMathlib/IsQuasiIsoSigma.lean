import LiquidTensorExperiment.ForMathlib.Ab4

#align_import for_mathlib.isQuasiIsoSigma

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]

namespace HomotopyCategory

instance isQuasiIsoSigma [AB4 A] {α : Type v} (X : α → HomotopyCategory A (ComplexShape.up ℤ))
    (P : α → HomotopyCategory A (ComplexShape.up ℤ)) (π : ∀ a, P a ⟶ X a) [∀ a, IsQuasiIso (π a)] :
    IsQuasiIso (Sigma.desc fun a : α => π a ≫ Sigma.ι X a) :=
  by
  constructor; intro i
  let F := homology'Functor _ _ _
  let t := _; change is_iso (F.map t)
  let eP : F.obj (∐ fun a : α => P a) ≅ ∐ fun a => F.obj (P a) :=
    (CategoryTheory.Limits.isColimitOfPreserves F (colimit.isColimit _)).coconePointUniqueUpToIso
        (colimit.isColimit _) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso fun _ => iso.refl _)
  let eX : F.obj (∐ fun a : α => X a) ≅ ∐ fun a => F.obj (X a) :=
    (CategoryTheory.Limits.isColimitOfPreserves F (colimit.isColimit _)).coconePointUniqueUpToIso
        (colimit.isColimit _) ≪≫
      HasColimit.isoOfNatIso (Discrete.natIso fun _ => iso.refl _)
  let tt : (∐ fun a => F.obj (P a)) ⟶ ∐ fun a => F.obj (X a) :=
    sigma.desc fun a : α => F.map (π a) ≫ sigma.ι _ a
  suffices F.map t = eP.hom ≫ tt ≫ eX.inv by rw [this]; infer_instance
  dsimp [eP, tt, eX]
  apply (CategoryTheory.Limits.isColimitOfPreserves F (colimit.isColimit (Discrete.functor P))).hom_ext
  intro i
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι, Category.assoc,
    HasColimit.isoOfNatIso_hom_desc_assoc]
  erw [(CategoryTheory.Limits.isColimitOfPreserves F (colimit.isColimit (Discrete.functor P))).fac_assoc]
  rw [← F.map_comp, colimit.ι_desc]
  dsimp
  simp only [Functor.map_comp, colimit.ι_desc_assoc, Cocones.precompose_obj_ι, NatTrans.comp_app,
    Discrete.natIso_hom_app, Cofan.mk_ι_app, Category.assoc,
    HasColimit.isoOfNatIso_ι_inv_assoc, Discrete.natIso_inv_app,
    colimit.comp_coconePointUniqueUpToIso_inv, Functor.mapCocone_ι_app, colimit.cocone_ι]
  dsimp
  simp only [Category.id_comp]

end HomotopyCategory

