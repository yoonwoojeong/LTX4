import LiquidTensorExperiment.ForMathlib.Ab4

#align_import for_mathlib.is_quasi_iso_sigma

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
    (is_colimit_of_preserves F (colimit.is_colimit _)).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  let eX : F.obj (∐ fun a : α => X a) ≅ ∐ fun a => F.obj (X a) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  let tt : (∐ fun a => F.obj (P a)) ⟶ ∐ fun a => F.obj (X a) :=
    sigma.desc fun a : α => F.map (π a) ≫ sigma.ι _ a
  suffices F.map t = eP.hom ≫ tt ≫ eX.inv by rw [this]; infer_instance
  dsimp [eP, tt, eX]
  apply (is_colimit_of_preserves F (colimit.is_colimit (discrete.functor P))).hom_ext
  intro i
  simp only [functor.map_cocone_ι_app, colimit.cocone_ι, category.assoc,
    has_colimit.iso_of_nat_iso_hom_desc_assoc]
  erw [(is_colimit_of_preserves F (colimit.is_colimit (discrete.functor P))).fac_assoc]
  rw [← F.map_comp, colimit.ι_desc]
  dsimp
  simp only [functor.map_comp, colimit.ι_desc_assoc, cocones.precompose_obj_ι, nat_trans.comp_app,
    discrete.nat_iso_hom_app, cofan.mk_ι_app, category.assoc,
    has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
    colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app, colimit.cocone_ι]
  dsimp
  simp only [category.id_comp]

end HomotopyCategory

