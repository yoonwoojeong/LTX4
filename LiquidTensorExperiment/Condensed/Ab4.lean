import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Group.ULift
import LiquidTensorExperiment.ForMathlib.Ab4
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Pt
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Ab4
import LiquidTensorExperiment.Condensed.Extr.Equivalence

#align_import condensed.ab4

universe u

open CategoryTheory

open CategoryTheory.Limits

instance : HasColimits (ExtrSheafProd.{u} Ab.{u + 1}) :=
  hasColimits_of_hasColimits_createsColimits (condensedExtrSheafProdEquiv _).inverse

instance : HasLimits (ExtrSheafProd.{u} Ab.{u + 1}) :=
  hasLimits_of_hasLimits_createsLimits (condensedExtrSheafProdEquiv _).inverse

instance : HasColimitsOfSize.{u} Ab.{u + 1} :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} Ab.{u + 1}

open scoped Classical

instance {C : Type (u + 1)} [Category.{u} C] : AB4 (C ⥤ Ab.{u + 1}) :=
  by
  constructor
  intro α X Y f hf
  let t := _; change mono t
  rw [CategoryTheory.NatTrans.mono_iff_mono_app]
  intro c
  let eX : (∐ fun a : α => X a).obj c ≅ ∐ fun a : α => (X a).obj c :=
    (is_colimit_of_preserves ((evaluation _ _).obj c)
            (colimit.is_colimit _)).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  let eY : (∐ fun a : α => Y a).obj c ≅ ∐ fun a : α => (Y a).obj c :=
    (is_colimit_of_preserves ((evaluation _ _).obj c)
            (colimit.is_colimit _)).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  let tt : (∐ fun a : α => (X a).obj c) ⟶ ∐ fun a : α => (Y a).obj c :=
    sigma.desc fun a => (f a).app c ≫ sigma.ι _ a
  have : mono tt := by
    dsimp [tt]
    apply AB4.cond; intro a; specialize hf a
    rw [CategoryTheory.NatTrans.mono_iff_mono_app] at hf 
    apply hf
  suffices t.app c = eX.hom ≫ tt ≫ eY.inv by rw [this]; infer_instance
  dsimp [eX, tt, t, eY]
  apply (is_colimit_of_preserves ((evaluation _ _).obj c) (colimit.is_colimit _)).hom_ext
  intro a
  dsimp [is_colimit.cocone_point_unique_up_to_iso]
  simp only [category.assoc, ← nat_trans.comp_app, colimit.ι_desc]
  slice_rhs 0 1 =>
    erw [(is_colimit_of_preserves ((evaluation _ _).obj c) (colimit.is_colimit _)).fac]
  slice_rhs 0 1 => erw [colimit.ι_desc]
  dsimp
  simp only [category.id_comp, colimit.ι_desc, cofan.mk_ι_app, category.assoc,
    has_colimit.iso_of_nat_iso_ι_inv, discrete.nat_iso_inv_app, functor.map_cocone_ι_app,
    colimit.cocone_ι, evaluation_obj_map]
  dsimp; simp; infer_instance

noncomputable instance : CreatesLimits (extrSheafProdToPresheaf.{u} Ab.{u + 1}) :=
  by
  change creates_limits ((extrSheafExtrSheafProdEquiv _).inverse ⋙ Sheaf_to_presheaf _ _)
  apply (config := { instances := false }) CategoryTheory.compCreatesLimits
  infer_instance
  exact
    @Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u + 2, u, u + 1}
      ExtrDisc.{u} _ ExtrDisc.proetaleTopology Ab.{u + 1} _ _

instance : AB4 (ExtrSheafProd.{u} Ab.{u + 1}) :=
  aB4_of_preservesColimits_of_reflects_limits_of_aB4 (extrSheafProdToPresheaf _)

-- TODO: Prove a lemma about transporting AB4 across an equivalence.
instance : AB4 (Condensed.{u} Ab.{u + 1}) :=
  aB4_of_preservesColimits_of_reflects_limits_of_aB4
    (condensedExtrSheafProdEquiv.{u} Ab.{u + 1}).Functor

