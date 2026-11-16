import LiquidTensorExperiment.ForMathlib.ExactFilteredColimits
import LiquidTensorExperiment.ForMathlib.ColimPreservesColimits
import LiquidTensorExperiment.Condensed.Exact
import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.ForMathlib.ExactFunctor

#align_import condensed.ab5

open CategoryTheory

open CategoryTheory.Limits

namespace Condensed

universe u

variable {J : Type (u + 1)} [SmallCategory J] [IsFiltered J]

-- Axiom AB5 for `Condensed Ab`
theorem exact_colim_of_exact_of_isFiltered (F G H : J ⥤ Condensed.{u} Ab.{u + 1}) (η : F ⟶ G)
    (γ : G ⟶ H) :
    (∀ j, Exact (η.app j) (γ.app j)) → Exact (Limits.colimMap η) (Limits.colimMap γ) :=
  by
  intro h
  simp_rw [Condensed.exact_iff_extrDisc] at *; intro S
  let eF :
    (colimit F).val.obj (ExtrDisc_to_Profinite.op.obj (Opposite.op S)) ≅
      colimit (F ⋙ Condensed.evaluation _ S.val) :=
    CategoryTheory.preservesColimitIso (Condensed.evaluation _ S.val) _
  let eG :
    (colimit G).val.obj (ExtrDisc_to_Profinite.op.obj (Opposite.op S)) ≅
      colimit (G ⋙ Condensed.evaluation _ S.val) :=
    CategoryTheory.preservesColimitIso (Condensed.evaluation _ S.val) _
  let eH :
    (colimit H).val.obj (ExtrDisc_to_Profinite.op.obj (Opposite.op S)) ≅
      colimit (H ⋙ Condensed.evaluation _ S.val) :=
    CategoryTheory.preservesColimitIso (Condensed.evaluation _ S.val) _
  let t := _; let s := _; change exact s t
  let ηS : F ⋙ Condensed.evaluation _ S.val ⟶ G ⋙ Condensed.evaluation _ S.val := whisker_right η _
  let γS : G ⋙ Condensed.evaluation _ S.val ⟶ H ⋙ Condensed.evaluation _ S.val := whisker_right γ _
  have hs : s = eF.hom ≫ colim_map ηS ≫ eG.inv :=
    by
    rw [← Iso.inv_comp_eq]
    dsimp [s, eG, eF, ηS]
    ext1
    simp only [ι_preserves_colimits_iso_inv_assoc, evaluation_map, ι_colim_map_assoc,
      CategoryTheory.whiskerRight_app, ι_preserves_colimits_iso_inv]
    simp only [← NatTrans.comp_app, ← Sheaf.Hom.comp_val]; congr 2
    simp
  have ht : t = eG.hom ≫ colim_map γS ≫ eH.inv :=
    by
    rw [← Iso.inv_comp_eq]
    dsimp [t, eG, eH, γS]
    ext1
    simp only [ι_preserves_colimits_iso_inv_assoc, evaluation_map, ι_colim_map_assoc,
      CategoryTheory.whiskerRight_app, ι_preserves_colimits_iso_inv]
    simp only [← NatTrans.comp_app, ← Sheaf.Hom.comp_val]; congr 2
    simp
  rw [hs, ht]
  rw [exact_iso_comp, ← Category.assoc, exact_comp_iso]
  -- we have exact_comp_hom_inv_comp_iff, but missing exact_comp_inv_hom_comp_iff...
  rw [← Iso.symm_hom]
  nth_rw 2 [← Iso.symm_inv]
  rw [exact_comp_hom_inv_comp_iff]
  apply AddCommGroupCat.exact_colim_of_exact_of_isFiltered; intro j; apply h

instance aB5 : AB5 (Condensed.{u} Ab.{u + 1}) :=
  by
  constructor; intro J _ _; intro F G H f g h
  apply exact_colim_of_exact_of_is_filtered
  exact (NatTrans.exact_iff_forall.{u + 2, u + 1, u + 1} f g).1 h

-- I think it would be better to use ExtrDisc equiv as opposed to the constructor from AB5.
noncomputable instance preservesFiniteLimits (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim : (J ⥤ Condensed.{u} Ab.{u + 1}) ⥤ _) :=
  by
  apply Functor.preservesFiniteLimitsOfExact
  apply AB5.colimExact

noncomputable example (J : Type (u + 1)) [SmallCategory J] :
    PreservesColimits (colim : (J ⥤ Condensed.{u} Ab.{u + 1}) ⥤ _) := by infer_instance

--category_theory.limits.colim_preserves_colimits _ _
end Condensed

