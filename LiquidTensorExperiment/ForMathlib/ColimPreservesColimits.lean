import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Tactic.ApplyFun

#align_import for_mathlib.colimPreservesColimits

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable (J : Type v) [SmallCategory J] (C : Type u) [Category.{v} C] [HasColimits C]

noncomputable def isColimitColimMapCocone {K : Type v} [SmallCategory K] (F : K ⥤ J ⥤ C)
    (T : Limits.Cocone F) (hT : Limits.IsColimit T) : Limits.IsColimit (Limits.colim.mapCocone T)
    where
  desc S :=
    colimit.desc T.pt
      ⟨S.pt,
        { app := fun j =>
            (isColimitOfPreserves ((evaluation J C).obj j) hT).desc
              ⟨S.pt,
                { app := fun k => by apply Limits.colimit.ι (F.obj k) j ≫ S.ι.app k
                  naturality := by
                    intro k₁ k₂ f
                    dsimp
                    simp [← S.w f] }⟩
          naturality := by
            intro j₁ j₂ f
            apply (Limits.isColimitOfPreserves ((evaluation J C).obj j₁) hT).hom_ext; intro k
            dsimp
            simp only [Category.comp_id]
            erw [(Limits.isColimitOfPreserves ((evaluation J C).obj j₁) hT).fac]
            rw [← NatTrans.naturality_assoc]
            erw [(Limits.isColimitOfPreserves ((evaluation J C).obj j₂) hT).fac]
            simp }⟩
  fac := by
    intro S k
    ext j; dsimp
    simp only [colimit.map_desc, colimit.ι_desc, Cocones.precompose_obj_ι, NatTrans.comp_app]
    apply (Limits.isColimitOfPreserves ((evaluation J C).obj j) hT).fac
  uniq := by
    intro S m hm
    ext j
    simp only [colimit.ι_desc]
    apply (Limits.isColimitOfPreserves ((evaluation J C).obj j) hT).hom_ext; intro k
    dsimp
    specialize hm k
    dsimp at hm 
    apply_fun fun e => colimit.ι _ j ≫ e at hm 
    simp only [colimit.ι_map_assoc] at hm 
    rw [hm]
    erw [(Limits.isColimitOfPreserves ((evaluation J C).obj j) hT).fac]

noncomputable instance colimPreservesColimits : PreservesColimits (colim : (J ⥤ C) ⥤ C) :=
  by
  constructor
  intro K hK; constructor
  intro F
  constructor
  intro T hT
  apply CategoryTheory.Limits.isColimitColimMapCocone
  assumption

end CategoryTheory.Limits

