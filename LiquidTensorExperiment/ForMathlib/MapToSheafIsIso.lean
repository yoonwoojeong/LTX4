import Mathlib.CategoryTheory.Sites.Sheafification

#align_import for_mathlib.map_to_sheaf_is_iso

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory.Sheaf

universe w v u

-- All the classes we need for sheafification
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {D : Type w}
  [Category.{max v u} D] [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

theorem isIso_of_eval {F : Sheaf J D} {G : Cᵒᵖ ⥤ D} (γ : F ⟶ (presheafToSheaf _ _).obj G)
    (η : F.val ⟶ G) [∀ X : C, IsIso (η.app (op X))] (h : γ.val = η ≫ J.toSheafify _) : IsIso γ := by
  haveI : IsIso (J.toSheafify F.val) := GrothendieckTopology.isIso_toSheafify J F.2
  have : γ.val = J.toSheafify F.val ≫ J.sheafifyMap η := by
    rw [← IsIso.inv_comp_eq]
    apply J.sheafify_hom_ext
    apply Sheaf.cond
    rw [← GrothendieckTopology.toSheafify_naturality, ← h]
    simp
  suffices IsIso ((sheafToPresheaf _ _).map γ) by
    apply isIso_of_fully_faithful (sheafToPresheaf J D)
  dsimp
  rw [this]
  suffices IsIso (J.sheafifyMap η) by
    apply IsIso.comp_isIso
  change IsIso ((sheafToPresheaf _ _).map ((presheafToSheaf _ _).map η))
  have : IsIso η := by
    -- Porting note: Lean 4 version of `op_induction'`
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ η ?_
    intro X
    induction X using Opposite.rec' with
    | h X => infer_instance
  infer_instance

end CategoryTheory.Sheaf

