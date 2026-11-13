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
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.op_induction' -/
theorem isIso_of_eval {F : Sheaf J D} {G : Cᵒᵖ ⥤ D} (γ : F ⟶ (presheafToSheaf _ _).obj G)
    (η : F.val ⟶ G) [∀ X : C, IsIso (η.app (op X))] (h : γ.val = η ≫ J.toSheafify _) : IsIso γ :=
  by
  haveI : is_iso (J.to_sheafify F.val) := grothendieck_topology.is_iso_to_sheafify J F.2
  have : γ.val = J.to_sheafify F.val ≫ J.sheafify_map η :=
    by
    rw [← is_iso.inv_comp_eq]
    apply J.sheafify_hom_ext; apply Sheaf.cond
    rw [← grothendieck_topology.to_sheafify_naturality, ← h]
    simp
  suffices is_iso ((Sheaf_to_presheaf _ _).map γ) by skip;
    apply is_iso_of_fully_faithful (Sheaf_to_presheaf J D)
  dsimp; rw [this]
  suffices is_iso (J.sheafify_map η) by skip; apply is_iso.comp_is_iso
  change is_iso ((Sheaf_to_presheaf _ _).map ((presheaf_to_Sheaf _ _).map η))
  have : is_iso η :=
    by
    apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
    intro X;
    run_tac
      tactic.op_induction';
    infer_instance
  infer_instance
  infer_instance

end CategoryTheory.Sheaf

