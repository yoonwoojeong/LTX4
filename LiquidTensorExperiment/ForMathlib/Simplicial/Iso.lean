import Mathlib.AlgebraicTopology.SimplicialObject

#align_import for_mathlib.simplicial.iso

open Opposite CategoryTheory CategoryTheory.Limits

open SimplexCategory

universe v u

namespace CategoryTheory

namespace Comma

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A]

variable {B : Type u₂} [Category.{v₂} B]

variable {T : Type u₃} [Category.{v₃} T]

variable {L : A ⥤ T} {R : B ⥤ T}

variable {X Y : Comma L R} (f : X ⟶ Y)

theorem isIso_of [IsIso f.left] [IsIso f.right] : IsIso f :=
  {
    out :=
      ⟨{  left := inv f.left
          right := inv f.right
          w' := by
            dsimp
            simp only [is_iso.eq_comp_inv, functor.map_inv, comma_morphism.w, is_iso.inv_comp_eq,
              category.assoc]
            simp },
        by constructor <;> ext <;> dsimp <;> simp only [is_iso.hom_inv_id, is_iso.inv_hom_id]⟩ }

end Comma

namespace SimplicialObject

variable {C : Type u} [Category.{v} C]

section

variable {X Y : SimplicialObject C} (f : X ⟶ Y)

theorem isIso_of [hf : ∀ n, IsIso (f.app n)] : IsIso f :=
  {
    out :=
      by
      let g : Y ⟶ X :=
        { app := fun n => inv (f.app n)
          naturality' := fun m n φ => _ }
      ·
        refine' ⟨g, _, _⟩ <;>
          · ext n
            simp only [nat_trans.id_app, nat_trans.comp_app, is_iso.hom_inv_id, is_iso.inv_hom_id]
      ·
        simp only [is_iso.inv_hom_id_assoc, nat_trans.naturality, is_iso.comp_inv_eq,
          category.assoc] }

end

attribute [local instance] CategoryTheory.SimplicialObject.isIso_of

namespace Augmented

variable {X Y : Augmented C} (f : X ⟶ Y)

theorem isIso_of [∀ n, IsIso (f.left.app n)] [IsIso f.right] : IsIso f :=
  CategoryTheory.Comma.isIso_of _

end Augmented

end SimplicialObject

end CategoryTheory

