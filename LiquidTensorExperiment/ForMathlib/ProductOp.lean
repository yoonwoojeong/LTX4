import Mathlib.CategoryTheory.Limits.Shapes.Products

#align_import for_mathlib.product_op

namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

open Opposite

noncomputable def opProductIso {α : Type v} (X : α → C) [HasProduct X]
    [HasCoproduct fun a => op (X a)] : op (∏ X) ≅ ∐ fun a => op (X a)
    where
  Hom :=
    Quiver.Hom.op
        (Pi.lift fun a => Quiver.Hom.unop (Sigma.ι (fun a => op (X a)) a) ≫ eqToHom (unop_op _)) ≫
      eqToHom (op_unop _)
  inv := Sigma.desc fun a => Quiver.Hom.op <| Pi.π _ _
  hom_inv_id' := by
    apply Quiver.Hom.unop_inj
    ext j
    simp only [eq_to_hom_refl, category.comp_id, unop_comp, Quiver.Hom.unop_op, category.assoc,
      limit.lift_π, fan.mk_π_app, unop_id_op, category.id_comp]
    rw [← unop_comp, colimit.ι_desc, cofan.mk_ι_app]
    erw [category.id_comp]
    rcases j with ⟨⟩
    rfl
  inv_hom_id' := by
    ext j
    simp only [eq_to_hom_refl, category.comp_id, colimit.ι_desc_assoc, cofan.mk_ι_app]
    rw [← op_comp, limit.lift_π, fan.mk_π_app]
    rcases j with ⟨⟩
    rfl

end CategoryTheory.Limits

