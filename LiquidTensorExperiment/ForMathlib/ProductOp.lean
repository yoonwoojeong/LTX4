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
  hom :=
    Quiver.Hom.op
        (Pi.lift fun a => Quiver.Hom.unop (Sigma.ι (fun a => op (X a)) a) ≫ eqToHom (unop_op _)) ≫
      eqToHom (op_unop _)
  inv := Sigma.desc fun a => Quiver.Hom.op <| Pi.π _ _
  hom_inv_id := by
    apply Quiver.Hom.unop_inj
    ext j
    simp only [CategoryTheory.eqToHom_refl, Category.comp_id, unop_comp, Quiver.Hom.unop_op, Category.assoc,
      limit.lift_π, Fan.mk_π_app, unop_id_op, Category.id_comp]
    rw [← unop_comp, colimit.ι_desc, Cofan.mk_ι_app]
    erw [Category.id_comp]
    rcases j with ⟨⟩
    rfl
  inv_hom_id := by
    ext j
    simp only [CategoryTheory.eqToHom_refl, Category.comp_id, colimit.ι_desc_assoc, Cofan.mk_ι_app]
    rw [← op_comp, limit.lift_π, Fan.mk_π_app]
    rcases j with ⟨⟩
    rfl

end CategoryTheory.Limits

