import Mathlib.CategoryTheory.Limits.Shapes.Products

#align_import for_mathlib.coprod_op

namespace CategoryTheory.Limits

open CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [HasCoproducts.{v} A]

open Opposite

noncomputable def opFan {α : Type v} (X : α → A) : Fan fun a => op (X a) :=
  Fan.mk (op <| ∐ X) fun b => (Sigma.ι _ _).op

noncomputable def isLimitOpFan {α : Type v} (X : α → A) : IsLimit (opFan X)
    where
  lift S :=
    let e : ∐ X ⟶ S.pt.unop := Sigma.desc fun b => (S.π.app (Discrete.mk b)).unop
    e.op
  fac := by
    intro S j
    dsimp [op_fan]
    rw [← op_comp, colimit.ι_desc]
    cases j
    rfl
  uniq := by
    intro S m hm
    dsimp
    rw [← m.op_unop]; congr 1
    apply colimit.hom_ext
    intro j
    simp only [colimit.ι_desc, cofan.mk_ι_app, ← hm]
    cases j
    rfl

end CategoryTheory.Limits

