import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Group.ULift

#align_import for_mathlib.AddCommGroup.pt

universe u

def Ab.pt {X : Ab.{u}} (x : X) : AddCommGroupCat.of (ULift.{u} ℤ) ⟶ X
    where
  toFun a := zmultiplesAddHom _ x a.down
  map_zero' := by simp
  map_add' a b := by rw [ULift.add_down, AddMonoidHom.map_add]

theorem Ab.pt_apply {X : Ab.{u}} (x : X) (n : ℤ) : Ab.pt x ⟨n⟩ = n • x := by
  simp only [Ab.pt, zmultiplesAddHom_apply, AddMonoidHom.coe_mk]

theorem Ab.pt_apply' {X : Ab.{u}} (x : X) : Ab.pt x ⟨1⟩ = x := by rw [Ab.pt_apply, one_smul]

theorem Ab.pt_comp {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) : Ab.pt x ≫ f = Ab.pt (f x) := by ext ⟨n⟩;
  simp only [Ab.pt_apply, CategoryTheory.comp_apply, map_zsmul]

theorem Ab.apply_eq_pt_comp {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) : f x = (Ab.pt x ≫ f) ⟨1⟩ := by
  rw [CategoryTheory.comp_apply, Ab.pt_apply']

theorem Ab.apply_eq_zero {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) : f x = 0 ↔ Ab.pt x ≫ f = 0 :=
  by
  constructor
  · intro h; ext ⟨n⟩
    simp only [CategoryTheory.comp_apply, AddCommGroupCat.zero_apply, Ab.pt_apply, map_zsmul, h,
      smul_zero]
  · intro h; rw [Ab.apply_eq_pt_comp, h, AddCommGroupCat.zero_apply]

