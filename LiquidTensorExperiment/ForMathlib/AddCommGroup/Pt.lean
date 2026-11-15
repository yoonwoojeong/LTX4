import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Group.ULift

#align_import for_mathlib.AddCommGroup.pt

universe u

-- Porting note: `≫` and `⟶` are scoped notations in Lean 4
open CategoryTheory

def Ab.pt {X : Ab.{u}} (x : X) : AddCommGroupCat.of (ULift.{u} ℤ) ⟶ X
    where
  toFun a := zmultiplesAddHom _ x a.down
  map_zero' := by simp
  -- Porting note: `ULift.add_down` is `rfl`, `rw` no longer finds the pattern
  map_add' a b := (zmultiplesAddHom _ x).map_add a.down b.down

theorem Ab.pt_apply {X : Ab.{u}} (x : X) (n : ℤ) : Ab.pt x ⟨n⟩ = n • x := by
  -- Porting note: the unfolded structure application needs `rfl`
  simp only [Ab.pt, zmultiplesAddHom_apply, AddMonoidHom.coe_mk]
  rfl

theorem Ab.pt_apply' {X : Ab.{u}} (x : X) : Ab.pt x ⟨1⟩ = x := by rw [Ab.pt_apply, one_smul]

theorem Ab.pt_comp {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) : Ab.pt x ≫ f = Ab.pt (f x) := by
  ext ⟨n⟩
  -- Porting note: `(f ≫ g) x = g (f x)` holds by `rfl`, but `comp_apply` does not fire
  show f (Ab.pt x ⟨n⟩) = Ab.pt (f x) ⟨n⟩
  simp only [Ab.pt_apply, map_zsmul]

theorem Ab.apply_eq_pt_comp {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) : f x = (Ab.pt x ≫ f) ⟨1⟩ := by
  -- Porting note: `comp_apply` does not fire
  show f x = f (Ab.pt x ⟨1⟩)
  rw [Ab.pt_apply']

theorem Ab.apply_eq_zero {X Y : Ab.{u}} (f : X ⟶ Y) (x : X) : f x = 0 ↔ Ab.pt x ≫ f = 0 :=
  by
  constructor
  · intro h
    ext ⟨n⟩
    -- Porting note: `comp_apply` does not fire
    show f (Ab.pt x ⟨n⟩) = 0
    simp only [Ab.pt_apply, map_zsmul, h, smul_zero]
  · intro h
    rw [Ab.apply_eq_pt_comp, h, AddCommGroupCat.zero_apply]
