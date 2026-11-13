import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Kernels
import Mathlib.Algebra.Category.GroupCat.Abelian

#align_import for_mathlib.AddCommGroup.exact

universe u

open CategoryTheory

namespace AddCommGroupCat

variable {A B C : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B ⟶ C)

/-
Porting note: LTE's `AddCommGroup.exact_iff : exact f g ↔ f.range = g.ker` was later added to
mathlib with the same name and statement; in Lean 4 it is `AddCommGroupCat.exact_iff` in
`Mathlib.Algebra.Category.GroupCat.Abelian` (imported here), so it is not redeclared.
-/

theorem exact_iff' : Exact f g ↔ f ≫ g = 0 ∧ g.ker ≤ f.range :=
  by
  rw [exact_iff, le_antisymm_iff]
  refine' and_congr _ Iff.rfl
  constructor
  · intro h; ext x; exact h (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)
  · rintro h _ ⟨x, rfl⟩; exact AddMonoidHom.congr_fun h x

end AddCommGroupCat

