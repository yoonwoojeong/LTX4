import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.Category.CompHaus.Projective

#align_import for_mathlib.CompHaus

namespace CompHaus

open CategoryTheory

noncomputable instance : Limits.PreservesLimits (forget CompHaus) := by
  apply limits.comp_preserves_limits compHausToTop (forget TopCat)

@[simp]
theorem coe_id (X : CompHaus) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
theorem coe_comp {A B C : CompHaus} (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g : A → C) = g ∘ f :=
  rfl

theorem coe_id_apply {X : CompHaus} (x : X) : (𝟙 X : X → X) x = x := by simp

theorem coe_comp_apply {X Y Z : CompHaus} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) :=
  by simp

end CompHaus

