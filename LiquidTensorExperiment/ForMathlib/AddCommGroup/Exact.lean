import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Kernels

#align_import for_mathlib.AddCommGroup.exact

universe u

open CategoryTheory

namespace AddCommGroupCat

variable {A B C : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B ⟶ C)

theorem exact_iff : Exact f g ↔ f.range = g.ker :=
  by
  rw [Abelian.exact_iff' f g (kernel_is_limit _) (cokernel_is_colimit _)]
  constructor
  · rintro ⟨hfg, h⟩; ext x; constructor
    · rintro ⟨x, rfl⟩; exact AddMonoidHom.congr_fun hfg x
    · intro hx; rw [← QuotientAddGroup.eq_zero_iff]; exact AddMonoidHom.congr_fun h ⟨x, hx⟩
  · intro h
    constructor
    · ext x; show f x ∈ g.ker; rw [← h]; simp only [AddMonoidHom.mem_range, exists_apply_eq_apply]
    · ext ⟨x, hx⟩; dsimp [kernel_cone, cokernel_cocone]
      simpa only [comp_apply, AddSubgroup.coeSubtype, AddSubgroup.coe_mk,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, h] using hx

theorem exact_iff' : Exact f g ↔ f ≫ g = 0 ∧ g.ker ≤ f.range :=
  by
  rw [exact_iff, le_antisymm_iff]
  refine' and_congr _ Iff.rfl
  constructor
  · intro h; ext x; exact h (add_monoid_hom.mem_range.mpr ⟨x, rfl⟩)
  · rintro h _ ⟨x, rfl⟩; exact AddMonoidHom.congr_fun h x

end AddCommGroupCat

