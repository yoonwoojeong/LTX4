import Mathlib.AlgebraicTopology.CechNerve

#align_import for_mathlib.cech

universe v u

open CategoryTheory Opposite

-- dedup with `cech_iso_zero` in `src/prop819.lean`
noncomputable def Arrow.cechNerveObj0 {C : Type u} [Category.{v} C] (F : Arrow C)
    [Limits.HasLimits.{v} C] : F.cechNerve.obj (op (SimplexCategory.mk 0)) ≅ F.left
    where
  hom := Limits.WidePullback.π _ 0
  inv :=
    Limits.WidePullback.lift F.Hom (fun _ => 𝟙 _) (by simp only [category.id_comp, forall_const])
  hom_inv_id' := by
    apply limits.wide_pullback.hom_ext
    · intro i
      simp only [limits.wide_pullback.lift_π, category.id_comp, category.comp_id, category.assoc]
      congr; dsimp; simp only [eq_iff_true_of_subsingleton]
    ·
      simp only [category.id_comp, category.assoc, limits.wide_pullback.lift_base,
        limits.wide_pullback.π_arrow]
  inv_hom_id' := Limits.WidePullback.lift_π _ _ _ _ 0

