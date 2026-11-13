import Mathlib.CategoryTheory.Limits.Fubini

#align_import for_mathlib.limit_flip_comp_iso

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

noncomputable def limitFlipCompLimIsoLimitCompLim' {J : Type _} [Category J] [HasLimitsOfShape J C]
    {K : Type _} [Category K] [HasLimitsOfShape K C] (F : J ⥤ K ⥤ C) :
    limit (F.flip ⋙ lim) ≅ limit (F ⋙ lim)
    where
  hom :=
    limit.lift (F ⋙ lim)
      ⟨limit (F.flip ⋙ lim),
        { app := fun j =>
            limit.lift (F.obj j)
              ⟨limit (F.flip ⋙ lim),
                { app := fun k => limit.π _ k ≫ limit.π _ j
                  naturality := by
                    intro k1 k2 f
                    dsimp; simp only [Category.id_comp, Category.assoc]
                    rw [← limit.w _ f]
                    simp }⟩
          naturality := by
            intro j1 j2 f
            ext
            dsimp
            simp only [Category.id_comp, Category.assoc, limit.lift_π, limit.lift_map,
              Cones.postcompose_obj_π, NatTrans.comp_app]
            rw [← limit.w _ f]
            rfl }⟩
  inv :=
    limit.lift (F.flip ⋙ lim)
      ⟨limit (F ⋙ lim),
        { app := fun k =>
            limit.lift (F.flip.obj k)
              ⟨limit (F ⋙ lim),
                { app := fun j => limit.π _ j ≫ limit.π _ k
                  naturality := by
                    intro j1 j2 f
                    dsimp; simp only [Category.id_comp, Category.assoc]
                    rw [← limit.w _ f]
                    simp }⟩
          naturality := by
            intro k1 k2 f
            ext
            dsimp
            simp only [Category.id_comp, Category.assoc, limit.lift_π, limit.lift_map,
              Cones.postcompose_obj_π, NatTrans.comp_app]
            rw [← limit.w _ f]
            rfl }⟩
  hom_inv_id := by ext; dsimp; simp
  inv_hom_id := by ext; dsimp; simp

@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim'_hom_π_π {J : Type _} [Category J] [HasLimitsOfShape J C]
    {K : Type _} [Category K] [HasLimitsOfShape K C] (F : J ⥤ K ⥤ C) (j) (k) :
    (limitFlipCompLimIsoLimitCompLim' F).hom ≫ limit.π _ j ≫ limit.π _ k =
      limit.π _ k ≫ limit.π _ j :=
  by
  dsimp [CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim']
  simp

@[simp, reassoc]
theorem limitFlipCompLimIsoLimitCompLim'_inv_π_π {J : Type _} [Category J] [HasLimitsOfShape J C]
    {K : Type _} [Category K] [HasLimitsOfShape K C] (F : J ⥤ K ⥤ C) (j) (k) :
    (limitFlipCompLimIsoLimitCompLim' F).inv ≫ limit.π _ j ≫ limit.π _ k =
      limit.π _ k ≫ limit.π _ j :=
  by
  dsimp [CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim']
  simp

end CategoryTheory.Limits

