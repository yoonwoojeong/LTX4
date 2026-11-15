import Mathlib.CategoryTheory.Limits.Fubini

#align_import for_mathlib.limit_flip_comp_iso

open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

-- Porting note: the proofs in this definition need more than the default heartbeats in Lean 4
set_option maxHeartbeats 400000 in
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
            -- Porting note: `ext` is not recursive in Lean 4
            apply limit.hom_ext
            intro k
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
            -- Porting note: `ext` is not recursive in Lean 4
            apply limit.hom_ext
            intro j
            dsimp
            simp only [Category.id_comp, Category.assoc, limit.lift_π, limit.lift_map,
              Cones.postcompose_obj_π, NatTrans.comp_app]
            rw [← limit.w _ f]
            rfl }⟩
  hom_inv_id := by
    -- Porting note: `ext` is not recursive in Lean 4
    apply limit.hom_ext
    intro k
    apply limit.hom_ext
    intro j
    dsimp
    simp
  inv_hom_id := by
    apply limit.hom_ext
    intro j
    apply limit.hom_ext
    intro k
    dsimp
    simp

@[reassoc (attr := simp)]
theorem limitFlipCompLimIsoLimitCompLim'_hom_π_π {J : Type _} [Category J] [HasLimitsOfShape J C]
    {K : Type _} [Category K] [HasLimitsOfShape K C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (limitFlipCompLimIsoLimitCompLim' F).hom ≫ limit.π (F ⋙ lim) j ≫ limit.π (F.obj j) k =
      limit.π (F.flip ⋙ lim) k ≫ limit.π (F.flip.obj k) j :=
  by
  dsimp [CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim']
  simp

@[reassoc (attr := simp)]
theorem limitFlipCompLimIsoLimitCompLim'_inv_π_π {J : Type _} [Category J] [HasLimitsOfShape J C]
    {K : Type _} [Category K] [HasLimitsOfShape K C] (F : J ⥤ K ⥤ C) (j : K) (k : J) :
    (limitFlipCompLimIsoLimitCompLim' F).inv ≫ limit.π (F.flip ⋙ lim) j ≫ limit.π (F.flip.obj j) k =
      limit.π (F ⋙ lim) k ≫ limit.π (F.obj k) j :=
  by
  dsimp [CategoryTheory.Limits.limitFlipCompLimIsoLimitCompLim']
  simp

end CategoryTheory.Limits

