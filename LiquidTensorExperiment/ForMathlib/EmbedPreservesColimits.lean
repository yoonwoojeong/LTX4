import LiquidTensorExperiment.ForMathlib.ComplexExtend
import LiquidTensorExperiment.ForMathlib.HomologicalComplexAbelian

#align_import for_mathlib.embed_preserves_colimits

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

variable {ι₁ ι₂ : Type _} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} (e : c₁.Embedding c₂)
  {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] {J : Type _} [Category J]
  [HasColimitsOfShape J C]

instance : PreservesColimitsOfShape J (HomologicalComplex.embed e : HomologicalComplex C c₁ ⥤ _) :=
  ⟨fun G =>
    by
    suffices
      ∀ i₂, preserves_colimit G (HomologicalComplex.embed e ⋙ HomologicalComplex.eval C c₂ i₂)
      by
      constructor
      intro s hs
      refine' HomologicalComplex.isColimitOfIsColimitEval _ _ _
      intro i₂
      haveI := this i₂
      change is_colimit ((HomologicalComplex.embed e ⋙ HomologicalComplex.eval C c₂ i₂).mapCocone s)
      apply is_colimit_of_preserves
      exact hs
    intro i₂
    by_cases hi₂ : ∃ i₁ : ι₁, i₂ = e.f i₁
    · let i₁ := hi₂.some
      have hi₂' : i₂ = e.f i₁ := hi₂.some_spec
      have α :=
        iso_whisker_left _ (HomologicalComplex.congrEval _ _ _ _ hi₂') ≪≫
          HomologicalComplex.embedCompEval C e i₁
      exact preserves_colimit_of_nat_iso _ α.symm
    · have α : HomologicalComplex.embed e ⋙ HomologicalComplex.eval C c₂ i₂ ≅ 0 :=
        by
        refine' is_zero.iso _ (is_zero_zero _)
        rw [is_zero.iff_id_eq_zero]
        ext X
        simp only [nat_trans.id_app, nat_trans.app_zero, ← is_zero.iff_id_eq_zero]
        dsimp [HomologicalComplex.embed, HomologicalComplex.Embed.obj]
        rw [e.r_none i₂ hi₂]
        apply is_zero_zero
      have : preserves_colimit G (0 : HomologicalComplex C c₁ ⥤ C) :=
        by
        constructor
        intro s hs
        exact
          { desc := fun s => 0
            fac := fun s j => by
              apply is_zero.eq_of_src
              exact (functor.is_zero_iff 0).mp (is_zero_zero _) _
            uniq := fun s m hm => by
              apply is_zero.eq_of_src
              exact (functor.is_zero_iff 0).mp (is_zero_zero _) _ }
      exact preserves_colimit_of_nat_iso _ α.symm⟩

