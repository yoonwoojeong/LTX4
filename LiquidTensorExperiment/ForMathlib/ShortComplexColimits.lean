import LiquidTensorExperiment.ForMathlib.ShortComplexProjections
import LiquidTensorExperiment.ForMathlib.HomologicalComplexAbelian
import LiquidTensorExperiment.ForMathlib.HomologyMapDatum
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.FunctorCategory
import LiquidTensorExperiment.ForMathlib.ShortComplexFunctorCategory

#align_import for_mathlib.short_complex_colimits

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

open scoped ZeroObject

universe v

namespace ShortComplex

section Construction

variable {C : Type _} [Category C] [HasZeroMorphisms C]

variable {J : Type _} [Category J] (F : J ⥤ ShortComplex C) [HasColimit (F ⋙ π₁)]
  [HasColimit (F ⋙ π₂)] [HasColimit (F ⋙ π₃)]

@[simps]
def ColimitCocone.cocone : Cocone F
    where
  pt :=
    mk (colimMap (𝟙 F ◫ φ₁₂)) (colimMap (𝟙 F ◫ φ₂₃))
      (by
        ext
        dsimp
        simp only [ι_colim_map_assoc, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app, π₂_map,
          ι_colim_map, φ₂₃_app, π₃_map, assoc, comp_zero]
        erw [composable_morphisms.id_τ₂, id_comp, (F.obj j).zero_assoc, zero_comp])
  ι :=
    { app := fun j =>
        by
        refine' ⟨colimit.ι (F ⋙ π₁) j, colimit.ι (F ⋙ π₂) j, colimit.ι (F ⋙ π₃) j, _, _⟩
        · dsimp
          simp only [ι_colim_map, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app, π₂_map, assoc]
          erw [composable_morphisms.id_τ₂, id_comp]
        · dsimp
          simp only [ι_colim_map, nat_trans.hcomp_app, φ₂₃_app, nat_trans.id_app, π₃_map, assoc]
          erw [composable_morphisms.id_τ₃, id_comp]
      naturality' := fun i j f => by
        ext
        · dsimp; simpa only [comp_id] using colimit.w (F ⋙ π₁) f
        · dsimp; simpa only [comp_id] using colimit.w (F ⋙ π₂) f
        · dsimp; simpa only [comp_id] using colimit.w (F ⋙ π₃) f }

def colimitCocone : ColimitCocone F
    where
  Cocone := ColimitCocone.cocone F
  IsColimit :=
    { desc := fun s =>
        by
        refine'
          ⟨colimit.desc (F ⋙ π₁) (π₁.map_cocone s), colimit.desc (F ⋙ π₂) (π₂.map_cocone s),
            colimit.desc (F ⋙ π₃) (π₃.map_cocone s), _, _⟩
        · ext
          dsimp
          simp only [ι_colim_map_assoc, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app, π₂_map,
            colimit.ι_desc, functor.map_cocone_ι_app, assoc, colimit.ι_desc_assoc, π₁_map]
          erw [composable_morphisms.id_τ₂, id_comp]
          exact (s.ι.app j).comm₁₂
        · ext
          dsimp
          simp only [ι_colim_map_assoc, nat_trans.hcomp_app, φ₂₃_app, nat_trans.id_app, π₃_map,
            colimit.ι_desc, functor.map_cocone_ι_app, assoc, colimit.ι_desc_assoc, π₂_map]
          erw [composable_morphisms.id_τ₃, id_comp]
          exact (s.ι.app j).comm₂₃
      fac := fun s j => by
        ext
        · dsimp; simp only [colimit.ι_desc, functor.map_cocone_ι_app, π₁_map]
        · dsimp; simp only [colimit.ι_desc, functor.map_cocone_ι_app, π₂_map]
        · dsimp; simp only [colimit.ι_desc, functor.map_cocone_ι_app, π₃_map]
      uniq := fun s m hm =>
        by
        have h₁ := fun j => congr_arg (fun φ : F.obj j ⟶ s.X => π₁.map φ) (hm j)
        have h₂ := fun j => congr_arg (fun φ : F.obj j ⟶ s.X => π₂.map φ) (hm j)
        have h₃ := fun j => congr_arg (fun φ : F.obj j ⟶ s.X => π₃.map φ) (hm j)
        dsimp at h₁ h₂ h₃ 
        ext
        · dsimp; simp only [h₁, colimit.ι_desc, functor.map_cocone_ι_app, π₁_map]
        · dsimp; simp only [h₂, colimit.ι_desc, functor.map_cocone_ι_app, π₂_map]
        · dsimp; simp only [h₃, colimit.ι_desc, functor.map_cocone_ι_app, π₃_map] }

instance : HasColimit F :=
  ⟨Nonempty.intro (colimitCocone F)⟩

def π₁PreservesColimit : PreservesColimit F (π₁ : ShortComplex C ⥤ C) :=
  preservesColimitOfPreservesColimitCocone (colimitCocone F).IsColimit
    (IsColimit.ofIsoColimit (getColimitCocone (F ⋙ π₁)).IsColimit
      (Cocones.ext (Iso.refl _) fun j => comp_id _))

def π₂PreservesColimit : PreservesColimit F (π₂ : ShortComplex C ⥤ C) :=
  preservesColimitOfPreservesColimitCocone (colimitCocone F).IsColimit
    (IsColimit.ofIsoColimit (getColimitCocone (F ⋙ π₂)).IsColimit
      (Cocones.ext (Iso.refl _) fun j => comp_id _))

def π₃PreservesColimit : PreservesColimit F (π₃ : ShortComplex C ⥤ C) :=
  preservesColimitOfPreservesColimitCocone (colimitCocone F).IsColimit
    (IsColimit.ofIsoColimit (getColimitCocone (F ⋙ π₃)).IsColimit
      (Cocones.ext (Iso.refl _) fun j => comp_id _))

end Construction

section Preserves

variable {C : Type _} [Category C] [HasZeroMorphisms C]

variable {J D : Type _} [Category J] [Category D]

def π₁₂₃ReflectsColimits {F : J ⥤ ShortComplex C} (s : Cocone F) (h₁ : IsColimit (π₁.mapCocone s))
    (h₂ : IsColimit (π₂.mapCocone s)) (h₃ : IsColimit (π₃.mapCocone s)) : IsColimit s :=
  by
  haveI : has_colimit (F ⋙ π₁) := ⟨Nonempty.intro ⟨_, h₁⟩⟩
  haveI : has_colimit (F ⋙ π₂) := ⟨Nonempty.intro ⟨_, h₂⟩⟩
  haveI : has_colimit (F ⋙ π₃) := ⟨Nonempty.intro ⟨_, h₃⟩⟩
  refine' is_colimit.of_iso_colimit (colimit_cocone F).IsColimit (cocones.ext _ _)
  · suffices is_iso ((colimit_cocone F).IsColimit.desc s)
      by
      haveI := this
      exact as_iso ((colimit_cocone F).IsColimit.desc s)
    apply is_iso_of_is_isos
    · exact is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) h₁)
    · exact is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) h₂)
    · exact is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) h₃)
  · intro j
    simp only [as_iso_hom, is_colimit.fac]

def π₁₂₃ReflectPreservesColimits (G : J ⥤ D) (F : D ⥤ ShortComplex C)
    (h₁ : PreservesColimit G (F ⋙ π₁)) (h₂ : PreservesColimit G (F ⋙ π₂))
    (h₃ : PreservesColimit G (F ⋙ π₃)) : PreservesColimit G F :=
  ⟨fun s hs =>
    π₁₂₃ReflectsColimits _ (@isColimitOfPreserves _ _ _ _ _ _ G (F ⋙ π₁) _ hs _)
      (@isColimitOfPreserves _ _ _ _ _ _ G (F ⋙ π₂) _ hs _)
      (@isColimitOfPreserves _ _ _ _ _ _ G (F ⋙ π₃) _ hs _)⟩

variable (J)

def preservesColimitsOfShapeOfProjections (F : D ⥤ ShortComplex C)
    (h₁ : PreservesColimitsOfShape J (F ⋙ π₁)) (h₂ : PreservesColimitsOfShape J (F ⋙ π₂))
    (h₃ : PreservesColimitsOfShape J (F ⋙ π₃)) : PreservesColimitsOfShape J F :=
  ⟨by intro G; apply π₁₂₃_reflect_preserves_colimits <;> infer_instance⟩

end Preserves

section FunctorHomologicalComplex

variable {C : Type _} [Category C] [Abelian C]

variable {M : Type _} {c : ComplexShape M}

variable {J : Type _} [Category J]

instance zeroPreservesColimitsOfShape {D : Type _} [Category D] :
    PreservesColimitsOfShape J (0 : D ⥤ C) :=
  ⟨fun F =>
    ⟨fun s hs =>
      { desc := fun t => 0
        fac := fun t j => by
          dsimp
          apply is_zero.eq_of_src
          apply is_zero.obj
          apply is_zero_zero
        uniq := fun t m j => by
          dsimp
          apply is_zero.eq_of_src
          apply is_zero.obj
          apply is_zero_zero }⟩⟩

theorem functorHomologicalComplexπ₁IsoEval (i j : M) (hij : c.Rel j i) :
    functorHomologicalComplex C c i ⋙ π₁ ≅ HomologicalComplex.eval C c j :=
  NatIso.ofComponents (fun X => X.xPrevIso hij) fun X Y f =>
    by
    dsimp
    simp only [HomologicalComplex.Hom.prev_eq f hij, assoc, iso.inv_hom_id, comp_id]

theorem functorHomologicalComplexπ₃IsoEval (i j : M) (hij : c.Rel i j) :
    functorHomologicalComplex C c i ⋙ π₃ ≅ HomologicalComplex.eval C c j :=
  NatIso.ofComponents (fun X => X.xNextIso hij) fun X Y f =>
    by
    dsimp
    simp only [HomologicalComplex.Hom.next_eq f hij, assoc, iso.inv_hom_id, comp_id]

instance (i : M) [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (ShortComplex.functorHomologicalComplex C c i) := by
  apply preserves_colimits_of_shape_of_projections <;>
    · exact (inferInstance : preserves_colimits_of_shape J (HomologicalComplex.eval C c _))

end FunctorHomologicalComplex

section FunctorHomology

variable {C : Type _} [Category.{v} C] [Abelian C]

variable {M : Type _} {c : ComplexShape M} {J : Type v} [SmallCategory J] [IsFiltered J]
  [HasColimitsOfShape J C] [PreservesFiniteLimits (Limits.colim : (J ⥤ C) ⥤ C)]
  [PreservesFiniteColimits (Limits.colim : (J ⥤ C) ⥤ C)]

namespace HomologyFunctorPreservesColimit

variable (F : ShortComplex (J ⥤ C))

def isoDatum :=
  HomologyIsoDatum.tautological' F.1.f F.1.g F.2

instance (j : J) : PreservesFiniteLimits ((evaluation J C).obj j) :=
  ⟨by intro F; intro; intro; infer_instance⟩

instance (j : J) : PreservesFiniteColimits ((evaluation J C).obj j) :=
  ⟨by intro F; intro; intro; infer_instance⟩

instance (j : J) : Functor.Additive ((evaluation J C).obj j) where

instance colim_additive : Functor.additive (colim : (J ⥤ C) ⥤ C) where

@[simps]
def natTransι (j : J) : (evaluation J C).obj j ⟶ (colim : (J ⥤ C) ⥤ C)
    where
  app F := colimit.ι F j
  naturality' F₁ F₂ φ := by dsimp; simp only [colimit.ι_map]

def isoDatum₁ :=
  (isoDatum F).applyExactFunctor (colim : (J ⥤ C) ⥤ C)

def f₀ :=
  FunctorCategoryEquivalence.functor.obj F

def e₁ : f₀ F ⋙ homologyFunctor ≅ (isoDatum F).h :=
  NatIso.ofComponents (fun j => ((isoDatum F).applyExactFunctor ((evaluation J C).obj j)).Iso.symm)
    fun i j f => by
    simp only [functor.comp_map, iso.symm_hom]
    erw [((iso_datum F).mapNatTrans ((evaluation J C).map f)).homology'_map_eq]
    simpa only [evaluation_map_app, assoc, iso.hom_inv_id, comp_id, iso.cancel_iso_inv_left]

def e₂ : colim.mapShortComplex.obj F ≅ (ColimitCocone.cocone (f₀ F)).pt :=
  by
  refine' iso_mk _ _ _ _ _
  · refine' colim.map_iso (nat_iso.of_components (fun j => iso.refl _) fun i j f => _)
    dsimp; erw [id_comp, comp_id]; rfl
  · refine' colim.map_iso (nat_iso.of_components (fun j => iso.refl _) fun i j f => _)
    dsimp; erw [id_comp, comp_id]; rfl
  · refine' colim.map_iso (nat_iso.of_components (fun j => iso.refl _) fun i j f => _)
    dsimp; erw [id_comp, comp_id]; rfl
  · ext; dsimp;
    simp only [colimit.ι_map_assoc, colimit.ι_map, nat_iso.of_components_hom_app, iso.refl_hom,
      id_comp, ι_colim_map, nat_trans.hcomp_app, φ₁₂_app, nat_trans.id_app, π₂_map, assoc]
    erw [id_comp]; rfl
  · ext; dsimp;
    simp only [colimit.ι_map_assoc, colimit.ι_map, nat_iso.of_components_hom_app, iso.refl_hom,
      id_comp, ι_colim_map, nat_trans.hcomp_app, φ₂₃_app, nat_trans.id_app, π₃_map, assoc]
    erw [id_comp]; rfl

def e₃ : colimit (f₀ F ⋙ homologyFunctor) ≅ (colim.mapShortComplex.obj F).homology' :=
  colim.mapIso (e₁ F) ≪≫ (isoDatum₁ F).Iso

def e₄ : colimit (f₀ F ⋙ homologyFunctor) ≅ (ColimitCocone.cocone (f₀ F)).pt.homology' :=
  e₃ F ≪≫ homologyFunctor.mapIso (e₂ F)

theorem compatibility (j : J) :
    (colimit.cocone (f₀ F ⋙ homologyFunctor)).ι.app j ≫ (e₃ F).Hom =
      homologyFunctor.map ((natTransι j).mapShortComplex.app F) :=
  by
  rw [((iso_datum F).mapNatTrans (nat_trans_ι j)).homology'_map_eq]
  dsimp only [e₁, e₃, iso_datum₁, nat_iso.of_components]
  simpa only [colimit.cocone_ι, iso.trans_hom, functor.map_iso_hom, colimit.ι_map_assoc,
    iso.symm_hom, nat_trans_ι_app, iso.cancel_iso_hom_right_assoc, iso.cancel_iso_inv_left]

theorem preserves : PreservesColimit (f₀ F) ShortComplex.homologyFunctor :=
  ⟨fun s hs =>
    by
    have e₁ : s ≅ colimit_cocone.cocone (F₀ F) :=
      by
      refine' is_initial.unique_up_to_iso _ _
      all_goals equiv_rw (cocone.is_colimit_equiv_is_initial _).symm
      exacts [hs, (colimit_cocone (F₀ F)).IsColimit]
    suffices is_colimit (homology_functor.map_cocone (colimit_cocone.cocone (F₀ F))) by
      exact
        is_colimit.of_iso_colimit this ((cocones.functoriality _ homology'Functor).mapIso e₁.symm)
    clear e₁ hs s
    refine'
      is_colimit.of_iso_colimit (colimit.is_colimit (F₀ F ⋙ homology'Functor))
        (cocones.ext (e₄ F) _)
    intro j
    dsimp only [functor.map_cocone, cocones.functoriality, e₄, iso.trans, functor.map_iso]
    rw [← assoc, compatibility, ← homology_functor.map_comp]
    congr 1
    ext1
    all_goals dsimp [e₂];
      simp only [colimit.ι_map, nat_iso.of_components_hom_app, iso.refl_hom, id_comp]⟩

end HomologyFunctorPreservesColimit

instance (F₀ : J ⥤ ShortComplex C) : PreservesColimit F₀ ShortComplex.homologyFunctor :=
  by
  let F := functor_category_equivalence.inverse.obj F₀
  haveI : preserves_colimit (homology_functor_preserves_colimit.F₀ F) homology'Functor :=
    homology_functor_preserves_colimit.preserves F
  have h : homology_functor_preserves_colimit.F₀ F ≅ F₀ :=
    functor_category_equivalence.counit_iso.app F₀
  exact preserves_colimit_of_iso_diagram ShortComplex.homologyFunctor h

instance : PreservesColimitsOfShape J (ShortComplex.homologyFunctor : ShortComplex C ⥤ C) :=
  ⟨fun F => inferInstance⟩

end FunctorHomology

end ShortComplex

