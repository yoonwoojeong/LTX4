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
        simp only [ι_colim_map_assoc, NatTrans.hcomp_app, φ₁₂_app, NatTrans.id_app, π₂_map,
          ι_colim_map, φ₂₃_app, π₃_map, assoc, comp_zero]
        erw [ComposableMorphisms.id_τ₂, id_comp, (F.obj j).zero_assoc, zero_comp])
  ι :=
    { app := fun j =>
        by
        refine' ⟨colimit.ι (F ⋙ π₁) j, colimit.ι (F ⋙ π₂) j, colimit.ι (F ⋙ π₃) j, _, _⟩
        · dsimp
          simp only [ι_colim_map, NatTrans.hcomp_app, φ₁₂_app, NatTrans.id_app, π₂_map, assoc]
          erw [ComposableMorphisms.id_τ₂, id_comp]
        · dsimp
          simp only [ι_colim_map, NatTrans.hcomp_app, φ₂₃_app, NatTrans.id_app, π₃_map, assoc]
          erw [ComposableMorphisms.id_τ₃, id_comp]
      naturality := fun i j f => by
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
          ⟨colimit.desc (F ⋙ π₁) (π₁.mapCocone s), colimit.desc (F ⋙ π₂) (π₂.mapCocone s),
            colimit.desc (F ⋙ π₃) (π₃.mapCocone s), _, _⟩
        · ext
          dsimp
          simp only [ι_colim_map_assoc, NatTrans.hcomp_app, φ₁₂_app, NatTrans.id_app, π₂_map,
            colimit.ι_desc, Functor.mapCocone_ι_app, assoc, colimit.ι_desc_assoc, π₁_map]
          erw [ComposableMorphisms.id_τ₂, id_comp]
          exact (s.ι.app j).comm₁₂
        · ext
          dsimp
          simp only [ι_colim_map_assoc, NatTrans.hcomp_app, φ₂₃_app, NatTrans.id_app, π₃_map,
            colimit.ι_desc, Functor.mapCocone_ι_app, assoc, colimit.ι_desc_assoc, π₂_map]
          erw [ComposableMorphisms.id_τ₃, id_comp]
          exact (s.ι.app j).comm₂₃
      fac := fun s j => by
        ext
        · dsimp; simp only [colimit.ι_desc, Functor.mapCocone_ι_app, π₁_map]
        · dsimp; simp only [colimit.ι_desc, Functor.mapCocone_ι_app, π₂_map]
        · dsimp; simp only [colimit.ι_desc, Functor.mapCocone_ι_app, π₃_map]
      uniq := fun s m hm =>
        by
        have h₁ := fun j => congr_arg (fun φ : F.obj j ⟶ s.X => π₁.map φ) (hm j)
        have h₂ := fun j => congr_arg (fun φ : F.obj j ⟶ s.X => π₂.map φ) (hm j)
        have h₃ := fun j => congr_arg (fun φ : F.obj j ⟶ s.X => π₃.map φ) (hm j)
        dsimp at h₁ h₂ h₃ 
        ext
        · dsimp; simp only [h₁, colimit.ι_desc, Functor.mapCocone_ι_app, π₁_map]
        · dsimp; simp only [h₂, colimit.ι_desc, Functor.mapCocone_ι_app, π₂_map]
        · dsimp; simp only [h₃, colimit.ι_desc, Functor.mapCocone_ι_app, π₃_map] }

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
  refine' IsColimit.ofIsoColimit (colimit_cocone F).IsColimit (Cocones.ext _ _)
  · suffices is_iso ((colimit_cocone F).IsColimit.desc s)
      by
      haveI := this
      exact CategoryTheory.asIso ((colimit_cocone F).IsColimit.desc s)
    apply ShortComplex.isIso_of_is_isos
    · exact IsIso.of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₁)
    · exact IsIso.of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₂)
    · exact IsIso.of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₃)
  · intro j
    simp only [CategoryTheory.asIso_hom, IsColimit.fac]

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
          apply IsZero.eq_of_src
          apply IsZero.obj
          apply is_zero_zero
        uniq := fun t m j => by
          dsimp
          apply IsZero.eq_of_src
          apply IsZero.obj
          apply is_zero_zero }⟩⟩

theorem functorHomologicalComplexπ₁IsoEval (i j : M) (hij : c.Rel j i) :
    functorHomologicalComplex C c i ⋙ π₁ ≅ HomologicalComplex.eval C c j :=
  NatIso.ofComponents (fun X => X.xPrevIso hij) fun X Y f =>
    by
    dsimp
    simp only [HomologicalComplex.Hom.prev_eq f hij, assoc, Iso.inv_hom_id, comp_id]

theorem functorHomologicalComplexπ₃IsoEval (i j : M) (hij : c.Rel i j) :
    functorHomologicalComplex C c i ⋙ π₃ ≅ HomologicalComplex.eval C c j :=
  NatIso.ofComponents (fun X => X.xNextIso hij) fun X Y f =>
    by
    dsimp
    simp only [HomologicalComplex.Hom.next_eq f hij, assoc, Iso.inv_hom_id, comp_id]

instance (i : M) [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (ShortComplex.functorHomologicalComplex C c i) := by
  apply ShortComplex.preservesColimitsOfShapeOfProjections <;>
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
  naturality F₁ F₂ φ := by dsimp; simp only [colimit.ι_map]

def isoDatum₁ :=
  (isoDatum F).applyExactFunctor (colim : (J ⥤ C) ⥤ C)

def f₀ :=
  FunctorCategoryEquivalence.functor.obj F

def e₁ : f₀ F ⋙ homologyFunctor ≅ (isoDatum F).h :=
  NatIso.ofComponents (fun j => ((isoDatum F).applyExactFunctor ((evaluation J C).obj j)).Iso.symm)
    fun i j f => by
    simp only [Functor.comp_map, Iso.symm_hom]
    erw [((ShortComplex.HomologyFunctorPreservesColimit.isoDatum F).mapNatTrans ((evaluation J C).map f)).homology'_map_eq]
    simpa only [evaluation_map_app, assoc, Iso.hom_inv_id, comp_id, Iso.cancel_iso_inv_left]

def e₂ : colim.mapShortComplex.obj F ≅ (ColimitCocone.cocone (f₀ F)).pt :=
  by
  refine' iso_mk _ _ _ _ _
  · refine' colim.map_iso (NatIso.ofComponents (fun j => iso.refl _) fun i j f => _)
    dsimp; erw [id_comp, comp_id]; rfl
  · refine' colim.map_iso (NatIso.ofComponents (fun j => iso.refl _) fun i j f => _)
    dsimp; erw [id_comp, comp_id]; rfl
  · refine' colim.map_iso (NatIso.ofComponents (fun j => iso.refl _) fun i j f => _)
    dsimp; erw [id_comp, comp_id]; rfl
  · ext; dsimp;
    simp only [colimit.ι_map_assoc, colimit.ι_map, NatIso.ofComponents_hom_app, Iso.refl_hom,
      id_comp, ι_colim_map, NatTrans.hcomp_app, φ₁₂_app, NatTrans.id_app, π₂_map, assoc]
    erw [id_comp]; rfl
  · ext; dsimp;
    simp only [colimit.ι_map_assoc, colimit.ι_map, NatIso.ofComponents_hom_app, Iso.refl_hom,
      id_comp, ι_colim_map, NatTrans.hcomp_app, φ₂₃_app, NatTrans.id_app, π₃_map, assoc]
    erw [id_comp]; rfl

def e₃ : colimit (f₀ F ⋙ homologyFunctor) ≅ (colim.mapShortComplex.obj F).homology' :=
  colim.mapIso (e₁ F) ≪≫ (isoDatum₁ F).Iso

def e₄ : colimit (f₀ F ⋙ homologyFunctor) ≅ (ColimitCocone.cocone (f₀ F)).pt.homology' :=
  e₃ F ≪≫ homologyFunctor.mapIso (e₂ F)

theorem compatibility (j : J) :
    (colimit.cocone (f₀ F ⋙ homologyFunctor)).ι.app j ≫ (e₃ F).hom =
      homologyFunctor.map ((natTransι j).mapShortComplex.app F) :=
  by
  rw [((ShortComplex.HomologyFunctorPreservesColimit.isoDatum F).mapNatTrans (nat_trans_ι j)).homology'_map_eq]
  dsimp only [e₁, e₃, iso_datum₁, NatIso.ofComponents]
  simpa only [colimit.cocone_ι, Iso.trans_hom, Functor.mapIso_hom, colimit.ι_map_assoc,
    Iso.symm_hom, nat_trans_ι_app, Iso.cancel_iso_hom_right_assoc, Iso.cancel_iso_inv_left]

theorem preserves : PreservesColimit (f₀ F) ShortComplex.homologyFunctor :=
  ⟨fun s hs =>
    by
    have e₁ : s ≅ colimit_cocone.cocone (F₀ F) :=
      by
      refine' IsInitial.uniqueUpToIso _ _
      all_goals equiv_rw (Cocone.isColimitEquivIsInitial _).symm
      exacts [hs, (colimit_cocone (F₀ F)).IsColimit]
    suffices is_colimit (homology_functor.mapCocone (colimit_cocone.cocone (F₀ F))) by
      exact
        IsColimit.ofIsoColimit this ((Cocones.functoriality _ homology'Functor).mapIso e₁.symm)
    clear e₁ hs s
    refine'
      IsColimit.ofIsoColimit (colimit.isColimit (F₀ F ⋙ homology'Functor))
        (Cocones.ext (e₄ F) _)
    intro j
    dsimp only [Functor.mapCocone, Cocones.functoriality, e₄, Iso.trans, Functor.mapIso]
    rw [← assoc, compatibility, ← homology_functor.map_comp]
    congr 1
    ext1
    all_goals dsimp [e₂];
      simp only [colimit.ι_map, NatIso.ofComponents_hom_app, Iso.refl_hom, id_comp]⟩

end HomologyFunctorPreservesColimit

instance (F₀ : J ⥤ ShortComplex C) : PreservesColimit F₀ ShortComplex.homologyFunctor :=
  by
  let F := FunctorCategoryEquivalence.Inverse.obj F₀
  haveI : preserves_colimit (HomologyFunctorPreservesColimit.f₀ F) homology'Functor :=
    HomologyFunctorPreservesColimit.preserves F
  have h : HomologyFunctorPreservesColimit.f₀ F ≅ F₀ :=
    functor_category_equivalence.counitIso.app F₀
  exact CategoryTheory.Limits.preservesColimitOfIsoDiagram ShortComplex.homologyFunctor h

instance : PreservesColimitsOfShape J (ShortComplex.homologyFunctor : ShortComplex C ⥤ C) :=
  ⟨fun F => inferInstance⟩

end FunctorHomology

end ShortComplex

