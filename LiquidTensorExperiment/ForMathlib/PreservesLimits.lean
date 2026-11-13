import LiquidTensorExperiment.ForMathlib.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import LiquidTensorExperiment.ForMathlib.Homology

#align_import for_mathlib.preservesLimits

open CategoryTheory CategoryTheory.Limits

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] [Abelian C]

variable {D : Type u₂} [Category.{v} D] [Abelian D] (F : C ⥤ D)

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F] [Functor.Additive F]

variable {ι : Type _} {c : ComplexShape ι}

@[simps]
noncomputable def CategoryTheory.Limits.cokernel.mapArrowIso {C : Type u₁} [Category.{v} C]
    [HasZeroMorphisms C] {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCokernel f₁]
    [HasCokernel f₂] (e : Arrow.mk f₁ ≅ Arrow.mk f₂) : cokernel f₁ ≅ cokernel f₂
    where
  hom := cokernel.map _ _ e.hom.left e.hom.right e.hom.w.symm
  inv := cokernel.map _ _ e.inv.left e.inv.right e.inv.w.symm
  hom_inv_id := by
    ext
    simp only [Category.comp_id, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc,
      coequalizer_as_cokernel]
    rw [← Category.assoc, ← Comma.comp_right, e.hom_inv_id, Arrow.id_right]
    exact Category.id_comp _
  inv_hom_id := by
    ext
    simp only [Category.comp_id, cokernel.π_desc, cokernel.π_desc_assoc, Category.assoc,
      coequalizer_as_cokernel]
    rw [← Category.assoc, ← Comma.comp_right, e.inv_hom_id, Arrow.id_right]
    exact Category.id_comp _

@[simps]
noncomputable def CategoryTheory.Limits.kernel.mapArrowIso {C : Type u₁} [Category.{v} C]
    [HasZeroMorphisms C] {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasKernel f₁]
    [HasKernel f₂] (e : Arrow.mk f₁ ≅ Arrow.mk f₂) : kernel f₁ ≅ kernel f₂
    where
  hom := kernel.map _ _ e.hom.left e.hom.right e.hom.w.symm
  inv := kernel.map _ _ e.inv.left e.inv.right e.inv.w.symm
  hom_inv_id := by
    ext
    simp only [Category.id_comp, kernel.lift_ι, kernel.lift_ι_assoc, Category.assoc,
      equalizer_as_kernel]
    rw [← Comma.comp_left, e.hom_inv_id, Arrow.id_left]
    exact Category.comp_id _
  inv_hom_id := by
    ext
    simp only [Category.id_comp, kernel.lift_ι, kernel.lift_ι_assoc, Category.assoc,
      equalizer_as_kernel]
    rw [← Comma.comp_left, e.inv_hom_id, Arrow.id_left]
    exact Category.comp_id _

noncomputable def CategoryTheory.Functor.mapHomologicalComplexXPrev (F : C ⥤ D) [F.Additive]
    (X : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj X).xPrev i ≅ F.obj (X.xPrev i) :=
  Iso.refl _

theorem CategoryTheory.Functor.mapHomologicalComplexXPrev_eq (F : C ⥤ D) [F.Additive]
    (X : HomologicalComplex C c) {i : ι} : F.mapHomologicalComplexXPrev X i = Iso.refl _ :=
  rfl

noncomputable def CategoryTheory.Functor.mapHomologicalComplexXNext (F : C ⥤ D) [F.Additive]
    (X : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj X).xNext i ≅ F.obj (X.xNext i) :=
  Iso.refl _

theorem CategoryTheory.Functor.mapHomologicalComplexXNext_eq (F : C ⥤ D) [F.Additive]
    (X : HomologicalComplex C c) {i : ι} : F.mapHomologicalComplexXNext X i = Iso.refl _ :=
  rfl

theorem CategoryTheory.Functor.mapHomologicalComplex_dFrom (F : C ⥤ D) [F.Additive]
    (X : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj X).dFrom i = F.map (X.dFrom i) :=
  rfl

theorem CategoryTheory.Functor.mapHomologicalComplex_dTo (F : C ⥤ D) [F.Additive]
    (X : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj X).dTo i = F.map (X.dTo i) :=
  rfl

@[simp, reassoc]
theorem CategoryTheory.Limits.preserves_kernel_iso_inv_map (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (iX : X₁ ⟶ X₂)
    (iY : Y₁ ⟶ Y₂) (e) :
    (PreservesKernel.iso F f₁).inv ≫ F.map (kernel.map _ _ iX iY e) =
      kernel.map _ _ (F.map iX) (F.map iY) (by simp_rw [← F.map_comp, e]) ≫
        (PreservesKernel.iso F f₂).inv :=
  by
  rw [Iso.eq_comp_inv, Category.assoc, eq_comm, Iso.eq_inv_comp]
  ext
  simp

-- attribute [reassoc] kernel.lift_map
open CategoryTheory CategoryTheory.Limits

@[simp, reassoc]
theorem homology'.π'_iso_cokernel_lift_hom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology'.π' f g w ≫ (homology'IsoCokernelLift f g w).hom = cokernel.π _ := by
  delta homology'.π'; simp

@[reassoc]
theorem homology'.π'_iso_cokernel_lift_inv {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    cokernel.π _ ≫ (homology'IsoCokernelLift f g w).inv = homology'.π' f g w :=
  rfl

noncomputable def preservesHomologyOfExact (i : ι) :
    F.mapHomologicalComplex c ⋙ homology'Functor _ c i ≅ homology'Functor _ c i ⋙ F :=
  by
  fapply NatIso.ofComponents
  · intro X
    refine'
      homology'IsoCokernelLift _ _ _ ≪≫
        cokernel.mapArrowIso _ _ (Arrow.isoMk _ _ _) ≪≫
          (PreservesCokernel.iso _ _).symm ≪≫ F.map_iso (homology'IsoCokernelLift _ _ _).symm
    · exact iso.refl _
    · refine' kernel.mapArrowIso _ _ (Arrow.isoMk _ _ _) ≪≫ (PreservesKernel.iso _ _).symm
      · exact iso.refl _
      · exact iso.refl _
      · dsimp; rw [Category.id_comp, F.map_homological_complex_d_from, Category.comp_id]
    · dsimp; rw [← Category.assoc, Iso.eq_comp_inv]; ext; simp [F.map_homological_complex_d_to]
  · intro X Y f; apply homology'.hom_from_ext
    simp only [CategoryTheory.Limits.kernel.mapArrowIso_hom, CategoryTheory.Functor.mapIso_inv,
      CategoryTheory.Functor.mapHomologicalComplex_map_f, HomologicalComplex.Hom.sqFrom_right,
      CategoryTheory.Iso.refl_hom, homology'.π'_iso_cokernel_lift_hom_assoc,
      CategoryTheory.Arrow.isoMk_hom_right, CategoryTheory.Arrow.isoMk_hom_left,
      CategoryTheory.Limits.cokernel.mapArrowIso_hom, CategoryTheory.Functor.comp_map,
      homology'Functor_map, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Limits.cokernel.π_desc_assoc, CategoryTheory.Limits.PreservesCokernel.iso_inv,
      CategoryTheory.Functor.mapIso_symm, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.trans_hom, HomologicalComplex.Hom.sqTo_right,
      CategoryTheory.Limits.π_comp_cokernelComparison_assoc, homology'.π'_map_assoc]
    simp only [← Functor.map_comp]
    rw [homology'.π'_iso_cokernel_lift_inv_assoc, homology'.π'_iso_cokernel_lift_inv,
      homology'.π'_map, F.map_comp, preserves_kernel_iso_inv_map_assoc]
    simp only [← Category.assoc]
    congr 2
    ext
    simp only [CategoryTheory.Limits.equalizer_as_kernel, HomologicalComplex.Hom.sqFrom_right,
      CategoryTheory.Category.assoc, CategoryTheory.Limits.kernel.lift_ι,
      HomologicalComplex.Hom.sqTo_right, CategoryTheory.Limits.kernel.lift_ι_assoc]
    dsimp
    rw [Category.id_comp, Category.comp_id]

-- def preserves_limit_of_lim_commute (J : Type*) [category J] [has_limits_of_shape J C]
--   [has_limits_of_shape J D]  (F : C ⥤ D) (e : lim ⋙ F ≅ (whiskering_right J C D).obj F ⋙ lim):
--     preserves_limits_of_shape J F :=
-- begin
--   refine ⟨λ K, preserves_limit_of_preserves_limit_cone (limit.is_limit _) _⟩,
--   apply is_limit.of_iso_limit (limit.is_limit _),
--   ext, swap,
--   { exact e.symm.app K },
--   { dsimp,
--     have := congr_arg (λ f, f ≫ limit.π _ j) (e.hom.naturality (limit.cone K).π),
--     dsimp at this,
--     simp only [whisker_right_app, limit.cone_π, lim_map_π, category.assoc] at this,
--     let : limit K ≅ limit ((category_theory.functor.const J).obj (limit K)),
--     { refine ⟨limit.lift _ ⟨_, 𝟙 _⟩, lim_map (limit.cone K).π, _, _⟩,
--       { ext, simp },
--       { ext, simp, dsimp, simp,  } }  }
--   -- have := cone.iso_mk
-- end
