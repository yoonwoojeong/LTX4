import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.Algebra.Homology.Additive
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.Equalizers
import LiquidTensorExperiment.ForMathlib.HomologyMapDatum
import LiquidTensorExperiment.ForMathlib.ShortComplex
import LiquidTensorExperiment.ForMathlib.Derived.Defs

#align_import for_mathlib.exact_functor

namespace CategoryTheory

universe v u u'

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
  (F G : A ⥤ B) [Functor.Additive F] [Functor.Additive G] (φ : F ⟶ G)

theorem Exact.mono_desc {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} (e : Exact f g) :
    Mono (Limits.cokernel.desc _ _ e.w) :=
  Abelian.CategoryTheory.Limits.Cokernel.Desc.CategoryTheory.mono f g e

--WAT?
theorem Exact.epi_lift {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} (e : Exact f g) :
    Epi (Limits.kernel.lift _ _ e.w) :=
  Limits.kernel.lift.epi e

theorem Exact.epi_of_exact_zero_right {X Y Z : A} {f : X ⟶ Y} (e : Exact f (0 : Y ⟶ Z)) : Epi f :=
  by
  rw [abelian.epi_iff_cokernel_π_eq_zero]
  rw [abelian.exact_iff] at e 
  cases' e with e1 e2
  simpa using e2

theorem Exact.mono_of_exact_zero_left {X Y Z : A} {f : Y ⟶ Z} (e : Exact (0 : X ⟶ Y) f) : Mono f :=
  by
  rw [abelian.mono_iff_kernel_ι_eq_zero]
  rw [abelian.exact_iff] at e 
  cases' e with e1 e2
  simpa using e2

namespace Functor

open CategoryTheory.Limits

def Exact : Prop :=
  ∀ ⦃X Y Z : A⦄ (f : X ⟶ Y) (g : Y ⟶ Z), Exact f g → Exact (F.map f) (F.map g)

noncomputable section

-- Sanity check
example : PreservesZeroMorphisms F :=
  inferInstance

open scoped ZeroObject Classical

theorem epi_of_epi_of_exact (h : F.exact) {X Y : A} (f : X ⟶ Y) [Epi f] : Epi (F.map f) :=
  by
  have : CategoryTheory.Exact f (0 : _ ⟶ 0) := exact_epi_zero f
  replace this := h _ _ this
  simp at this 
  apply this.epi_of_exact_zero_right

theorem mono_of_mono_of_exact (h : F.exact) {X Y : A} (f : X ⟶ Y) [Mono f] : Mono (F.map f) :=
  by
  have : CategoryTheory.Exact (0 : X ⟶ _) f := exact_zero_left_of_mono X
  replace this := h _ _ this
  simp at this 
  apply this.mono_of_exact_zero_left

theorem isIso_cokernelComparison_of_exact (hh : F.exact) {X Y : A} (f : X ⟶ Y) :
    IsIso (cokernelComparison f F) :=
  by
  have : CategoryTheory.Exact (F.map f) (F.map (cokernel.π f)) := by apply hh;
    exact abelian.exact_cokernel f
  dsimp [cokernel_comparison]
  apply (config := { instances := false }) is_iso_of_mono_of_epi
  infer_instance
  apply this.mono_desc
  constructor; intro Z a b h
  apply_fun fun e => cokernel.π _ ≫ e at h 
  simp at h 
  haveI := epi_of_epi_of_exact _ hh (cokernel.π f)
  rwa [cancel_epi] at h 

def preservesCoequalizersOfExact (hh : F.exact) {X Y : A} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) F :=
  preservesColimitOfPreservesColimitCocone (coforkOfCokernelIsColimit _ _)
    (by
      let e : parallel_pair f g ⋙ F ≅ parallel_pair (F.map f) (F.map g) :=
        diagram_iso_parallel_pair _
      equiv_rw (is_colimit.precompose_inv_equiv e _).symm
      apply is_colimit.of_iso_colimit (cofork_of_cokernel_is_colimit (F.map f) (F.map g))
      haveI := is_iso_cokernel_comparison_of_exact F hh (f - g)
      refine'
        cocones.ext
          (cokernel.map_iso (F.map f - F.map g) (F.map (f - g)) (iso.refl _) (iso.refl _)
              (by simp) ≪≫
            as_iso (cokernel_comparison (f - g) F))
          _
      rintro (_ | _)
      tidy)

def preservesFiniteColimitsOfExact (hh : F.exact) : PreservesFiniteColimits F :=
  by
  apply (config := { instances := false })
    preserves_finite_colimits_of_preserves_coequalizers_and_finite_coproducts
  any_goals infer_instance
  · constructor
    intro K
    apply (config := { instances := false }) preserves_colimit_of_iso_diagram
    exact (diagram_iso_parallel_pair K).symm
    apply preserves_coequalizers_of_exact F hh
  · intro J hI
    apply preserves_coproducts_of_shape_of_preserves_biproducts_of_shape

theorem isIso_kernelComparison_of_exact (hh : F.exact) {X Y : A} (f : X ⟶ Y) :
    IsIso (kernelComparison f F) :=
  by
  have : CategoryTheory.Exact (F.map (kernel.ι f)) (F.map f) := by apply hh; exact exact_kernel_ι
  dsimp [kernel_comparison]
  apply (config := { instances := false }) is_iso_of_mono_of_epi
  infer_instance
  constructor
  intro Z a b h
  apply_fun fun e => e ≫ kernel.ι _ at h 
  simp at h 
  haveI := mono_of_mono_of_exact _ hh (kernel.ι f)
  rwa [cancel_mono] at h 
  apply this.epi_lift

def preservesEqualizersOfExact (hh : F.exact) {X Y : A} (f g : X ⟶ Y) :
    PreservesLimit (parallelPair f g) F :=
  preservesLimitOfPreservesLimitCone (forkOfKernelIsLimit _ _)
    (by
      let e : parallel_pair f g ⋙ F ≅ parallel_pair (F.map f) (F.map g) :=
        diagram_iso_parallel_pair _
      equiv_rw (is_limit.postcompose_hom_equiv e _).symm
      apply is_limit.of_iso_limit (fork_of_kernel_is_limit (F.map f) (F.map g))
      haveI := is_iso_kernel_comparison_of_exact F hh (f - g)
      symm
      refine'
        cones.ext
          (as_iso (kernel_comparison (f - g) F) ≪≫
            kernel.map_iso (F.map (f - g)) (F.map f - F.map g) (iso.refl _) (iso.refl _) (by simp))
          _
      rintro (_ | _)
      tidy)

def preservesFiniteLimitsOfExact (h : F.exact) : PreservesFiniteLimits F :=
  by
  apply (config := { instances := false })
    preserves_finite_limits_of_preserves_equalizers_and_finite_products
  any_goals infer_instance
  · constructor
    intro K
    apply (config := { instances := false }) preserves_limit_of_iso_diagram
    exact (diagram_iso_parallel_pair K).symm
    apply preserves_equalizers_of_exact F h
  · intro J hJ
    apply preserves_products_of_shape_of_preserves_biproducts_of_shape

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

def homologyNatIso :
    (ShortComplex.homologyFunctor : ShortComplex A ⥤ A) ⋙ F ≅
      F.mapShortComplex ⋙ ShortComplex.homologyFunctor :=
  NatIso.ofComponents
    (fun S => ((HomologyIsoDatum.tautological' S.1.f S.1.g S.2).applyExactFunctor F).Iso)
    fun S₁ S₂ φ => by
    simp only [comp_map, iso.hom_inv_id_assoc,
      ((HomologyMapDatum.tautological' φ).mapExactFunctor F).homology'_map_eq]

def homology'Iso {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w w') :
    F.obj (homology' f g w) ≅ homology' (F.map f) (F.map g) w' :=
  F.homologyNatIso.app (ShortComplex.mk f g w)

def homology'FunctorIso {M : Type _} (c : ComplexShape M) (i : M) :
    homology'Functor A c i ⋙ F ≅ F.mapHomologicalComplex _ ⋙ homology'Functor B c i :=
  by
  calc
    homology'Functor A c i ⋙ F ≅
        (ShortComplex.functorHomologicalComplex A c i ⋙ ShortComplex.homologyFunctor) ⋙ F :=
      _
    _ ≅ ShortComplex.functorHomologicalComplex A c i ⋙ ShortComplex.homologyFunctor ⋙ F := _
    _ ≅
        ShortComplex.functorHomologicalComplex A c i ⋙
          F.map_short_complex ⋙ ShortComplex.homologyFunctor :=
      _
    _ ≅
        (ShortComplex.functorHomologicalComplex A c i ⋙ F.map_short_complex) ⋙
          ShortComplex.homologyFunctor :=
      _
    _ ≅
        (F.map_homological_complex _ ⋙ ShortComplex.functorHomologicalComplex B c i) ⋙
          ShortComplex.homologyFunctor :=
      _
    _ ≅
        F.map_homological_complex _ ⋙
          ShortComplex.functorHomologicalComplex B c i ⋙ ShortComplex.homologyFunctor :=
      _
    _ ≅ F.map_homological_complex _ ⋙ homology'Functor B c i := _
  · exact iso_whisker_right (ShortComplex.homologyFunctorIso A c i) F
  · apply associator
  · exact iso_whisker_left _ F.homology_nat_iso
  · symm; apply associator
  · exact iso_whisker_right (ShortComplex.functorHomologicalComplexMap F c i) _
  · apply associator
  · exact iso_whisker_left _ (ShortComplex.homologyFunctorIso B c i).symm

variable {F G}

def naturality_homologyNatIso_app (S : ShortComplex A) :
    φ.app S.homology' ≫ G.homologyNatIso.Hom.app S =
      F.homologyNatIso.Hom.app S ≫ ShortComplex.homologyFunctor.map (φ.mapShortComplex.app S) :=
  by
  let h := HomologyIsoDatum.tautological' S.obj.f S.obj.g S.zero
  simpa [← cancel_epi (h.apply_exact_functor F).Iso.Hom, iso.hom_inv_id_assoc] using
    (h.map_nat_trans φ).homology'_map_eq.symm

/-- naturality of `homology_functor_iso` on the variable `F` -/
theorem naturality_homology'FunctorIso_hom_app {M : Type _} {c : ComplexShape M}
    (X : HomologicalComplex A c) (i : M) :
    φ.app ((homology'Functor A c i).obj X) ≫ (G.homology'FunctorIso c i).Hom.app X =
      (F.homology'FunctorIso c i).Hom.app X ≫
        (homology'Functor B c i).map ((NatTrans.mapHomologicalComplex φ c).app X) :=
  by
  dsimp only [homology_functor_iso, iso.trans, iso_whisker_left, whiskering_left, whisker_left,
    iso_whisker_right, whiskering_right, whisker_right, map_iso, associator, iso.symm,
    ShortComplex.homologyFunctorIso, nat_iso.of_components, iso.refl]
  simp only [category.assoc, nat_trans.comp_app, category.id_comp, F.map_id, G.map_id]
  erw [category.id_comp, category.id_comp, category.comp_id]
  slice_lhs 1 2 =>
    erw [naturality_homology_nat_iso_app φ ((ShortComplex.functorHomologicalComplex A c i).obj X)]
  rw [category.assoc, ← short_complex.homology_functor.map_comp]
  simpa only [ShortComplex.naturality_functorHomologicalComplexMap,
    short_complex.homology_functor.map_comp]

theorem naturality_homology'FunctorIso {M : Type _} (c : ComplexShape M) (i : M) :
    (𝟙 (homology'Functor A c i) ◫ φ) ≫ (G.homology'FunctorIso c i).Hom =
      (F.homology'FunctorIso c i).Hom ≫
        NatTrans.mapHomologicalComplex φ c ◫ 𝟙 (homology'Functor B c i) :=
  by
  ext1; ext1 X
  simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app, G.map_id, category.comp_id]
  erw [category.id_comp]
  apply naturality_homology_functor_iso_hom_app

variable (F)

def homologyFunctorIsoOnHomotopyCategory {M : Type _} (c : ComplexShape M) (i : M) :
    HomotopyCategory.homology'Functor A c i ⋙ F ≅
      F.mapHomotopyCategory _ ⋙ HomotopyCategory.homology'Functor B c i :=
  NatIso.ofComponents (fun X => (F.homology'FunctorIso c i).app X.as) fun X Y f =>
    by
    nth_rw 1 [← HomotopyCategory.quotient_map_out f]
    erw [(F.homology_functor_iso c i).Hom.naturality (Quot.out f)]
    rfl

def mapQuasiIsoOnHomotopyCategory {M : Type _} {c : ComplexShape M} {X₁ X₂ : HomotopyCategory A c}
    (φ : X₁ ⟶ X₂) [hφ : HomotopyCategory.IsQuasiIso φ] :
    HomotopyCategory.IsQuasiIso ((F.mapHomotopyCategory c).map φ) :=
  ⟨by
    intro i
    let F₁ := HomotopyCategory.homology'Functor A c i ⋙ F
    let F₂ := map_homotopy_category c F ⋙ HomotopyCategory.homology'Functor B c i
    change is_iso (F₂.map φ)
    let e : F₁ ≅ F₂ := F.homology_functor_iso_on_homotopy_category c i
    have h := e.hom.naturality φ
    rw [← cancel_epi (e.inv.app X₁)] at h 
    conv_rhs at h => rw [← category.assoc, ← nat_trans.comp_app, e.inv_hom_id]
    rw [nat_trans.id_app, category.id_comp] at h 
    rw [← h]
    haveI : is_iso (F₁.map φ) := by
      haveI := hφ.cond
      dsimp only [F₁, Functor.Comp]
      apply functor.map_is_iso
    infer_instance⟩

end Functor

-- TODO: Exact iff preserves finite limits and colimits
end CategoryTheory

