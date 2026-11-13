import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Main
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Sites.LeftExact
import LiquidTensorExperiment.ForMathlib.ChainComplexExact
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.ExactFunctor

#align_import for_mathlib.abelian_sheaves.exact

universe w v u

open CategoryTheory

open CategoryTheory.Limits

variable {C : Type max v u} [Category.{v} C] {J : GrothendieckTopology C}

variable {A : Type w} [Category.{max v u} A] [Abelian A]

variable [ConcreteCategory.{max v u} A]

variable [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), Limits.HasMultiequalizer (S.index P)]

variable [Limits.PreservesLimits (forget A)]

variable [∀ X : C, Limits.HasColimitsOfShape (J.cover X)ᵒᵖ A]

variable [∀ X : C, Limits.PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget A)]

variable [ReflectsIsomorphisms (forget A)]

noncomputable section

-- Just checking...
example : Abelian (Sheaf J A) :=
  inferInstance

example : PreservesFiniteLimits (presheafToSheaf J A) :=
  inferInstance

example : Functor.PreservesZeroMorphisms (presheafToSheaf J A) :=
  inferInstance

-- Missing
instance : PreservesColimits (presheafToSheaf J A) :=
  (sheafificationAdjunction J A).leftAdjointPreservesColimits

namespace CategoryTheory.Sheaf

theorem exact_of_exact (X Y Z : Cᵒᵖ ⥤ A) (f : X ⟶ Y) (g : Y ⟶ Z) (e : Exact f g) :
    Exact ((presheafToSheaf J A).map f) ((presheafToSheaf J A).map g) :=
  by
  rw [Abelian.exact_iff] at *
  constructor
  · rw [← Functor.map_comp, e.1]; simp
  · let K := kernel g
    let Q := cokernel f
    let P := presheaf_to_Sheaf J A
    let eK : P.obj K ≅ kernel (P.map g) := PreservesKernel.iso _ _
    let eQ : P.obj Q ≅ cokernel (P.map f) := PreservesCokernel.iso _ _
    have : kernel.ι (P.map g) = eK.inv ≫ P.map (kernel.ι g) :=
      by
      dsimp [eK]
      rw [Iso.eq_inv_comp]
      simp only [PreservesKernel.iso_hom, kernel_comparison_comp_ι]
    rw [this]; clear this
    have : cokernel.π (P.map f) = P.map (cokernel.π f) ≫ eQ.hom :=
      by
      dsimp [eQ]; rw [← Iso.comp_inv_eq]
      simp only [PreservesCokernel.iso_inv, π_comp_cokernel_comparison]
    rw [this]; clear this
    simp only [Category.assoc, e.2, ← P.map_comp_assoc, P.map_zero, zero_comp, comp_zero]

instance presheafToSheaf_additive : Functor.Additive (presheafToSheaf J A) :=
  by
  apply (config := { instances := false }) Functor.additive_of_preservesBinaryBiproducts
  apply (config := { instances := false }) CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts
  infer_instance
  apply CategoryTheory.Limits.preservesBinaryBiproductsOfPreservesBinaryCoproducts
  infer_instance

theorem map_presheafToSheaf_homology'_zero_of_homology'_zero (D : ChainComplex (Cᵒᵖ ⥤ A) ℕ)
    (h : ∀ i : ℕ, IsZero (D.homology' i)) :
    ∀ i : ℕ, IsZero ((((presheafToSheaf J A).mapHomologicalComplex _).obj D).homology' i) :=
  by
  rw [← ChainComplex.epi_and_exact_iff_zero_homology'] at *
  constructor
  · haveI := h.1; apply CategoryTheory.preserves_epi_of_preservesColimit
  · intro i
    apply exact_of_exact
    apply h.2

theorem sheafificationExact : Functor.Exact (presheafToSheaf J A) := fun X Y Z f g h =>
  exact_of_exact _ _ _ _ _ h

end CategoryTheory.Sheaf

namespace CategoryTheory

instance evaluation_additive (X : C) : Functor.Additive ((evaluation C A).obj X) :=
  ⟨fun F G η γ => rfl⟩

def evaluationHomologyIso (X Y Z : C ⥤ A) (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (t : C) :
    (homology' f g w).obj t ≅ homology' (f.app t) (g.app t) <| by rw [← NatTrans.comp_app, w]; simp
    where
  hom :=
    homology'.lift _ _ _ ((homology'.ι f g w).app t ≫ (NatTrans.cokernelObjIso f t).hom)
      (by
        rw [Category.assoc]; let e := _; change _ ≫ e = _
        have he : e = (cokernel.desc f g w).app t :=
          by
          dsimp [e]
          rw [← Iso.eq_inv_comp]
          ext
          simp
        rw [he, ← NatTrans.comp_app]
        simp only [homology'.condition_ι, NatTrans.app_zero])
  inv :=
    homology'.desc' _ _ _ ((NatTrans.kernelObjIso g t).inv ≫ (homology'.π' f g w).app t)
      (by
        rw [← Category.assoc]; let e := _; change e ≫ _ = _
        have he : e = (kernel.lift g f w).app t :=
          by
          dsimp [e]; rw [Iso.comp_inv_eq]
          ext
          simp
        rw [he, ← NatTrans.comp_app]
        simp only [homology'.condition_π', NatTrans.app_zero])
  hom_inv_id := by
    let a := _; change a ≫ _ = _
    have : epi ((homology'.π' f g w).app t) :=
      by
      rw [Abelian.epi_iff_cokernel_π_eq_zero]
      let b := homology'.π' f g w
      have : cokernel.π (b.app t) = (cokernel.π b).app t ≫ (NatTrans.cokernelObjIso b _).hom :=
        by simp
      rw [this, ← Iso.eq_comp_inv, zero_comp]
      suffices cokernel.π b = 0 by simp [this]
      rw [← Abelian.epi_iff_cokernel_π_eq_zero]
      dsimp [b, homology'.π']
      apply epi_comp
    rw [← cancel_epi ((homology'.π' f g w).app t)]
    have ha :
      (homology'.π' f g w).app t ≫ a = (NatTrans.kernelObjIso _ _).hom ≫ homology'.π' _ _ _ :=
      by
      dsimp [a]
      apply homology'.hom_to_ext
      simp only [Category.assoc, homology'.lift_ι, homology'.π'_ι,
        NatTrans.kernelObjIso_hom_ι_assoc]
      rw [← Category.assoc, ← Iso.eq_comp_inv]
      simp only [Category.assoc, NatTrans.cokernelObjIso_π_inv]
      rw [← NatTrans.comp_app, homology'.π'_ι, NatTrans.comp_app]
    rw [reassoc_of ha]
    simp only [homology'.π'_desc', Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    apply homology'.hom_from_ext; apply homology'.hom_to_ext
    simp only [Category.assoc, homology'.π'_desc'_assoc, homology'.lift_ι, Category.comp_id,
      homology'.π'_ι]
    rw [Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv, ← NatTrans.comp_app, homology'.π'_ι]
    simp

-- Homology of functors is computed pointwise...
theorem homology'_zero_of_eval (D : ChainComplex (C ⥤ A) ℕ)
    (h :
      ∀ (X : C) (i : ℕ),
        IsZero (((((evaluation C A).obj X).mapHomologicalComplex _).obj D).homology' i)) :
    ∀ i : ℕ, IsZero (D.homology' i) :=
  by
  rw [← ChainComplex.epi_and_exact_iff_zero_homology']
  constructor
  · apply (config := { instances := false }) NatTrans.epi_of_epi_app
    intro X
    specialize h X
    rw [← ChainComplex.epi_and_exact_iff_zero_homology'] at h 
    exact h.1
  · intro i; rw [Preadditive.exact_iff_homology'_zero]
    refine' ⟨_, _⟩
    · ext X; specialize h X
      rw [← ChainComplex.epi_and_exact_iff_zero_homology'] at h ; replace h := h.2 i
      rw [Preadditive.exact_iff_homology'_zero] at h 
      obtain ⟨w, hw⟩ := h; exact w
    · refine' ⟨IsZero.isoZero _⟩
      apply Functor.isZero
      intro X
      specialize h X (i + 1)
      refine' IsZero.of_iso _ (CategoryTheory.evaluationHomologyIso _ _ _ _ _ _ _)
      apply IsZero.of_iso h
      symm; apply homology_iso <;> exact rfl

end CategoryTheory

