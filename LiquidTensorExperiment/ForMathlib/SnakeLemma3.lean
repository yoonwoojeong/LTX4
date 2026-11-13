import LiquidTensorExperiment.ForMathlib.SnakeLemma2
import Mathlib.CategoryTheory.Abelian.Homology
import LiquidTensorExperiment.ForMathlib.ExactSeq2

#align_import for_mathlib.snake_lemma3

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜]

namespace CategoryTheory

local notation "kernel_map" => kernel.map _ _ _ _

local notation "cokernel_map" => cokernel.map _ _ _ _

namespace Snake

theorem col_exact_aux (X : CochainComplex 𝒜 ℤ) :
    ExactSeq 𝒜
      [kernel.ι (HomologicalComplex.dTo X 0),
        kernel.lift (HomologicalComplex.dFrom X 0) (HomologicalComplex.dTo X 0) (by simp),
        homology'.π' (HomologicalComplex.dTo X 0) (HomologicalComplex.dFrom X 0) (by simp)] :=
  by
  apply exact_seq.cons
  · rw [abelian.exact_iff]
    refine' ⟨by ext; simp, _⟩
    have :
      kernel.ι (kernel.lift (HomologicalComplex.dFrom X 0) (HomologicalComplex.dTo X 0) _) =
        kernel.lift _ (kernel.ι _) _ ≫ kernel.ι (HomologicalComplex.dTo X 0) :=
      by simp
    rw [this]
    simp only [category.assoc, cokernel.condition, comp_zero]
    have :
      HomologicalComplex.dTo X 0 =
        kernel.lift (HomologicalComplex.dFrom X 0) (HomologicalComplex.dTo X 0) (by simp) ≫
          kernel.ι _ :=
      by simp
    slice_lhs 2 3 => rw [this]
    rw [kernel.condition_assoc]
    simp
  · rw [← exact_iff_exact_seq]
    change exact _ (_ ≫ _)
    rw [exact_comp_iso]
    apply abelian.exact_cokernel

theorem row_exact₁_aux (X Y Z : CochainComplex 𝒜 ℤ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Exact (f.f (-1)) (g.f (-1))) [Epi (g.f (-1))] [Epi (g.f 0)] [Epi (g.f 1)] [Mono (f.f (-1))]
    [Mono (f.f 0)] [Mono (f.f 1)] :
    Exact (HomologicalComplex.Hom.prev f 0) (HomologicalComplex.Hom.prev g 0) :=
  by
  rw [f.prev_eq, g.prev_eq]
  rotate_left 2; exact -1; swap; exact -1; simp; swap; simp
  simp
  rw [← category.assoc, exact_comp_iso]
  apply CategoryTheory.exact_comp_inv_hom_comp _ h

theorem row_exact₂_aux (X Y Z : CochainComplex 𝒜 ℤ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h0 : Exact (f.f 0) (g.f 0)) (h1 : Exact (f.f 1) (g.f 1)) [Epi (g.f (-1))] [Epi (g.f 0)]
    [Epi (g.f 1)] [Mono (f.f (-1))] [Mono (f.f 0)] [Mono (f.f 1)] :
    Exact
      (kernel.lift (HomologicalComplex.dFrom Y 0) (kernel.ι (HomologicalComplex.dFrom X 0) ≫ f.f 0)
        (by simp))
      (kernel.lift (HomologicalComplex.dFrom Z 0) (kernel.ι (HomologicalComplex.dFrom Y 0) ≫ g.f 0)
        (by simp)) :=
  by
  have : mono (HomologicalComplex.Hom.next f 0) :=
    by
    rw [f.next_eq]
    rotate_left 2; exact 1; swap; simp
    apply (config := { instances := false }) mono_comp
    swap
    apply (config := { instances := false }) mono_comp
    all_goals infer_instance
  have : exact (HomologicalComplex.Hom.next f 0) (HomologicalComplex.Hom.next g 0) :=
    by
    rw [f.next_eq, g.next_eq]
    rotate_left 2; exact 1; swap; exact 1; simp; swap; simp
    simp
    rw [← category.assoc, exact_comp_iso]
    apply CategoryTheory.exact_comp_inv_hom_comp _ h1
  have S :=
    mk_of_sequence_hom (X.X 0) (Y.X 0) (Z.X 0) (X.X_next 0) (Y.X_next 0) (Z.X_next 0) (f.f 0)
      (g.f 0) (X.d_from 0) (Y.d_from 0) (Z.d_from 0) (f.next 0) (g.next 0) (by simp) (by simp) h0
      this
  exact S.six_term_exact_seq.pair

theorem mk_of_homology (X Y Z : CochainComplex 𝒜 ℤ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hn1 : Exact (f.f (-1)) (g.f (-1))) (h0 : Exact (f.f 0) (g.f 0)) (h1 : Exact (f.f 1) (g.f 1))
    [Epi (g.f (-1))] [Epi (g.f 0)] [Epi (g.f 1)] [Mono (f.f (-1))] [Mono (f.f 0)] [Mono (f.f 1)] :
    Snake
      (-- the objects
        kernel
        (X.dTo 0))
      (kernel (Y.dTo 0)) (kernel (Z.dTo 0)) (X.xPrev 0) (Y.xPrev 0) (Z.xPrev 0) (kernel (X.dFrom 0))
      (kernel (Y.dFrom 0)) (kernel (Z.dFrom 0)) ((homology'Functor _ _ 0).obj X)
      ((homology'Functor _ _ 0).obj Y) ((homology'Functor _ _ 0).obj Z)
      (-- the maps
        kernel.map
        _ _ (f.prev _) (f.f _) (by simp))
      (kernel.map _ _ (g.prev _) (g.f _) (by simp)) (kernel.ι _) (kernel.ι _) (kernel.ι _)
      (f.prev _) (g.prev _) (kernel.lift _ (X.dTo _) (by simp)) (kernel.lift _ (Y.dTo _) (by simp))
      (kernel.lift _ (Z.dTo _) (by simp)) (kernel.map _ _ (f.f _) (f.next _) (by simp))
      (kernel.map _ _ (g.f _) (g.next _) (by simp)) (homology'.π' _ _ _) (homology'.π' _ _ _)
      (homology'.π' _ _ _) ((homology'Functor _ _ _).map f) ((homology'Functor _ _ _).map g) :=
  { row_exact₁ := row_exact₁_aux _ _ _ _ _ hn1
    row_exact₂ := row_exact₂_aux _ _ _ _ _ h0 h1
    row_epi := by
      rw [g.prev_eq]
      rotate_left 2; exact -1
      swap; simp
      apply (config := { instances := false }) epi_comp
      swap
      apply (config := { instances := false }) epi_comp
      all_goals infer_instance
    row_mono := inferInstance
    col_exact_a := col_exact_aux _
    col_exact_b := col_exact_aux _
    col_exact_c := col_exact_aux _
    col_mono_a := inferInstance
    col_mono_b := inferInstance
    col_mono_c := inferInstance
    col_epi_a := epi_comp _ _
    col_epi_b := epi_comp _ _
    col_epi_c := epi_comp _ _
    sq_a₀ := by simp
    sq_b₀ := by simp
    sq_a₁ := by ext; simp
    sq_b₁ := by ext; simp
    sq_a₂ := by simp
    sq_b₂ := by simp }

end Snake

end CategoryTheory

