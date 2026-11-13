import LiquidTensorExperiment.ForMathlib.SnakeLemma

#align_import for_mathlib.snake_lemma_naturality

namespace CategoryTheory

local notation x "⟶[" D "]" y => D.map (SnakeDiagram.hom x y)

namespace SnakeLemma

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] {F G : SnakeDiagram ⥤ A} (η : F ⟶ G)

namespace δNaturalSetup

@[reassoc]
theorem aux1 (hF : IsSnakeInput F) (hG : IsSnakeInput G) :
    η.app (0, 2) ≫ hG.toKernel =
      hF.toKernel ≫
        kernel.lift _ (kernel.ι _ ≫ η.app _)
          (by simp only [category.assoc, ← η.naturality, kernel.condition_assoc, zero_comp]) :=
  by
  apply equalizer.hom_ext
  dsimp [is_snake_input.to_kernel]
  simp

@[reassoc]
theorem aux2 (hF : IsSnakeInput F) (hG : IsSnakeInput G) :
    kernel.lift ((1, 2)⟶[G](2, 2)) (kernel.ι ((1, 2)⟶[F](2, 2)) ≫ η.app (1, 2))
          (by simp only [category.assoc, ← η.naturality, kernel.condition_assoc, zero_comp]) ≫
        inv hG.cokernelToTopRightKernelToRightKernel =
      inv hF.cokernelToTopRightKernelToRightKernel ≫
        cokernel.desc _
          (kernel.lift _ (kernel.ι _ ≫ η.app _)
              (by simp only [category.assoc, ← η.naturality, kernel.condition_assoc, zero_comp]) ≫
            cokernel.π _)
          (by
            dsimp [is_snake_input.to_top_right_kernel]
            simp only [← category.assoc]; let t := _; change t ≫ _ = _
            have ht : t = η.app _ ≫ kernel.lift ((1, 1)⟶[G](2, 2)) ((1, 0)⟶[G](1, 1)) _ := by
              apply equalizer.hom_ext; simp
            rw [ht, category.assoc, cokernel.condition, comp_zero]) :=
  by
  simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.assoc]
  dsimp only [is_snake_input.cokernel_to_top_right_kernel_to_right_kernel]
  apply equalizer.hom_ext
  simp only [le_refl, and_true_iff, category.assoc, nat_trans.naturality, kernel.condition_assoc,
    zero_comp, true_and_iff, cokernel.condition, comp_zero, equalizer_as_kernel, kernel.lift_ι]
  apply coequalizer.hom_ext
  simp only [category.assoc, nat_trans.naturality, cokernel.π_desc_assoc, kernel.lift_ι_assoc,
    kernel.lift_ι]

@[reassoc]
theorem aux3 (hF : IsSnakeInput F) (hG : IsSnakeInput G) :
    kernel.lift hG.bottomLeftCokernelTo
          (kernel.ι hF.bottomLeftCokernelTo ≫
            cokernel.desc ((1, 0)⟶[F](2, 1)) (η.app (2, 1) ≫ cokernel.π ((1, 0)⟶[G](2, 1)))
              (by simp only [category.assoc, η.naturality_assoc, cokernel.condition, comp_zero]))
          (by
            dsimp [is_snake_input.bottom_left_cokernel_to]
            simp only [category.assoc]; let t := _; change _ ≫ t = _
            have ht : t = cokernel.desc ((1, 0)⟶[F](2, 1)) ((2, 1)⟶[F](2, 2)) _ ≫ η.app _ := by
              apply coequalizer.hom_ext; simp
            rw [ht, kernel.condition_assoc, zero_comp]) ≫
        inv hG.leftCokernelToKernelBottomLeftCokernelTo =
      inv hF.leftCokernelToKernelBottomLeftCokernelTo ≫
        cokernel.desc _ (η.app _ ≫ cokernel.π _)
          (by simp only [category.assoc, η.naturality_assoc, cokernel.condition, comp_zero]) :=
  by
  rw [is_iso.comp_inv_eq, category.assoc (inv _), is_iso.eq_inv_comp]
  dsimp [is_snake_input.left_cokernel_to_kernel_bottom_left_cokernel_to]
  apply coequalizer.hom_ext; apply equalizer.hom_ext
  simp only [nat_trans.naturality_assoc, category.assoc, cokernel.π_desc_assoc, cokernel.π_desc,
    kernel.lift_ι, kernel.lift_ι_assoc]

end δNaturalSetup

open δNaturalSetup

theorem δ_natural (hF : IsSnakeInput F) (hG : IsSnakeInput G) :
    η.app (0, 2) ≫ hG.δ = hF.δ ≫ η.app (3, 0) :=
  by
  dsimp only [is_snake_input.δ]
  simp only [category.assoc]
  rw [aux1_assoc η hF hG]
  rw [aux2_assoc η hF hG]
  simp_rw [cancel_epi]
  apply coequalizer.hom_ext
  dsimp only [is_snake_input.δ_aux]
  simp only [cokernel.π_desc_assoc, category.assoc]
  simp only [← category.assoc]; let t := _; change (t ≫ _) ≫ _ = _
  let s := _; change _ = ((s ≫ _) ≫ _) ≫ _
  have ht :
    t =
      s ≫
        kernel.lift _
          (kernel.ι _ ≫
            cokernel.desc _ (η.app _ ≫ cokernel.π _)
              (by simp only [category.assoc, η.naturality_assoc, cokernel.condition, comp_zero]))
          _
  rotate_left 2
  · dsimp only [is_snake_input.bottom_left_cokernel_to]; simp only [category.assoc]
    let t := _; change _ ≫ t = _
    have ht : t = cokernel.desc ((1, 0)⟶[F](2, 1)) ((2, 1)⟶[F](2, 2)) _ ≫ η.app _ :=
      by
      apply coequalizer.hom_ext
      simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, nat_trans.naturality]
    rw [ht, kernel.condition_assoc, zero_comp]
  · dsimp only [t, s]
    apply equalizer.hom_ext
    simp only [category.assoc, nat_trans.naturality_assoc, cokernel.π_desc, kernel.lift_ι,
      kernel.lift_ι_assoc]
  rw [ht]; dsimp only [s]; clear ht t s
  simp only [category.assoc]; congr 1
  rw [aux3_assoc η hF hG]; congr 1
  dsimp only [is_snake_input.cokernel_to]
  apply coequalizer.hom_ext
  simp only [cokernel.π_desc_assoc, category.assoc, cokernel.π_desc, nat_trans.naturality]

end SnakeLemma

end CategoryTheory

