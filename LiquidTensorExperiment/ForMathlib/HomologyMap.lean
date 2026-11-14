import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp
import LiquidTensorExperiment.ForMathlib.HasHomology

#align_import for_mathlib.homologyMap

noncomputable section

open CategoryTheory Opposite

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {ι : Type _} {c : ComplexShape ι}

theorem isIso_of_square {A B C D : 𝓐} (a : A ⟶ B) (b : B ⟶ D) (a' : A ⟶ C) (c : C ⟶ D)
    (w : a ≫ b = a' ≫ c) (ha : IsIso a) (hb : IsIso b) (ha' : IsIso a') : IsIso c :=
  by
  have hc : c = inv a' ≫ a ≫ b := by rw [IsIso.eq_inv_comp, w]
  rw [hc]; infer_instance

def homology'.map' {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐} {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)
    {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0) {a : A₁ ⟶ A₂} {b : B₁ ⟶ B₂} {c : C₁ ⟶ C₂}
    (sq1 : Commsq f₁ a b f₂) (sq2 : Commsq g₁ b c g₂) : homology' f₁ g₁ w₁ ⟶ homology' f₂ g₂ w₂ :=
  (homology'.has f₁ g₁ w₁).map (homology'.has f₂ g₂ w₂) sq1 sq2

theorem homology'.map_eq {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐} {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)
    {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0) (sq1 : Arrow.mk f₁ ⟶ Arrow.mk f₂)
    (sq2 : Arrow.mk g₁ ⟶ Arrow.mk g₂) (H) :
    homology'.map w₁ w₂ sq1 sq2 H =
      @homology'.map' _ _ _ _ _ _ _ _ _ _ _ w₁ _ _ w₂ sq1.left sq1.right sq2.right
        (Commsq.ofEq sq1.w.symm) (Commsq.ofEq <| by rw [H]; exact sq2.w.symm) :=
  by
  apply (homology'.has f₂ g₂ w₂).ext_ι
  erw [HasHomology.map_ι]
  apply (homology'.has f₁ g₁ w₁).ext_π
  erw [← Category.assoc, homology'.π'_map, Category.assoc, homology'.π'_ι, HasHomology.π_comp_desc,
    Limits.kernel.lift_ι_assoc, Category.assoc]

