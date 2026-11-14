import LiquidTensorExperiment.ForMathlib.Derived.Defs
import LiquidTensorExperiment.ForMathlib.HomologyMap
import LiquidTensorExperiment.ForMathlib.HasHomology

#align_import for_mathlib.isQuasiIso

noncomputable section

open CategoryTheory Opposite

open HomotopyCategory

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {ι : Type _} {c : ComplexShape ι}

def Commsq.op {A B C D : 𝓐} {a : A ⟶ B} {b : B ⟶ D} {a' : A ⟶ C} {c : C ⟶ D}
    (sq : Commsq a a' b c) : Commsq c.op b.op a'.op a.op :=
  by
  apply Commsq.ofEq
  simp only [← op_comp, sq.w]

theorem homology'_map_homologyOpIso {A₁ B₁ C₁ A₂ B₂ C₂ : 𝓐} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
    (w₁ : f₁ ≫ g₁ = 0) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (w₂ : f₂ ≫ g₂ = 0) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (c : C₁ ⟶ C₂) (sq1 : Commsq f₁ a b f₂) (sq2 : Commsq g₁ b c g₂) :
    homology'.map' _ _ sq2.op sq1.op ≫ (HasHomology.homologyOpIso f₁ g₁ w₁).hom =
      (HasHomology.homologyOpIso _ _ _).hom ≫ (homology'.map' w₁ w₂ sq1 sq2).op :=
  by
  suffices
    (homology'.map' w₁ w₂ sq1 sq2).op =
      (homology'.has _ _ _).op.map (homology'.has _ _ _).op sq2.op sq1.op
    by
    erw [this, HasHomology.map_comp_map, HasHomology.map_comp_map]
    apply (homology'.has _ _ _).ext_π
    apply (homology'.has _ _ _).op.ext_ι
    simp only [HasHomology.π_map, HasHomology.lift_comp_ι, Iso.refl_hom]
    erw [HasHomology.lift_comp_ι]
    congr 2; rw [Category.id_comp, Category.comp_id]
  apply (homology'.has _ _ _).op.ext_π
  apply (homology'.has _ _ _).op.ext_ι
  simp only [HasHomology.π_map, HasHomology.lift_comp_ι]
  dsimp only [HasHomology.op, CategoryTheory.kernelOpOp_hom, CategoryTheory.cokernelOpOp_inv]
  simp only [← op_comp, homology'.map', Category.assoc, HasHomology.π_map_assoc,
    HasHomology.lift_comp_ι_assoc, Limits.kernel.lift_ι_assoc, Limits.cokernel.π_desc]
  simp only [op_comp, Category.assoc]
  rfl

theorem isQuasiIsoOfOp {X Y : (ChainComplex 𝓐 ℤ)ᵒᵖ} (f : X ⟶ Y)
    (h : IsQuasiIso ((Quotient _ _).map (HomologicalComplex.opFunctor.map f))) :
    IsQuasiIso ((Quotient _ _).map f.unop) :=
  by
  refine' ⟨fun i => _⟩
  obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
  rw [← HomotopyCategory.homology'Functor_map_factors, CategoryTheory.homology'_iso_map (i + 1 + 1) (i + 1) i]
  swap; · dsimp; rfl; swap; · dsimp; rfl
  apply (config := { instances := false }) IsIso.comp_isIso; · infer_instance
  apply (config := { instances := false }) IsIso.comp_isIso; swap; · infer_instance
  have aux := @IsQuasiIso.cond _ _ _ _ _ _ _ _ h (i + 1)
  rw [← HomotopyCategory.homology'Functor_map_factors, CategoryTheory.homology'_iso_map i (i + 1) (i + 1 + 1)] at
    aux 
  swap; · dsimp; rfl; swap; · dsimp; rfl
  replace aux := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ aux
  replace aux := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ _ aux
  rw [← CategoryTheory.isIso_op_iff]
  refine'
    isIso_of_square _ (HasHomology.homologyOpIso _ _ _).hom (HasHomology.homologyOpIso _ _ _).hom _
      _ aux _ _
  swap; · infer_instance; swap; · infer_instance
  rw [homology'.map_eq, homology'.map_eq, ← homology'_map_homologyOpIso]
  congr 2

