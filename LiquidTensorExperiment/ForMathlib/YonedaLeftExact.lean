import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Kernels

#align_import for_mathlib.yoneda_left_exact

noncomputable section

universe v

namespace CategoryTheory

namespace Limits

section KernelComparison

variable {C D : Type _} [Category.{v} C] [Category.{v} D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]

theorem kernelComparison_isIso_of_isLimit {A₁ A₂ : C} (f : A₁ ⟶ A₂) [HasKernel f]
    [HasKernel (F.map f)] (s : KernelFork f) (hs₁ : IsLimit s)
    (hs₂ :
      IsLimit
        (KernelFork.ofι (F.map s.ι)
          (show _ ≫ F.map f = 0 by rw [← F.map_comp, KernelFork.condition, F.map_zero]))) :
    IsIso (Limits.kernelComparison f F) :=
  by
  let α : kernel f ≅ s.X := IsLimit.conePointUniqueUpToIso (limit.isLimit _) hs₁
  let β : F.obj s.X ≅ kernel (F.map f) :=
    IsLimit.conePointUniqueUpToIso hs₂ (limit.isLimit _)
  suffices Limits.kernelComparison f F = (F.map_iso α ≪≫ β).hom by rw [this]; infer_instance
  rw [← cancel_mono (kernel.ι (F.map f))]
  dsimp only [α, β]
  simp only [kernel_comparison_comp_ι, Iso.trans_hom, Fork.ofι_π_app, Functor.mapIso_hom,
    Category.assoc, limit.conePointUniqueUpToIso_hom_comp, ← F.map_comp]
  congr
  rw [← cancel_epi ((limit.isLimit (CategoryTheory.Limits.parallelPair f 0)).conePointUniqueUpToIso hs₁).inv]
  simp only [Iso.inv_hom_id_assoc, limit.conePointUniqueUpToIso_inv_comp, Fork.app_zero_eq_ι]

end KernelComparison

variable {C : Type _} [Category C] [Preadditive C]

theorem AddCommGroupCat.kernelForkIsLimit {X Y : AddCommGroupCat} (φ : X ⟶ Y) (s : KernelFork φ)
    (hs₁ : Function.Injective s.ι) (hs₂ : ∀ x : X, φ x = 0 → ∃ z : s.pt, s.ι z = x) : IsLimit s :=
  by
  refine' IsLimit.ofIsoLimit (AddCommGroupCat.kernelIsLimit φ) _
  let e : s.X ≃+ φ.ker :=
    { toFun := fun w =>
        ⟨s.ι w, by
          rw [AddMonoidHom.mem_ker]
          exact congr_arg (fun f : s.X ⟶ Y => (f w : Y)) s.condition⟩
      invFun := fun x => (hs₂ x.1 x.2).some
      left_inv := fun w => by apply hs₁; exact (hs₂ _ _).choose_spec
      right_inv := fun x => by ext; exact (hs₂ x.1 x.2).choose_spec
      map_add' := fun w₁ w₂ => by ext; simp only [map_add, AddSubmonoid.mk_add_mk, SetLike.coe_mk] }
  symm
  refine' Cones.ext (AddEquiv.toAddCommGroupCatIso e) _
  rintro (_ | _)
  · ext; rfl
  · ext; dsimp [e]; simp only [KernelFork.app_one, comp_zero]

instance preadditiveYoneda_kernelComparison_isIso (B : C) {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂)
    [HasKernel f] : IsIso (Limits.kernelComparison f (preadditiveYoneda.obj B)) :=
  by
  let hs₁ : is_limit (_ : kernel_fork f) := limit.isLimit _
  apply CategoryTheory.Limits.kernelComparison_isIso_of_isLimit (preadditive_yoneda.obj B) f _ hs₁
  apply AddCommGroupCat.kernelForkIsLimit
  · intro g₁ g₂ h
    dsimp at g₁ g₂ h ⊢
    rw [cancel_epi (kernel.ι f).unop] at h 
    exact h
  · intro x hx
    dsimp at x hx ⊢
    use(kernel.lift f x.op (Quiver.Hom.unop_inj hx)).unop
    rw [← unop_comp]
    simp only [kernel.lift_ι, Quiver.Hom.unop_op]

end Limits

end CategoryTheory

