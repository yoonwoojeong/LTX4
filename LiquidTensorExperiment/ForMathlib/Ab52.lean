import LiquidTensorExperiment.ForMathlib.Ab5

#align_import for_mathlib.ab52

namespace CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [Limits.HasColimits A] [AB5 A]

def mono_colimMap_of_mono {J : Type v} [SmallCategory J] [IsFiltered J] {F G : J ⥤ A} (η : F ⟶ G)
    [∀ i, Mono (η.app i)] : Mono (Limits.colimMap η) :=
  by
  haveI : limits.preservesFiniteLimits (Limits.colim : (J ⥤ A) ⥤ A) :=
    Functor.preservesFiniteLimitsOfExact _ (AB5.cond A J)
  rw [Abelian.mono_iff_kernel_ι_eq_zero]
  let e : Limits.kernel (Limits.colimMap η) ≅ Limits.colimit (Limits.kernel η) :=
    (Limits.PreservesKernel.iso (Limits.colim : (J ⥤ A) ⥤ A) η).symm
  have he : Limits.kernel.ι (Limits.colimMap η) = e.hom ≫ Limits.colimMap (Limits.kernel.ι η) :=
    by
    dsimp [e]; rw [Iso.eq_inv_comp]; simp; dsimp [Limits.kernelComparison]
    erw [Limits.kernel.lift_ι]; rfl
  rw [he]
  simp only [Preadditive.IsIso.comp_left_eq_zero]
  ext j
  simp only [limits.ι_colim_map, Limits.comp_zero]
  let q : (Limits.kernel η).obj j ≅ Limits.kernel (η.app j) :=
    Limits.PreservesKernel.iso ((evaluation _ A).obj j) η
  have : (Limits.kernel.ι η).app j = q.hom ≫ Limits.kernel.ι _ := by simp;
    dsimp [Limits.kernelComparison]; simp
  rw [this]
  have : mono (η.app j) := inferInstance
  rw [Abelian.mono_iff_kernel_ι_eq_zero] at this 
  simp [this]

end CategoryTheory

