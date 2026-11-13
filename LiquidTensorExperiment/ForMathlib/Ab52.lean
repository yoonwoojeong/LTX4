import LiquidTensorExperiment.ForMathlib.Ab5

#align_import for_mathlib.ab52

namespace CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [Limits.HasColimits A] [AB5 A]

def mono_colimMap_of_mono {J : Type v} [SmallCategory J] [IsFiltered J] {F G : J ⥤ A} (η : F ⟶ G)
    [∀ i, Mono (η.app i)] : Mono (Limits.colimMap η) :=
  by
  haveI : limits.preserves_finite_limits (limits.colim : (J ⥤ A) ⥤ A) :=
    functor.preserves_finite_limits_of_exact _ (AB5.cond A J)
  rw [abelian.mono_iff_kernel_ι_eq_zero]
  let e : limits.kernel (limits.colim_map η) ≅ limits.colimit (limits.kernel η) :=
    (limits.preserves_kernel.iso (limits.colim : (J ⥤ A) ⥤ A) η).symm
  have he : limits.kernel.ι (limits.colim_map η) = e.hom ≫ limits.colim_map (limits.kernel.ι η) :=
    by
    dsimp [e]; rw [iso.eq_inv_comp]; simp; dsimp [limits.kernel_comparison]
    erw [limits.kernel.lift_ι]; rfl
  rw [he]
  simp only [preadditive.is_iso.comp_left_eq_zero]
  ext j
  simp only [limits.ι_colim_map, limits.comp_zero]
  let q : (limits.kernel η).obj j ≅ limits.kernel (η.app j) :=
    limits.preserves_kernel.iso ((evaluation _ A).obj j) η
  have : (limits.kernel.ι η).app j = q.hom ≫ limits.kernel.ι _ := by simp;
    dsimp [limits.kernel_comparison]; simp
  rw [this]
  have : mono (η.app j) := inferInstance
  rw [abelian.mono_iff_kernel_ι_eq_zero] at this 
  simp [this]

end CategoryTheory

