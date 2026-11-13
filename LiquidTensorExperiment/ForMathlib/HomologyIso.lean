import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Homology

#align_import for_mathlib.homology_iso

namespace CategoryTheory

open CategoryTheory.Limits

variable {A ι : Type _} [Category A] [Abelian A] {c : ComplexShape ι} (X : HomologicalComplex A c)

variable (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k)

section

noncomputable section

@[simps]
def kernelDFromIso : kernel (X.dFrom j) ≅ kernel (X.d j k)
    where
  Hom :=
    kernel.lift _ (kernel.ι _)
      (by
        apply_fun fun e => e ≫ (X.X_next_iso hjk).inv
        swap
        · intro u v h
          apply_fun fun e => e ≫ (X.X_next_iso hjk).Hom at h 
          simpa using h
        dsimp
        rw [category.assoc, ← X.d_from_eq hjk]
        simp)
  inv :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [X.d_from_eq hjk]
        simp)
  hom_inv_id' := by ext; simp
  inv_hom_id' := by ext; simp

@[reassoc]
theorem kernel_lift_comp_kernelDFromIso_hom :
    kernel.lift (X.dFrom j) (X.dTo j) (by simp) ≫ (kernelDFromIso X j k hjk).Hom =
      kernel.lift _ (X.dTo _) (by simp [X.d_to_eq hij]) :=
  by ext; dsimp; simp

theorem kernel_lift_eq :
    kernel.lift (X.d j k) (HomologicalComplex.dTo X j) (by simp [X.d_to_eq hij]) =
      (X.xPrevIso hij).Hom ≫ kernel.lift _ _ (X.d_comp_d i j k) :=
  by
  ext
  dsimp
  simp [X.d_to_eq hij]

end

-- TODO: replace this with the defn below it
noncomputable def homologyIso : (homology'Functor A _ j).obj X ≅ homology' _ _ (X.d_comp_d i j k)
    where
  Hom :=
    homology'.desc' _ _ _ ((kernelDFromIso _ _ k hjk).Hom ≫ homology'.π' _ _ _)
      (by
        rw [kernel_lift_comp_kernel_d_from_iso_hom_assoc _ _ _ _ hij hjk,
          kernel_lift_eq _ _ _ _ hij hjk]
        simp only [category.assoc, homology'.condition_π', comp_zero])
  inv :=
    homology'.desc' _ _ _ ((kernelDFromIso _ _ k hjk).inv ≫ homology'.π' _ _ _)
      (by
        have := kernel_lift_comp_kernel_d_from_iso_hom X i j k hij hjk
        rw [← iso.eq_comp_inv, kernel_lift_eq _ _ _ _ hij hjk, category.assoc, ← iso.inv_comp_eq] at
          this 
        rw [← category.assoc, ← this]
        simp only [category.assoc, homology'.condition_π', comp_zero])
  hom_inv_id' := by ext;
    simp only [category.assoc, kernel_d_from_iso_inv, kernel_d_from_iso_hom,
      homology'.π'_desc'_assoc, homology'.π'_ι, kernel.lift_ι_assoc, category.id_comp]
  inv_hom_id' := by ext;
    simp only [category.assoc, kernel_d_from_iso_hom, kernel_d_from_iso_inv,
      homology'.π'_desc'_assoc, homology'.π'_ι, kernel.lift_ι_assoc, category.id_comp]

noncomputable def homologyIso' :
    (homology'Functor A _ j).obj X ≅ homology' _ _ (X.d_comp_d i j k) :=
  by
  refine' homology'.mapIso _ _ _ _ _
  · refine' arrow.iso_mk (X.X_prev_iso hij) (iso.refl _) _
    dsimp; simp only [X.d_to_eq hij, category.comp_id]
  · refine' arrow.iso_mk (iso.refl _) (X.X_next_iso hjk) _
    dsimp; simp only [X.d_from_comp_X_next_iso hjk, category.id_comp]
  · rfl

noncomputable def homology'_iso_map {X Y : HomologicalComplex A c} (f : X ⟶ Y) :
    (homology'Functor A _ j).map f =
      (homologyIso' X _ _ _ hij hjk).Hom ≫
        homology'.map _ _ ⟨f.f i, f.f j, f.comm _ _⟩ ⟨f.f j, f.f k, f.comm _ _⟩ rfl ≫
          (homologyIso' Y _ _ _ hij hjk).inv :=
  by
  simp only [homology'Functor_map, homology_iso', HomologicalComplex.Hom.sqFrom_left,
    homology'.mapIso, homology'.map_comp]
  congr 1 <;> ext
  ·
    simp only [HomologicalComplex.Hom.sqTo_left, comma.comp_left, arrow.iso_mk_hom_left,
      arrow.iso_mk_inv_left, f.prev_eq hij]
  · simp only [HomologicalComplex.Hom.sqTo_right, comma.comp_right, arrow.iso_mk_hom_right,
      iso.refl_hom, arrow.iso_mk_inv_right, iso.refl_inv, category.id_comp]
    erw [category.comp_id]
  · simp only [HomologicalComplex.Hom.sqFrom_left, comma.comp_left, arrow.iso_mk_hom_left,
      iso.refl_hom, arrow.iso_mk_inv_left, iso.refl_inv, category.id_comp]
    erw [category.comp_id]
  ·
    simp only [HomologicalComplex.Hom.sqFrom_right, comma.comp_right, arrow.iso_mk_hom_right,
      arrow.iso_mk_inv_right, f.next_eq hjk]

noncomputable def homology'_iso_inv_homology'Functor_map {X Y : HomologicalComplex A c}
    (f : X ⟶ Y) :
    (homologyIso' X _ _ _ hij hjk).inv ≫ (homology'Functor A _ j).map f =
      homology'.map _ _ ⟨f.f i, f.f j, f.comm _ _⟩ ⟨f.f j, f.f k, f.comm _ _⟩ rfl ≫
        (homologyIso' Y _ _ _ hij hjk).inv :=
  by rw [iso.inv_comp_eq, homology_iso_map]

attribute [reassoc] cokernel.map_desc

end CategoryTheory

