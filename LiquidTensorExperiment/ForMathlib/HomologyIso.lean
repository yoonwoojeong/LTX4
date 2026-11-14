import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Homology

#align_import for_mathlib.homologyIso

namespace CategoryTheory

open CategoryTheory.Limits

variable {A ι : Type _} [Category A] [Abelian A] {c : ComplexShape ι} (X : HomologicalComplex A c)

variable (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k)

-- Porting note: Lean 3's `noncomputable theory` inside this section
noncomputable section

@[simps]
def kernelDFromIso : kernel (X.dFrom j) ≅ kernel (X.d j k)
    where
  hom :=
    kernel.lift _ (kernel.ι _)
      (by
        apply_fun fun e => e ≫ (X.xNextIso hjk).inv
        swap
        · intro u v h
          apply_fun fun e => e ≫ (X.xNextIso hjk).hom at h 
          simpa using h
        dsimp
        rw [Category.assoc, ← X.dFrom_eq hjk]
        simp)
  inv :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [X.dFrom_eq hjk]
        simp)
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

-- Porting note: Lean 4 does not include section variables that are only used inside a
-- tactic block of the statement, so the binders are stated explicitly (as in Lean 3).
@[reassoc]
theorem kernel_lift_comp_kernelDFromIso_hom (X : HomologicalComplex A c) (i j k : ι)
    (hij : c.Rel i j) (hjk : c.Rel j k) :
    kernel.lift (X.dFrom j) (X.dTo j) (by simp) ≫ (kernelDFromIso X j k hjk).hom =
      kernel.lift _ (X.dTo _) (by simp [X.dTo_eq hij]) :=
  by ext; dsimp; simp

theorem kernel_lift_eq (X : HomologicalComplex A c) (i j k : ι) (hij : c.Rel i j)
    (hjk : c.Rel j k) :
    kernel.lift (X.d j k) (HomologicalComplex.dTo X j) (by simp [X.dTo_eq hij]) =
      (X.xPrevIso hij).hom ≫ kernel.lift _ _ (X.d_comp_d i j k) :=
  by
  ext
  dsimp
  simp [X.dTo_eq hij]

end

-- TODO: replace this with the defn below it
noncomputable def homologyIso : (homology'Functor A _ j).obj X ≅ homology' _ _ (X.d_comp_d i j k)
    where
  hom :=
    homology'.desc' _ _ _ ((kernelDFromIso _ _ k hjk).hom ≫ homology'.π' _ _ _)
      (by
        rw [CategoryTheory.kernel_lift_comp_kernelDFromIso_hom_assoc _ _ _ _ hij hjk,
          kernel_lift_eq _ _ _ _ hij hjk]
        simp only [Category.assoc, homology'.condition_π', comp_zero])
  inv :=
    homology'.desc' _ _ _ ((kernelDFromIso _ _ k hjk).inv ≫ homology'.π' _ _ _)
      (by
        have := CategoryTheory.kernel_lift_comp_kernelDFromIso_hom X i j k hij hjk
        rw [← Iso.eq_comp_inv, kernel_lift_eq _ _ _ _ hij hjk, Category.assoc,
          ← Iso.inv_comp_eq] at this
        rw [← Category.assoc, ← this]
        simp only [Category.assoc, homology'.condition_π', comp_zero])
  hom_inv_id := by
    apply homology'.hom_from_ext
    simp only [Category.assoc, CategoryTheory.kernelDFromIso_inv, CategoryTheory.kernelDFromIso_hom,
      homology'.π'_desc'_assoc, homology'.π'_desc', homology'.π'_ι, kernel.lift_ι_assoc,
      Category.id_comp]
    -- Porting note: Lean 3's `simp` set also closed the remaining kernel goal
    rw [← Category.assoc]
    erw [Category.comp_id]
    convert Category.id_comp _ using 2
    apply equalizer.hom_ext
    simp
  inv_hom_id := by
    apply homology'.hom_from_ext
    simp only [Category.assoc, CategoryTheory.kernelDFromIso_hom, CategoryTheory.kernelDFromIso_inv,
      homology'.π'_desc'_assoc, homology'.π'_desc', homology'.π'_ι, kernel.lift_ι_assoc,
      Category.id_comp]
    -- Porting note: Lean 3's `simp` set also closed the remaining kernel goal
    rw [← Category.assoc]
    erw [Category.comp_id]
    convert Category.id_comp _ using 2
    apply equalizer.hom_ext
    simp

noncomputable def homologyIso' :
    (homology'Functor A _ j).obj X ≅ homology' _ _ (X.d_comp_d i j k) :=
  by
  refine' homology'.mapIso _ _ _ _ _
  · refine' Arrow.isoMk (X.xPrevIso hij) (Iso.refl _) _
    dsimp; rw [X.dTo_eq hij]; simp only [Category.comp_id]
  · refine' Arrow.isoMk (Iso.refl _) (X.xNextIso hjk) _
    dsimp; simp only [X.dFrom_comp_xNextIso hjk, Category.id_comp]
  · rfl

noncomputable def homology'_iso_map {X Y : HomologicalComplex A c} (f : X ⟶ Y) :
    (homology'Functor A _ j).map f =
      (homologyIso' X _ _ _ hij hjk).hom ≫
        homology'.map _ _ ⟨f.f i, f.f j, f.comm _ _⟩ ⟨f.f j, f.f k, f.comm _ _⟩ rfl ≫
          (homologyIso' Y _ _ _ hij hjk).inv :=
  by
  simp only [homology'Functor_map, CategoryTheory.homologyIso', HomologicalComplex.Hom.sqFrom_left,
    homology'.mapIso, homology'.map_comp]
  congr 1 <;> ext
  -- Porting note: the Lean 3 `simp only` sets do not apply verbatim in Lean 4
  · simpa using f.prev_eq hij
  · simp
  · simp
  · simpa using f.next_eq hjk

noncomputable def homology'_iso_inv_homology'Functor_map {X Y : HomologicalComplex A c}
    (f : X ⟶ Y) :
    (homologyIso' X _ _ _ hij hjk).inv ≫ (homology'Functor A _ j).map f =
      homology'.map _ _ ⟨f.f i, f.f j, f.comm _ _⟩ ⟨f.f j, f.f k, f.comm _ _⟩ rfl ≫
        (homologyIso' Y _ _ _ hij hjk).inv :=
  by rw [Iso.inv_comp_eq, CategoryTheory.homology'_iso_map]

attribute [reassoc] cokernel.map_desc

end CategoryTheory

