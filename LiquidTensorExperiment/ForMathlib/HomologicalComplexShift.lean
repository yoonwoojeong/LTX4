import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Data.Int.Parity
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Generator
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.InjectiveResolution
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Preadditive.OfBiproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.Tactic.Ring
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.NegOnePow

#align_import for_mathlib.homological_complex_shift

attribute [local simp] CategoryTheory.Preadditive.zsmul_comp CategoryTheory.Preadditive.comp_zsmul

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable (V : Type u) [Category.{v} V] [Preadditive V]

namespace HomologicalComplex

theorem ComplexShape.up'_add_right_cancel {α : Type _} [AddCancelCommMonoid α] (a : α) {i j}
    (k : α) : (ComplexShape.up' a).Rel (i + k) (j + k) ↔ (ComplexShape.up' a).Rel i j := by dsimp;
  rw [add_assoc, add_comm k a, ← add_assoc]; exact add_left_inj _

theorem ComplexShape.up_add_right_cancel {α : Type _} [AddCancelCommMonoid α] [One α] {i j}
    (k : α) : (ComplexShape.up α).Rel (i + k) (j + k) ↔ (ComplexShape.up α).Rel i j :=
  ComplexShape.up'_add_right_cancel 1 k

@[simps]
def shiftFunctor (n : ℤ) : CochainComplex V ℤ ⥤ CochainComplex V ℤ
    where
  obj X :=
    { pt := fun i => X.pt (i + n)
      d := fun i j => n.neg_one_pow • X.d _ _
      shape' := fun i j h => by
        rw [X.shape (i + n) (j + n), smul_zero]
        rwa [complex_shape.up_add_right_cancel] }
  map X Y f := { f := fun i => f.f _ }

variable {V} {ι : Type _} {c : ComplexShape ι}

def xEqToIso (X : HomologicalComplex V c) {i j : ι} (h : i = j) : X.pt i ≅ X.pt j :=
  eqToIso <| congr_arg X.pt h

@[simp]
theorem xEqToIso_inv (X : HomologicalComplex V c) {i j : ι} (h : i = j) :
    (X.xEqToIso h).inv = (X.xEqToIso h.symm).Hom :=
  rfl

@[simp, reassoc]
theorem xEqToIso_d (X : HomologicalComplex V c) {i j k : ι} (h : i = j) :
    (X.xEqToIso h).Hom ≫ X.d j k = X.d i k := by subst h; exact category.id_comp _

@[simp, reassoc]
theorem x_d_eq_to_iso (X : HomologicalComplex V c) {i j k : ι} (h : j = k) :
    X.d i j ≫ (X.xEqToIso h).Hom = X.d i k := by subst h; exact category.comp_id _

@[simp, reassoc]
theorem xEqToIso_trans (X : HomologicalComplex V c) {i j k : ι} (h : i = j) (h' : j = k) :
    (X.xEqToIso h).Hom ≫ (X.xEqToIso h').Hom = (X.xEqToIso (h.trans h')).Hom := by
  simp [X_eq_to_iso]

@[simp]
theorem xEqToIso_refl (X : HomologicalComplex V c) {i : ι} : (X.xEqToIso (refl i)).Hom = 𝟙 _ :=
  rfl

@[simp, reassoc]
theorem xEqToIso_f {X Y : HomologicalComplex V c} (f : X ⟶ Y) {i j : ι} (h : i = j) :
    (X.xEqToIso h).Hom ≫ f.f j = f.f i ≫ (Y.xEqToIso h).Hom := by subst h; simp [X_eq_to_iso]

variable (V)

instance : HasShift (CochainComplex V ℤ) ℤ :=
  hasShiftMk _ _
    { f := shiftFunctor V
      ε :=
        NatIso.ofComponents
          (fun X =>
            Hom.isoOfComponents (fun i => X.xEqToIso (add_zero _).symm) fun i j r => by dsimp; simp)
          fun X Y f => by ext; dsimp; simp
      μ := fun n m =>
        NatIso.ofComponents
          (fun X =>
            Hom.isoOfComponents (fun i => X.xEqToIso (by rw [add_comm n m, add_assoc])) fun i j r =>
              by dsimp; simp [smul_smul, mul_comm])
          fun i j f => by ext; dsimp; simp
      associativity := fun m₁ m₂ m₃ X => by ext; dsimp; simp [X_eq_to_iso]
      left_unitality := fun n X => by ext; dsimp; simpa [X_eq_to_iso]
      right_unitality := fun n X => by ext; dsimp; simpa [X_eq_to_iso] }

attribute [local instance] endofunctor_monoidal_category

@[simp]
theorem shift_x (X : CochainComplex V ℤ) (n m : ℤ) : X⟦n⟧.pt m = X.pt (m + n) :=
  rfl

@[simp]
theorem shift_d (X : CochainComplex V ℤ) (n i j : ℤ) :
    X⟦n⟧.d i j = n.neg_one_pow • X.d (i + n) (j + n) :=
  rfl

@[simp]
theorem shift_f {X Y : CochainComplex V ℤ} (f : X ⟶ Y) (n i : ℤ) : f⟦n⟧'.f i = f.f (i + n) :=
  rfl

instance (n : ℤ) : Functor.Additive ((shiftMonoidalFunctor (CochainComplex V ℤ) ℤ).obj ⟨n⟩) where

instance shiftFunctor_additive (n : ℤ) : Functor.additive (shiftFunctor V n) where

variable {V}

def homotopyShift {X Y : CochainComplex V ℤ} {f g : X ⟶ Y} (h : Homotopy f g) (n : ℤ) :
    Homotopy (f⟦n⟧') (g⟦n⟧')
    where
  Hom i j := n.neg_one_pow • h.Hom _ _
  zero' i j r := by rw [← complex_shape.up_add_right_cancel n] at r ; simp [h.zero _ _ r]
  comm i := by
    dsimp; delta d_from d_to fromNext toPrev
    simp only [h.comm (i + n), dNext, prevD, add_left_inj, AddMonoidHom.mk'_apply, shift_d, shift_X,
      zsmul_comp, comp_zsmul, Int.negOnePow_smul_self]
    delta X_next X_prev; dsimp
    congr 3 <;> simp only [CochainComplex.next, CochainComplex.prev] <;> ring

variable (V)

def HomotopyCategory.shiftFunctor (n : ℤ) :
    HomotopyCategory V (ComplexShape.up ℤ) ⥤ HomotopyCategory V (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _ (shiftFunctor _ n ⋙ HomotopyCategory.quotient _ _)
    (by
      rintro X Y f g ⟨h⟩
      apply HomotopyCategory.eq_of_homotopy
      exact homotopy_shift h n)

def HomotopyCategory.shiftε : 𝟭 _ ≅ HomotopyCategory.shiftFunctor V 0 :=
  by
  refine' nat_iso.of_components _ _
  · rintro ⟨X⟩
    refine' (HomotopyCategory.quotient _ _).mapIso (hom.iso_of_components _ _)
    exact fun i => X.X_eq_to_iso (add_zero _).symm
    · introv ; dsimp; simp
  · rintro ⟨X⟩ ⟨Y⟩ f; dsimp
    rw [← HomotopyCategory.quotient_map_out f]
    erw [quotient.lift_map_functor_map]
    simp only [functor.comp_map, ← functor.map_comp]
    congr 1; ext; dsimp; simp

def HomotopyCategory.shiftFunctorAdd (n m : ℤ) :
    HomotopyCategory.shiftFunctor V n ⋙ HomotopyCategory.shiftFunctor V m ≅
      HomotopyCategory.shiftFunctor V (n + m) :=
  by
  refine' nat_iso.of_components _ _
  · rintro ⟨X⟩
    refine' (HomotopyCategory.quotient _ _).mapIso (hom.iso_of_components _ _)
    exact fun i => X.X_eq_to_iso (by rw [add_comm n m, add_assoc])
    · introv r; dsimp [homotopy_category.shift_functor]; simp [smul_smul, mul_comm]
  · rintro ⟨X⟩ ⟨Y⟩ f; dsimp
    rw [← HomotopyCategory.quotient_map_out f]
    erw [quotient.lift_map_functor_map]
    conv_rhs => erw [quotient.lift_map_functor_map]
    simp only [functor.comp_map, ← functor.map_comp]
    congr 1; ext; dsimp; simp

@[simp]
theorem HomotopyCategory.shiftFunctor_obj_as {X : CochainComplex V ℤ} (n : ℤ) :
    (HomotopyCategory.shiftFunctor V n).obj ⟨X⟩ = ⟨X⟦n⟧⟩ :=
  rfl

@[simp]
theorem HomotopyCategory.shiftFunctor_map_quotient (n : ℤ) {X Y : CochainComplex V ℤ} (f : X ⟶ Y) :
    (HomotopyCategory.shiftFunctor V n).map ((HomotopyCategory.quotient V _).map f) =
      (HomotopyCategory.quotient V _).map (f⟦n⟧') :=
  rfl

theorem quotient_eqToHom {X Y : HomotopyCategory V (ComplexShape.up ℤ)} (h : X = Y) :
    eqToHom h = (HomotopyCategory.quotient V (ComplexShape.up ℤ)).map (eqToHom (by rw [h])) := by
  subst h; simpa

theorem HomotopyCategory.has_shift_associativity_aux :
    ∀ (m₁ m₂ m₃ : ℤ) (X : HomotopyCategory V (ComplexShape.up ℤ)),
      (HomotopyCategory.shiftFunctor V m₃).map
            ((HomotopyCategory.shiftFunctorAdd V m₁ m₂).Hom.app X) ≫
          (HomotopyCategory.shiftFunctorAdd V (m₁ + m₂) m₃).Hom.app X ≫
            eqToHom (by rw [add_assoc]) =
        (HomotopyCategory.shiftFunctorAdd V m₂ m₃).Hom.app
            ((HomotopyCategory.shiftFunctor V m₁).obj X) ≫
          (HomotopyCategory.shiftFunctorAdd V m₁ (m₂ + m₃)).Hom.app X :=
  fun m₁ m₂ m₃ ⟨X⟩ => by
  dsimp [homotopy_category.shift_functor_add]
  rw [quotient_eq_to_hom]; simp only [← functor.map_comp]; congr 1; ext; simp [X_eq_to_iso]

theorem HomotopyCategory.has_shift_left_unitality_aux :
    ∀ (n : ℤ) (X : HomotopyCategory V (ComplexShape.up ℤ)),
      (HomotopyCategory.shiftFunctor V n).map ((HomotopyCategory.shiftε V).Hom.app X) ≫
          (HomotopyCategory.shiftFunctorAdd V 0 n).Hom.app X =
        eqToHom (by dsimp; rw [zero_add]) :=
  fun n ⟨X⟩ =>
  by
  dsimp [homotopy_category.shift_ε, homotopy_category.shift_functor_add]
  rw [quotient_eq_to_hom]; simp only [← functor.map_comp]
  congr 1; ext; simp [X_eq_to_iso]

theorem HomotopyCategory.has_shift_right_unitality_aux :
    ∀ (n : ℤ) (X : HomotopyCategory V (ComplexShape.up ℤ)),
      (HomotopyCategory.shiftε V).Hom.app ((HomotopyCategory.shiftFunctor V n).obj X) ≫
          (HomotopyCategory.shiftFunctorAdd V n 0).Hom.app X =
        eqToHom (by dsimp; rw [add_zero]) :=
  fun n ⟨X⟩ =>
  by
  dsimp [homotopy_category.shift_ε, homotopy_category.shift_functor_add]
  rw [quotient_eq_to_hom]; simp only [← functor.map_comp]
  congr 1; ext; simp [X_eq_to_iso]

instance HomotopyCategory.hasShift : HasShift (HomotopyCategory V (ComplexShape.up ℤ)) ℤ :=
  hasShiftMk _ _
    { f := HomotopyCategory.shiftFunctor V
      ε := HomotopyCategory.shiftε V
      μ := HomotopyCategory.shiftFunctorAdd V
      associativity := by simpa using homotopy_category.has_shift_associativity_aux _
      left_unitality := by simpa using homotopy_category.has_shift_left_unitality_aux _
      right_unitality := by simpa using homotopy_category.has_shift_right_unitality_aux _ }

@[simp]
theorem HomotopyCategory.quotient_obj_shift (X : CochainComplex V ℤ) (n : ℤ) :
    (HomotopyCategory.quotient V _).obj X⟦n⟧ = ⟨X⟦n⟧⟩ :=
  rfl

@[simp]
theorem HomotopyCategory.shift_as (X : HomotopyCategory V (ComplexShape.up ℤ)) (n : ℤ) :
    X⟦n⟧.as = X.as⟦n⟧ :=
  rfl

@[simp]
theorem HomotopyCategory.quotient_map_shift {X Y : CochainComplex V ℤ} (f : X ⟶ Y) (n : ℤ) :
    (HomotopyCategory.quotient V _).map f⟦n⟧' = (HomotopyCategory.quotient V _).map (f⟦n⟧') :=
  rfl

@[simp]
theorem shift_ε_app (X : CochainComplex V ℤ) :
    (shiftMonoidalFunctor _ ℤ).ε.app ((HomotopyCategory.quotient _ _).obj X) =
      (HomotopyCategory.quotient _ _).map ((shiftMonoidalFunctor _ ℤ).ε.app X) :=
  rfl

@[simp]
theorem shift_ε_inv_app (X : CochainComplex V ℤ) :
    (shiftMonoidalFunctor _ ℤ).εIso.inv.app ((HomotopyCategory.quotient _ _).obj X) =
      (HomotopyCategory.quotient _ _).map ((shiftMonoidalFunctor _ ℤ).εIso.inv.app X) :=
  by
  rw [← cancel_mono ((shift_monoidal_functor _ ℤ).ε.app ((HomotopyCategory.quotient _ _).obj X)),
    ε_inv_hom_app, shift_ε_app, ← functor.map_comp, ε_inv_hom_app]
  rfl

@[simp]
theorem shift_μ_app (i j : ℤ) (X : CochainComplex V ℤ) :
    ((shiftMonoidalFunctor _ ℤ).μ ⟨i⟩ ⟨j⟩).app ((HomotopyCategory.quotient _ _).obj X) =
      (HomotopyCategory.quotient _ _).map (((shiftMonoidalFunctor _ ℤ).μ ⟨i⟩ ⟨j⟩).app X) :=
  rfl

@[simp]
theorem shift_μ_inv_app (i j : ℤ) (X : CochainComplex V ℤ) :
    ((shiftMonoidalFunctor _ ℤ).μIso ⟨i⟩ ⟨j⟩).inv.app ((HomotopyCategory.quotient _ _).obj X) =
      (HomotopyCategory.quotient _ _).map (((shiftMonoidalFunctor _ ℤ).μIso ⟨i⟩ ⟨j⟩).inv.app X) :=
  by
  rw [←
    cancel_mono
      (((shift_monoidal_functor _ ℤ).μ ⟨i⟩ ⟨j⟩).app ((HomotopyCategory.quotient _ _).obj X)),
    μ_inv_hom_app, shift_μ_app, ← functor.map_comp, μ_inv_hom_app]
  rfl

attribute [local reducible] Discrete.addMonoidal

@[simp]
theorem shift_μ_hom_app_f (A : CochainComplex V ℤ) (i j k : ℤ) :
    Hom.f (((shiftMonoidalFunctor _ ℤ).μ ⟨i⟩ ⟨j⟩).app A) k = (A.xEqToIso <| by dsimp; ring).Hom :=
  rfl

@[simp]
theorem shift_μ_inv_app_f (A : CochainComplex V ℤ) (i j k : ℤ) :
    Hom.f (((shiftMonoidalFunctor _ ℤ).μIso ⟨i⟩ ⟨j⟩).inv.app A) k =
      (A.xEqToIso <| by dsimp; ring).Hom :=
  by
  generalize_proofs h
  rw [← cancel_epi (A.X_eq_to_iso h.symm).Hom]
  conv_lhs => rw [← shift_μ_hom_app_f, ← comp_f]
  simpa [-comp_f]

@[simp]
theorem shift_ε_hom_app_f (A : CochainComplex V ℤ) (i : ℤ) :
    Hom.f ((shiftMonoidalFunctor _ ℤ).ε.app A) i = (A.xEqToIso <| by dsimp; ring).Hom :=
  rfl

@[simp]
theorem shift_ε_inv_app_f (A : CochainComplex V ℤ) (i : ℤ) :
    Hom.f ((shiftMonoidalFunctor _ ℤ).εIso.inv.app A) i = (A.xEqToIso <| by dsimp; ring).Hom :=
  by
  have : epi (hom.f ((shift_monoidal_functor _ ℤ).ε.app A) i) := by rw [shift_ε_hom_app_f];
    infer_instance
  rw [← cancel_epi (hom.f ((shift_monoidal_functor _ ℤ).ε.app A) i), ← comp_f,
    CategoryTheory.ε_hom_inv_app, HomologicalComplex.id_f]
  dsimp; simpa

open CategoryTheory.Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable def homologyShiftObjIso (X : CochainComplex A ℤ) (i j : ℤ) :
    (homology'Functor _ _ j).obj (X⟦i⟧) ≅ (homology'Functor _ _ (j + i)).obj X :=
  by
  refine'
    homology_iso _ (j - 1) j (j + 1) _ _ ≪≫
      _ ≪≫ (homology_iso _ (j - 1 + i) (j + i) (j + 1 + i) _ _).symm
  · simp
  · simp
  ·
    exact
      homology'.mapIso _ _ (Int.negOnePowArrowIsoLeft _ _).symm
        (Int.negOnePowArrowIsoRight _ _).symm rfl
  · dsimp; abel
  · dsimp; abel

@[simp, reassoc]
theorem homology'.π'_ι {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology'.π' f g w ≫ homology'.ι f g w = kernel.ι g ≫ cokernel.π f := by
  delta homology'.π' homology'.ι homology'IsoKernelDesc; simp

@[simp, reassoc]
theorem homology'.desc'_ι {X X' Y Z Z' : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (f' : X' ⟶ Y)
    (g' : Y ⟶ Z') (w' : f' ≫ g' = 0) (h₁) (h₂) (h₃) :
    homology'.desc' _ _ w (kernel.lift _ (kernel.ι _) h₁ ≫ homology'.π' _ _ _) h₂ ≫
        homology'.ι _ _ w' =
      homology'.ι _ _ _ ≫ cokernel.desc _ (cokernel.π _) h₃ :=
  by ext; simp

@[simp, reassoc]
theorem homology'.π'_lift {X X' Y Z Z' : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (f' : X' ⟶ Y)
    (g' : Y ⟶ Z') (w' : f' ≫ g' = 0) (h₁) (h₂) (h₃) :
    homology'.π' _ _ w ≫
        homology'.lift _ _ w' (homology'.ι _ _ _ ≫ cokernel.desc _ (cokernel.π _) h₁) h₂ =
      kernel.lift _ (kernel.ι _) h₃ ≫ homology'.π' _ _ _ :=
  by ext; simp

variable (A)

@[simp]
theorem shiftFunctor_eq (V : Type _) [Category V] [Preadditive V] (i) :
    HomologicalComplex.shiftFunctor V i = CategoryTheory.shiftFunctor _ i :=
  rfl

noncomputable def homologyShiftIso (i j : ℤ) :
    shiftFunctor _ i ⋙ homology'Functor A (ComplexShape.up ℤ) j ≅
      homology'Functor A (ComplexShape.up ℤ) (j + i) :=
  NatIso.ofComponents (fun X => homologyShiftObjIso X i j : _)
    (by
      intro X Y f
      ext
      dsimp [homology_shift_obj_iso, homology_iso, homology'.mapIso]
      simp)

end HomologicalComplex

