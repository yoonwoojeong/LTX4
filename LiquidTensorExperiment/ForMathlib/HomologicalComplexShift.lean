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
    (k : α) : (ComplexShape.up' a).Rel (i + k) (j + k) ↔ (ComplexShape.up' a).Rel i j := by
  dsimp
  rw [add_assoc, add_comm k a, ← add_assoc]
  exact add_left_inj _

theorem ComplexShape.up_add_right_cancel {α : Type _} [AddCancelCommMonoid α] [One α] {i j}
    (k : α) : (ComplexShape.up α).Rel (i + k) (j + k) ↔ (ComplexShape.up α).Rel i j :=
  ComplexShape.up'_add_right_cancel 1 k

@[simps]
def shiftFunctor (n : ℤ) : CochainComplex V ℤ ⥤ CochainComplex V ℤ where
  obj X :=
    { X := fun i => X.X (i + n)
      d := fun i j => n.negOnePow • X.d _ _
      shape := fun i j h => by
        dsimp only
        rw [X.shape (i + n) (j + n), smul_zero]
        rwa [ComplexShape.up_add_right_cancel] }
  map f := { f := fun i => f.f _ }

variable {V} {ι : Type _} {c : ComplexShape ι}

def xEqToIso (X : HomologicalComplex V c) {i j : ι} (h : i = j) : X.X i ≅ X.X j :=
  eqToIso <| congr_arg X.X h

@[simp]
theorem xEqToIso_inv (X : HomologicalComplex V c) {i j : ι} (h : i = j) :
    (X.xEqToIso h).inv = (X.xEqToIso h.symm).hom :=
  rfl

@[reassoc (attr := simp)]
theorem xEqToIso_d (X : HomologicalComplex V c) {i j k : ι} (h : i = j) :
    (X.xEqToIso h).hom ≫ X.d j k = X.d i k := by subst h; exact Category.id_comp _

@[reassoc (attr := simp)]
theorem x_d_eq_to_iso (X : HomologicalComplex V c) {i j k : ι} (h : j = k) :
    X.d i j ≫ (X.xEqToIso h).hom = X.d i k := by subst h; exact Category.comp_id _

@[reassoc (attr := simp)]
theorem xEqToIso_trans (X : HomologicalComplex V c) {i j k : ι} (h : i = j) (h' : j = k) :
    (X.xEqToIso h).hom ≫ (X.xEqToIso h').hom = (X.xEqToIso (h.trans h')).hom := by
  simp [xEqToIso]

@[simp]
theorem xEqToIso_refl (X : HomologicalComplex V c) {i : ι} : (X.xEqToIso (refl i)).hom = 𝟙 _ :=
  rfl

@[reassoc (attr := simp)]
theorem xEqToIso_f {X Y : HomologicalComplex V c} (f : X ⟶ Y) {i j : ι} (h : i = j) :
    (X.xEqToIso h).hom ≫ f.f j = f.f i ≫ (Y.xEqToIso h).hom := by subst h; simp [xEqToIso]

variable (V)

-- Porting note: mathlib4's `ShiftMkCore` uses the inverse directions `zero : F 0 ≅ 𝟭 C`,
-- `add n m : F (n + m) ≅ F n ⋙ F m` compared to the Lean 3 `ε` and `μ`.
instance : HasShift (CochainComplex V ℤ) ℤ :=
  hasShiftMk _ _
    { F := shiftFunctor V
      zero :=
        NatIso.ofComponents
          (fun X =>
            Hom.isoOfComponents (fun i => X.xEqToIso (add_zero _)) fun i j r => by dsimp; simp)
          fun f => by ext; dsimp; simp
      add := fun n m =>
        NatIso.ofComponents
          (fun X =>
            Hom.isoOfComponents (fun i => X.xEqToIso (by rw [add_comm n m, add_assoc])) fun i j r =>
              by dsimp; simp [smul_smul, mul_comm])
          fun f => by ext; dsimp; simp
      assoc_hom_app := fun m₁ m₂ m₃ X => by ext; dsimp; simp [xEqToIso]
      zero_add_hom_app := fun n X => by ext; dsimp; simp [xEqToIso]
      add_zero_hom_app := fun n X => by ext; dsimp; simp [xEqToIso] }

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

@[simp]
theorem shift_x (X : CochainComplex V ℤ) (n m : ℤ) : X⟦n⟧.X m = X.X (m + n) :=
  rfl

@[simp]
theorem shift_d (X : CochainComplex V ℤ) (n i j : ℤ) :
    X⟦n⟧.d i j = n.negOnePow • X.d (i + n) (j + n) :=
  rfl

@[simp]
theorem shift_f {X Y : CochainComplex V ℤ} (f : X ⟶ Y) (n i : ℤ) : f⟦n⟧'.f i = f.f (i + n) :=
  rfl

instance (n : ℤ) : Functor.Additive ((shiftMonoidalFunctor (CochainComplex V ℤ) ℤ).obj ⟨n⟩) :=
  { map_add := by intros; aesop_cat }

instance shiftFunctor_additive (n : ℤ) : Functor.Additive (shiftFunctor V n) :=
  { map_add := by intros; aesop_cat }

variable {V}

def homotopyShift {X Y : CochainComplex V ℤ} {f g : X ⟶ Y} (h : Homotopy f g) (n : ℤ) :
    Homotopy (f⟦n⟧') (g⟦n⟧') where
  hom i j := n.negOnePow • h.hom _ _
  zero i j r := by rw [← ComplexShape.up_add_right_cancel n] at r ; simp [h.zero _ _ r]
  comm i := by
    -- Porting note: reproved using `dNext_eq` and `prevD_eq` (the `delta` approach of Lean 3 does not work)
    dsimp
    rw [h.comm (i + n)]
    have e1 : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have e2 : (ComplexShape.up ℤ).Rel (i + n) (i + 1 + n) := by dsimp; ring
    have e3 : (ComplexShape.up ℤ).Rel (i - 1) i := by dsimp; ring
    have e4 : (ComplexShape.up ℤ).Rel (i - 1 + n) (i + n) := by dsimp; ring
    rw [dNext_eq _ e2, prevD_eq _ e4]
    -- Porting note: `erw` is needed to see through the shifted complex
    erw [dNext_eq _ e1, prevD_eq _ e3]
    simp [smul_smul]

variable (V)

def HomotopyCategory.shiftFunctor (n : ℤ) :
    HomotopyCategory V (ComplexShape.up ℤ) ⥤ HomotopyCategory V (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _ (HomologicalComplex.shiftFunctor _ n ⋙ HomotopyCategory.quotient _ _)
    (by
      rintro X Y f g ⟨h⟩
      apply HomotopyCategory.eq_of_homotopy
      exact HomologicalComplex.homotopyShift h n)

def HomotopyCategory.shiftε : 𝟭 _ ≅ HomotopyCategory.shiftFunctor V 0 :=
  by
  refine' NatIso.ofComponents _ _
  · rintro ⟨X⟩
    refine' (HomotopyCategory.quotient _ _).mapIso (Hom.isoOfComponents _ _)
    exact fun i => X.xEqToIso (add_zero _).symm
    · introv ; dsimp; simp
  · rintro ⟨X⟩ ⟨Y⟩ f; dsimp
    rw [← HomotopyCategory.quotient_map_out f]
    erw [Quotient.lift_map_functor_map]
    simp only [Functor.comp_map, ← Functor.map_comp]
    congr 1; ext; dsimp; simp

def HomotopyCategory.shiftFunctorAdd (n m : ℤ) :
    HomotopyCategory.shiftFunctor V n ⋙ HomotopyCategory.shiftFunctor V m ≅
      HomotopyCategory.shiftFunctor V (n + m) :=
  by
  refine' NatIso.ofComponents _ _
  · rintro ⟨X⟩
    refine' (HomotopyCategory.quotient _ _).mapIso (Hom.isoOfComponents _ _)
    exact fun i => X.xEqToIso (by rw [add_comm n m, add_assoc])
    · introv r; dsimp [HomotopyCategory.shiftFunctor, CategoryTheory.Quotient.lift]; simp [smul_smul, mul_comm, HomotopyCategory.quotient_obj_as]
  · rintro ⟨X⟩ ⟨Y⟩ f; dsimp
    rw [← HomotopyCategory.quotient_map_out f]
    erw [Quotient.lift_map_functor_map]
    conv_rhs => erw [Quotient.lift_map_functor_map]
    simp only [Functor.comp_map, ← Functor.map_comp]
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
  subst h
  simp
  -- Porting note: the remaining goal holds by eta for structures
  rfl

theorem HomotopyCategory.has_shift_associativity_aux :
    ∀ (m₁ m₂ m₃ : ℤ) (X : HomotopyCategory V (ComplexShape.up ℤ)),
      (HomotopyCategory.shiftFunctor V m₃).map
            ((HomotopyCategory.shiftFunctorAdd V m₁ m₂).hom.app X) ≫
          (HomotopyCategory.shiftFunctorAdd V (m₁ + m₂) m₃).hom.app X ≫
            eqToHom (by rw [add_assoc]) =
        (HomotopyCategory.shiftFunctorAdd V m₂ m₃).hom.app
            ((HomotopyCategory.shiftFunctor V m₁).obj X) ≫
          (HomotopyCategory.shiftFunctorAdd V m₁ (m₂ + m₃)).hom.app X :=
  fun m₁ m₂ m₃ ⟨X⟩ => by
  dsimp [HomotopyCategory.shiftFunctorAdd]
  rw [HomologicalComplex.quotient_eqToHom]; simp only [← Functor.map_comp]; congr 1; ext; simp [xEqToIso]

theorem HomotopyCategory.has_shift_left_unitality_aux :
    ∀ (n : ℤ) (X : HomotopyCategory V (ComplexShape.up ℤ)),
      (HomotopyCategory.shiftFunctor V n).map ((HomotopyCategory.shiftε V).hom.app X) ≫
          (HomotopyCategory.shiftFunctorAdd V 0 n).hom.app X =
        eqToHom (by dsimp; rw [zero_add]) :=
  fun n ⟨X⟩ =>
  by
  dsimp [HomotopyCategory.shiftε, HomotopyCategory.shiftFunctorAdd]
  rw [HomologicalComplex.quotient_eqToHom]; simp only [← Functor.map_comp]
  congr 1; ext; simp [xEqToIso]

theorem HomotopyCategory.has_shift_right_unitality_aux :
    ∀ (n : ℤ) (X : HomotopyCategory V (ComplexShape.up ℤ)),
      (HomotopyCategory.shiftε V).hom.app ((HomotopyCategory.shiftFunctor V n).obj X) ≫
          (HomotopyCategory.shiftFunctorAdd V n 0).hom.app X =
        eqToHom (by dsimp; rw [add_zero]) :=
  fun n ⟨X⟩ =>
  by
  dsimp [HomotopyCategory.shiftε, HomotopyCategory.shiftFunctorAdd]
  rw [HomologicalComplex.quotient_eqToHom]; simp only [← Functor.map_comp]
  congr 1; ext; simp [xEqToIso]

-- Porting note: mathlib4's `ShiftMkCore` uses the inverse directions `zero : F 0 ≅ 𝟭 C`,
-- `add n m : F (n + m) ≅ F n ⋙ F m` compared to the Lean 3 `ε` and `μ`.
instance HomotopyCategory.hasShift : HasShift (HomotopyCategory V (ComplexShape.up ℤ)) ℤ :=
  hasShiftMk _ _
    { F := HomotopyCategory.shiftFunctor V
      zero := (HomotopyCategory.shiftε V).symm
      add := fun n m => (HomotopyCategory.shiftFunctorAdd V n m).symm
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        have h := HomotopyCategory.has_shift_associativity_aux V m₁ m₂ m₃ X
        have h2 : (HomotopyCategory.shiftFunctor V m₃).map
            ((HomotopyCategory.shiftFunctorAdd V m₁ m₂).hom.app X) ≫
              (HomotopyCategory.shiftFunctorAdd V (m₁ + m₂) m₃).hom.app X =
            (HomotopyCategory.shiftFunctorAdd V m₂ m₃).hom.app
                ((HomotopyCategory.shiftFunctor V m₁).obj X) ≫
              (HomotopyCategory.shiftFunctorAdd V m₁ (m₂ + m₃)).hom.app X ≫
                eqToHom (by rw [add_assoc]) := by
          rw [← Category.assoc, ← h]
          simp
        rw [← cancel_epi ((HomotopyCategory.shiftFunctor V m₃).map
            ((HomotopyCategory.shiftFunctorAdd V m₁ m₂).hom.app X) ≫
              (HomotopyCategory.shiftFunctorAdd V (m₁ + m₂) m₃).hom.app X)]
        conv_rhs => rw [h2]
        simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app]
        rw [← Functor.map_comp, Iso.hom_inv_id_app]
        exact CategoryTheory.Functor.map_id _ _
      zero_add_hom_app := fun n X => by
        have h := HomotopyCategory.has_shift_left_unitality_aux V n X
        simp only [Iso.symm_hom, Iso.symm_inv]
        rw [← cancel_mono ((HomotopyCategory.shiftFunctorAdd V 0 n).hom.app X),
          Iso.inv_hom_id_app, Category.assoc, h, eqToHom_trans, eqToHom_refl]
      add_zero_hom_app := fun n X => by
        have h := HomotopyCategory.has_shift_right_unitality_aux V n X
        simp only [Iso.symm_hom, Iso.symm_inv]
        rw [← cancel_mono ((HomotopyCategory.shiftFunctorAdd V n 0).hom.app X),
          Iso.inv_hom_id_app, Category.assoc, h, eqToHom_trans, eqToHom_refl] }

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
  rw [← cancel_mono ((CategoryTheory.shiftMonoidalFunctor _ ℤ).ε.app ((HomotopyCategory.quotient _ _).obj X)),
    ε_inv_hom_app, shift_ε_app, ← Functor.map_comp, ε_inv_hom_app]
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
      (((CategoryTheory.shiftMonoidalFunctor _ ℤ).μ ⟨i⟩ ⟨j⟩).app ((HomotopyCategory.quotient _ _).obj X)),
    μ_inv_hom_app, shift_μ_app, ← Functor.map_comp, μ_inv_hom_app]
  rfl

-- Porting note: `reducible` cannot be a `local` attribute in Lean 4
-- attribute [local reducible] Discrete.addMonoidal

@[simp]
theorem shift_μ_hom_app_f (A : CochainComplex V ℤ) (i j k : ℤ) :
    Hom.f (((shiftMonoidalFunctor _ ℤ).μ ⟨i⟩ ⟨j⟩).app A) k = (A.xEqToIso <| by dsimp; ring).hom :=
  rfl

@[simp]
theorem shift_μ_inv_app_f (A : CochainComplex V ℤ) (i j k : ℤ) :
    Hom.f (((shiftMonoidalFunctor _ ℤ).μIso ⟨i⟩ ⟨j⟩).inv.app A) k =
      (A.xEqToIso <| by dsimp; ring).hom :=
  by
  generalize_proofs h
  rw [← cancel_epi (A.xEqToIso h.symm).hom]
  conv_lhs => rw [← shift_μ_hom_app_f, ← comp_f]
  simp [-comp_f]
  -- Porting note: remaining goal is closed by `rfl`
  rfl

@[simp]
theorem shift_ε_hom_app_f (A : CochainComplex V ℤ) (i : ℤ) :
    Hom.f ((shiftMonoidalFunctor _ ℤ).ε.app A) i = (A.xEqToIso <| by dsimp; ring).hom :=
  rfl

@[simp]
theorem shift_ε_inv_app_f (A : CochainComplex V ℤ) (i : ℤ) :
    Hom.f ((shiftMonoidalFunctor _ ℤ).εIso.inv.app A) i = (A.xEqToIso <| by dsimp; ring).hom :=
  by
  have : Epi (Hom.f ((CategoryTheory.shiftMonoidalFunctor _ ℤ).ε.app A) i) := by
    rw [shift_ε_hom_app_f]
    infer_instance
  rw [← cancel_epi (Hom.f ((CategoryTheory.shiftMonoidalFunctor _ ℤ).ε.app A) i), ← comp_f,
    CategoryTheory.ε_hom_inv_app, HomologicalComplex.id_f]
  dsimp; simp

open CategoryTheory.Abelian

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable def homologyShiftObjIso (X : CochainComplex A ℤ) (i j : ℤ) :
    (homology'Functor _ _ j).obj (X⟦i⟧) ≅ (homology'Functor _ _ (j + i)).obj X :=
  by
  refine'
    homologyIso _ (j - 1) j (j + 1) _ _ ≪≫
      _ ≪≫ (homologyIso _ (j - 1 + i) (j + i) (j + 1 + i) _ _).symm
  · simp
  · simp
  ·
    exact
      homology'.mapIso _ _ (Int.negOnePowArrowIsoLeft _ _).symm
        (Int.negOnePowArrowIsoRight _ _).symm rfl
  · dsimp; abel
  · dsimp; abel

@[reassoc (attr := simp)]
theorem homology'.π'_ι {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    homology'.π' f g w ≫ homology'.ι f g w = kernel.ι g ≫ cokernel.π f := by
  delta homology'.π' homology'.ι homology'IsoKernelDesc; simp

@[reassoc (attr := simp)]
theorem homology'.desc'_ι {X X' Y Z Z' : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (f' : X' ⟶ Y)
    (g' : Y ⟶ Z') (w' : f' ≫ g' = 0) (h₁) (h₂) (h₃) :
    homology'.desc' _ _ w (kernel.lift _ (kernel.ι _) h₁ ≫ homology'.π' _ _ _) h₂ ≫
        homology'.ι _ _ w' =
      homology'.ι _ _ _ ≫ cokernel.desc _ (cokernel.π _) h₃ :=
  by ext; simp

@[reassoc (attr := simp)]
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
      -- Porting note: Lean 3's recursive `ext` replaced by explicit ext lemmas
      apply homology'.hom_from_ext
      apply homology'.hom_to_ext
      dsimp [HomologicalComplex.homologyShiftObjIso, homologyIso, homology'.mapIso]
      simp)

end HomologicalComplex

