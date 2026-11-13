import Mathlib.Algebra.Homology.HomotopyCategory
import LiquidTensorExperiment.ForMathlib.HomologicalComplexShift
import LiquidTensorExperiment.ForMathlib.AbelianCategory

#align_import for_mathlib.homotopy_category

universe v u

open scoped Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {ι : Type _}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι}

namespace CategoryTheory

namespace Quotient

variable {𝒞 : Type _} [Category 𝒞] {r : HomRel 𝒞} [Congruence r]

variable {X Y : 𝒞} {f g : X ⟶ Y}

theorem CompClosure.rel (h : CompClosure r f g) : r f g := by cases h; apply congruence.comp_left;
  apply congruence.comp_right; assumption

end Quotient

end CategoryTheory

namespace Homotopy

variable {C D : HomologicalComplex V c} {f f₁ f₂ g g₁ g₂ : C ⟶ D}

@[simps (config := { fullyApplied := false })]
protected def neg (h : Homotopy f g) : Homotopy (-f) (-g)
    where
  Hom := -h.Hom
  zero' i j H := by dsimp; rw [h.zero i j H, neg_zero]
  comm i := by simp only [neg_f_apply, AddMonoidHom.map_neg, h.comm, neg_add]

@[simps (config := { fullyApplied := false })]
def addLeft (f : C ⟶ D) (h : Homotopy g₁ g₂) : Homotopy (f + g₁) (f + g₂) :=
  { h with
    comm := fun i => by simp only [add_f_apply, h.comm];
      rw [add_comm, add_comm (f.f i), ← add_assoc] }

@[simps (config := { fullyApplied := false })]
def addRight (h : Homotopy f₁ f₂) (g : C ⟶ D) : Homotopy (f₁ + g) (f₂ + g) :=
  { h with comm := fun i => by simp only [add_f_apply, h.comm, add_assoc] }

@[simps (config := { fullyApplied := false })]
def subLeft (f : C ⟶ D) (h : Homotopy g₁ g₂) : Homotopy (f - g₁) (f - g₂) :=
  { h.neg with
    comm := fun i => by
      simp only [h.comm, add_f_apply, neg_f_apply, neg_hom, sub_eq_add_neg, AddMonoidHom.map_neg,
        add_comm _ (f.f i), ← add_assoc, neg_add] }

@[simps (config := { fullyApplied := false })]
def subRight (h : Homotopy f₁ f₂) (g : C ⟶ D) : Homotopy (f₁ - g) (f₂ - g) :=
  { h with comm := fun i => by simp only [sub_f_apply, h.comm, add_sub] }

end Homotopy

namespace HomotopyCategory

/-
Generalize this stuff to suitable quotient categories?
-/
variable (A B : HomotopyCategory V c)

@[simp]
theorem quot_mk {A B : HomologicalComplex V c} (f : A ⟶ B) : Quot.mk _ f = (quotient V c).map f :=
  rfl

instance : Zero (A ⟶ B) :=
  ⟨(quotient V c).map 0⟩

instance : Neg (A ⟶ B) :=
  ⟨Quot.lift (fun f => (quotient V c).map (-f))
      fun (f g : A.as ⟶ B.as) (h : Quotient.CompClosure (homotopic V c) f g) =>
      eq_of_homotopy _ _ h.Rel.some.neg⟩

instance : Add (A ⟶ B) :=
  ⟨Quot.lift₂ (fun f g => (quotient V c).map (f + g))
      (fun (f g₁ g₂ : A.as ⟶ B.as) (h : Quotient.CompClosure (homotopic V c) g₁ g₂) =>
        eq_of_homotopy _ _ (h.Rel.some.addLeft _))
      fun (f₁ f₂ g : A.as ⟶ B.as) (h : Quotient.CompClosure (homotopic V c) f₁ f₂) =>
      eq_of_homotopy _ _ (h.Rel.some.addRight g)⟩

instance : Sub (A ⟶ B) :=
  ⟨Quot.lift₂ (fun f g => (quotient V c).map (f - g))
      (fun (f g₁ g₂ : A.as ⟶ B.as) (h : Quotient.CompClosure (homotopic V c) g₁ g₂) =>
        eq_of_homotopy _ _ (h.Rel.some.subLeft _))
      fun (f₁ f₂ g : A.as ⟶ B.as) (h : Quotient.CompClosure (homotopic V c) f₁ f₂) =>
      eq_of_homotopy _ _ (h.Rel.some.subRight g)⟩

instance hasNsmul : SMul ℕ (A ⟶ B) :=
  ⟨fun n => nsmulRec n⟩

instance hasZsmul : SMul ℤ (A ⟶ B) :=
  ⟨fun n => zsmulRec n⟩

theorem quotient_map_neg {A B : HomologicalComplex V c} (f : A ⟶ B) :
    (quotient V c).map (-f) = -(quotient V c).map f :=
  rfl

theorem quotient_map_add {A B : HomologicalComplex V c} (f g : A ⟶ B) :
    (quotient V c).map (f + g) = (quotient V c).map f + (quotient V c).map g :=
  rfl

theorem quotient_map_sub {A B : HomologicalComplex V c} (f g : A ⟶ B) :
    (quotient V c).map (f - g) = (quotient V c).map f - (quotient V c).map g :=
  rfl

theorem quotient_map_nsmul {A B : HomologicalComplex V c} (n : ℕ) (f : A ⟶ B) :
    (quotient V c).map (n • f) = n • (quotient V c).map f :=
  by
  induction' n with n ih
  · rw [zero_smul]; rfl
  · rw [succ_nsmul, quotient_map_add, ih]; rfl

theorem quotient_map_zsmul {A B : HomologicalComplex V c} (n : ℤ) (f : A ⟶ B) :
    (quotient V c).map (n • f) = n • (quotient V c).map f :=
  by
  cases n
  · rw [ofNat_zsmul, quotient_map_nsmul]; rfl
  · rw [negSucc_zsmul, quotient_map_neg, quotient_map_nsmul]; rfl

instance : AddCommGroup (A ⟶ B) :=
  Function.Surjective.addCommGroup (fun f => (quotient V c).map f) (surjective_quot_mk _) rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun f n => quotient_map_nsmul n f) fun f n =>
    quotient_map_zsmul n f

instance : Preadditive (HomotopyCategory V c)
    where
  add_comp X Y Z f₁ f₂ g := by
    apply Quot.induction_on₃ f₁ f₂ g; clear f₁ f₂ g
    intro f₁ f₂ g
    repeat' erw [quot_mk]
    rw [← quotient_map_add]
    calc
      (Quotient V c).map (f₁ + f₂) ≫ (Quotient V c).map g = (Quotient V c).map ((f₁ + f₂) ≫ g) := by
        rw [(Quotient V c).map_comp]
      _ = (Quotient V c).map (f₁ ≫ g + f₂ ≫ g) := by rw [preadditive.add_comp]
      _ = (Quotient V c).map (f₁ ≫ g) + (Quotient V c).map (f₂ ≫ g) := by rw [quotient_map_add]
  comp_add X Y Z f g₁ g₂ := by
    apply Quot.induction_on₃ f g₁ g₂; clear f g₁ g₂
    intro f g₁ g₂
    repeat' erw [quot_mk]
    rw [← quotient_map_add]
    calc
      (Quotient V c).map f ≫ (Quotient V c).map (g₁ + g₂) = (Quotient V c).map (f ≫ (g₁ + g₂)) := by
        rw [(Quotient V c).map_comp]
      _ = (Quotient V c).map (f ≫ g₁ + f ≫ g₂) := by rw [preadditive.comp_add]
      _ = (Quotient V c).map (f ≫ g₁) + (Quotient V c).map (f ≫ g₂) := by rw [quotient_map_add]

instance quotient.additive : (quotient V c).Additive where

deriving instance Full for Quotient

open scoped ZeroObject

protected def zero [HasZeroObject V] : HomotopyCategory V c where as := HomologicalComplex.zero

protected theorem isZero_zero [HasZeroObject V] :
    IsZero (HomotopyCategory.zero : HomotopyCategory V c) :=
  by
  rw [is_zero_iff_id_eq_zero]
  apply eq_of_homotopy
  apply Homotopy.ofEq
  rw [← is_zero_iff_id_eq_zero]
  exact HomologicalComplex.isZero_zero

instance [HasZeroObject V] : HasZeroObject (HomotopyCategory V c) :=
  ⟨⟨HomotopyCategory.zero, HomotopyCategory.isZero_zero⟩⟩

instance shiftFunctor_additive (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory V (ComplexShape.up ℤ)) n).Additive where

end HomotopyCategory

namespace CategoryTheory

namespace Functor

@[simps]
def mapHomotopyCategoryComp {W : Type _} [Category W] [Preadditive W] (F : V ⥤ W)
    [Functor.Additive F] (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c ≅
      HomotopyCategory.quotient V c ⋙ Functor.mapHomotopyCategory c F :=
  NatIso.ofComponents (fun X => eqToIso (by rfl)) fun X Y f =>
    by
    simp only [functor.comp_map, eq_to_iso_refl, iso.refl_hom, category.comp_id,
      functor.map_homotopy_category_map, category.id_comp]
    apply CategoryTheory.Quotient.sound
    exact Nonempty.intro (F.map_homotopy (HomotopyCategory.homotopyOutMap f)).symm

end Functor

end CategoryTheory

