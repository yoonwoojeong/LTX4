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

theorem CompClosure.rel (h : CompClosure r f g) : r f g := by
  cases h
  apply Congruence.compLeft
  apply Congruence.compRight
  assumption

end Quotient

end CategoryTheory

namespace Homotopy

variable {C D : HomologicalComplex V c} {f f₁ f₂ g g₁ g₂ : C ⟶ D}

@[simps (config := { fullyApplied := false })]
protected def neg (h : Homotopy f g) : Homotopy (-f) (-g)
    where
  hom := -h.hom
  zero i j H := by dsimp; rw [h.zero i j H, neg_zero]
  comm i := by simp only [neg_f_apply, AddMonoidHom.map_neg, h.comm, neg_add]

@[simps (config := { fullyApplied := false })]
def addLeft (f : C ⟶ D) (h : Homotopy g₁ g₂) : Homotopy (f + g₁) (f + g₂) :=
  { h with
    comm := fun i => by
      simp only [add_f_apply, h.comm]
      rw [add_comm, add_comm (f.f i), ← add_assoc] }

@[simps (config := { fullyApplied := false })]
def addRight (h : Homotopy f₁ f₂) (g : C ⟶ D) : Homotopy (f₁ + g) (f₂ + g) :=
  { h with comm := fun i => by simp only [add_f_apply, h.comm, add_assoc] }

@[simps (config := { fullyApplied := false })]
def subLeft (f : C ⟶ D) (h : Homotopy g₁ g₂) : Homotopy (f - g₁) (f - g₂) :=
  { h.neg with
    comm := fun i => by
      simp only [h.comm, add_f_apply, neg_f_apply, neg_hom, sub_eq_add_neg, AddMonoidHom.map_neg,
        add_comm _ (f.f i), ← add_assoc, neg_add]
      -- Porting note: `simp only` no longer closes the goal
      abel }

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

/-! Porting note: the instances `Zero`, `Neg`, `Add`, `Sub`, `SMul ℕ`, `SMul ℤ`, `AddCommGroup`
on `A ⟶ B` and `Preadditive (HomotopyCategory V c)` (and `quotient.additive`) were upstreamed to
mathlib (`CategoryTheory.Quotient.preadditive`); LTE's copies are removed to avoid diamonds. -/

theorem quotient_map_neg {A B : HomologicalComplex V c} (f : A ⟶ B) :
    (quotient V c).map (-f) = -(quotient V c).map f :=
  Functor.map_neg _

theorem quotient_map_add {A B : HomologicalComplex V c} (f g : A ⟶ B) :
    (quotient V c).map (f + g) = (quotient V c).map f + (quotient V c).map g :=
  Functor.map_add _

theorem quotient_map_sub {A B : HomologicalComplex V c} (f g : A ⟶ B) :
    (quotient V c).map (f - g) = (quotient V c).map f - (quotient V c).map g :=
  Functor.map_sub _

theorem quotient_map_nsmul {A B : HomologicalComplex V c} (n : ℕ) (f : A ⟶ B) :
    (quotient V c).map (n • f) = n • (quotient V c).map f :=
  Functor.map_nsmul _

theorem quotient_map_zsmul {A B : HomologicalComplex V c} (n : ℤ) (f : A ⟶ B) :
    (quotient V c).map (n • f) = n • (quotient V c).map f :=
  Functor.map_zsmul _

open scoped ZeroObject

protected def zero [HasZeroObject V] : HomotopyCategory V c where as := HomologicalComplex.zero

protected theorem isZero_zero [HasZeroObject V] :
    IsZero (HomotopyCategory.zero : HomotopyCategory V c) :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero]
  apply eq_of_homotopy
  apply Homotopy.ofEq
  rw [← CategoryTheory.Limits.isZero_iff_id_eq_zero]
  exact HomologicalComplex.isZero_zero

instance [HasZeroObject V] : HasZeroObject (HomotopyCategory V c) :=
  ⟨⟨HomotopyCategory.zero, HomotopyCategory.isZero_zero⟩⟩

instance shiftFunctor_additive (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory V (ComplexShape.up ℤ)) n).Additive where
  map_add := by
    -- Porting note: `aesop_cat` no longer proves this
    intro X Y f g
    rw [← quotient_map_out f, ← quotient_map_out g, ← quotient_map_add]
    erw [HomotopyCategory.shiftFunctor_map_quotient, HomotopyCategory.shiftFunctor_map_quotient,
      HomotopyCategory.shiftFunctor_map_quotient, ← quotient_map_add]
    congr 1

end HomotopyCategory

namespace CategoryTheory

namespace Functor

@[simps]
def mapHomotopyCategoryComp {W : Type _} [Category W] [Preadditive W] (F : V ⥤ W)
    [Functor.Additive F] (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⋙ HomotopyCategory.quotient W c ≅
      HomotopyCategory.quotient V c ⋙ Functor.mapHomotopyCategory F c :=
  NatIso.ofComponents (fun X => eqToIso (by rfl)) fun {X Y} f =>
    by
    simp only [Functor.comp_map, eqToIso_refl, Iso.refl_hom, Category.comp_id,
      Functor.mapHomotopyCategory_map, Category.id_comp]
    -- Porting note: the `simp only` call above already closes the goal (new definition of
    -- `Functor.mapHomotopyCategory` in mathlib)

end Functor

end CategoryTheory

