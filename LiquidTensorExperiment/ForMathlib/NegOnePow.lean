import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Data.Int.Parity
import Mathlib.Tactic.Ring
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

#align_import for_mathlib.neg_one_pow

attribute [local simp] CategoryTheory.Preadditive.zsmul_comp CategoryTheory.Preadditive.comp_zsmul

-- move this section
namespace Int

#print Int.negOnePow /-
def negOnePow (n : ℤ) : ℤ :=
  @Pow.pow (Units ℤ) ℤ _ (-1) n
-/

#print Int.negOnePow_add /-
@[simp]
theorem negOnePow_add (n m : ℤ) : negOnePow (n + m) = negOnePow n * negOnePow m := by
  delta neg_one_pow; rw [zpow_add]; simp
-/

#print Int.negOnePow_one /-
@[simp]
theorem negOnePow_one : negOnePow 1 = -1 :=
  rfl
-/

-- This lemma is provable by `neg_one_pow_neg`, but it is nice to have a rfl-lemma for this.
-- The priority is thus higher to silence the linter.
@[simp]
theorem negOnePow_neg_one : negOnePow (-1) = -1 :=
  rfl

@[simp]
theorem negOnePow_neg_zero : negOnePow 0 = 1 :=
  rfl

theorem negOnePow_ite (n : ℤ) : negOnePow n = if Even n then 1 else -1 :=
  by
  induction' n using Int.induction_on with n h n h
  · simp [neg_one_pow]
  · simp [h, apply_ite Neg.neg, parity_simps]
  · rw [sub_eq_add_neg, neg_one_pow_add]
    simp [h, apply_ite Neg.neg, parity_simps]

#print Int.negOnePow_even /-
theorem negOnePow_even {n : ℤ} (h : Even n) : negOnePow n = 1 := by rw [neg_one_pow_ite, if_pos h]
-/

#print Int.negOnePow_odd /-
theorem negOnePow_odd {n : ℤ} (h : Odd n) : negOnePow n = -1 := by
  rw [neg_one_pow_ite, if_neg (odd_iff_not_even.mp h)]
-/

@[simp]
theorem negOnePow_bit0 (n : ℤ) : negOnePow (bit0 n) = 1 :=
  negOnePow_even (even_bit0 n)

@[simp]
theorem negOnePow_bit1 (n : ℤ) : negOnePow (bit1 n) = -1 :=
  negOnePow_odd (odd_bit1 n)

theorem negOnePow_eq_pow_abs (n : ℤ) : negOnePow n = (-1) ^ n.natAbs :=
  by
  rw [neg_one_pow_ite]
  convert (neg_one_pow_ite n.nat_abs).symm using 2
  · simp [parity_simps]
  · delta neg_one_pow; simp

theorem negOnePow_eq_neg_one_npow (n : ℕ) : negOnePow n = (-1) ^ n := by delta neg_one_pow; simp

#print Int.negOnePow_neg /-
@[simp]
theorem negOnePow_neg (n : ℤ) : negOnePow (-n) = negOnePow n := by
  simp [neg_one_pow_ite, parity_simps]
-/

#print Int.negOnePow_sub /-
@[simp]
theorem negOnePow_sub (n m : ℤ) : negOnePow (n - m) = negOnePow n * negOnePow m := by
  rw [sub_eq_neg_add, neg_one_pow_add, neg_one_pow_neg, mul_comm]
-/

@[simp]
theorem negOnePow_hMul_self (n : ℤ) : negOnePow n * negOnePow n = 1 := by delta neg_one_pow; simp

@[simp]
theorem negOnePow_smul_self {α : Type _} [AddCommGroup α] (n : ℤ) (X : α) :
    negOnePow n • negOnePow n • X = X := by simp [smul_smul]

open CategoryTheory

variable {A : Type _} [Category A] [Preadditive A]

@[simps]
def negOnePowSmulIso (n : ℤ) {X Y : A} (e : X ≅ Y) : X ≅ Y
    where
  Hom := n.neg_one_pow • e.Hom
  inv := n.neg_one_pow • e.inv

@[simps]
def negOnePowArrowIsoLeft (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (n.neg_one_pow • f) :=
  Arrow.isoMk (n.negOnePowSmulIso (Iso.refl _)) (Iso.refl _) (by dsimp; simp)

@[simps]
def negOnePowArrowIsoRight (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    Arrow.mk f ≅ Arrow.mk (n.neg_one_pow • f) :=
  Arrow.isoMk (Iso.refl _) (n.negOnePowSmulIso (Iso.refl _)) (by dsimp; simp)

end Int

