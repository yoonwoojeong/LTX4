import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Homology.HomologicalComplex

#align_import for_mathlib.simplicial.complex

namespace CategoryTheory

variable {C : Type _} [Category C] [Preadditive C] (M : CosimplicialObject C)

namespace CosimplicialObject

open SimplexCategory Finset AddMonoidHom CategoryTheory.Preadditive

open scoped Simplicial BigOperators

/-- The coboundary map in the alternating face map cochain complex. -/
def coboundary (n : ℕ) : M.obj [n] ⟶ M.obj [n + 1] :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • M.δ i

theorem coboundary_zero : coboundary M 0 = M.δ 0 - M.δ 1 := by
  simp only [coboundary, Fin.sum_univ_succ, Fin.default_eq_zero, Fin.val_zero, one_zsmul,
    Fin.val_succ, univ_unique, neg_zsmul, pow_one, Fin.succ_zero_eq_one', sum_singleton, pow_zero,
    sub_eq_add_neg]

@[reassoc]
theorem coboundary_coboundary (n : ℕ) : coboundary M n ≫ coboundary M (n + 1) = 0 :=
  by
  let s : Finset (Fin (n + 2) × Fin (n + 3)) := univ.filter fun ij => (ij.2 : ℕ) ≤ ij.1
  calc
    coboundary M n ≫ coboundary M (n + 1) =
        comp_hom (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • M.δ i)
          (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • M.δ i) :=
      rfl
    _ = ∑ (i : Fin (n + 2)) (j : Fin (n + 3)), (-1 : ℤ) ^ (i + j : ℕ) • M.δ i ≫ M.δ j := _
    _ = ∑ ij : Fin (n + 2) × Fin (n + 3), (-1 : ℤ) ^ (ij.1 + ij.2 : ℕ) • M.δ ij.1 ≫ M.δ ij.2 := by
      rw [← univ_product_univ, sum_product]
    _ =
        ∑ ij in s, (-1 : ℤ) ^ (ij.1 + ij.2 : ℕ) • M.δ ij.1 ≫ M.δ ij.2 +
          ∑ ij in sᶜ, (-1 : ℤ) ^ (ij.1 + ij.2 : ℕ) • M.δ ij.1 ≫ M.δ ij.2 :=
      by rw [sum_add_sum_compl]
    _ = 0 := _
  · simp only [map_sum, map_zsmul, finset_sum_apply, smul_apply, smul_sum, pow_add, mul_smul]
    rfl
  erw [← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  -- The sums are equal because we can give a bijection
  -- between the indexing sets, such that corresponding terms are equal.
  -- We get 4 goals. All the substance is in the second goal.
  refine'
    Finset.sum_bij
      (fun (ij : Fin (n + 2) × Fin (n + 3)) hij =>
        (ij.2.castLT (lt_of_le_of_lt (mem_filter.mp hij).right ij.1.is_lt), ij.1.succ))
      _ _ _ _
  · -- Show that our function is well-defined
    rintro ⟨i, j⟩ hij;
    simp only [mem_filter, true_and_iff, mem_univ, not_le, mem_compl, Fin.val_succ]
    dsimp [s] at hij ⊢; simp only [true_and_iff, mem_filter, mem_univ] at hij 
    apply Nat.lt_of_succ_le; apply Nat.succ_le_succ; exact hij
  · -- The core of the proof.
    -- After all, we have to use the simplicial identity somewhere.
    rintro ⟨i, j⟩ hij_aux
    have hij := (mem_filter.mp hij_aux).2
    dsimp at hij ⊢
    rw [δ_comp_δ]; swap
    · rwa [← Fin.val_fin_le]
    rw [← neg_zsmul]
    congr 1
    calc
      (-1) ^ (i + j : ℕ) = -(-1) ^ (i + j + 1 : ℕ) := _
      _ = -(-1) ^ (j + (i + 1) : ℕ) := _
      _ = _ := _
    · rw [pow_succ, neg_one_mul, neg_neg]
    · rw [add_assoc, add_left_comm]
    · simp only [Fin.val_succ]
  · -- Show that our function is injective
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hij₁ hij₂ h
    rw [Prod.mk.inj_iff, Fin.eq_iff_veq, Fin.eq_iff_veq] at h ⊢
    simp at h 
    rwa [and_comm'] at h 
  · -- Show that our function is surjective
    rintro ⟨i, j⟩ hij
    refine' ⟨⟨j.pred _, i.cast_succ⟩, _, _⟩
    · intro H
      rw [H, mem_compl, mem_filter, not_and] at hij 
      exact hij (mem_univ _) (Nat.zero_le _)
    · cases i
      simp only [true_and_iff, mem_compl, mem_filter, mem_univ, not_le, Fin.coe_pred] at hij ⊢
      exact Nat.le_pred_of_lt hij
    · ext <;> simp only [Fin.succ_pred, Fin.pred_succ, Fin.castLT_castSucc]

/-- Make a cochain complex from a cosimplicial object. -/
def toCocomplex : CochainComplex C ℕ :=
  CochainComplex.of (fun n => M.obj [n]) (fun n => M.coboundary n) M.coboundary_coboundary

/-- A functorial version of `to_cocomplex`. -/
def cocomplex : CosimplicialObject C ⥤ CochainComplex C ℕ
    where
  obj := toCocomplex
  map M N f :=
    { f := fun i => f.app _
      comm' := by
        rintro i j (rfl : i + 1 = j)
        dsimp [to_cocomplex, CochainComplex.of]
        simp only [if_pos rfl, Category.comp_id, CategoryTheory.eqToHom_refl, coboundary, δ,
          Preadditive.sum_comp, Preadditive.comp_sum, comp_zsmul, zsmul_comp,
          NatTrans.naturality] }

namespace Augmented

/-- The objects defining the cochain complex associated to an augmented cosimplicial object. -/
@[nolint unused_arguments]
def toCocomplexObj (M : Augmented C) : ℕ → C
  | 0 => Augmented.point.obj M
  | n + 1 => (Augmented.drop.obj M).obj [n]

/-- The boundary maps defining the cochain complex associated to an augmented cosimplicial object.-/
def toCocomplexD {M : Augmented C} : ∀ n : ℕ, toCocomplexObj M n ⟶ toCocomplexObj M (n + 1)
  | 0 => M.hom.app _
  | n + 1 => (Augmented.drop.obj M).coboundary _

/-- The cochain complex associated to an augmented cosimplicial object. -/
@[simps]
def toCocomplex (M : Augmented C) : CochainComplex C ℕ :=
  CochainComplex.of (toCocomplexObj M) toCocomplexD
    (by
      rintro (_ | _)
      · dsimp [CategoryTheory.CosimplicialObject.Augmented.toCocomplexD]
        erw [coboundary_zero, Preadditive.comp_sub, sub_eq_zero, ← M.hom.naturality, ←
          M.hom.naturality]
        rfl
      · apply coboundary_coboundary)

/-- A functorial version of to_cocomplex. -/
def cocomplex : Augmented C ⥤ CochainComplex C ℕ
    where
  obj := toCocomplex
  map M N f :=
    { f := fun i =>
        match i with
        | 0 => point.map f
        | n + 1 => (drop.map f).app _
      comm' := by
        rintro i j (rfl : i + 1 = j)
        dsimp [to_cocomplex, CochainComplex.of]
        simp only [if_pos rfl, CategoryTheory.eqToHom_refl, Category.comp_id]
        cases i
        · dsimp [CategoryTheory.CosimplicialObject.Augmented.toCocomplexD]
          erw [← NatTrans.comp_app, ← f.w]
          rfl
        · dsimp [CategoryTheory.CosimplicialObject.Augmented.toCocomplexD, coboundary]
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, comp_zsmul, zsmul_comp]
          apply Fintype.sum_congr
          intro i
          erw [(drop.map f).naturality]
          rfl }
  map_id M := by ext (_ | _); tidy
  map_comp M N K f g := by ext (_ | _); tidy

end Augmented

end CosimplicialObject

end CategoryTheory

namespace CategoryTheory

variable {C : Type _} [Category C] [Preadditive C] (M : SimplicialObject C)

namespace SimplicialObject

open SimplexCategory Finset CategoryTheory.Preadditive Opposite

open scoped Simplicial BigOperators

/-- The boundary map in the alternating face map chain complex. -/
def boundary (n : ℕ) : M.obj (Opposite.op [n + 1]) ⟶ M.obj (Opposite.op [n]) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • M.δ i

theorem boundary_zero : boundary M 0 = M.δ 0 - M.δ 1 := by
  simp only [boundary, Fin.sum_univ_succ, Fin.default_eq_zero, Fin.val_zero, one_zsmul,
    Fin.val_succ, univ_unique, neg_zsmul, pow_one, Fin.succ_zero_eq_one', sum_singleton, pow_zero,
    sub_eq_add_neg]

theorem coboundary_rightOp (n : ℕ) :
    (CosimplicialObject.coboundary M.rightOp n).unop = boundary M n :=
  by
  dsimp only [CosimplicialObject.coboundary, boundary]
  simp only [unop_sum, unop_zsmul]
  rfl

@[reassoc]
theorem boundary_boundary (n : ℕ) : boundary M (n + 1) ≫ boundary M n = 0 := by
  rw [← CategoryTheory.SimplicialObject.coboundary_rightOp, ← CategoryTheory.SimplicialObject.coboundary_rightOp, ← unop_comp,
    CosimplicialObject.coboundary_coboundary, unop_zero]

/-- Make a chain complex from a simplicial object. -/
def toComplex : ChainComplex C ℕ :=
  ChainComplex.of (fun n => M.obj (Opposite.op [n])) (fun n => M.boundary n) M.boundary_boundary

/-- A functorial version of `to_complex`. -/
def complex : SimplicialObject C ⥤ ChainComplex C ℕ
    where
  obj := toComplex
  map M N f :=
    { f := fun i => f.app _
      comm' := by
        rintro i j (rfl : j + 1 = i)
        dsimp [to_complex, ChainComplex.of]
        simp only [if_pos rfl, Category.id_comp, CategoryTheory.eqToHom_refl, boundary, δ, Preadditive.sum_comp,
          Preadditive.comp_sum, comp_zsmul, zsmul_comp, NatTrans.naturality] }

namespace Augmented

/-- The objects defining the chain complex associated to an augmented simplicial object. -/
@[nolint unused_arguments]
def toComplexObj (M : Augmented C) : ℕ → C
  | 0 => Augmented.point.obj M
  | n + 1 => (Augmented.drop.obj M).obj (Opposite.op [n])

/-- The boundary maps defining the chain complex associated to an augmented simplicial object.-/
def toComplexD {M : Augmented C} : ∀ n : ℕ, toComplexObj M (n + 1) ⟶ toComplexObj M n
  | 0 => M.hom.app _
  | n + 1 => (Augmented.drop.obj M).boundary _

/-- The chain complex associated to an augmented simplicial object. -/
@[simps]
def toComplex (M : Augmented C) : ChainComplex C ℕ :=
  ChainComplex.of (toComplexObj M) toComplexD
    (by
      rintro (_ | _)
      · dsimp [CategoryTheory.SimplicialObject.Augmented.toComplexD]
        erw [boundary_zero, Preadditive.sub_comp, sub_eq_zero, M.hom.naturality, M.hom.naturality]
        rfl
      · apply boundary_boundary)

/-- A functorial version of to_complex. -/
def complex : Augmented C ⥤ ChainComplex C ℕ
    where
  obj := toComplex
  map M N f :=
    { f := fun i =>
        match i with
        | 0 => point.map f
        | n + 1 => (drop.map f).app _
      comm' := by
        rintro i j (rfl : j + 1 = i)
        dsimp [to_complex, ChainComplex.of]
        simp only [if_pos rfl, CategoryTheory.eqToHom_refl, Category.id_comp]
        cases j
        · dsimp [CategoryTheory.SimplicialObject.Augmented.toComplexD]
          erw [← NatTrans.comp_app, f.w]
          rfl
        · dsimp [CategoryTheory.SimplicialObject.Augmented.toComplexD, boundary]
          simp only [Preadditive.sum_comp, Preadditive.comp_sum, comp_zsmul, zsmul_comp]
          apply Fintype.sum_congr
          intro i
          erw [(drop.map f).naturality]
          rfl }
  map_id M := by ext (_ | _); tidy
  map_comp M N K f g := by ext (_ | _); tidy

end Augmented

end SimplicialObject

end CategoryTheory

