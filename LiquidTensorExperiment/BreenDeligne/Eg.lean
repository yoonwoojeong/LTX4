import LiquidTensorExperiment.BreenDeligne.Constants

#align_import breen_deligne.eg

open scoped NNReal

namespace BreenDeligne

namespace Eg

/-!

# An explicit nontrivial example of Breen-Deligne data

This example is explained in Definition 1.10 of
the blueprint https://leanprover-community.github.io/liquid/ .

-/


open UniversalMap

/-- The `i`-th rank of this BD package is `2^i`. -/
def rank (i : ℕ) : FreeMat :=
  2 ^ i

/-- `σπ n` is an abreviation for `proj n 2 - sum n 2`. -/
def σπ (n : ℕ) :=
  UniversalMap.proj n 2 - UniversalMap.sum n 2

theorem σπ_comp_hMul_two {m n} (f : UniversalMap m n) : comp (σπ n) (mul 2 f) = comp f (σπ m) := by
  simp only [σπ, AddMonoidHom.map_sub, AddMonoidHom.sub_apply, sum_comp_mul, proj_comp_mul]

/-- The `i`-th map of this BD package is inductively defined
as the simplest solution to the homotopy condition,
so that the homotopy will consist of identity maps. -/
def map : ∀ n, rank (n + 1) ⟶ rank n
  | 0 => σπ 1
  | n + 1 => σπ (rank (n + 1)) - mul 2 (map n)

theorem map_succ (n : ℕ) : map (n + 1) = σπ (rank (n + 1)) - mul 2 (map n) :=
  rfl

theorem is_complex_zero : map 1 ≫ map 0 = 0 :=
  show comp (σπ 1) (σπ 2 - mul 2 (σπ 1)) = 0 by
    rw [AddMonoidHom.map_sub, σπ_comp_mul_two, sub_eq_zero]; rfl

theorem is_complex_succ (n : ℕ) (ih : (comp (map n)) (map (n + 1)) = 0) :
    comp (map (n + 1)) (map (n + 1 + 1)) = 0 := by
  rw [map_succ (n + 1), AddMonoidHom.map_sub, ← σπ_comp_mul_two, ← AddMonoidHom.sub_apply, ←
    AddMonoidHom.map_sub, map_succ n, sub_sub_cancel, ← mul_comp, ← map_succ, ih,
    AddMonoidHom.map_zero]

/-- The Breen--Deligne data for the example BD package. -/
def bD : Data where
  pt := rank
  d i j := if h : j + 1 = i then by subst h <;> exact map j else 0
  shape' i j h := dif_neg h
  d_comp_d' := by
    rintro i j k (rfl : j + 1 = i) (rfl : k + 1 = j)
    simp only [dif_pos rfl]
    induction' k with k ih
    · exact is_complex_zero
    · exact is_complex_succ k ih

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

open HomologicalComplex

/-- The `n`-th homotopy map for the example BD package is the identity. -/
def hmap : ∀ (j i : ℕ) (h : j + 1 = i), ((Data.mul 2).obj bD).pt j ⟶ bD.pt i
  | j, i, rfl => 𝟙 _

/-- The identity maps form a homotopy between the chain maps `proj 2` and `sum 2`
for the Breen--Deligne data `eg.BD`. -/
def h : Homotopy (bD.proj 2) (bD.Sum 2)
    where
  Hom j i := if h : j + 1 = i then hmap j i h else 0
  zero' i j h := dif_neg h
  comm := by
    intro j
    rw [dNext_nat, prevD_eq]; swap; · dsimp; rfl
    cases j
    · dsimp; rw [dif_pos rfl, dif_neg, comp_zero, zero_add]
      swap; · decide
      dsimp [BD, hmap, map, σπ]
      erw [dif_pos rfl, category.id_comp, ← sub_eq_iff_eq_add]; rfl
    · rw [dif_pos rfl, dif_pos]; swap; · rfl
      dsimp [BD, hmap, map, σπ]
      erw [dif_pos rfl, dif_pos rfl, category.id_comp]
      dsimp [Nat.succ_eq_add_one]
      erw [hmap, category.comp_id, ← sub_eq_iff_eq_add, add_sub, eq_comm, sub_eq_iff_eq_add']
      rfl

end Eg

/-- An example of a Breen--Deligne package coming from a nontrivial complex. -/
def eg : Package :=
  ⟨Eg.bD, Eg.h⟩

namespace Eg

noncomputable section

variable (r r' : ℝ≥0) [Fact (r < 1)]

/-- Very suitable sequence of constants for the example Breen--Deligne package -/
def κ : ℕ → ℝ≥0 :=
  eg.data.κ r r'

instance verySuitable [Fact (0 < r')] : eg.data.VerySuitable r r' (κ r r') :=
  eg.data.cVerySuitable _ _

instance [Fact (0 < r')] (n : ℕ) : Fact (0 < κ r r' n) :=
  Data.c__pos _ _ _ _

/-- Adept sequence of constants for the example Breen--Deligne package -/
def κ' : ℕ → ℝ≥0 :=
  eg.κ' (eg.κ r r')

instance adept [Fact (0 < r')] : Package.Adept eg (κ r r') (κ' r r') :=
  eg.κ'Adept _

end Eg

end BreenDeligne

#lint

