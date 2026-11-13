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
import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.IntervalCases
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import LiquidTensorExperiment.ForMathlib.ShortExactSequence
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.FinFunctor
import LiquidTensorExperiment.ForMathlib.ExactSeq

#align_import for_mathlib.snake_lemma

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open scoped Pseudoelement

universe v u

namespace Eq

variable {X : Type _} {x y : X} (h : x = y)

@[nolint unused_arguments]
abbrev lhs (h : x = y) :=
  x

@[nolint unused_arguments]
abbrev rhs (h : x = y) :=
  y

@[simp]
theorem lhs_def : h.lhs = x :=
  rfl

@[simp]
theorem rhs_def : h.rhs = y :=
  rfl

end Eq

namespace CategoryTheory

/-- The base diagram for the snake lemma. The object are indexed by `fin 4 × fin 3`:

(0,0) --> (0,1) --> (0,2)              | the kernels
  |         |         |
  v         v         v
(1,0) --> (1,1) --> (1,2)              | the first exact row
  |         |         |
  v         v         v
(2,0) --> (2,1) --> (2,2)              | the second exact row
  |         |         |
  v         v         v
(3,0) --> (3,1) --> (3,2)              | the cokernels

-/
def SnakeDiagram :=
  Fin 4 × Fin 3
deriving Preorder, DecidableEq

namespace SnakeDiagram

@[simps]
def o (i : Fin 4) (j : Fin 3) : SnakeDiagram :=
  (i, j)

@[simp]
theorem o_le_o (i j : Fin 4) (k l : Fin 3) : o i k ≤ o j l ↔ i ≤ j ∧ k ≤ l :=
  Iff.rfl

-- Porting note: Lean 3 `meta def hom_tac` was the tactic block
-- `simp only [o_le_o, o_fst, o_snd, prod.le_def, and_true, true_and, le_refl], dec_trivial!`;
-- mathport cannot translate Lean 3 metaprograms, so it is re-expressed as a Lean 4 macro.
macro "hom_tac" : tactic =>
  `(tactic| (simp only [CategoryTheory.SnakeDiagram.o_le_o, CategoryTheory.SnakeDiagram.o_fst,
    CategoryTheory.SnakeDiagram.o_snd, Prod.le_def, and_true, true_and, le_refl]; decide))

def hom (i j : SnakeDiagram)
    (hij : i ≤ j := by
      hom_tac) :
    i ⟶ j :=
  homOfLE hij

theorem hom_ext {i j : SnakeDiagram} (f g : i ⟶ j) : f = g := by ext

section

-- Porting note: Lean 3 `meta def map_tac` was
-- `dsimp only [mk_functor, mk_functor.map', eq_to_hom_refl, hom_of_le_refl, true_and, le_refl],
--  simp only [category.id_comp, category.comp_id, functor.map_id], refl`;
-- re-expressed as a Lean 4 macro (hygiene off: the lemmas are declared after this point).
set_option hygiene false in
macro "map_tac" : tactic =>
  `(tactic| (dsimp only [CategoryTheory.SnakeDiagram.mkFunctor, CategoryTheory.SnakeDiagram.MkFunctor.map', CategoryTheory.eqToHom_refl,
      CategoryTheory.homOfLE_refl, true_and, le_refl]
    simp only [CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id,
      CategoryTheory.Functor.map_id]
    rfl))

parameter {C : Type u} [Category.{v} C]

parameter (F : Fin 4 → Fin 3 → C)

parameter (f0 : F 0 0 ⟶ F 0 1) (g0 : F 0 1 ⟶ F 0 2)

parameter (a0 : F 0 0 ⟶ F 1 0) (b0 : F 0 1 ⟶ F 1 1) (c0 : F 0 2 ⟶ F 1 2)

parameter (f1 : F 1 0 ⟶ F 1 1) (g1 : F 1 1 ⟶ F 1 2)

parameter (a1 : F 1 0 ⟶ F 2 0) (b1 : F 1 1 ⟶ F 2 1) (c1 : F 1 2 ⟶ F 2 2)

parameter (f2 : F 2 0 ⟶ F 2 1) (g2 : F 2 1 ⟶ F 2 2)

parameter (a2 : F 2 0 ⟶ F 3 0) (b2 : F 2 1 ⟶ F 3 1) (c2 : F 2 2 ⟶ F 3 2)

parameter (f3 : F 3 0 ⟶ F 3 1) (g3 : F 3 1 ⟶ F 3 2)

parameter (sq00 : a0 ≫ f1 = f0 ≫ b0) (sq01 : b0 ≫ g1 = g0 ≫ c0)

parameter (sq10 : a1 ≫ f2 = f1 ≫ b1) (sq11 : b1 ≫ g2 = g1 ≫ c1)

parameter (sq20 : a2 ≫ f3 = f2 ≫ b2) (sq21 : b2 ≫ g3 = g2 ≫ c2)

namespace MkFunctor

def col : ∀ j : Fin 3, Fin 4 ⥤ C
  | ⟨0, h⟩ => fin4FunctorMk (flip F 0) a0 a1 a2
  | ⟨1, h⟩ => fin4FunctorMk (flip F 1) b0 b1 b2
  | ⟨2, h⟩ => fin4FunctorMk (flip F 2) c0 c1 c2
  | ⟨j + 3, h⟩ => by exfalso; revert h; decide

def row : ∀ i : Fin 4, Fin 3 ⥤ C
  | ⟨0, h⟩ => fin3FunctorMk (F 0) f0 g0
  | ⟨1, h⟩ => fin3FunctorMk (F 1) f1 g1
  | ⟨2, h⟩ => fin3FunctorMk (F 2) f2 g2
  | ⟨3, h⟩ => fin3FunctorMk (F 3) f3 g3
  | ⟨j + 4, h⟩ => by exfalso; revert h; decide

theorem col_obj (i : Fin 4) (j : Fin 3) : (col j).obj i = F i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem row_obj (i : Fin 4) (j : Fin 3) : (row i).obj j = F i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem row_eq_col_obj (i : Fin 4) (j : Fin 3) : (row i).obj j = (col j).obj i :=
  (row_obj i j).trans (col_obj i j).symm

def map' (x y : SnakeDiagram) (h : x ≤ y) : F x.1 x.2 ⟶ F y.1 y.2 :=
  eqToHom (by rw [row_obj]) ≫
    (row x.1).map h.2.hom ≫
      eqToHom (by rw [row_obj, col_obj]) ≫ (col y.2).map h.1.hom ≫ eqToHom (by rw [col_obj])

theorem map'_id (x : SnakeDiagram) : map' x x le_rfl = 𝟙 _ := by
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, Category.id_comp,
    CategoryTheory.eqToHom_refl]

def SquareCommutes (i j : Fin 4) (k l : Fin 3) (hij : i ≤ j) (hkl : k ≤ l) : Prop :=
  (col k).map hij.hom ≫ eqToHom (by rw [row_obj, col_obj]) ≫ (row j).map hkl.hom =
    eqToHom (by rw [col_obj] <;> rfl) ≫
      map' (o i k) (o j l) ⟨hij, hkl⟩ ≫ eqToHom (by rw [row_obj] <;> rfl)

theorem squareCommutes_row (i : Fin 4) (k l : Fin 3) (hkl : k ≤ l) :
    square_commutes i i k l le_rfl hkl :=
  by
  dsimp [square_commutes, map']
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [CategoryTheory.homOfLE_refl]
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Category.assoc, eq_comm]
  convert Category.comp_id _

theorem squareCommutes_col (i j : Fin 4) (k : Fin 3) (hij : i ≤ j) :
    square_commutes i j k k hij le_rfl :=
  by
  dsimp [square_commutes, map']
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [CategoryTheory.homOfLE_refl]
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [eq_comm]
  convert Category.id_comp _

theorem squareCommutes_one (i : Fin 4) (j : Fin 3) (hi : i < 3) (hj : j < 2) :
    square_commutes i (i + 1) j (j + 1) (by decide!) (by decide!) :=
  by
  fin_cases i; pick_goal 4; · exfalso; revert hi; decide
  all_goals
    fin_cases j; pick_goal 3; · exfalso; revert hj; decide
    all_goals
      simp only [square_commutes, map', CategoryTheory.eqToHom_refl, Category.comp_id, Category.id_comp]
      assumption

theorem squareCommutes_comp_row (i j k : Fin 4) (l m : Fin 3) (hij : i ≤ j) (hjk : j ≤ k)
    (hlm : l ≤ m) (h1 : square_commutes i j l m hij hlm) (h2 : square_commutes j k l m hjk hlm) :
    square_commutes i k l m (hij.trans hjk) hlm :=
  by
  dsimp [square_commutes, map'] at h1 h2 ⊢
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc,
    Category.id_comp, Category.comp_id, Category.assoc] at h1 h2 ⊢
  let φ : _ := _; let ψ : _ := _
  calc
    _ = φ ≫ h2.lhs := _
    _ = φ ≫ h2.rhs := by congr 1
    _ = h1.lhs ≫ ψ := _
    _ = h1.rhs ≫ ψ := by congr 1
    _ = _ := _
  pick_goal 5; · exact Functor.map _ hij.hom
  pick_goal 4;
  · refine' eq_to_hom _ ≫ _ ≫ eq_to_hom _
    swap; · apply row_eq_col_obj <;> assumption
    pick_goal 3; · symm; apply row_eq_col_obj <;> assumption
    exact Functor.map _ hjk.hom
  all_goals dsimp [φ, ψ, Eq.lhs_def, Eq.rhs_def]
  · simp only [← Functor.map_comp_assoc]; rfl
  · simp only [Category.assoc]; rfl
  · simp only [CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc, Category.assoc]
    dsimp
    simp only [CategoryTheory.homOfLE_refl, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc, Category.id_comp,
      Category.comp_id, Category.assoc, ← Functor.map_comp_assoc]
    rfl

theorem squareCommutes_comp_col (i j : Fin 4) (l m n : Fin 3) (hij : i ≤ j) (hlm : l ≤ m)
    (hmn : m ≤ n) (h1 : square_commutes i j l m hij hlm) (h2 : square_commutes i j m n hij hmn) :
    square_commutes i j l n hij (hlm.trans hmn) :=
  by
  dsimp [square_commutes, map'] at h1 h2 ⊢
  simp only [map', CategoryTheory.homOfLE_refl, Functor.map_id, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc,
    Category.id_comp, Category.comp_id, Category.assoc] at h1 h2 ⊢
  let φ : _ := _; let ψ : _ := _
  calc
    _ = h1.lhs ≫ φ := _
    _ = h1.rhs ≫ φ := by congr 1
    _ = ψ ≫ h2.lhs := _
    _ = ψ ≫ h2.rhs := by congr 1
    _ = _ := _
  pick_goal 5; · exact Functor.map _ hmn.hom
  pick_goal 4;
  · refine' eq_to_hom _ ≫ _ ≫ eq_to_hom _
    swap; · symm; apply row_eq_col_obj <;> assumption
    pick_goal 3; · apply row_eq_col_obj <;> assumption
    exact Functor.map _ hlm.hom
  all_goals dsimp [φ, ψ, Eq.lhs_def, Eq.rhs_def]
  · simp only [Category.assoc, ← Functor.map_comp]; rfl
  · simp only [Category.assoc]; rfl
  · simp only [CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc, Category.assoc]
    dsimp
    simp only [CategoryTheory.homOfLE_refl, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_trans_assoc, Category.id_comp,
      Category.comp_id, Category.assoc, ← Functor.map_comp_assoc]
    rfl

theorem col_comp_row (i j : Fin 4) (k l : Fin 3) (hij : i ≤ j) (hkl : k ≤ l) :
    (col k).map hij.hom ≫ eqToHom (by rw [row_obj, col_obj]) ≫ (row j).map hkl.hom =
      eqToHom (by rw [col_obj] <;> rfl) ≫
        map' (o i k) (o j l) ⟨hij, hkl⟩ ≫ eqToHom (by rw [row_obj] <;> rfl) :=
  by
  cases' i with i hi; cases' j with j hj; cases' k with k hk; cases' l with l hl
  have hkl' := hkl
  rw [← Fin.val_fin_le, Fin.val_mk, Fin.val_mk] at hij hkl 
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hij
  induction' j with j IHj
  · apply CategoryTheory.SnakeDiagram.MkFunctor.squareCommutes_row <;> assumption
  refine'
    CategoryTheory.SnakeDiagram.MkFunctor.squareCommutes_comp_row F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 sq00 sq01 sq10
      sq11 sq20 sq21 ⟨i, hi⟩ ⟨i + j, _⟩ _ _ _ _ _ hkl' _ _
  · refine' lt_trans _ hj; exact lt_add_one (i + j)
  · simp only [← Fin.val_fin_le, Fin.val_mk]; exact le_self_add
  · simp only [← Fin.val_fin_le, Fin.val_mk]; exact (lt_add_one (i + j)).le
  · refine' IHj _ _
  clear IHj hkl
  induction' l with l IHl
  · apply CategoryTheory.SnakeDiagram.MkFunctor.squareCommutes_col <;> assumption
  refine'
    CategoryTheory.SnakeDiagram.MkFunctor.squareCommutes_comp_col F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 sq00 sq01 sq10
      sq11 sq20 sq21 _ _ ⟨k, hk⟩ ⟨k + l, _⟩ _ _ _ _ _ _
  · refine' lt_trans _ hl; exact lt_add_one (k + l)
  · simp only [← Fin.val_fin_le, Fin.val_mk]; exact le_self_add
  · simp only [← Fin.val_fin_le, Fin.val_mk]; exact (lt_add_one (k + l)).le
  · refine' IHl _ _ _; simp only [← Fin.val_fin_le, Fin.val_mk]; exact le_self_add
  clear IHl
  convert
    CategoryTheory.SnakeDiagram.MkFunctor.squareCommutes_one F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 sq00 sq01 sq10 sq11
      sq20 sq21 _ _ _ _ using
    2
  · rw [Nat.one_mod, add_assoc, Nat.mod_eq_of_lt hj]
  · rw [Nat.one_mod, add_assoc, Nat.mod_eq_of_lt hl]
  · rw [← Fin.val_fin_lt, Fin.val_mk]; refine' Nat.lt_of_succ_lt_succ hj
  · rw [← Fin.val_fin_lt, Fin.val_mk]; refine' Nat.lt_of_succ_lt_succ hl

theorem map'_comp (x y z : SnakeDiagram) (hxy : x ≤ y) (hyz : y ≤ z) :
    map' x y hxy ≫ map' y z hyz = map' x z (hxy.trans hyz) :=
  by
  delta map'
  slice_lhs 4 7 => rw [CategoryTheory.eqToHom_trans_assoc]
  rw [col_comp_row]
  · dsimp [map']
    simp only [map', CategoryTheory.eqToHom_trans_assoc, Category.assoc, CategoryTheory.eqToHom_refl, Category.comp_id,
      Category.id_comp, ← Functor.map_comp_assoc]
    rfl
  all_goals assumption

end MkFunctor

def mkFunctor : SnakeDiagram ⥤ C where
  obj := Function.uncurry F
  map x y h := MkFunctor.map' F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 x y h.le
  map_id x := MkFunctor.map'_id F f0 g0 a0 b0 c0 f1 g1 a1 b1 c1 f2 g2 a2 b2 c2 f3 g3 x
  map_comp x y z hxy hyz := by rw [MkFunctor.map'_comp] <;> assumption

@[simp]
theorem mkFunctor_map_f0 : mk_functor.map (hom (0, 0) (0, 1)) = f0 := by
  map_tac

@[simp]
theorem mkFunctor_map_g0 : mk_functor.map (hom (0, 1) (0, 2)) = g0 := by
  map_tac

@[simp]
theorem mkFunctor_map_a0 : mk_functor.map (hom (0, 0) (1, 0)) = a0 := by
  map_tac

@[simp]
theorem mkFunctor_map_b0 : mk_functor.map (hom (0, 1) (1, 1)) = b0 := by
  map_tac

@[simp]
theorem mkFunctor_map_c0 : mk_functor.map (hom (0, 2) (1, 2)) = c0 := by
  map_tac

@[simp]
theorem mkFunctor_map_f1 : mk_functor.map (hom (1, 0) (1, 1)) = f1 := by
  map_tac

@[simp]
theorem mkFunctor_map_g1 : mk_functor.map (hom (1, 1) (1, 2)) = g1 := by
  map_tac

@[simp]
theorem mkFunctor_map_a1 : mk_functor.map (hom (1, 0) (2, 0)) = a1 := by
  map_tac

@[simp]
theorem mkFunctor_map_b1 : mk_functor.map (hom (1, 1) (2, 1)) = b1 := by
  map_tac

@[simp]
theorem mkFunctor_map_c1 : mk_functor.map (hom (1, 2) (2, 2)) = c1 := by
  map_tac

@[simp]
theorem mkFunctor_map_f2 : mk_functor.map (hom (2, 0) (2, 1)) = f2 := by
  map_tac

@[simp]
theorem mkFunctor_map_g2 : mk_functor.map (hom (2, 1) (2, 2)) = g2 := by
  map_tac

@[simp]
theorem mkFunctor_map_a2 : mk_functor.map (hom (2, 0) (3, 0)) = a2 := by
  map_tac

@[simp]
theorem mkFunctor_map_b2 : mk_functor.map (hom (2, 1) (3, 1)) = b2 := by
  map_tac

@[simp]
theorem mkFunctor_map_c2 : mk_functor.map (hom (2, 2) (3, 2)) = c2 := by
  map_tac

@[simp]
theorem mkFunctor_map_f3 : mk_functor.map (hom (3, 0) (3, 1)) = f3 := by
  map_tac

@[simp]
theorem mkFunctor_map_g3 : mk_functor.map (hom (3, 1) (3, 2)) = g3 := by
  map_tac

end

section

variable {𝒜 ℬ : Type _} [Category 𝒜] [Category ℬ]

variable (A : Fin 3 → 𝒜) (F : Fin 4 → 𝒜 ⥤ ℬ)

variable (f : A 0 ⟶ A 1) (g : A 1 ⟶ A 2) (α : F 0 ⟶ F 1) (β : F 1 ⟶ F 2) (γ : F 2 ⟶ F 3)

def mkFunctor' : SnakeDiagram ⥤ ℬ :=
  mkFunctor (fun i => (F i).obj ∘ A)
    ((-- FA₀₀
          F
          0).map
      f)
    ((-- FA₀₁
          F
          0).map
      g)
    (-- FA₀₂
        α.app
      _)
    (α.app _) (α.app _)
    ((-- FA₁₀
          F
          1).map
      f)
    ((-- FA₁₁
          F
          1).map
      g)
    (-- FA₁₂
        β.app
      _)
    (β.app _) (β.app _)
    ((-- FA₂₀
          F
          2).map
      f)
    ((-- FA₂₁
          F
          2).map
      g)
    (-- FA₂₂
        γ.app
      _)
    (γ.app _) (γ.app _)
    ((-- FA₃₀
          F
          3).map
      f)
    ((-- FA₃₁
          F
          3).map
      g)
    (-- FA₃₂
          α.naturality
        _).symm
    (α.naturality _).symm (β.naturality _).symm (β.naturality _).symm (γ.naturality _).symm
    (γ.naturality _).symm

end

section

variable {𝒜 ℬ 𝒞 : Type _} [Category 𝒜] [Category ℬ] [Category 𝒞]

variable (A : Fin 3 → 𝒜 ⥤ ℬ) (F : Fin 4 → ℬ ⥤ 𝒞)

variable (f : A 0 ⟶ A 1) (g : A 1 ⟶ A 2) (α : F 0 ⟶ F 1) (β : F 1 ⟶ F 2) (γ : F 2 ⟶ F 3)

def mkFunctor'' : 𝒜 → SnakeDiagram ⥤ 𝒞 := fun x =>
  mkFunctor' ![(A 0).obj x, (A 1).obj x, (A 2).obj x] F (f.app x) (g.app x) α β γ

end

section

variable {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜]

-- move (ang generalize) this
theorem exact_kernel_ι_self {A B : 𝒜} (f : A ⟶ B) : Exact (kernel.ι f) f := by
  rw [Abelian.exact_iff]; tidy

-- why do we not have abelian.exact_kernel?
-- move this
theorem exact_self_cokernel_π {A B : 𝒜} (f : A ⟶ B) : Exact f (cokernel.π f) :=
  Abelian.exact_cokernel _

local notation "kernel_map" => kernel.map _ _ _ _

local notation "cokernel_map" => cokernel.map _ _ _ _

def mkOfShortExactSequenceHom (A B : ShortExactSequence 𝒜) (f : A ⟶ B) : SnakeDiagram ⥤ 𝒜 :=
  mkFunctor-- == Passing in the matrix of objects first, to make Lean happy ==
    ![![kernel f.1, kernel f.2, kernel f.3], ![A.1, A.2, A.3], ![B.1, B.2, B.3],
      ![cokernel f.1, cokernel f.2, cokernel f.3]]
    (-- == All the morphisms in the diagram == 
      -- ker f.1
      kernel_map
      f.sq1)
    (-- ker f.2
      kernel_map
      f.sq2)
    (-- ker f.3
      kernel.ι
      _)
    (kernel.ι _)
    (kernel.ι _)--   A.1
      A.f--   A.2
      A.g--   A.3
      f.1
    f.2
    f.3--   B.1
      B.f--   B.2
      B.g
    (--   B.3
      cokernel.π
      _)
    (cokernel.π _) (cokernel.π _)
    (-- coker f.1
      cokernel_map
      f.sq1)
    (-- coker f.2
      cokernel_map
      f.sq2)
    (-- coker f.3 
    -- == Prove that the squares commute ==
    by delta kernel.map; rw [kernel.lift_ι])
    (by delta kernel.map; rw [kernel.lift_ι]) f.sq1 f.sq2
    (by delta cokernel.map; rw [cokernel.π_desc]) (by delta cokernel.map; rw [cokernel.π_desc])

end

end SnakeDiagram

open SnakeDiagram (o hom)

example (i : Fin 4) : o i 0 ⟶ o i 1 :=
  hom (i, 0) (i, 1)

local notation x "⟶[" D "]" y => D.map (hom x y)

section Definitions

variable (𝒜 : Type u) [Category.{v} 𝒜] [HasImages 𝒜] [HasZeroMorphisms 𝒜] [HasKernels 𝒜]

variable {𝒜}

structure IsSnakeInput (D : SnakeDiagram ⥤ 𝒜) : Prop where
  row_exact₁ : Exact ((1, 0)⟶[D](1, 1)) ((1, 1)⟶[D](1, 2))
  row_exact₂ : Exact ((2, 0)⟶[D](2, 1)) ((2, 1)⟶[D](2, 2))
  col_exact₁ : ∀ j, Exact ((0, j)⟶[D](1, j)) ((1, j)⟶[D](2, j))
  col_exact₂ : ∀ j, Exact ((1, j)⟶[D](2, j)) ((2, j)⟶[D](3, j))
  col_mono : ∀ j, Mono ((0, j)⟶[D](1, j))
  col_epi : ∀ j, Epi ((2, j)⟶[D](3, j))
  row_mono : Mono ((2, 0)⟶[D](2, 1))
  row_epi : Epi ((1, 1)⟶[D](1, 2))

namespace IsSnakeInput

variable {D : SnakeDiagram ⥤ 𝒜}

@[nolint unused_arguments]
theorem map_eq (hD : IsSnakeInput D) {x y : SnakeDiagram} (f g : x ⟶ y) : D.map f = D.map g :=
  congr_arg _ (SnakeDiagram.hom_ext _ _)

@[nolint unused_arguments]
theorem map_eq_id (hD : IsSnakeInput D) {x : SnakeDiagram} (f : x ⟶ x) : D.map f = 𝟙 _ := by
  rw [SnakeDiagram.hom_ext f (𝟙 x), D.map_id]

theorem hom_eq_zero₁ (hD : IsSnakeInput D) {x y : SnakeDiagram} (f : x ⟶ y)
    (h : x.1 < 2 ∧ x.1 + 1 < y.1 := by
      hom_tac) :
    D.map f = 0 := by
  cases' x with i j; cases' y with k l; cases' h with h₀ h₁; rcases f with ⟨⟨⟨hik, hjl⟩⟩⟩
  dsimp at h₀ h₁ hik hjl 
  let f₁ := hom (i, j) (i + 1, j)
  let f₂ := hom (i + 1, j) (i + 2, j)
  let f₃ := hom (i + 2, j) (k, l)
  calc
    D.map _ = D.map ((f₁ ≫ f₂) ≫ f₃) := hD.map_eq _ _
    _ = (D.map f₁ ≫ D.map f₂) ≫ D.map f₃ := by simp only [D.map_comp]
    _ = 0 ≫ D.map f₃ := _
    _ = 0 := zero_comp
  congr 1
  obtain rfl | rfl : i = 0 ∨ i = 1 := by decide!
  · exact (hD.col_exact₁ j).w
  · exact (hD.col_exact₂ j).w

open SnakeDiagram

-- Porting note: Lean 3 `meta def aux_simp` was
-- `dsimp only [snake_diagram.mk_of_short_exact_sequence_hom], simp only [mk_functor_map_f0, …]`;
-- re-expressed as a Lean 4 macro.
set_option hygiene false in
macro "aux_simp" : tactic =>
  `(tactic| (dsimp only [CategoryTheory.SnakeDiagram.mkOfShortExactSequenceHom]
    simp only [CategoryTheory.SnakeDiagram.mkFunctor_map_f0, CategoryTheory.SnakeDiagram.mkFunctor_map_g0, CategoryTheory.SnakeDiagram.mkFunctor_map_a0, CategoryTheory.SnakeDiagram.mkFunctor_map_b0, CategoryTheory.SnakeDiagram.mkFunctor_map_c0, CategoryTheory.SnakeDiagram.mkFunctor_map_f1, CategoryTheory.SnakeDiagram.mkFunctor_map_g1, CategoryTheory.SnakeDiagram.mkFunctor_map_a1, CategoryTheory.SnakeDiagram.mkFunctor_map_b1, CategoryTheory.SnakeDiagram.mkFunctor_map_c1, CategoryTheory.SnakeDiagram.mkFunctor_map_f2, CategoryTheory.SnakeDiagram.mkFunctor_map_g2, CategoryTheory.SnakeDiagram.mkFunctor_map_a2, CategoryTheory.SnakeDiagram.mkFunctor_map_b2, CategoryTheory.SnakeDiagram.mkFunctor_map_c2, CategoryTheory.SnakeDiagram.mkFunctor_map_f3, CategoryTheory.SnakeDiagram.mkFunctor_map_g3]))

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.is_snake_input.aux_simp -/
theorem mkOfShortExactSequenceHom {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜] (A B : ShortExactSequence 𝒜)
    (f : A ⟶ B) : IsSnakeInput (SnakeDiagram.mkOfShortExactSequenceHom A B f) :=
  { row_exact₁ := by
      aux_simp;
      exact A.exact'
    row_exact₂ := by
      aux_simp;
      exact B.exact'
    col_exact₁ := fun j => by
      fin_cases j <;>
        aux_simp;
      all_goals apply exact_kernel_ι_self
    col_exact₂ := fun j => by
      fin_cases j <;>
        aux_simp;
      all_goals apply exact_self_cokernel_π
    col_mono := fun j => by
      fin_cases j <;>
        aux_simp;
      all_goals infer_instance
    col_epi := fun j => by
      fin_cases j <;>
        aux_simp;
      all_goals infer_instance
    row_mono := by
      aux_simp;
      exact B.mono'
    row_epi := by
      aux_simp;
      exact A.epi' }

end IsSnakeInput

end Definitions

section

open Abelian.Pseudoelement

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

variable {D : SnakeDiagram ⥤ 𝒜}

namespace IsSnakeInput

attribute [local instance] Abelian.Pseudoelement.overToSort Abelian.Pseudoelement.homToFun
  Abelian.Pseudoelement.hasZero

section MoveMe

attribute [local instance] Abelian.Pseudoelement.overToSort Abelian.Pseudoelement.homToFun

theorem injective_iff_mono {P Q : 𝒜} (f : P ⟶ Q) : Function.Injective f ↔ Mono f :=
  ⟨fun h => mono_of_zero_of_map_zero _ (zero_of_map_zero _ h), by
    intro h <;> apply pseudo_injective_of_mono⟩

theorem surjective_iff_epi {P Q : 𝒜} (f : P ⟶ Q) : Function.Surjective f ↔ Epi f :=
  ⟨epi_of_pseudo_surjective _, by intro h <;> apply pseudo_surjective_of_epi⟩

theorem exists_of_exact {P Q R : 𝒜} {f : P ⟶ Q} {g : Q ⟶ R} (e : Exact f g) (q) (hq : g q = 0) :
    ∃ p, f p = q :=
  (pseudo_exact_of_exact e).2 _ hq

theorem eq_zero_of_exact {P Q R : 𝒜} {f : P ⟶ Q} {g : Q ⟶ R} (e : Exact f g) (p) : g (f p) = 0 :=
  (pseudo_exact_of_exact e).1 _

@[simp]
theorem kernel_ι_apply {P Q : 𝒜} (f : P ⟶ Q) (a) : f (kernel.ι f a) = 0 :=
  by
  rw [← Abelian.Pseudoelement.comp_apply]
  simp

-- (AT) I don't know if we actually want this lemma, but it came in handy below.
theorem eq_zero_iff_kernel_ι_eq_zero {P Q : 𝒜} (f : P ⟶ Q) (q) : kernel.ι f q = 0 ↔ q = 0 :=
  by
  constructor
  · intro h
    apply_fun kernel.ι f
    simp [h]
    rw [injective_iff_mono]
    infer_instance
  · intro h
    simp [h]

@[simp]
theorem cokernel_π_apply {P Q : 𝒜} (f : P ⟶ Q) (a) : cokernel.π f (f a) = 0 :=
  by
  rw [← Abelian.Pseudoelement.comp_apply]
  simp

theorem exists_of_cokernel_π_eq_zero {P Q : 𝒜} (f : P ⟶ Q) (a) :
    cokernel.π f a = 0 → ∃ b, f b = a := by
  intro h
  apply exists_of_exact _ _ h
  apply SnakeDiagram.exact_self_cokernel_π

theorem cokernel_π_surjective {P Q : 𝒜} (f : P ⟶ Q) : Function.Surjective (cokernel.π f) :=
  by
  rw [surjective_iff_epi]
  infer_instance

--move
theorem exact_isIso_iff {P Q Q' R : 𝒜} (f : P ⟶ Q) (g : Q' ⟶ R) (e : Q ⟶ Q') [IsIso e] :
    Exact f (e ≫ g) ↔ Exact (f ≫ e) g := by
  let E := CategoryTheory.asIso e
  change exact f (E.hom ≫ g) ↔ exact (f ≫ E.hom) g
  conv_rhs => rw [show g = E.inv ≫ E.hom ≫ g by simp]
  rw [exact_comp_hom_inv_comp_iff]

--lemma exact_comp_is_iso {P Q R R' : 𝒜} (f : P ⟶ Q) (g : Q ⟶ R) (e : R ⟶ R') [is_iso e] :
--  exact f (g ≫ e) ↔ exact f g := exact_comp_iso
end MoveMe

theorem row_exact₀ (hD : IsSnakeInput D) : Exact ((0, 0)⟶[D](0, 1)) ((0, 1)⟶[D](0, 2)) :=
  by
  refine' exact_of_pseudo_exact _ _ ⟨fun a => _, _⟩
  · apply_fun (0, 2)⟶[D](1, 2)
    swap; · rw [injective_iff_mono]; exact hD.col_mono _
    simp_rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp, Abelian.Pseudoelement.apply_zero]
    change D.map (hom (0, 0) (1, 0) ≫ hom (1, 0) (1, 1) ≫ hom (1, 1) (1, 2)) a = 0
    simp [Abelian.Pseudoelement.comp_apply, eq_zero_of_exact hD.row_exact₁]
  · intro b hb
    apply_fun (0, 2)⟶[D](1, 2) at hb 
    simp_rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp, Abelian.Pseudoelement.apply_zero] at
      hb 
    change D.map (hom (0, 1) (1, 1) ≫ hom (1, 1) (1, 2)) b = 0 at hb 
    simp_rw [D.map_comp, Abelian.Pseudoelement.comp_apply] at hb 
    let b' := ((0, 1)⟶[D](1, 1)) b
    change ((1, 1)⟶[D](1, 2)) b' = 0 at hb 
    obtain ⟨c, hc⟩ := exists_of_exact hD.row_exact₁ b' hb
    have hcz : ((1, 0)⟶[D](2, 0)) c = 0 :=
      by
      apply_fun (2, 0)⟶[D](2, 1)
      swap; · rw [injective_iff_mono]; apply hD.row_mono
      simp_rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp, Abelian.Pseudoelement.apply_zero]
      change D.map (hom (1, 0) (1, 1) ≫ hom (1, 1) (2, 1)) c = 0
      simp_rw [D.map_comp, Abelian.Pseudoelement.comp_apply, hc]
      dsimp [b']
      apply eq_zero_of_exact
      apply hD.col_exact₁
    obtain ⟨d, hd⟩ := exists_of_exact (hD.col_exact₁ _) c hcz
    use d
    apply_fun (0, 1)⟶[D](1, 1)
    swap; · rw [injective_iff_mono]; exact hD.col_mono _
    dsimp only [b'] at hc 
    rw [← hc, ← hd]
    simp_rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp]
    rfl

theorem row_exact₃ (hD : IsSnakeInput D) : Exact ((3, 0)⟶[D](3, 1)) ((3, 1)⟶[D](3, 2)) :=
  by
  refine' exact_of_pseudo_exact _ _ ⟨fun a => _, fun b hb => _⟩
  · obtain ⟨b, hb⟩ := (surjective_iff_epi ((2, 0)⟶[D](3, 0))).2 (hD.col_epi 0) a
    rw [← hb, ← Abelian.Pseudoelement.comp_apply, ← Abelian.Pseudoelement.comp_apply, ← D.map_comp,
      ← D.map_comp,
      map_eq hD (hom (2, 0) (3, 0) ≫ hom _ (3, 1) ≫ hom _ (3, 2))
        (hom (2, 0) (2, 1) ≫ hom _ (2, 2) ≫ hom _ _),
      ← Category.assoc, D.map_comp _ (hom (2, 2) (3, 2)), D.map_comp, hD.row_exact₂.w, zero_comp,
      zero_apply]
  · set f₁ := hom (2, 1) (2, 2)
    set f₂ := hom (2, 2) (3, 2)
    set f₃ := hom (1, 1) (2, 1)
    set f₄ := hom (2, 0) (3, 0)
    set f₅ := hom (3, 0) (3, 1)
    obtain ⟨c, hc⟩ := (surjective_iff_epi ((2, 1)⟶[D](3, 1))).2 (hD.col_epi 1) b
    let d := D.map f₁ c
    have hd : D.map f₂ d = 0 := by
      rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp,
        map_eq hD (hom (2, 1) (2, 2) ≫ hom _ (3, 2)) (hom (2, 1) (3, 1) ≫ hom _ (3, 2)), D.map_comp,
        Abelian.Pseudoelement.comp_apply, hc, hb]
    obtain ⟨e, he⟩ := exists_of_exact (hD.col_exact₂ 2) d hd
    obtain ⟨f, hf⟩ := (surjective_iff_epi ((1, 1)⟶[D](1, 2))).2 hD.row_epi e
    have hfzero : ((2, 1)⟶[D](3, 1)) ((D.map f₃) f) = 0 := by
      rw [← Abelian.Pseudoelement.comp_apply, (hD.col_exact₂ 1).w, zero_apply]
    have hdiff : D.map f₁ c = D.map f₁ (D.map f₃ f) := by
      rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp,
        map_eq hD (hom (1, 1) (2, 1) ≫ hom _ (2, 2)) (hom (1, 1) (1, 2) ≫ hom _ (2, 2)), D.map_comp,
        Abelian.Pseudoelement.comp_apply, hf, he]
    obtain ⟨g, ⟨hg₁, hg₂⟩⟩ := sub_of_eq_image _ _ _ hdiff
    obtain ⟨h, hh⟩ := exists_of_exact hD.row_exact₂ g hg₁
    use D.map f₄ h
    rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp,
      map_eq hD (hom (2, 0) (3, 0) ≫ hom _ (3, 1)) (hom _ (2, 1) ≫ hom _ _), D.map_comp,
      Abelian.Pseudoelement.comp_apply, hh, hg₂ _ ((2, 1)⟶[D](3, 1)) hfzero, hc]

theorem row_exact (hD : IsSnakeInput D) (i : Fin 4) : Exact ((i, 0)⟶[D](i, 1)) ((i, 1)⟶[D](i, 2)) :=
  by fin_cases i; exacts [hD.row_exact₀, hD.row_exact₁, hD.row_exact₂, hD.row_exact₃]

theorem hom_eq_zero₂ (hD : IsSnakeInput D) {x y : SnakeDiagram} (f : x ⟶ y)
    (h : x.2 = 0 ∧ y.2 = 2 := by
      hom_tac) :
    D.map f = 0 := by
  cases' x with i j; cases' y with k l; rcases f with ⟨⟨⟨hik, hjl⟩⟩⟩
  dsimp at h hik hjl ; rcases h with ⟨rfl, rfl⟩
  let f₁ := hom (i, 0) (i, 1)
  let f₂ := hom (i, 1) (i, 2)
  let f₃ := hom (i, 2) (k, 2)
  calc
    D.map _ = D.map ((f₁ ≫ f₂) ≫ f₃) := hD.map_eq _ _
    _ = (D.map f₁ ≫ D.map f₂) ≫ D.map f₃ := by simp only [D.map_comp]
    _ = 0 := by rw [(hD.row_exact i).w, zero_comp]

section LongSnake

theorem ker_row₁_to_row₂ (hD : IsSnakeInput D) :
    (kernel.ι ((1, 0)⟶[D](1, 1)) ≫ (1, 0)⟶[D](2, 0)) = 0 :=
  by
  refine' zero_morphism_ext _ fun a => (injective_iff_mono ((2, 0)⟶[D](2, 1))).2 hD.row_mono _
  rw [apply_zero, ← Abelian.Pseudoelement.comp_apply, Category.assoc,
    Abelian.Pseudoelement.comp_apply, ← D.map_comp,
    map_eq hD (hom (1, 0) (2, 0) ≫ hom _ (2, 1)) (hom _ (1, 1) ≫ hom _ _), D.map_comp,
    Abelian.Pseudoelement.comp_apply, kernel_ι_apply, apply_zero]

def kerRow₁ToTopLeft (hD : IsSnakeInput D) : kernel ((1, 0)⟶[D](1, 1)) ⟶ D.obj (0, 0) :=
  letI := hD.col_mono 0
  Limits.kernel.lift _ _ (ker_row₁_to_row₂ hD) ≫
    Limits.kernel.lift _ _ ((Abelian.exact_iff _ _).1 (hD.col_exact₁ 0)).2 ≫
      inv (Abelian.factorThruImage ((0, 0)⟶[D](1, 0)))

theorem kerRow₁ToTopLeft_mono (hD : IsSnakeInput D) : Mono (kerRow₁ToTopLeft hD) :=
  by
  suffices
    mono
      (Limits.kernel.lift _ _ (ker_row₁_to_row₂ hD) ≫
        Limits.kernel.lift _ _ ((Abelian.exact_iff _ _).1 (hD.col_exact₁ 0)).2)
    by letI := this; exact mono_comp _ _
  exact mono_comp _ _

theorem kerRow₁ToTopLeft_comp_eq_ι (hD : IsSnakeInput D) :
    (kerRow₁ToTopLeft hD ≫ (0, 0)⟶[D](1, 0)) = kernel.ι ((1, 0)⟶[D](1, 1)) :=
  by
  letI := hD.col_mono 0
  have :
    (inv (Abelian.factorThruImage ((0, 0)⟶[D](1, 0))) ≫ (0, 0)⟶[D](1, 0)) =
      CategoryTheory.Abelian.image.ι _ :=
    by simp
  rw [ker_row₁_to_top_left, Category.assoc, Category.assoc, this]
  simp

theorem long_row₀_exact (hD : IsSnakeInput D) : Exact (kerRow₁ToTopLeft hD) ((0, 0)⟶[D](0, 1)) :=
  by
  refine' Abelian.Pseudoelement.exact_of_pseudo_exact _ _ ⟨fun a => _, fun a ha => _⟩
  · refine' (injective_iff_mono _).2 (hD.col_mono _) _
    rw [apply_zero, ← Abelian.Pseudoelement.comp_apply, ← D.map_comp,
      map_eq hD (hom (0, 0) (0, 1) ≫ hom _ (1, 1)) (hom _ (1, 0) ≫ hom _ _), D.map_comp, ←
      Abelian.Pseudoelement.comp_apply, ← Category.assoc, ker_row₁_to_top_left_comp_eq_ι hD,
      Abelian.Pseudoelement.comp_apply, kernel_ι_apply]
  · let b := ((0, 0)⟶[D](1, 0)) a
    have hb : ((1, 0)⟶[D](1, 1)) b = 0 := by
      rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp,
        map_eq hD (hom (0, 0) (1, 0) ≫ hom _ (1, 1)) (hom _ (0, 1) ≫ hom _ _), D.map_comp,
        Abelian.Pseudoelement.comp_apply, ha, apply_zero]
    obtain ⟨c, hc⟩ := exists_of_exact CategoryTheory.exact_kernel_ι _ hb
    refine' ⟨c, (injective_iff_mono _).2 (hD.col_mono _) _⟩
    rw [← Abelian.Pseudoelement.comp_apply, ker_row₁_to_top_left_comp_eq_ι hD, hc]

theorem row₁_middle_to_coker_row₂_eq_zero (hD : IsSnakeInput D) :
    ((1, 1)⟶[D](1, 2)) ≫ ((1, 2)⟶[D](2, 2)) ≫ Limits.cokernel.π ((2, 1)⟶[D](2, 2)) = 0 :=
  by
  refine' zero_morphism_ext _ fun a => _
  rw [← Category.assoc, Abelian.Pseudoelement.comp_apply, ← D.map_comp,
    map_eq hD (hom (1, 1) (1, 2) ≫ hom _ (2, 2)) (hom _ (2, 1) ≫ hom _ _), D.map_comp, ←
    Abelian.Pseudoelement.comp_apply]
  simp

theorem row₁_to_coker_row₂_eq_zero (hD : IsSnakeInput D) :
    ((1, 2)⟶[D](2, 2)) ≫ Limits.cokernel.π ((2, 1)⟶[D](2, 2)) = 0 :=
  by
  letI := hD.row_epi
  have := row₁_middle_to_coker_row₂_eq_zero hD
  rw [← Limits.comp_zero] at this 
  exact (cancel_epi _).1 this

theorem ker_col₂_to_coker_row₂_eq_zero (hD : IsSnakeInput D) :
    kernel.ι ((2, 2)⟶[D](3, 2)) ≫ Limits.cokernel.π ((1, 2)⟶[D](2, 2)) = 0 :=
  by
  refine' zero_morphism_ext _ fun a => _
  obtain ⟨c, hc⟩ := exists_of_exact (hD.col_exact₂ 2) (kernel.ι (_⟶[D]_) a) (kernel_ι_apply _ _)
  rw [Abelian.Pseudoelement.comp_apply, ← hc, cokernel_π_apply]

def bottomRightToCokerRow₂ (hD : IsSnakeInput D) : D.obj (3, 2) ⟶ cokernel ((2, 1)⟶[D](2, 2)) :=
  letI := hD.col_epi 2
  inv (Abelian.factorThruCoimage ((2, 2)⟶[D](3, 2))) ≫
    Limits.cokernel.desc _ _ (ker_col₂_to_coker_row₂_eq_zero hD) ≫
      Limits.cokernel.desc _ _ (row₁_to_coker_row₂_eq_zero hD)

theorem bottomRightToCokerRow₂_epi (hD : IsSnakeInput D) : Epi (bottomRightToCokerRow₂ hD) :=
  by
  suffices
    epi
      (Limits.cokernel.desc _ _ (ker_col₂_to_coker_row₂_eq_zero hD) ≫
        Limits.cokernel.desc _ _ (row₁_to_coker_row₂_eq_zero hD))
    by letI := this; exact epi_comp _ _
  exact epi_comp _ _

theorem bottomRightToCokerRow₂_comp_eq_π (hD : IsSnakeInput D) :
    ((2, 2)⟶[D](3, 2)) ≫ bottomRightToCokerRow₂ hD = cokernel.π ((2, 1)⟶[D](2, 2)) :=
  by
  letI := hD.col_epi 2
  have :
    ((2, 2)⟶[D](3, 2)) ≫ inv (Abelian.factorThruCoimage ((2, 2)⟶[D](3, 2))) =
      CategoryTheory.Abelian.coimage.π _ :=
    by simp
  rw [bottom_right_to_coker_row₂, ← Category.assoc, ← Category.assoc, this]
  simp

theorem long_row₃_exact (hD : IsSnakeInput D) :
    Exact ((3, 1)⟶[D](3, 2)) (bottomRightToCokerRow₂ hD) :=
  by
  refine' Abelian.Pseudoelement.exact_of_pseudo_exact _ _ ⟨fun a => _, fun a ha => _⟩
  · letI := hD.col_epi 1
    obtain ⟨b, hb⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi ((2, 1)⟶[D](3, 1)) a
    rw [← hb, ← Abelian.Pseudoelement.comp_apply, ← Abelian.Pseudoelement.comp_apply, ←
      Category.assoc, ← D.map_comp,
      map_eq hD (hom (2, 1) (3, 1) ≫ hom _ (3, 2)) (hom _ (2, 2) ≫ hom _ _), D.map_comp,
      Category.assoc, bottom_right_to_coker_row₂_comp_eq_π hD,
      (SnakeDiagram.exact_self_cokernel_π _).w, zero_apply]
  · letI := hD.col_epi 2
    obtain ⟨b, hb⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi ((2, 2)⟶[D](3, 2)) a
    rw [← hb, ← Abelian.Pseudoelement.comp_apply, bottom_right_to_coker_row₂_comp_eq_π hD] at ha 
    obtain ⟨c, hc⟩ := exists_of_exact (Abelian.exact_cokernel _) _ ha
    refine' ⟨((2, 1)⟶[D](3, 1)) c, _⟩
    rw [← hb, ← hc, ← Abelian.Pseudoelement.comp_apply, ← Abelian.Pseudoelement.comp_apply, ←
      D.map_comp, map_eq hD (hom (2, 1) (3, 1) ≫ hom _ (3, 2)) (hom _ (2, 2) ≫ hom _ _), D.map_comp]

end LongSnake

example (hD : IsSnakeInput D) (f : o 1 0 ⟶ o 2 2) : D.map f = 0 :=
  hD.hom_eq_zero₂ f

section Delta

variable (hD : IsSnakeInput D)

def toTopRightKernel : D.obj (1, 0) ⟶ kernel ((1, 1)⟶[D](2, 2)) :=
  kernel.lift _ (_⟶[D]_)
    (by
      rw [← D.map_comp]
      change D.map (hom (1, 0) (2, 0) ≫ hom (2, 0) (2, 1) ≫ hom (2, 1) (2, 2)) = 0
      simp [hD.row_exact₂.1])

def cokernelToTopRightKernelToRightKernel :
    cokernel hD.toTopRightKernel ⟶ kernel ((1, 2)⟶[D](2, 2)) :=
  cokernel.desc _
    (kernel.lift _ (kernel.ι _ ≫ _⟶[D]_)
      (by
        rw [Category.assoc, ← D.map_comp]
        have : hom (1, 1) (1, 2) ≫ hom (1, 2) (2, 2) = hom (1, 1) (2, 2) := rfl
        rw [this]; clear this
        simp [Abelian.Pseudoelement.comp_apply]))
    (by
      dsimp only [CategoryTheory.IsSnakeInput.toTopRightKernel]
      ext a
      apply_fun kernel.ι (D.map (hom (1, 2) (2, 2)))
      swap; · rw [injective_iff_mono]; infer_instance
      simp [← Abelian.Pseudoelement.comp_apply, hD.row_exact₁.1])

instance : Mono hD.cokernelToTopRightKernelToRightKernel :=
  by
  apply mono_of_zero_of_map_zero
  intro a h
  obtain ⟨b, rfl⟩ := cokernel_π_surjective _ a
  rw [← eq_zero_iff_kernel_ι_eq_zero] at h 
  simp [← Abelian.Pseudoelement.comp_apply, CategoryTheory.IsSnakeInput.cokernelToTopRightKernelToRightKernel] at h 
  simp [Abelian.Pseudoelement.comp_apply] at h 
  have : ∃ c, ((1, 0)⟶[D](1, 1)) c = kernel.ι ((1, 1)⟶[D](2, 2)) b :=
    by
    apply exists_of_exact _ _ h
    exact hD.row_exact₁
  obtain ⟨c, hc⟩ := this
  let f : cokernel hD.toTopRightKernel ⟶ cokernel ((1, 0)⟶[D](1, 1)) := cokernel.desc _ _ _
  swap; · refine' kernel.ι _ ≫ cokernel.π _
  swap; · simp [CategoryTheory.IsSnakeInput.toTopRightKernel]
  apply_fun f
  swap;
  · rw [injective_iff_mono]
    apply mono_of_zero_of_map_zero
    intro a ha
    dsimp [f] at ha 
    obtain ⟨a, rfl⟩ := cokernel_π_surjective _ a
    simp [← Abelian.Pseudoelement.comp_apply] at ha 
    simp [Abelian.Pseudoelement.comp_apply] at ha 
    have : ∃ c, ((1, 0)⟶[D](1, 1)) c = kernel.ι ((1, 1)⟶[D](2, 2)) a :=
      by
      apply exists_of_exact _ _ ha
      apply SnakeDiagram.exact_self_cokernel_π
    obtain ⟨c, hc⟩ := this
    have : hD.toTopRightKernel c = a :=
      by
      apply_fun kernel.ι ((1, 1)⟶[D](2, 2))
      swap; · rw [injective_iff_mono]; infer_instance
      dsimp [CategoryTheory.IsSnakeInput.toTopRightKernel]
      simp [← Abelian.Pseudoelement.comp_apply]
      erw [kernel.lift_ι]
      exact hc
    simp [← this]
  dsimp only [f]
  simp [← Abelian.Pseudoelement.comp_apply, CategoryTheory.IsSnakeInput.toTopRightKernel]
  simp [Abelian.Pseudoelement.comp_apply, ← hc]

instance : Epi hD.cokernelToTopRightKernelToRightKernel :=
  by
  apply epi_of_pseudo_surjective
  intro a
  let a' := kernel.ι ((1, 2)⟶[D](2, 2)) a
  obtain ⟨b, hb⟩ : ∃ b, ((1, 1)⟶[D](1, 2)) b = a' :=
    by
    suffices Function.Surjective ((1, 1)⟶[D](1, 2)) by apply this
    rw [surjective_iff_epi]
    apply hD.row_epi
  obtain ⟨c, hc⟩ : ∃ c, kernel.ι ((1, 1)⟶[D](2, 2)) c = b :=
    by
    have : exact (kernel.ι ((1, 1)⟶[D](2, 2))) ((1, 1)⟶[D](2, 2)) := exact_kernel_ι
    apply exists_of_exact this
    rw [show hom (1, 1) (2, 2) = hom (1, 1) (1, 2) ≫ hom (1, 2) (2, 2) by rfl, D.map_comp,
      Abelian.Pseudoelement.comp_apply, hb]
    dsimp only [a']
    simp
  use cokernel.π hD.toTopRightKernel c
  apply_fun kernel.ι ((1, 2)⟶[D](2, 2))
  swap; · rw [injective_iff_mono]; infer_instance
  dsimp only [CategoryTheory.IsSnakeInput.toTopRightKernel, CategoryTheory.IsSnakeInput.cokernelToTopRightKernelToRightKernel]
  simp [← Abelian.Pseudoelement.comp_apply]
  change _ = a'
  rw [← hb]
  simp [← hb, Abelian.Pseudoelement.comp_apply, ← hc]

instance : IsIso hD.cokernelToTopRightKernelToRightKernel :=
  isIso_of_mono_of_epi _

def bottomLeftCokernelTo : cokernel ((1, 0)⟶[D](2, 1)) ⟶ D.obj (2, 2) :=
  cokernel.desc _ (_⟶[D]_)
    (by
      rw [← D.map_comp]
      change D.map (hom (1, 0) (2, 0) ≫ hom (2, 0) (2, 1) ≫ hom (2, 1) (2, 2)) = 0
      simp_rw [D.map_comp]
      simp [hD.row_exact₂.1])

def leftCokernelToKernelBottomLeftCokernelTo :
    cokernel ((1, 0)⟶[D](2, 0)) ⟶ kernel hD.bottomLeftCokernelTo :=
  kernel.lift _
    (cokernel.desc _ ((_⟶[D]_) ≫ cokernel.π _)
      (by
        rw [← Category.assoc, ← D.map_comp]
        have : hom (1, 0) (2, 0) ≫ hom (2, 0) (2, 1) = hom _ _ := rfl
        rw [this]; clear this
        simp [Abelian.Pseudoelement.comp_apply]))
    (by
      dsimp only [CategoryTheory.IsSnakeInput.bottomLeftCokernelTo]
      ext a
      obtain ⟨b, rfl⟩ : ∃ b, cokernel.π ((1, 0)⟶[D](2, 0)) b = a :=
        by
        have : Function.Surjective (cokernel.π ((1, 0)⟶[D](2, 0))) := by rw [surjective_iff_epi];
          infer_instance
        apply this
      simp [← Abelian.Pseudoelement.comp_apply, hD.row_exact₂.1])

instance : Mono hD.leftCokernelToKernelBottomLeftCokernelTo :=
  by
  apply mono_of_zero_of_map_zero
  intro a ha
  obtain ⟨a, rfl⟩ := cokernel_π_surjective _ a
  dsimp [CategoryTheory.IsSnakeInput.leftCokernelToKernelBottomLeftCokernelTo] at ha 
  rw [← eq_zero_iff_kernel_ι_eq_zero] at ha 
  simp [← Abelian.Pseudoelement.comp_apply] at ha 
  simp [Abelian.Pseudoelement.comp_apply] at ha 
  obtain ⟨c, hc⟩ : ∃ c, ((1, 0)⟶[D](2, 1)) c = ((2, 0)⟶[D](2, 1)) a :=
    by
    apply exists_of_exact _ _ ha
    apply Abelian.exact_cokernel
  have : ((1, 0)⟶[D](2, 0)) c = a := by
    apply_fun (2, 0)⟶[D](2, 1)
    swap; · rw [injective_iff_mono]; apply hD.row_mono
    simpa only [← hc, ← Abelian.Pseudoelement.comp_apply, ← D.map_comp]
  simp [← this]

instance : Epi hD.leftCokernelToKernelBottomLeftCokernelTo :=
  by
  apply epi_of_pseudo_surjective
  intro a
  let a' := kernel.ι hD.bottomLeftCokernelTo a
  obtain ⟨b, hb⟩ := cokernel_π_surjective _ a'
  have : ((2, 1)⟶[D](2, 2)) b = 0 :=
    by
    apply_fun hD.bottomLeftCokernelTo at hb 
    dsimp [a', CategoryTheory.IsSnakeInput.bottomLeftCokernelTo] at hb 
    simpa [← Abelian.Pseudoelement.comp_apply] using hb
  obtain ⟨c, hc⟩ : ∃ c, ((2, 0)⟶[D](2, 1)) c = b :=
    by
    apply exists_of_exact _ _ this
    exact hD.row_exact₂
  use cokernel.π ((1, 0)⟶[D](2, 0)) c
  apply_fun kernel.ι hD.bottomLeftCokernelTo
  swap; · rw [injective_iff_mono]; infer_instance
  change _ = a'
  simp [← Abelian.Pseudoelement.comp_apply, ← hb, CategoryTheory.IsSnakeInput.leftCokernelToKernelBottomLeftCokernelTo]
  simp [Abelian.Pseudoelement.comp_apply, hc]

instance : IsIso hD.leftCokernelToKernelBottomLeftCokernelTo :=
  isIso_of_mono_of_epi _

def δAux : cokernel hD.toTopRightKernel ⟶ kernel hD.bottomLeftCokernelTo :=
  cokernel.desc _
    (kernel.lift _ (kernel.ι _ ≫ (_⟶[D]_) ≫ cokernel.π _)
      (by
        dsimp only [CategoryTheory.IsSnakeInput.bottomLeftCokernelTo]
        simp
        rw [← D.map_comp]
        have : hom (1, 1) (2, 1) ≫ hom (2, 1) (2, 2) = hom _ _ := rfl
        rw [this]
        simp [Abelian.Pseudoelement.comp_apply]))
    (by
      dsimp only [CategoryTheory.IsSnakeInput.toTopRightKernel]
      simp
      ext
      apply_fun kernel.ι hD.bottomLeftCokernelTo
      swap; · rw [injective_iff_mono]; infer_instance
      simp [← Abelian.Pseudoelement.comp_apply]
      rw [← Category.assoc, ← D.map_comp]
      have : hom (1, 0) (1, 1) ≫ hom (1, 1) (2, 1) = hom _ _; rfl; rw [this]; clear this
      simp [Abelian.Pseudoelement.comp_apply])

def toKernel : D.obj (0, 2) ⟶ kernel ((1, 2)⟶[D](2, 2)) :=
  kernel.lift _ (_⟶[D]_) (hD.col_exact₁ _).1

instance : Mono hD.toKernel := by
  dsimp [CategoryTheory.IsSnakeInput.toKernel]
  haveI : mono ((0, 2)⟶[D](1, 2)) := hD.col_mono _
  infer_instance

instance : Epi hD.toKernel :=
  kernel.lift.epi (hD.col_exact₁ _)

instance : IsIso hD.toKernel :=
  isIso_of_mono_of_epi _

def cokernelTo : cokernel ((1, 0)⟶[D](2, 0)) ⟶ D.obj (3, 0) :=
  cokernel.desc _ (_⟶[D]_) (hD.col_exact₂ _).1

instance : Mono hD.cokernelTo :=
  Abelian.CategoryTheory.Limits.Cokernel.Desc.CategoryTheory.mono _ _ (hD.col_exact₂ _)

instance : Epi hD.cokernelTo := by
  dsimp [cokernel_to]
  haveI : epi ((2, 0)⟶[D](3, 0)) := hD.col_epi _
  infer_instance

instance : IsIso hD.cokernelTo :=
  isIso_of_mono_of_epi _

def δ : D.obj (0, 2) ⟶ D.obj (3, 0) :=
  hD.toKernel ≫
    inv hD.cokernelToTopRightKernelToRightKernel ≫-- <-- this is an iso
          hD.δAux ≫-- <- this is the key
            inv
            hD.leftCokernelToKernelBottomLeftCokernelTo ≫
          hD.cokernelTo

-- <-- this is an iso
def toδAux : D.obj (0, 1) ⟶ cokernel hD.toTopRightKernel :=
  kernel.lift _ ((0, 1)⟶[D](1, 1))
      (by
        rw [show hom (1, 1) (2, 2) = hom (1, 1) (2, 1) ≫ hom _ _ by rfl, D.map_comp, ←
          Category.assoc, (hD.col_exact₁ _).1]
        simp) ≫
    cokernel.π _

def fromδAux : kernel hD.bottomLeftCokernelTo ⟶ D.obj (3, 1) :=
  kernel.ι _ ≫
    cokernel.desc _ ((2, 1)⟶[D](3, 1))
      (by
        rw [show hom (1, 0) (2, 1) = hom (1, 0) (1, 1) ≫ hom (1, 1) (2, 1) by rfl, D.map_comp,
          Category.assoc, (hD.col_exact₂ _).w]
        simp)

theorem exact_toδAux : Exact hD.toδAux hD.δAux :=
  by
  apply exact_of_pseudo_exact
  constructor
  · intro a
    dsimp [δ_aux, to_δ_aux]
    rw [← eq_zero_iff_kernel_ι_eq_zero]
    simp only [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι_assoc,
      Category.assoc, kernel.lift_ι]
    simp [Abelian.Pseudoelement.comp_apply, eq_zero_of_exact (hD.col_exact₁ _)]
  · intro b hb
    obtain ⟨b, rfl⟩ := cokernel_π_surjective _ b
    dsimp [δ_aux] at hb 
    rw [← eq_zero_iff_kernel_ι_eq_zero] at hb 
    simp only [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι] at hb 
    simp only [Abelian.Pseudoelement.comp_apply] at hb 
    let b' := kernel.ι ((1, 1)⟶[D](2, 2)) b
    obtain ⟨c, hc⟩ := exists_of_cokernel_π_eq_zero _ _ hb; clear hb
    change _ = ((1, 1)⟶[D](2, 1)) b' at hc 
    rw [show hom (1, 0) (2, 1) = hom (1, 0) (1, 1) ≫ hom _ _ by rfl, D.map_comp,
      Abelian.Pseudoelement.comp_apply] at hc 
    obtain ⟨z, h1, h2⟩ := sub_of_eq_image _ _ _ hc.symm; clear hc
    specialize h2 _ ((1, 1)⟶[D](1, 2)) (eq_zero_of_exact hD.row_exact₁ _)
    obtain ⟨w, hw⟩ : ∃ w, ((0, 1)⟶[D](1, 1)) w = z := exists_of_exact (hD.col_exact₁ _) _ h1
    clear h1
    use w
    dsimp only [b'] at h2 
    dsimp only [to_δ_aux]
    simp only [Abelian.Pseudoelement.comp_apply]
    apply_fun hD.cokernelToTopRightKernelToRightKernel
    swap; · rw [injective_iff_mono]; infer_instance
    dsimp only [CategoryTheory.IsSnakeInput.cokernelToTopRightKernelToRightKernel]
    simp only [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, Category.assoc]
    simp only [Abelian.Pseudoelement.comp_apply]
    apply_fun kernel.ι ((1, 2)⟶[D](2, 2))
    swap; · rw [injective_iff_mono]; infer_instance
    simp only [← Abelian.Pseudoelement.comp_apply, kernel.lift_ι_assoc, Category.assoc,
      kernel.lift_ι]
    simp only [Abelian.Pseudoelement.comp_apply]
    rw [hw, h2]

theorem exact_fromδAux : Exact hD.δAux hD.fromδAux :=
  by
  apply exact_of_pseudo_exact
  constructor
  · intro a
    dsimp [δ_aux, from_δ_aux]
    obtain ⟨a, rfl⟩ := cokernel_π_surjective _ a
    simp only [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι_assoc,
      Category.assoc]
    simp [Abelian.Pseudoelement.comp_apply, eq_zero_of_exact (hD.col_exact₂ _)]
  · intro b hb
    let b' := kernel.ι hD.bottomLeftCokernelTo b
    obtain ⟨c, hc⟩ := cokernel_π_surjective _ b'
    simp only [from_δ_aux, Abelian.Pseudoelement.comp_apply] at hb 
    change cokernel.desc ((1, 0)⟶[D](2, 1)) _ _ b' = 0 at hb 
    rw [← hc] at hb 
    simp only [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc] at hb 
    obtain ⟨d, hd⟩ : ∃ d, ((1, 1)⟶[D](2, 1)) d = c := exists_of_exact (hD.col_exact₂ _) _ hb
    obtain ⟨e, he⟩ : ∃ e, kernel.ι ((1, 1)⟶[D](2, 2)) e = d :=
      by
      apply exists_of_exact _ _ (_ : ((1, 1)⟶[D](2, 2)) d = 0)
      · apply exact_kernel_ι
      dsimp [b'] at hc 
      apply_fun hD.bottomLeftCokernelTo at hc 
      simp only [CategoryTheory.IsSnakeInput.bottomLeftCokernelTo, ← Abelian.Pseudoelement.comp_apply, cokernel.π_desc] at hc 
      rw [show hom (1, 1) (2, 2) = hom (1, 1) (2, 1) ≫ hom (2, 1) (2, 2) by rfl, D.map_comp,
        Abelian.Pseudoelement.comp_apply, hd, hc]
      simp only [Abelian.Pseudoelement.comp_apply]
      change hD.bottomLeftCokernelTo (kernel.ι hD.bottomLeftCokernelTo b) = 0
      apply kernel_ι_apply
    use cokernel.π hD.toTopRightKernel e
    apply_fun kernel.ι hD.bottomLeftCokernelTo
    swap; · rw [injective_iff_mono]; infer_instance
    change _ = b'
    dsimp [δ_aux]
    simp only [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι]
    simp only [Abelian.Pseudoelement.comp_apply]
    rw [he, hd, hc]

theorem exact_to_δ : Exact ((0, 1)⟶[D](0, 2)) hD.δ :=
  by
  dsimp [δ]
  rw [CategoryTheory.IsSnakeInput.exact_isIso_iff, CategoryTheory.IsSnakeInput.exact_isIso_iff, exact_comp_iso]
  convert hD.exact_toδAux using 1
  rw [IsIso.comp_inv_eq]
  dsimp [CategoryTheory.IsSnakeInput.toKernel, to_δ_aux, CategoryTheory.IsSnakeInput.cokernelToTopRightKernelToRightKernel]
  ext
  simp only [cokernel.π_desc, kernel.lift_ι_assoc, Category.assoc, kernel.lift_ι]
  simpa only [← D.map_comp]

theorem exact_from_δ : Exact hD.δ ((3, 0)⟶[D](3, 1)) :=
  by
  dsimp [δ]
  rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.IsSnakeInput.exact_isIso_iff, exact_iso_comp]
  convert hD.exact_fromδAux using 1
  rw [Category.assoc, IsIso.inv_comp_eq]
  dsimp [cokernel_to, CategoryTheory.IsSnakeInput.leftCokernelToKernelBottomLeftCokernelTo, from_δ_aux]
  ext
  simp only [cokernel.π_desc, kernel.lift_ι_assoc, cokernel.π_desc_assoc, Category.assoc]
  simpa only [← D.map_comp]

end Delta

section DeltaSpec

variable (hD : IsSnakeInput D)

def toKernel' : kernel ((1, 1)⟶[D](2, 2)) ⟶ D.obj (0, 2) :=
  kernel.lift _ (kernel.ι _ ≫ D.map (hom (1, 1) (1, 2)))
      (by erw [Category.assoc, ← D.map_comp, kernel.condition]) ≫
    inv hD.toKernel

instance to_kernel_epi : Epi hD.toKernel' :=
  by
  dsimp [CategoryTheory.IsSnakeInput.toKernel']
  apply (config := { instances := false }) epi_comp; swap; infer_instance
  haveI : epi ((1, 1)⟶[D](1, 2)) := hD.row_epi
  replace hh := pseudo_surjective_of_epi ((1, 1)⟶[D](1, 2))
  apply epi_of_pseudo_surjective
  intro t
  obtain ⟨s, hs⟩ := hh (kernel.ι ((1, 2)⟶[D](2, 2)) t)
  obtain ⟨w, hw⟩ : ∃ w, kernel.ι ((1, 1)⟶[D](2, 2)) w = s :=
    by
    have : exact (kernel.ι ((1, 1)⟶[D](2, 2))) ((1, 1)⟶[D](2, 2)) := exact_kernel_ι
    replace this := pseudo_exact_of_exact this
    apply this.2
    rw [show hom (1, 1) (2, 2) = hom (1, 1) (1, 2) ≫ hom (1, 2) (2, 2) by rfl, Functor.map_comp,
      Abelian.Pseudoelement.comp_apply, hs, ← Abelian.Pseudoelement.comp_apply, kernel.condition,
      Abelian.Pseudoelement.zero_apply]
  use w
  apply Abelian.Pseudoelement.pseudo_injective_of_mono (kernel.ι ((1, 2)⟶[D](2, 2)))
  rw [← hs, ← Abelian.Pseudoelement.comp_apply, kernel.lift_ι, Abelian.Pseudoelement.comp_apply, hw]

def cokernelTo' : D.obj (3, 0) ⟶ cokernel ((1, 0)⟶[D](2, 1)) :=
  inv hD.cokernelTo ≫
    cokernel.desc _ (D.map (hom (2, 0) (2, 1)) ≫ cokernel.π _)
      (by erw [← Category.assoc, ← D.map_comp, cokernel.condition])

instance cokernelTo'_mono : Mono hD.cokernelTo' :=
  by
  dsimp [CategoryTheory.IsSnakeInput.cokernelTo']
  apply (config := { instances := false }) mono_comp; infer_instance
  apply Abelian.Pseudoelement.mono_of_zero_of_map_zero
  intro a ha
  obtain ⟨b, rfl⟩ : ∃ b, cokernel.π ((1, 0)⟶[D](2, 0)) b = a := by
    apply Abelian.Pseudoelement.pseudo_surjective_of_epi
  rw [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc, Abelian.Pseudoelement.comp_apply] at ha 
  obtain ⟨c, hc⟩ : ∃ c, ((1, 0)⟶[D](2, 1)) c = ((2, 0)⟶[D](2, 1)) b :=
    by
    have : exact ((1, 0)⟶[D](2, 1)) (cokernel.π _) := Abelian.exact_cokernel _
    replace this := pseudo_exact_of_exact this
    apply this.2
    exact ha
  have hc' : ((1, 0)⟶[D](2, 0)) c = b :=
    by
    haveI : mono ((2, 0)⟶[D](2, 1)) := hD.row_mono
    apply Abelian.Pseudoelement.pseudo_injective_of_mono ((2, 0)⟶[D](2, 1))
    rw [← Abelian.Pseudoelement.comp_apply, ← D.map_comp]
    exact hc
  rw [← hc', ← Abelian.Pseudoelement.comp_apply, cokernel.condition,
    Abelian.Pseudoelement.zero_apply]

theorem δ_spec :
    hD.toKernel' ≫ hD.δ ≫ hD.cokernelTo' = kernel.ι _ ≫ D.map (hom (1, 1) (2, 1)) ≫ cokernel.π _ :=
  by
  dsimp only [is_snake_input.δ, IsSnakeInput.toKernel', IsSnakeInput.cokernelTo']
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]
  dsimp only [IsSnakeInput.cokernelToTopRightKernelToRightKernel]
  dsimp only [IsSnakeInput.leftCokernelToKernelBottomLeftCokernelTo]
  dsimp only [is_snake_input.δ_aux]
  let t := _; change _ ≫ _ ≫ _ ≫ t = _
  have ht : t = kernel.ι _ := by
    dsimp [t]
    rw [IsIso.inv_comp_eq]
    apply coequalizer.hom_ext
    simp only [cokernel.π_desc, Category.assoc, kernel.lift_ι, cokernel.π_desc_assoc]
  rw [ht]; clear ht; clear t
  let t := _; change t ≫ _ = _
  let s := _; change t ≫ s ≫ _ = _
  have hst : t ≫ s = cokernel.π _ := by
    dsimp [s, t]
    rw [IsIso.comp_inv_eq]
    apply equalizer.hom_ext
    simp only [cokernel.π_desc]
  rw [reassoc_of hst]; clear hst; clear s; clear t
  simp only [cokernel.π_desc_assoc, kernel.lift_ι]

theorem eq_δ_of_spec (e : D.obj (0, 2) ⟶ D.obj (3, 0))
    (he :
      hD.toKernel' ≫ e ≫ hD.cokernelTo' = kernel.ι _ ≫ D.map (hom (1, 1) (2, 1)) ≫ cokernel.π _) :
    e = hD.δ := by
  rw [← cancel_mono hD.cokernelTo']
  rw [← cancel_epi hD.toKernel']
  rw [he, δ_spec]

end DeltaSpec

attribute [local instance] Limits.HasZeroObject.zero'

theorem exact_zero_to_kerRow₁ToTopLeft (hD : IsSnakeInput D) :
    Exact (0 : 0 ⟶ kernel ((1, 0)⟶[D](1, 1))) hD.kerRow₁ToTopLeft :=
  by
  haveI : mono hD.kerRow₁ToTopLeft := ker_row₁_to_top_left_mono hD
  apply exact_zero_left_of_mono

theorem exact_bottomRightToCokerRow₂_to_zero (hD : IsSnakeInput D) :
    Exact hD.bottomRightToCokerRow₂ (0 : cokernel ((2, 1)⟶[D](2, 2)) ⟶ 0) :=
  by
  rw [← epi_iff_exact_zero_right]
  apply bottom_right_to_coker_row₂_epi hD

theorem ten_term_exactSeq (hD : IsSnakeInput D) :
    ExactSeq 𝒜
      [(0 : 0 ⟶ kernel ((1, 0)⟶[D](1, 1))), hD.kerRow₁ToTopLeft, (0, 0)⟶[D](0, 1), (0, 1)⟶[D](0, 2),
        hD.δ, (3, 0)⟶[D](3, 1), (3, 1)⟶[D](3, 2), hD.bottomRightToCokerRow₂,
        (0 : cokernel ((2, 1)⟶[D](2, 2)) ⟶ 0)] :=
  by
  refine' ExactSeq.cons _ _ hD.exact_zero_to_kerRow₁ToTopLeft _ _
  refine' ExactSeq.cons _ _ hD.long_row₀_exact _ _
  refine' ExactSeq.cons _ _ hD.row_exact₀ _ _
  refine' ExactSeq.cons _ _ hD.exact_to_δ _ _
  refine' ExactSeq.cons _ _ hD.exact_from_δ _ _
  refine' ExactSeq.cons _ _ hD.row_exact₃ _ _
  refine' ExactSeq.cons _ _ hD.long_row₃_exact _ _
  refine' ExactSeq.cons _ _ hD.exact_bottomRightToCokerRow₂_to_zero _ _
  refine' ExactSeq.single _

theorem eight_term_exactSeq (hD : IsSnakeInput D) :
    ExactSeq 𝒜
      [hD.kerRow₁ToTopLeft, (0, 0)⟶[D](0, 1), (0, 1)⟶[D](0, 2), hD.δ, (3, 0)⟶[D](3, 1),
        (3, 1)⟶[D](3, 2), hD.bottomRightToCokerRow₂] :=
  ExactSeq.extract hD.ten_term_exactSeq 1 7

theorem six_term_exactSeq (hD : IsSnakeInput D) :
    ExactSeq 𝒜 [(0, 0)⟶[D](0, 1), (0, 1)⟶[D](0, 2), hD.δ, (3, 0)⟶[D](3, 1), (3, 1)⟶[D](3, 2)] :=
  ExactSeq.extract hD.eight_term_exactSeq 1 5

end IsSnakeInput

variable (𝒜)

structure SnakeInput extends SnakeDiagram ⥤ 𝒜 where
  IsSnakeInput : IsSnakeInput to_functor

namespace SnakeInput

instance : Category (SnakeInput 𝒜) :=
  InducedCategory.category toFunctor

@[simps]
def proj (x : SnakeDiagram) : SnakeInput 𝒜 ⥤ 𝒜 :=
  inducedFunctor _ ⋙ (evaluation _ _).obj x

def mkOfShortExactSequenceHom (A B : ShortExactSequence 𝒜) (f : A ⟶ B) : SnakeInput 𝒜 :=
  ⟨SnakeDiagram.mkOfShortExactSequenceHom A B f, IsSnakeInput.mkOfShortExactSequenceHom A B f⟩

def kernelSequence (D : SnakeInput 𝒜) (h1 : Mono ((1, 0)⟶[D](1, 1))) (h2 : IsZero (D.obj (3, 0))) :
    ShortExactSequence 𝒜 where
  fst := D.obj (0, 0)
  snd := D.obj (0, 1)
  trd := D.obj (0, 2)
  f := (0, 0)⟶[D](0, 1)
  g := (0, 1)⟶[D](0, 2)
  mono' := by
    letI := h1
    refine' Abelian.Pseudoelement.mono_of_zero_of_map_zero _ fun a ha => _
    obtain ⟨b, hb⟩ :=
      IsSnakeInput.exists_of_exact (IsSnakeInput.long_row₀_exact D.is_snake_input) a ha
    rw [← hb]
    simp [IsSnakeInput.kerRow₁ToTopLeft, Limits.kernel.ι_of_mono ((1, 0)⟶[D](1, 1))]
  epi' := by
    rw [(Abelian.tfae_epi (D.obj (3, 0)) ((0, 1)⟶[D](0, 2))).out 0 2]
    convert D.2.exact_to_δ
    apply h2.eq_of_tgt
  exact' := D.2.row_exact _

end SnakeInput

class HasSnakeLemma where
  δ : SnakeInput.proj 𝒜 (0, 2) ⟶ SnakeInput.proj 𝒜 (3, 0)
  exact_δ : ∀ D : SnakeInput 𝒜, Exact ((0, 1)⟶[D](0, 2)) (δ.app D)
  δ_exact : ∀ D : SnakeInput 𝒜, Exact (δ.app D) ((3, 0)⟶[D.1](3, 1))

-- why can't I write `⟶[D]`
namespace SnakeLemma

variable [HasSnakeLemma 𝒜]

variable {𝒜}

def δ (D : SnakeInput 𝒜) : D.obj (0, 2) ⟶ D.obj (3, 0) :=
  HasSnakeLemma.δ.app D

theorem exact_δ (D : SnakeInput 𝒜) : Exact ((0, 1)⟶[D](0, 2)) (δ D) :=
  HasSnakeLemma.exact_δ D

theorem δ_exact (D : SnakeInput 𝒜) : Exact (δ D) ((3, 0)⟶[D](3, 1)) :=
  HasSnakeLemma.δ_exact D

end SnakeLemma

end

end CategoryTheory

