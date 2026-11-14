import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.ZPow
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Matrix.DMatrix
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup
import Mathlib.Data.Matrix.Kronecker
import LiquidTensorExperiment.HacksAndTricks.TypePow
import LiquidTensorExperiment.HacksAndTricks.ByExactIHack

#align_import BreenDeligne.UniversalMap

/-!
# Breen-Deligne resolutions

Reference:
https://www.math.uni-bonn.de/people/scholze/Condensed.pdf#section*.4
("Appendix to Lecture IV", p. 28)

We formalize the notion of `breen_deligne_data`.
Roughly speaking, this is a collection of formal finite sums of matrices
that encode that data that rolls out of the Breen--Deligne resolution.

## Main definitions

- `breen_deligne.basic_universal_map` : the map corresponding to a matrix
- `breen_deligne.universal_map` : a formal linear combination of basic universal maps.

-/


noncomputable section

-- get some notation working:
open scoped BigOperators DirectSum Kronecker

attribute [local instance] typePow

local notation "ℤ[" A "]" => FreeAbelianGroup A

namespace BreenDeligne

open FreeAbelianGroup

/-!
Suppose you have an abelian group `A`.
What data do you need to specify a "universal" map `f : ℤ[A^m] → ℤ[A^n]`?
That is, it should be functorial in `A`.

Well, such a map is specified by what it does to `(a 1, a 2, a 3, ..., a m)`.
It can send this element to an arbitrary element of `ℤ[A^n]`,
but it has to be "universal".

In the end, this means that `f` will be a `ℤ`-linear combination of
"basic universal maps", where a "basic universal map" is one that
sends `(a 1, a 2, ..., a m)` to `(b 1, ..., b n)`,
where `b i` is a `ℤ`-linear combination `c i 1 * a 1 + ... + c i m * a m`.
So a "basic universal map" is specified by the `n × m`-matrix `c`.
-/


/-- A `basic_universal_map m n` is an `n × m`-matrix.
It captures data for a homomorphism `ℤ[A^m] → ℤ[A^n]`
functorial in the abelian group `A`.

A general such homomorphism is a formal linear combination
of `basic_universal_map`s, which we aptly call `universal_map`s. -/
-- Porting note: `@[reducible]` so that the `Matrix` API (instances, `ext`) applies directly; the
-- Lean 3 proofs used it through definitional unfolding. The `AddCommGroup` instance below is
-- `Matrix`'s, so no instance diamond arises; `*` is matrix multiplication (Lean 3's `⬝`).
@[reducible]
def BasicUniversalMap (m n : ℕ) :=
  Matrix (Fin n) (Fin m) ℤ

-- Porting note: `deriving AddCommGroup` does not work in Lean 4; give the instance explicitly.
instance (m n : ℕ) : AddCommGroup (BasicUniversalMap m n) :=
  inferInstanceAs (AddCommGroup (Matrix (Fin n) (Fin m) ℤ))

namespace BasicUniversalMap

variable (A : Type _) [AddCommGroup A]

variable {k l m n : ℕ} (g : BasicUniversalMap m n) (f : BasicUniversalMap l m)

def preEval : BasicUniversalMap m n →+ A ^ m → A ^ n :=
  AddMonoidHom.mk' (fun f x i => ∑ j, f i j • (x : Fin _ → A) j)
    (by
      intro f₁ f₂
      ext x i
      simp only [Pi.add_apply, DMatrix.add_apply, Matrix.add_apply, add_smul,
        Finset.sum_add_distrib])

theorem preEval_apply : preEval A g = fun x i => ∑ j, g i j • (x : Fin _ → A) j :=
  rfl

/-- `f.eval A` for a `f : basic_universal_map m n`
is the homomorphism `ℤ[A^m] →+ ℤ[A^n]` induced by matrix multiplication. -/
def eval : ℤ[A ^ m] →+ ℤ[A ^ n] :=
  map <| preEval A g

theorem eval_of (x : A ^ m) : g.eval A (of x) = (of <| preEval A g x) :=
  lift.of _ _

/-- The composition of basic universal maps,
defined as matrix multiplication. -/
-- Porting note: type ascription on the product so that elaboration of `*` is not stuck.
def comp : BasicUniversalMap m n →+ BasicUniversalMap l m →+ BasicUniversalMap l n :=
  AddMonoidHom.mk' (fun g => (AddMonoidHom.mk' (fun f => (g * f : Matrix (Fin n) (Fin l) ℤ)) fun M N => Matrix.mul_add g M N))
    fun g₁ g₂ => by ext1 f; exact Matrix.add_mul g₁ g₂ f

theorem eval_comp : (comp g f).eval A = (g.eval A).comp (f.eval A) :=
  by
  ext1 x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, eval_of, BreenDeligne.BasicUniversalMap.preEval, comp, Finset.smul_sum,
    Matrix.mul_apply, Finset.sum_smul, mul_smul, AddMonoidHom.mk'_apply]
  congr 1
  funext i
  exact Finset.sum_comm

theorem comp_assoc (h : BasicUniversalMap m n) (g : BasicUniversalMap l m)
    (f : BasicUniversalMap k l) : comp (comp h g) f = comp h (comp g f) :=
  Matrix.mul_assoc h g f

/-- The identity `basic_universal_map`. -/
def id (n : ℕ) : BasicUniversalMap n n :=
  (1 : Matrix (Fin n) (Fin n) ℤ)

@[simp]
theorem id_comp : comp (id _) f = f :=
  Matrix.one_mul f

@[simp]
theorem comp_id : comp g (id _) = g :=
  Matrix.mul_one g

def mul (N : ℕ) : BasicUniversalMap m n →+ BasicUniversalMap (N * m) (N * n) :=
  AddMonoidHom.mk' (fun f => Matrix.reindexLinearEquiv ℕ _ finProdFinEquiv finProdFinEquiv (1 ⊗ₖ f))
    (by
      intro f g
      simp only [Matrix.kronecker_add, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
        Matrix.submatrix_add]
      rfl)

theorem hMul_apply (N : ℕ) (f : BasicUniversalMap m n) :
    mul N f = Matrix.reindexLinearEquiv ℕ _ finProdFinEquiv finProdFinEquiv (1 ⊗ₖ f) :=
  rfl

-- Porting note: `ext` replaced by `Matrix.ext`; `Matrix.of_apply` added to `simpa`.
theorem hMul_injective (N : ℕ) (hN : 0 < N) : Function.Injective (@mul m n N) :=
  by
  intro f g H
  refine Matrix.ext fun i j => ?_
  rw [Function.funext_iff] at H 
  specialize H (finProdFinEquiv (⟨0, hN⟩, i))
  rw [Function.funext_iff] at H 
  specialize H (finProdFinEquiv (⟨0, hN⟩, j))
  dsimp only [BasicUniversalMap.mul, Matrix.kroneckerMap, AddMonoidHom.mk'_apply,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply] at H 
  simpa only [Matrix.of_apply, one_mul, Equiv.symm_apply_apply, Matrix.one_apply_eq] using H

theorem hMul_comp (N : ℕ) (g : BasicUniversalMap m n) (f : BasicUniversalMap l m) :
    mul N (comp g f) = comp (mul N g) (mul N f) :=
  by
  dsimp only [mul, comp, AddMonoidHom.mk'_apply]
  rw [Matrix.reindexLinearEquiv_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

def oneMulHom (n) : BasicUniversalMap (1 * n) n :=
  Matrix.reindexLinearEquiv ℕ _ ((finOneEquiv.prodCongr <| Equiv.refl _).trans <| Equiv.punitProd _)
    finProdFinEquiv (1 : Matrix (Fin 1 × Fin n) _ ℤ)

def oneMulInv (n) : BasicUniversalMap n (1 * n) :=
  Matrix.reindexLinearEquiv ℕ _ finProdFinEquiv
    ((finOneEquiv.prodCongr <| Equiv.refl _).trans <| Equiv.punitProd _)
    (1 : Matrix (Fin 1 × Fin n) _ ℤ)

theorem oneMulHom_inv : comp (oneMulHom n) (oneMulInv n) = id n :=
  by
  dsimp only [comp, oneMulHom, BreenDeligne.BasicUniversalMap.oneMulInv, AddMonoidHom.mk'_apply, id]
  rw [Matrix.reindexLinearEquiv_mul, Matrix.one_mul, Matrix.reindexLinearEquiv_one]

theorem oneMulInv_hom : comp (oneMulInv n) (oneMulHom n) = id _ :=
  by
  dsimp only [comp, oneMulHom, BreenDeligne.BasicUniversalMap.oneMulInv, AddMonoidHom.mk'_apply, id]
  rw [Matrix.reindexLinearEquiv_mul, Matrix.one_mul, Matrix.reindexLinearEquiv_one]

def mulMulHom (m n i : ℕ) : BasicUniversalMap (m * (n * i)) (m * n * i) :=
  Matrix.reindexLinearEquiv ℕ _
    (((Equiv.refl _).prodCongr finProdFinEquiv.symm).trans <|
      (Equiv.prodAssoc _ _ _).symm.trans <|
        (finProdFinEquiv.prodCongr <| Equiv.refl _).trans finProdFinEquiv)
    finProdFinEquiv (1 : Matrix (Fin m × Fin (n * i)) (Fin m × Fin (n * i)) ℤ)

def mulMulInv (m n i : ℕ) : BasicUniversalMap (m * n * i) (m * (n * i)) :=
  Matrix.reindexLinearEquiv ℕ _ finProdFinEquiv
    (((Equiv.refl _).prodCongr finProdFinEquiv.symm).trans <|
      (Equiv.prodAssoc _ _ _).symm.trans <|
        (finProdFinEquiv.prodCongr <| Equiv.refl _).trans finProdFinEquiv)
    (1 : Matrix (Fin m × Fin (n * i)) (Fin m × Fin (n * i)) ℤ)

theorem mulMulHom_inv {m n i : ℕ} : comp (mulMulHom m n i) (mulMulInv m n i) = id _ :=
  by
  dsimp only [comp, mulMulHom, BreenDeligne.BasicUniversalMap.mulMulInv, AddMonoidHom.mk'_apply, id]
  rw [Matrix.reindexLinearEquiv_mul, Matrix.one_mul, Matrix.reindexLinearEquiv_one]

theorem mulMulInv_hom {m n i : ℕ} : comp (mulMulInv m n i) (mulMulHom m n i) = id _ :=
  by
  dsimp only [comp, mulMulHom, BreenDeligne.BasicUniversalMap.mulMulInv, AddMonoidHom.mk'_apply, id]
  rw [Matrix.reindexLinearEquiv_mul, Matrix.one_mul, Matrix.reindexLinearEquiv_one]

def projAux {N : ℕ} (k : Fin N) : Matrix PUnit.{1} (Fin N) ℤ := fun i j => if j = k then 1 else 0

def proj (n : ℕ) {N : ℕ} (k : Fin N) : BasicUniversalMap (N * n) n :=
  Matrix.reindexLinearEquiv ℕ _ (Equiv.punitProd _) finProdFinEquiv <| projAux k ⊗ₖ 1

theorem proj_comp_hMul {N : ℕ} (k : Fin N) (f : BasicUniversalMap m n) :
    comp (proj n k) (mul N f) = comp f (proj m k) :=
  by
  dsimp only [comp, proj, mul, AddMonoidHom.mk'_apply]
  have :
    f =
      (Matrix.reindexLinearEquiv ℕ _ (Equiv.punitProd (Fin n)) (Equiv.punitProd (Fin m)))
        ((1 : Matrix PUnit.{1} PUnit.{1} ℤ) ⊗ₖ f) :=
    by
    ext i j
    simp only [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.punitProd_symm_apply, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply_eq,
      one_mul]
  conv_rhs => rw [this]
  rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
  simp only [← Matrix.mul_kronecker_mul, Matrix.kronecker, Matrix.mul_one, Matrix.one_mul]

theorem oneMulHom_eq_proj : BasicUniversalMap.oneMulHom n = BasicUniversalMap.proj n 0 :=
  by
  dsimp only [BasicUniversalMap.oneMulHom, BasicUniversalMap.proj]
  rw [← LinearEquiv.symm_apply_eq, Matrix.reindexLinearEquiv_symm,
    Matrix.reindexLinearEquiv_comp_apply, Equiv.self_trans_symm, Equiv.trans_assoc,
    Equiv.self_trans_symm, Equiv.trans_refl]
  ext ⟨i, i'⟩ ⟨j, j'⟩ : 2
  change Fin 1 at j 
  dsimp only [Matrix.reindexLinearEquiv_apply, Matrix.kronecker]
  dsimp [finOneEquiv, Equiv.prodCongrLeft, BasicUniversalMap.projAux]
  simp only [Matrix.one_apply, Prod.mk.inj_iff, @eq_comm _ _ j]
  simp only [true_and_iff, mul_boole, if_true, Prod.mk.inj_iff, eq_self_iff_true,
    eq_iff_true_of_subsingleton]

theorem projAux_kronecker_projAux (a : Fin m) (b : Fin n) :
    projAux a ⊗ₖ projAux b =
      Matrix.reindexLinearEquiv ℕ _ (Equiv.prodPUnit _).symm finProdFinEquiv.symm
        (projAux (finProdFinEquiv (a, b))) :=
  by
  ext ⟨i, i'⟩ ⟨j, j'⟩ : 2
  dsimp [Matrix.reindexLinearEquiv_apply, Matrix.kronecker, BreenDeligne.BasicUniversalMap.projAux]
  simp only [Equiv.apply_eq_iff_eq, boole_mul, Prod.mk.inj_iff, ← ite_and]

-- Porting note: proof rewritten (Lean 3 `finish` is unavailable).
theorem projAux_apply (a : Fin m) (b : Fin m) : projAux a PUnit.unit b = ite (a = b) 1 0 :=
  by
  by_cases h : a = b
  · rw [if_pos h]
    simp only [BreenDeligne.BasicUniversalMap.projAux, if_pos h.symm]
  · rw [if_neg h]
    simp only [BreenDeligne.BasicUniversalMap.projAux, if_neg (Ne.symm h)]

theorem comp_proj_hMul_proj (n N : ℕ) (j : Fin (2 * 2 ^ N)) :
    (comp (proj n (finProdFinEquiv.symm j).fst)) (mul 2 (proj n (finProdFinEquiv.symm j).snd)) =
      (comp (proj n j)) (mulMulHom 2 (2 ^ N) n) :=
  by
  dsimp only [mulMulHom, proj, comp, hMul_apply, AddMonoidHom.mk'_apply]
  rw [Matrix.reindexLinearEquiv_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_reindexLinearEquiv_one]
  simp only [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Function.comp.right_id,
    Matrix.submatrix_submatrix, Equiv.refl_symm, Equiv.coe_refl]
  ext x y
  dsimp [Matrix.submatrix, -finProdFinEquiv_symm_apply]
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [mul_boole, mul_ite, MulZeroClass.mul_zero, Equiv.symm_apply_apply, mul_one]
  congr 2
  simp only [BreenDeligne.BasicUniversalMap.projAux_apply, boole_mul]
  rw [← ite_and]
  congr 1
  rw [← Prod.mk.inj_iff, Prod.mk.eta, Equiv.symm_apply_eq]

end BasicUniversalMap

/-- A `universal_map m n` is a formal `ℤ`-linear combination
of `basic_universal_map`s.
It captures the data for a homomorphism `ℤ[A^m] → ℤ[A^n]`. -/
-- Porting note: `@[reducible]`, see `BasicUniversalMap`.
@[reducible]
def UniversalMap (m n : ℕ) :=
  ℤ[BasicUniversalMap m n]

-- Porting note: `deriving AddCommGroup` does not work in Lean 4; give the instance explicitly.
instance (m n : ℕ) : AddCommGroup (UniversalMap m n) :=
  inferInstanceAs (AddCommGroup (ℤ[BasicUniversalMap m n]))

namespace UniversalMap

universe u

variable {k l m n : ℕ} (g : UniversalMap m n) (f : UniversalMap l m)

variable (A : Type u) [AddCommGroup A]

/-- `f.eval A` for a `f : universal_map m n`
is the homomorphism `ℤ[A^m] →+ ℤ[A^n]` induced by matrix multiplication
of the summands occurring in the formal linear combination `f`. -/
def eval : UniversalMap m n →+ ℤ[A ^ m] →+ ℤ[A ^ n] :=
  FreeAbelianGroup.lift fun f : BasicUniversalMap m n => f.eval A

@[simp]
theorem eval_of (f : BasicUniversalMap m n) : eval A (of f) = f.eval A :=
  lift.of _ _

/-- The composition of `universal_map`s `g` and `f`,
given by the formal linear combination of all compositions
of summands occurring in `g` and `f`. -/
def comp : UniversalMap m n →+ UniversalMap l m →+ UniversalMap l n :=
  FreeAbelianGroup.lift fun g : BasicUniversalMap m n =>
    FreeAbelianGroup.lift fun f => of <| BasicUniversalMap.comp g f

@[simp]
theorem comp_of (g : BasicUniversalMap m n) (f : BasicUniversalMap l m) :
    comp (of g) (of f) = of (BasicUniversalMap.comp g f) := by
  -- Porting note: `rw [comp, lift.of, lift.of]` no longer works
  simp only [comp, lift.of]

section

open AddMonoidHom

-- Porting note: the Lean 3 proofs used `congr; clear; ext` on partially applied homomorphisms;
-- these are replaced by induction on the free abelian groups.
theorem eval_comp : eval A (comp g f) = (eval A g).comp (eval A f) := by
  induction g using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 g =>
    induction f using FreeAbelianGroup.induction_on with
    | C0 => simp
    | C1 f => simp only [BasicUniversalMap.eval_comp, comp_of, eval_of]
    | Cn f ih => simp only [map_neg, ih, AddMonoidHom.comp_neg]
    | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.comp_add]
  | Cn g ih => simp only [map_neg, ih, AddMonoidHom.neg_apply, AddMonoidHom.neg_comp]
  | Cp g₁ g₂ ih₁ ih₂ =>
    simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply, AddMonoidHom.add_comp]

theorem comp_assoc (h : UniversalMap m n) (g : UniversalMap l m) (f : UniversalMap k l) :
    comp (comp h g) f = comp h (comp g f) := by
  induction h using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 h =>
    induction g using FreeAbelianGroup.induction_on with
    | C0 => simp
    | C1 g =>
      induction f using FreeAbelianGroup.induction_on with
      | C0 => simp
      | C1 f => simp only [BasicUniversalMap.comp_assoc, comp_of]
      | Cn f ih => simp only [map_neg, ih]
      | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
    | Cn g ih => simp only [map_neg, ih, AddMonoidHom.neg_apply]
    | Cp g₁ g₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply]
  | Cn h ih => simp only [map_neg, ih, AddMonoidHom.neg_apply]
  | Cp h₁ h₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply]

/-- The identity `universal_map`. -/
def id (n : ℕ) : UniversalMap n n :=
  of (BasicUniversalMap.id n)

@[simp]
theorem id_comp : comp (id _) f = f := by
  induction f using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 f => simp only [id, comp_of, BasicUniversalMap.id_comp]
  | Cn f ih => simp only [map_neg, ih]
  | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

@[simp]
theorem comp_id : comp g (id _) = g := by
  induction g using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 g => simp only [id, comp_of, BasicUniversalMap.comp_id]
  | Cn g ih => simp only [map_neg, ih, AddMonoidHom.neg_apply]
  | Cp g₁ g₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply]

def bound : ℕ :=
  ∑ g in f.support, (FreeAbelianGroup.coeff g f).natAbs

def BoundBy (N : ℕ) : Prop :=
  f.bound ≤ N

theorem of_boundBy (f : BasicUniversalMap m n) : BoundBy (of f) 1 := by
  simp only [BoundBy, bound, coeff_of_self, Int.natAbs_one, Finset.sum_singleton, support_of]
  exact le_rfl

theorem zero_boundBy (N : ℕ) : (0 : UniversalMap m n).BoundBy N := by
  simp only [BoundBy, bound, zero_le', Finset.sum_const_zero, AddMonoidHom.map_zero,
    Int.natAbs_zero]

theorem zero_boundBy_zero : (0 : UniversalMap m n).BoundBy 0 :=
  zero_boundBy _

-- Porting note: `calc` steps proved inline (Lean 3 `calc ... := _` with trailing goals is unsupported).
theorem BoundBy.random_index {f : UniversalMap m n} {N : ℕ} (hf : f.BoundBy N)
    (s : Finset (BasicUniversalMap m n)) : ∑ g in s, (FreeAbelianGroup.coeff g f).natAbs ≤ N :=
  by
  calc
    ∑ g in s, (FreeAbelianGroup.coeff g f).natAbs =
        ∑ g in s ∩ f.support, (FreeAbelianGroup.coeff g f).natAbs +
          ∑ g in s \ f.support, (FreeAbelianGroup.coeff g f).natAbs := by
      rw [Finset.sum_inter_add_sum_diff]
    _ = ∑ g in s ∩ f.support, (FreeAbelianGroup.coeff g f).natAbs := by
      simp only [and_imp, add_right_eq_self, Int.natAbs_eq_zero, imp_self, imp_true_iff,
        Finset.mem_sdiff, Finset.sum_eq_zero_iff, FreeAbelianGroup.not_mem_support_iff]
    _ ≤
        ∑ g in f.support ∩ s, (FreeAbelianGroup.coeff g f).natAbs +
          ∑ g in f.support \ s, (FreeAbelianGroup.coeff g f).natAbs := by
      rw [Finset.inter_comm]; simp only [le_add_iff_nonneg_right, zero_le']
    _ ≤ ∑ g in f.support, (FreeAbelianGroup.coeff g f).natAbs := by
      rw [Finset.sum_inter_add_sum_diff]
    _ ≤ N := hf

theorem BoundBy.add {f₁ f₂ : UniversalMap m n} {N₁ N₂ : ℕ} (h₁ : f₁.BoundBy N₁)
    (h₂ : f₂.BoundBy N₂) : (f₁ + f₂).BoundBy (N₁ + N₂) :=
  by
  calc
    (f₁ + f₂).bound ≤
        ∑ g : BreenDeligne.BasicUniversalMap m n in support (f₁ + f₂),
          ((coeff g f₁).natAbs + (coeff g f₂).natAbs) := by
      apply Finset.sum_le_sum
      intro g hg
      rw [AddMonoidHom.map_add]
      apply Int.natAbs_add_le
    _ ≤ N₁ + N₂ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (h₁.random_index _) (h₂.random_index _)

theorem boundBy_sum {ι : Type _} (s : Finset ι) (f : ι → UniversalMap m n) (N : ι → ℕ)
    (h : ∀ i ∈ s, (f i).BoundBy (N i)) : (∑ i in s, f i).BoundBy (∑ i in s, N i) := by
  classical
  revert h
  -- Porting note: `apply <eliminator>` needs an expected type in Lean 4
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.not_mem_empty, IsEmpty.forall_iff, Finset.sum_empty, imp_true_iff,
      forall_true_left]
    exact zero_boundBy_zero
  · intro i s his IH h
    simp only [Finset.sum_insert his]
    exact (h i <| s.mem_insert_self i).add (IH fun j hj => h j <| Finset.mem_insert_of_mem hj)

end

section Mul

open AddMonoidHom

/-
TODO: refactor `mul` to be a functor
TODO: put a monoidal structure on `FreeMat`, so that this is just `N ⊗ _`.
-/
def mul (N : ℕ) : UniversalMap m n →+ UniversalMap (N * m) (N * n) :=
  map (BasicUniversalMap.mul N)

theorem hMul_of (N : ℕ) (f : BasicUniversalMap m n) :
    mul N (of f) = of (BasicUniversalMap.mul N f) :=
  map_of_apply _

-- Porting note: the Lean 3 proofs of this and the following lemmas used `congr; clear; ext` on
-- partially applied homomorphisms; they are replaced by induction on the free abelian groups.
theorem hMul_comp (N : ℕ) (g : UniversalMap m n) (f : UniversalMap l m) :
    mul N (comp g f) = comp (mul N g) (mul N f) := by
  induction g using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 g =>
    induction f using FreeAbelianGroup.induction_on with
    | C0 => simp
    | C1 f => simp only [comp_of, hMul_of, BasicUniversalMap.hMul_comp]
    | Cn f ih => simp only [map_neg, ih]
    | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | Cn g ih => simp only [map_neg, ih, AddMonoidHom.neg_apply]
  | Cp g₁ g₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply]

theorem mem_support_hMul (N : ℕ) (hN : 0 < N) (f : UniversalMap m n) (g) :
    g ∈ (mul N f).support ↔ ∃ g', g' ∈ f.support ∧ g = BasicUniversalMap.mul N g' :=
  by
  apply FreeAbelianGroup.mem_support_map
  exact BasicUniversalMap.hMul_injective N hN

@[simp]
theorem coeff_hMul (N : ℕ) (hN : 0 < N) (f : UniversalMap m n) (g : BasicUniversalMap m n) :
    coeff (BasicUniversalMap.mul N g) (mul N f) = coeff g f := by
  induction f using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 f =>
    simp only [hMul_of, coeff, AddMonoidHom.coe_comp, Function.comp_apply,
      FreeAbelianGroup.toFinsupp_of, Finsupp.applyAddHom_apply, Finsupp.single_apply,
      (BasicUniversalMap.hMul_injective N hN).eq_iff]
  | Cn f ih => simp only [map_neg, ih]
  | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

end Mul

/-
TODO: refactor `sum` and `proj` to be natural transformations from `mul n` to `𝟭 _`.
-/
def sum (n N : ℕ) : UniversalMap (N * n) n :=
  of (∑ i, BasicUniversalMap.proj n i)

def proj (n N : ℕ) : UniversalMap (N * n) n :=
  ∑ i, of (BasicUniversalMap.proj n i)

theorem sum_comp_hMul (N : ℕ) (f : UniversalMap m n) :
    comp (sum n N) (mul N f) = comp f (sum m N) := by
  induction f using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 f =>
    simp only [sum, hMul_of, comp_of, map_sum, AddMonoidHom.finset_sum_apply,
      BasicUniversalMap.proj_comp_hMul]
    congr 1
    refine (map_sum (BasicUniversalMap.comp.flip (BasicUniversalMap.mul N f))
      (fun i => BasicUniversalMap.proj n i) Finset.univ).trans ?_
    simp only [AddMonoidHom.flip_apply, BasicUniversalMap.proj_comp_hMul]
  | Cn f ih => simp only [map_neg, ih, AddMonoidHom.neg_apply]
  | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply]

theorem proj_comp_hMul (N : ℕ) (f : UniversalMap m n) :
    comp (proj n N) (mul N f) = comp f (proj m N) := by
  induction f using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 f =>
    simp only [proj, hMul_of, comp_of, map_sum, AddMonoidHom.finset_sum_apply,
      BasicUniversalMap.proj_comp_hMul]
  | Cn f ih => simp only [map_neg, ih, AddMonoidHom.neg_apply]
  | Cp f₁ f₂ ih₁ ih₂ => simp only [map_add, ih₁, ih₂, AddMonoidHom.add_apply]

theorem proj_boundBy (n N : ℕ) : (proj n N).BoundBy N :=
  le_trans (boundBy_sum _ _ _ fun i _ => of_boundBy _) <| by
    simp only [Finset.card_fin, mul_one, Algebra.id.smul_eq_mul, Finset.sum_const]
    exact le_rfl

end UniversalMap

end BreenDeligne

-- #lint- only unused_arguments def_lemma doc_blame
