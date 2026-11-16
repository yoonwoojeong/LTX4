import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Module.Hom
import LiquidTensorExperiment.BreenDeligne.Category
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup
import LiquidTensorExperiment.Facts.Nnreal

#align_import breen_deligne.suitable

/-!

# "suitability" of a universal map

If `f` is a universal map then a pair `(c₁, c₂)` of non-negative reals is
`f`-suitable, if (morally) `f` sends things of norm at most `c₁` to things
of norm at most `c₂`. The formal definition is in definitions 1.11 and 1.12
of the blueprint.

## Main definitions

- `breen_deligne.basic_univeral_map.suitable` :  see blueprint definition 1.11.
- `breen_deligne.universal_map.suitable` : see blueprint definition 1.12.
- `breen_deligne.data.suitable` : see blueprint definition 1.13.

These are all precise ways of controlling the norm on maps between normed
objects induced by `f`.
-/


open scoped NNReal BigOperators Kronecker

-- move this??
/-- `rescale_constants κ N` for a sequence `κ : ℕ → ℝ≥0`,
  is the sequence `(κ i) / N`. -/
noncomputable def rescaleConstants (κ : ℕ → ℝ≥0) (N : ℝ≥0) : ℕ → ℝ≥0 := fun i => κ i * N⁻¹

namespace rescaleConstants

@[simp]
theorem one (κ : ℕ → ℝ≥0) : rescaleConstants κ 1 = κ := by
  funext i
  simp only [rescaleConstants, mul_one, inv_one]

end rescaleConstants

namespace BreenDeligne

variable {k l m n : ℕ}

variable (r r' : ℝ≥0) (S : Type _) (c c₁ c₂ c₃ c₄ : ℝ≥0) [Fintype S]

namespace BasicUniversalMap

variable (f : BasicUniversalMap m n)

/-- Addition goes from `Lbar r' S c` to `Lbar r' S κ` for suitable `κ`.
This predicate says what *suitable* means for basic universal maps.
See Lemma 9.11 of [Analytic]. -/
-- Porting note: in Lean 4 `attribute [class]` is not allowed on a `def`, so `Suitable` is
-- declared as a class with a single field `out` (the original body).
class Suitable (f : BasicUniversalMap m n) (c₁ c₂ : ℝ≥0) : Prop where
  out : ∀ i, (∑ j, ↑(f i j).natAbs) * c₁ ≤ c₂

theorem sup_hMul_le (f : BasicUniversalMap m n) (c₁ c₂ : ℝ≥0) [h : f.Suitable c₁ c₂] :
    (Finset.univ.sup fun i => ∑ j, ↑(f i j).natAbs) * c₁ ≤ c₂ :=
  by
  by_cases H : c₁ = 0
  · subst H; rw [MulZeroClass.mul_zero]; exact zero_le'
  rw [mul_comm, NNReal.mul_le_iff_le_inv H, Finset.sup_le_iff]
  rintro i -
  rw [← NNReal.mul_le_iff_le_inv H, mul_comm]
  exact h.out i

instance suitable_hMul_left (f : BasicUniversalMap m n) [h : f.Suitable c₁ c₂] :
    f.Suitable (c * c₁) (c * c₂) :=
  ⟨fun i => by
    rw [mul_left_comm]
    exact mul_le_mul' le_rfl (h.out i)⟩

instance suitable_hMul_right (f : BasicUniversalMap m n) [h : f.Suitable c₁ c₂] :
    f.Suitable (c₁ * c) (c₂ * c) := by
  rw [mul_comm _ c, mul_comm _ c]
  exact BasicUniversalMap.suitable_hMul_left _ _ _ _

instance suitable_id : (id n).Suitable c c := by
  refine ⟨fun i => ?_⟩
  refine (mul_le_mul' (le_of_eq ?_) le_rfl).trans (one_mul c).le
  simp only [id, Int.natAbs]
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.one_apply_eq, Nat.cast_one, Int.natAbs_one]
  · rintro j - hj
    simp only [Int.natAbs_eq_zero, Matrix.one_apply_ne' hj, Nat.cast_eq_zero, one_ne_zero]
  · intro h; exact (h <| Finset.mem_univ _).elim

-- this cannot be an instance, because c₂ cannot be inferred
theorem suitable_comp {g : BasicUniversalMap m n} {f : BasicUniversalMap l m} {c₁ : ℝ≥0} (c₂ : ℝ≥0)
    {c₃ : ℝ≥0} [hg : g.Suitable c₂ c₃] [hf : f.Suitable c₁ c₂] : (comp g f).Suitable c₁ c₃ :=
  by
  refine ⟨fun i => ?_⟩
  simp only [← Nat.coe_castRingHom, ← RingHom.map_sum, comp, Matrix.mul_apply]
  calc
    ↑(∑ k, (∑ j, g i j * f j k).natAbs) * c₁ ≤ ↑(∑ j, (g i j).natAbs * ∑ k, (f j k).natAbs) * c₁ :=
      ?_
    -- proof below
    _ = ∑ j, ↑(g i j).natAbs * ((∑ k, ↑(f j k).natAbs) * c₁) := ?_
    -- proof below
    _ ≤ ∑ j, ↑(g i j).natAbs * c₂ := ?_
    -- proof below
    _ ≤ c₃ := by rw [← Finset.sum_mul]; exact hg.out i
  · refine' mul_le_mul' _ le_rfl
    rw [Nat.cast_le]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    rintro k -
    simp only [← Int.natAbs_mul]
    apply nat_abs_sum_le
  · simp only [← Nat.coe_castRingHom, RingHom.map_sum, RingHom.map_mul, Finset.sum_mul, mul_assoc]
  · apply Finset.sum_le_sum; rintro j -; exact mul_le_mul' le_rfl (hf.out j)

instance (priority := 1001) zero_suitable : (0 : BasicUniversalMap m n).Suitable c₁ c₂ :=
  ⟨fun i => by
    -- Porting note: `show` is needed to see `0 i j` as a matrix entry
    show (∑ _j : Fin m, (((0 : ℤ).natAbs : ℕ) : ℝ≥0)) * c₁ ≤ c₂
    simp only [Nat.cast_zero, MulZeroClass.zero_mul, zero_le', Finset.sum_const_zero,
      Int.natAbs_zero]⟩

instance suitable_zero_left (f : BasicUniversalMap m n) (c : ℝ≥0) : f.Suitable 0 c :=
  ⟨fun _ => by
    rw [MulZeroClass.mul_zero]
    exact zero_le'⟩

theorem Suitable.le (hf : f.Suitable c₂ c₃) (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) : f.Suitable c₁ c₄ :=
  ⟨fun j => (mul_le_mul' le_rfl h1).trans ((hf.out j).trans h2)⟩

theorem suitable_of_le [hf : f.Suitable c₂ c₃] (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) : f.Suitable c₁ c₄ :=
  hf.le _ _ _ _ _ h1 h2

instance suitable_hMul_left_one_le (f : BasicUniversalMap m n) [h : f.Suitable c₁ c₂]
    [Fact (1 ≤ c)] : f.Suitable c₁ (c * c₂) :=
  h.le _ _ _ _ _ le_rfl <| Fact.out

instance suitable_hMul_right_one_le (f : BasicUniversalMap m n) [h : f.Suitable c₁ c₂]
    [Fact (1 ≤ c)] : f.Suitable c₁ (c₂ * c) :=
  h.le _ _ _ _ _ le_rfl <| Fact.out

instance suitable_hMul_left_le_one (f : BasicUniversalMap m n) [h : f.Suitable c₁ c₂]
    [Fact (c ≤ 1)] : f.Suitable (c * c₁) c₂ :=
  h.le _ _ _ _ _ Fact.out le_rfl

instance suitable_hMul_right_le_one (f : BasicUniversalMap m n) [h : f.Suitable c₁ c₂]
    [Fact (c ≤ 1)] : f.Suitable (c₁ * c) c₂ :=
  h.le _ _ _ _ _ Fact.out le_rfl

instance suitable_add (f g : BasicUniversalMap m n) (c cf cg : ℝ≥0) [hf : f.Suitable c cf]
    [hg : g.Suitable c cg] : (f + g).Suitable c (cf + cg) :=
  by
  refine ⟨fun i => ?_⟩
  calc
    (∑ j : Fin m, ↑((f + g) i j).natAbs) * c ≤
        (∑ j : Fin m, ↑(f i j).natAbs + ∑ j : Fin m, ↑(g i j).natAbs) * c :=
      ?_
    _ ≤ cf + cg := ?_
  · rw [← Finset.sum_add_distrib]
    refine' mul_le_mul' (Finset.sum_le_sum _) le_rfl
    rintro j -
    rw [← Nat.cast_add, Nat.cast_le]
    apply Int.natAbs_add_le
  · rw [add_mul]; apply add_le_add (hf.out i) (hg.out i)

instance suitable_sum {ι : Type _} (s : Finset ι) (f : ι → BasicUniversalMap m n) {c : ℝ≥0}
    {κ' : ι → ℝ≥0} [hf : ∀ i, (f i).Suitable c (κ' i)] :
    (∑ i in s, f i).Suitable c (∑ i in s, κ' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    infer_instance
  | @insert i s his IH =>
    simp only [Finset.sum_insert his]
    infer_instance

instance proj_suitable (N : ℕ) (k : Fin N) (c : ℝ≥0) : (proj n k).Suitable c c :=
  by
  refine ⟨fun i => ?_⟩
  apply le_of_eq
  dsimp [proj, Matrix.kronecker, BreenDeligne.BasicUniversalMap.projAux, -finProdFinEquiv_symm_apply]
  rw [Finset.sum_eq_single (finProdFinEquiv (k, i))]
  ·
    simp only [Equiv.symm_apply_apply, if_true, Matrix.one_apply_eq, Nat.cast_one,
      Int.natAbs_one, one_mul, mul_one]
  · rintro j - hj
    generalize hj' : finProdFinEquiv.symm j = j'
    rw [Equiv.symm_apply_eq] at hj' ; subst j
    cases' j' with a b
    rw [Matrix.one_apply, boole_mul, ← ite_and]
    simpa only [Int.natAbs_eq_zero, ite_eq_right_iff, Nat.cast_eq_zero, one_ne_zero,
      Equiv.apply_eq_iff_eq, Prod.mk.inj_iff, Ne.def, @eq_comm _ b] using hj
  · intro h; exact (h <| Finset.mem_univ _).elim

instance hMul_suitable (N : ℕ) (f : BasicUniversalMap m n) [hf : f.Suitable c₁ c₂] :
    (BasicUniversalMap.mul N f).Suitable c₁ c₂ :=
  by
  refine ⟨fun i => ?_⟩
  refine' (le_of_eq _).trans (hf.out <| (finProdFinEquiv.symm i).2)
  congr 1
  rw [← finProdFinEquiv.sum_comp, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  dsimp [mul, Matrix.kronecker, -finProdFinEquiv_symm_apply]
  rw [Finset.sum_eq_single (finProdFinEquiv.symm i).1]
  · congr 2
    simp only [one_mul, Equiv.symm_apply_apply, Matrix.one_apply_eq]
  · rintro k - hk
    simp only [Equiv.symm_apply_apply, Int.natAbs_eq_zero, Nat.cast_eq_zero, mul_eq_zero,
      Matrix.one_apply_ne' hk, eq_self_iff_true, true_or_iff]
  · intro h; exact (h <| Finset.mem_univ _).elim

instance oneMulHom_suitable : (oneMulHom n).Suitable c c := by
  rw [BreenDeligne.BasicUniversalMap.oneMulHom_eq_proj]
  infer_instance

instance mulMulInv_suitable (k : ℕ) : (mulMulInv m n k).Suitable c c :=
  by
  refine ⟨fun i => ?_⟩
  refine (mul_le_mul' (le_of_eq ?_) le_rfl).trans (one_mul c).le
  dsimp only [BreenDeligne.BasicUniversalMap.mulMulInv]
  simp only [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.one_apply, Equiv.eq_symm_apply]
  rw [Finset.sum_eq_single, if_pos rfl, Int.natAbs_one, Nat.cast_one]
  · rintro j - hj
    rw [if_neg, Int.natAbs_zero, Nat.cast_zero]
    exact hj.symm
  · intro h; exact (h <| Finset.mem_univ _).elim

end BasicUniversalMap

namespace UniversalMap

open FreeAbelianGroup

/-- A univeral map `f` is `suitable c₁ c₂` if all of the matrices `g`
occuring in the formal sum `f` satisfy `g.suitable c₁ c₂`.
This definition is tailored in such a way that we get a sensible
`CLCFP V r' c₂ n ⟶ CLCFP V r' c₁ m`
if `f.suitable c₁ c₂`.

See Lemma 9.11 of [Analytic]. -/
-- Porting note: in Lean 4 `attribute [class]` is not allowed on a `def`, so `Suitable` is
-- declared as a class with a single field `out` (the original body).
class Suitable (c₁ c₂ : ℝ≥0) (f : UniversalMap m n) : Prop where
  out : ∀ g ∈ f.support, BasicUniversalMap.Suitable g c₁ c₂

theorem suitable_of_mem_support (f : UniversalMap m n) (c₁ c₂ : ℝ≥0) (g : BasicUniversalMap m n)
    (hg : g ∈ f.support) [h : f.Suitable c₁ c₂] : g.Suitable c₁ c₂ :=
  h.out g hg

theorem suitable_freePredicate (c₁ c₂ : ℝ≥0) : FreePredicate (@Suitable m n c₁ c₂) := by
  intro x
  constructor
  · intro h g hg
    refine ⟨fun g' hg' => ?_⟩
    rw [support_of, Finset.mem_singleton] at hg'
    rw [hg']
    exact h.out g hg
  · intro h
    refine ⟨fun g hg => ?_⟩
    exact (h g hg).out g (by simp only [support_of, Finset.mem_singleton])

theorem suitable_congr (f g : UniversalMap m n) (c₁ c₂ : ℝ≥0) (h : f = g) :
    f.Suitable c₁ c₂ ↔ g.Suitable c₁ c₂ := by subst h; exact Iff.rfl

theorem Suitable.le {f : UniversalMap m n} (hf : f.Suitable c₂ c₃) (h1 : c₁ ≤ c₂) (h2 : c₃ ≤ c₄) :
    f.Suitable c₁ c₄ :=
  ⟨fun g hg => have := hf.out g hg; this.le _ _ _ _ _ h1 h2⟩

theorem suitable_of_le (f : UniversalMap m n) [hf : f.Suitable c₂ c₃] (h1 : c₁ ≤ c₂)
    (h2 : c₃ ≤ c₄) : f.Suitable c₁ c₄ :=
  hf.le _ _ _ _ h1 h2

/-- `f.factor` for `f : universal_map m n`
is the ratio `c₂ / c₁` that two constants need to satisfy
in order that `f.suitable c₁ c₂` holds. -/
noncomputable def factor (f : UniversalMap m n) : ℝ≥0 :=
  (f.support.product Finset.univ).sup fun gi => ∑ j, ↑(gi.1 gi.2 j).natAbs

theorem le_factor (f : UniversalMap m n) (g : BasicUniversalMap m n) (hg : g ∈ f.support)
    (i : Fin n) : ∑ j, ↑(g i j).natAbs ≤ f.factor :=
  by
  unfold factor
  exact
    Finset.le_sup (f := fun gi : BasicUniversalMap m n × Fin n => ∑ j, ((gi.1 gi.2 j).natAbs : ℝ≥0))
      (b := (g, i)) (Finset.mem_product.2 ⟨hg, Finset.mem_univ _⟩)

theorem suitable_of_factor_le (f : UniversalMap m n) (hf : f.factor ≤ c₂ * c₁⁻¹) :
    f.Suitable c₁ c₂ := by
  refine ⟨fun g hg => ⟨fun i => ?_⟩⟩
  by_cases h : c₁ = 0
  · simp only [h, zero_le', MulZeroClass.mul_zero]
  rw [mul_comm, NNReal.mul_le_iff_le_inv h, mul_comm]
  exact (le_factor _ _ hg _).trans hf

theorem factor_le_of_suitable (f : UniversalMap m n) [hf : f.Suitable c₁ c₂] [h : Fact (0 < c₁)] :
    f.factor ≤ c₂ * c₁⁻¹ := by
  refine' Finset.sup_le _
  rintro ⟨g, i⟩ hg
  replace hg : g ∈ support f := (Finset.mem_product.1 hg).1
  rw [mul_comm, ← NNReal.mul_le_iff_le_inv h.1.ne', mul_comm]
  exact (hf.out g hg).out i

@[simp]
theorem factor_neg (f : UniversalMap m n) : (-f).factor = f.factor := by
  simp only [factor, support_neg]

theorem factor_add (f₁ f₂ : UniversalMap m n) : factor (f₁ + f₂) ≤ max f₁.factor f₂.factor :=
  by
  refine' Finset.sup_le _
  simp only [Prod.forall, and_true_iff, Finset.mem_univ, le_max_iff]
  intro g i hg
  replace hg := support_add f₁ f₂ (Finset.mem_product.1 hg).1
  -- Porting note: the `DecidableEq` instances on the two sides differ, so we use `convert`
  have hg' : g ∈ support f₁ ∨ g ∈ support f₂ := Finset.mem_union.1 (by convert hg)
  exact hg'.imp (fun h => le_factor _ _ h _) (fun h => le_factor _ _ h _)

theorem factor_sub (f₁ f₂ : UniversalMap m n) : factor (f₁ - f₂) ≤ max f₁.factor f₂.factor := by
  simpa only [factor_neg, sub_eq_add_neg] using factor_add f₁ (-f₂)

end UniversalMap

namespace BasicUniversalMap

open FreeAbelianGroup

theorem suitable_of_suitable_of (f : BasicUniversalMap m n) (c₁ c₂ : ℝ≥0)
    [h : UniversalMap.Suitable c₁ c₂ (of f)] : f.Suitable c₁ c₂ :=
  h.out f <| by simp only [Finset.mem_singleton, support_of]

end BasicUniversalMap

namespace UniversalMap

open FreeAbelianGroup

instance suitable_of (f : BasicUniversalMap m n) (c₁ c₂ : ℝ≥0) [f.Suitable c₁ c₂] :
    Suitable c₁ c₂ (of f) := by
  refine ⟨fun g hg => ?_⟩
  rw [support_of, Finset.mem_singleton] at hg 
  rwa [hg]

@[simp]
theorem suitable_of_iff (f : BasicUniversalMap m n) (c₁ c₂ : ℝ≥0) :
    Suitable c₁ c₂ (of f) ↔ f.Suitable c₁ c₂ :=
  ⟨by intro h; apply BasicUniversalMap.suitable_of_suitable_of, by intro h; infer_instance⟩

instance suitable_zero : (0 : UniversalMap m n).Suitable c₁ c₂ :=
  (suitable_freePredicate c₁ c₂).zero

instance suitable_zero_left (f : UniversalMap m n) (c : ℝ≥0) : f.Suitable 0 c :=
  ⟨fun g _ => by infer_instance⟩

instance suitable_neg (f : UniversalMap m n) (c₁ c₂ : ℝ≥0) [h : f.Suitable c₁ c₂] :
    Suitable c₁ c₂ (-f) :=
  (suitable_freePredicate c₁ c₂).neg h

@[simp]
theorem suitable_neg_iff (f : UniversalMap m n) (c₁ c₂ : ℝ≥0) :
    Suitable c₁ c₂ (-f) ↔ f.Suitable c₁ c₂ :=
  (suitable_freePredicate c₁ c₂).neg_iff

instance suitable_add {f g : UniversalMap m n} {c₁ c₂ : ℝ≥0} [hf : f.Suitable c₁ c₂]
    [hg : g.Suitable c₁ c₂] : Suitable c₁ c₂ (f + g) :=
  (suitable_freePredicate c₁ c₂).add hf hg

instance suitable_sum {ι : Type _} (s : Finset ι) (f : ι → UniversalMap m n) {c₁ c₂ : ℝ≥0}
    [hf : ∀ i, (f i).Suitable c₁ c₂] : (∑ i in s, f i).Suitable c₁ c₂ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    infer_instance
  | @insert i s his IH =>
    simp only [Finset.sum_insert his]
    infer_instance

instance suitable_sub {f g : UniversalMap m n} {c₁ c₂ : ℝ≥0} [hf : f.Suitable c₁ c₂]
    [hg : g.Suitable c₁ c₂] : Suitable c₁ c₂ (f - g) := by rw [sub_eq_add_neg] <;> infer_instance

theorem suitable_smul_iff (k : ℤ) (hk : k ≠ 0) (f : UniversalMap m n) (c₁ c₂ : ℝ≥0) :
    Suitable c₁ c₂ (k • f) ↔ f.Suitable c₁ c₂ :=
  (suitable_freePredicate c₁ c₂).smul_iff k hk

instance suitable_hMul_left (f : UniversalMap m n) [h : f.Suitable c₁ c₂] :
    f.Suitable (c * c₁) (c * c₂) :=
  ⟨fun g hg => @BasicUniversalMap.suitable_hMul_left _ _ _ _ _ _ (h.out g hg)⟩

instance suitable_hMul_right (f : UniversalMap m n) [h : f.Suitable c₁ c₂] :
    f.Suitable (c₁ * c) (c₂ * c) := by
  rw [mul_comm _ c, mul_comm _ c]
  exact UniversalMap.suitable_hMul_left _ _ _ _

instance suitable_hMul_left_one_le (f : UniversalMap m n) [h : f.Suitable c₁ c₂] [Fact (1 ≤ c)] :
    f.Suitable c₁ (c * c₂) :=
  h.le _ _ _ _ le_rfl <| Fact.out

instance suitable_hMul_right_one_le (f : UniversalMap m n) [h : f.Suitable c₁ c₂] [Fact (1 ≤ c)] :
    f.Suitable c₁ (c₂ * c) :=
  h.le _ _ _ _ le_rfl <| Fact.out

instance suitable_hMul_left_le_one (f : UniversalMap m n) [h : f.Suitable c₁ c₂] [Fact (c ≤ 1)] :
    f.Suitable (c * c₁) c₂ :=
  h.le _ _ _ _ Fact.out le_rfl

instance suitable_hMul_right_le_one (f : UniversalMap m n) [h : f.Suitable c₁ c₂] [Fact (c ≤ 1)] :
    f.Suitable (c₁ * c) c₂ :=
  h.le _ _ _ _ Fact.out le_rfl

instance suitable_id : (id n).Suitable c c :=
  ⟨fun g hg => by
    simp only [id, Finset.mem_singleton, support_of] at hg
    subst hg
    infer_instance⟩

-- this cannot be an instance, because c₂ cannot be inferred
theorem Suitable.comp {g : UniversalMap m n} {f : UniversalMap l m} {c₁ : ℝ≥0} (c₂ : ℝ≥0) {c₃ : ℝ≥0}
    [hg : g.Suitable c₂ c₃] [hf : f.Suitable c₁ c₂] : (comp g f).Suitable c₁ c₃ :=
  by
  refine
    FreeAbelianGroup.induction_on_freePredicate
      (P := fun g => Suitable c₁ c₃ (UniversalMap.comp g f))
      (Suitable c₂ c₃) (suitable_freePredicate c₂ c₃) g hg ?_ ?_ ?_ ?_
  · simpa only [Pi.zero_apply, AddMonoidHom.zero_apply, AddMonoidHom.map_zero] using
      BreenDeligne.UniversalMap.suitable_zero _ _
  · intro g hg
    refine
      FreeAbelianGroup.induction_on_freePredicate (P := fun f => Suitable c₁ c₃ (UniversalMap.comp (of g) f))
        (Suitable c₁ c₂) (suitable_freePredicate c₁ c₂) f hf ?_ ?_ ?_ ?_
    · simp only [AddMonoidHom.map_zero]
      infer_instance
    · intro f hf
      rw [comp_of]
      rw [suitable_of_iff] at hf hg ⊢
      exact BreenDeligne.BasicUniversalMap.suitable_comp c₂
    · intro g hg H
      simpa only [AddMonoidHom.map_neg, suitable_neg_iff]
    · intro g₁ g₂ hg₁ hg₂ H₁ H₂
      simp only [AddMonoidHom.map_add]
      infer_instance
  · intro f hf H
    simpa only [Pi.neg_apply, AddMonoidHom.map_neg, suitable_neg_iff, AddMonoidHom.neg_apply]
  · intro f₁ f₂ hf₁ hf₂ H₁ H₂
    simp only [AddMonoidHom.add_apply, AddMonoidHom.map_add, Pi.add_apply]
    infer_instance

-- Porting note: `N⁻¹` needs the explicit cast `(N : ℝ≥0)⁻¹` (Lean 3 elaborated it as `(↑N)⁻¹`)
instance sum_suitable (c : ℝ≥0) (n N : ℕ) : (sum n N).Suitable (c * (N : ℝ≥0)⁻¹) c :=
  by
  by_cases hN : N = 0
  · subst N; simp only [Nat.cast_zero, inv_zero, MulZeroClass.mul_zero]; infer_instance
  refine' @UniversalMap.suitable_of _ _ _ _ _ (_root_.id _)
  have key : (∑ i : Fin N, c * (N : ℝ≥0)⁻¹) = c := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_left_comm, mul_inv_cancel, mul_one]
    exact_mod_cast hN
  -- Porting note: the Lean 3 `conv { congr, skip, skip, rw this }` is replaced by `rwa ... at`
  have := (inferInstance : BasicUniversalMap.Suitable (∑ i : Fin N, BasicUniversalMap.proj n i)
    (c * (N : ℝ≥0)⁻¹) (∑ i : Fin N, c * (N : ℝ≥0)⁻¹))
  rwa [key] at this

instance sum_two_suitable (c : ℝ≥0) (n : ℕ) : (sum n 2).Suitable (c * (2 : ℝ≥0)⁻¹) c := by
  convert UniversalMap.sum_suitable c n 2

instance proj_suitable (c : ℝ≥0) (n N : ℕ) : (proj n N).Suitable c c :=
  UniversalMap.suitable_sum _ _

instance hMul_suitable (f : UniversalMap m n) [h : f.Suitable c₁ c₂] (N : ℕ) [hN : Fact (0 < N)] :
    (mul N f).Suitable c₁ c₂ := by
  refine ⟨fun g hg => ?_⟩
  rw [UniversalMap.mem_support_hMul N hN.out] at hg 
  rcases hg with ⟨g, hg, rfl⟩
  haveI := UniversalMap.suitable_of_mem_support f c₁ c₂ g hg
  infer_instance

end UniversalMap

namespace Data

/-- A sequence of nonnegative real numbers `κ 0`, `κ 1`, ...
is *suitable* with respect to a Breen--Deligne data `BD`,
if for all `i : ℕ`, the constants `κ (i+1)` and `κ i` are
suitable with respect to the universal map `BD.d (i+1) i`.

This definition ensures that we get a well-defined complex
of normed groups `CLCFP V r' (κ i) (BD.rank i)`,
induced by the maps `BD.d (i+1) i`. -/
class Suitable (BD : Data) (κ : ℕ → ℝ≥0) : Prop where
  universal_suitable : ∀ i j, (BD.d i j).Suitable (κ i) (κ j)

attribute [instance] Suitable.universal_suitable

variable (BD : Data) (κ : ℕ → ℝ≥0) (i j j' : ℕ)

theorem Suitable.ofBasic (H : ∀ i, (BD.d (i + 1) i).Suitable (κ (i + 1)) (κ i)) : BD.Suitable κ :=
  ⟨fun j i => by
    by_cases hij : i + 1 = j
    · subst j; exact H i
    · rw [BD.shape _ _ hij]; infer_instance⟩

instance comp_suitable [BD.Suitable κ] :
    (UniversalMap.comp (BD.d j i) (BD.d j' j)).Suitable (κ j') (κ i) :=
  UniversalMap.Suitable.comp (κ j)

instance suitableMulLeft [BD.Suitable κ] (c : ℝ≥0) : BD.Suitable fun i => c * κ i :=
  ⟨fun i j => by infer_instance⟩

instance suitableMulRight [BD.Suitable κ] (c : ℝ≥0) : BD.Suitable fun i => κ i * c :=
  ⟨fun i j => by infer_instance⟩

instance suitableRescaleConstants [BD.Suitable κ] (N : ℝ≥0) : BD.Suitable (rescaleConstants κ N) :=
  Data.suitableMulRight _ _ _

instance mulObjSuitable [BD.Suitable κ] (N : ℕ) [Fact (0 < N)] : ((mul N).obj BD).Suitable κ :=
  by
  constructor
  intro i j
  dsimp [mul_obj_d]
  infer_instance

-- Porting note: explicit cast `(N : ℝ≥0)⁻¹`, as in Lean 3 (`(↑N)⁻¹`)
instance sum_suitable (i N : ℕ) (N' : ℝ≥0) [hN' : Fact (N'⁻¹ ≤ (N : ℝ≥0)⁻¹)] :
    UniversalMap.Suitable (rescaleConstants κ N' i) (κ i) ((BD.sum N).f i) :=
  (UniversalMap.sum_suitable _ _ _).le _ _ _ _ (mul_le_mul' le_rfl hN'.1) le_rfl

instance proj_suitable_strict (i N : ℕ) : UniversalMap.Suitable c c ((BD.proj N).f i) :=
  UniversalMap.proj_suitable _ _ _

instance proj_suitable (i N : ℕ) (N' : ℝ≥0) [Fact (N'⁻¹ ≤ 1)] :
    UniversalMap.Suitable (rescaleConstants κ N' i) (κ i) ((BD.proj N).f i) :=
  by
  refine' (UniversalMap.proj_suitable _ _ _).le _ _ _ _ _ le_rfl
  dsimp [rescaleConstants]
  apply Fact.out

instance homPow'_suitable_strict (f : (mul 2).obj BD ⟶ BD) (i : ℕ)
    [UniversalMap.Suitable c c (f.f i)] : ∀ N, ((homPow' f N).f i).Suitable c c
  | 0 => by dsimp [BreenDeligne.Data.homPow']; exact UniversalMap.suitable_id _
  | N + 1 => by
    dsimp [BreenDeligne.Data.homPow']
    refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ c _ _ (id _)
    refine' @UniversalMap.hMul_suitable _ _ _ _ _ (id _) _ ⟨two_pos⟩
    -- Porting note: `apply_assumption` replaced by the explicit recursive call
    apply homPow'_suitable_strict

instance homPow'_sum_suitable (i N : ℕ) :
    ((Data.homPow' (BD.sum 2) N).f i).Suitable (c * (2 ^ N)⁻¹) c :=
  by
  induction' N with N ih
  · simp only [BreenDeligne.Data.homPow', rescaleConstants, pow_zero, inv_one, mul_one]
    exact UniversalMap.suitable_id _
  simp only [BreenDeligne.Data.homPow', rescaleConstants, pow_succ, mul_inv] at ih ⊢; skip
  refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ (c * 2⁻¹) _ (id _) (id _)
  · apply UniversalMap.sum_two_suitable
  · rw [← mul_assoc, mul_right_comm]
    haveI : Fact (0 < 2) := ⟨two_pos⟩
    apply UniversalMap.hMul_suitable

end Data

namespace UniversalMap

/-- A universal map `f` satisfies `very_suitable r r' c₁ c₂` if it satisfies a technical predicate
that is useful when evaluating `f` on a special type of semi-normed groups,
namely those considered in the system of complexes occuring in `first_target`.

In this case, we have the naive evaluation of `f`, whose norm is bounded by `N = f.bound`,
but we can compose this sufficiently often with a restriction map whose norm is stricly `< 1`.

This predicate records the conditions that make sure that the resulting composition
is norm-nonincreasing: In addition to `f` being `suitable c₁ κ` we require
that `κ ≤ c₂` leaves enough room to apply the restriction map `b` times,
where `b` satisfies `r ^ b * N ≤ 1` and `κ ≤ r' ^ b * c₂`. -/
-- Porting note: in Lean 4 `attribute [class]` is not allowed on a `def`, so `VerySuitable` is
-- declared as a class with a single field `out` (the original body).
class VerySuitable (f : UniversalMap m n) (r r' : outParam ℝ≥0) (c₁ c₂ : ℝ≥0) : Prop where
  out : ∃ (N b : ℕ) (κ : ℝ≥0), f.BoundBy N ∧ f.Suitable c₁ κ ∧ r ^ b * N ≤ 1 ∧ κ ≤ r' ^ b * c₂

namespace VerySuitable

variable (f : UniversalMap m n)

instance (priority := 100) suitable [hr' : Fact (r' ≤ 1)] [hf : f.VerySuitable r r' c₁ c₂] :
    f.Suitable c₁ c₂ := by
  rcases hf.out with ⟨N, b, κ, hN, hf, hr, H⟩
  exact hf.le _ _ _ _ le_rfl (H.trans <| Fact.out)

instance hMul_left (f : UniversalMap m n) [h : f.VerySuitable r r' c₁ c₂] :
    f.VerySuitable r r' (c * c₁) (c * c₂) :=
  by
  rcases h.out with ⟨N, b, κ, hN, hf, hr, H⟩
  refine' ⟨⟨N, b, c * κ, hN, inferInstance, hr, _⟩⟩
  rw [mul_left_comm]
  exact mul_le_mul' le_rfl H

instance hMul_right (f : UniversalMap m n) [h : f.VerySuitable r r' c₁ c₂] :
    f.VerySuitable r r' (c₁ * c) (c₂ * c) := by
  rw [mul_comm _ c, mul_comm _ c]
  apply UniversalMap.VerySuitable.hMul_left

theorem zero : (0 : UniversalMap m n).VerySuitable r r' c₁ c₂ :=
  by
  refine' ⟨⟨0, 0, c₂, zero_boundBy 0, inferInstance, _, _⟩⟩
  · simp only [Nat.cast_zero, zero_le', MulZeroClass.mul_zero]
  · simp only [one_mul, pow_zero, le_refl]

end VerySuitable

end UniversalMap

namespace Data

/-- A sequence of constants `κ : ℕ → ℝ≥0` is `very_suitable` for some Breen--Deligne data `BD`
if every pair of constants is `very_suitable` for the corresponding differential in `BD`. -/
class VerySuitable (BD : Data) (r r' : outParam ℝ≥0) (κ : ℕ → ℝ≥0) : Prop where
  universal_verySuitable : ∀ i j, (BD.d i j).VerySuitable r r' (κ i) (κ j)
  -- Porting note: field renamed from mathport's `Pos` to `pos`, as in Lean 3
  pos : ∀ i, 0 < κ i

theorem pos (BD : Data) {r r' : ℝ≥0} (κ : ℕ → ℝ≥0) [BD.VerySuitable r r' κ] (i : ℕ) : 0 < κ i :=
  VerySuitable.pos BD i

attribute [instance] VerySuitable.universal_verySuitable

namespace VerySuitable

variable (BD : Data) (κ : ℕ → ℝ≥0)

instance (priority := 100) suitable [hr' : Fact (r' ≤ 1)] [h : BD.VerySuitable r r' κ] :
    BD.Suitable κ where universal_suitable i j := by infer_instance

theorem ofSucc (h1 : ∀ i, UniversalMap.VerySuitable (BD.d (i + 1) i) r r' (κ (i + 1)) (κ i))
    (h2 : ∀ i, 0 < κ i) : BD.VerySuitable r r' κ :=
  { universal_verySuitable := by
      intro i j
      by_cases hij : i = j + 1
      · rw [hij]; exact h1 _
      · rw [BD.shape]; swap; exact Ne.symm hij
        exact UniversalMap.VerySuitable.zero r r' (κ i) (κ j)
    pos := h2 }

end VerySuitable

end Data

end BreenDeligne

