import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Topology.Order
import Mathlib.Topology.Separation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Irreducible
import Mathlib.Data.Real.NNReal

#align_import Lbar.bounded

/-!

# \overline{\mathcal{M}}_r(S)_{\leq c}

Throughout, `S` is finite (not profinite).

`ℳ-bar_{r'}(S)_{≤c}` is the filtration on `ℳ-bar_{r'}(S)` by profinite subsets described
at the beginning of section 9 of `analytic.pdf`. It's defined not as a subset
of `ℳ-bar_{r'}(S)` but as an independent type. It's a projective limit of
types `Lbar_bdd r' S c M` which have an additional hypothesis that the power
series involved are actually polynomials of degree at most `M`.

## Main definitions

- `Lbar_bdd r' S c M`: the subset of `S → Tℤ[[T]]/(T^{M+1})` consisting of
  elements `F_s = ∑_{n=1}^M a_{n,s} T^n` such that `∑_{s,n} |a_{n,s}| (r')^n ≤ c`.
- `Lbar_bdd.limit r' S c`: the projective limit of `Lbar_bdd r' S c M`, as a subtype
  of the product.

-/


noncomputable section

open scoped BigOperators Classical NNReal

open Set

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
/-- `Lbar_bdd r' S c M` is the subset of `S → Tℤ[[T]]/(T^{M+1})` consisting of elements
`F_s = ∑_{n=1}^M a_{n,s} T^n` such that `∑_{s,n} |a_{n,s}| r^n ≤ c`.
This is an auxiliary object used to define the profinite topology on `Lbar r' S`. -/
structure LbarBdd (r : ℝ≥0) (S : FintypeCat) (c : ℝ≥0) (M : ℕ) where
  toFun : S → Fin (M + 1) → ℤ
  coeff_zero' : ∀ s, toFun s 0 = 0
  sum_le' : ∑ s, ∑ i : Fin (M + 1), ↑(toFun s i).natAbs * r ^ (i : ℕ) ≤ c

namespace LbarBdd

variable {r' : ℝ≥0} {S : FintypeCat} {c c₁ c₂ : ℝ≥0} {M : ℕ}

instance hasCoeToFun : CoeFun (LbarBdd r' S c M) fun _ => S → Fin (M + 1) → ℤ :=
  ⟨LbarBdd.toFun⟩

@[simp]
theorem coe_mk (x h₁ h₂) : ((⟨x, h₁, h₂⟩ : LbarBdd r' S c M) : S → Fin (M + 1) → ℤ) = x :=
  rfl

@[simp]
protected theorem coeff_zero (x : LbarBdd r' S c M) (s : S) : x s 0 = 0 :=
  x.coeff_zero' s

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
protected theorem sum_le (x : LbarBdd r' S c M) : ∑ s, ∑ i : Fin (M + 1), ↑(x s i).natAbs * r' ^ (i : ℕ) ≤ c :=
  x.sum_le'

/-- The obvious map from `Lbar_bdd r' S c₁ M` to `Lbar_bdd r' S c₂ M`, for `c₁ ≤ c₂`. -/
protected def castLe [hc : Fact (c₁ ≤ c₂)] (x : LbarBdd r' S c₁ M) : LbarBdd r' S c₂ M :=
  ⟨x.1, x.coeff_zero, x.sum_le.trans hc.out⟩

@[ext]
theorem ext (x y : LbarBdd r' S c M) (h : (⇑x : S → Fin (M + 1) → ℤ) = y) : x = y := by
  cases x
  cases y
  congr

instance : Zero (LbarBdd r' S c M)
    where zero :=
    { toFun := 0
      coeff_zero' := fun s => rfl
      sum_le' := by
        simp only [MulZeroClass.zero_mul, Pi.zero_apply, Finset.sum_const_zero, Nat.cast_zero,
          zero_le', Int.natAbs_zero] }

instance : Inhabited (LbarBdd r' S c M) :=
  ⟨0⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
theorem coeff_bound [h0r : Fact (0 < r')] (F : S → Fin (M + 1) → ℤ)
    (hF : ∑ s, ∑ i : Fin (M + 1), ↑(F s i).natAbs * r' ^ (i : ℕ) ≤ c) (n : Fin (M + 1)) (s : S) :
    ↑(F s n).natAbs ≤ c / min (r' ^ M) 1 :=
  by
  rw [div_eq_mul_inv]
  apply le_mul_inv_of_mul_le (lt_min (pow_pos h0r.out _) zero_lt_one).ne.symm
  calc
    ↑(F s n).natAbs * min (r' ^ M) 1 ≤ ↑(F s n).natAbs * r' ^ (n : ℕ) := ?_
    -- see below for proof
    _ ≤ ∑ i : Fin (M + 1), ↑(F s i).natAbs * r' ^ (i : ℕ) :=
      (Finset.single_le_sum (f := fun i : Fin (M + 1) => (↑(F s i).natAbs * r' ^ (i : ℕ) : ℝ≥0))
        (fun (i : Fin (M + 1)) _ => zero_le _) (Finset.mem_univ n))
    _ ≤ ∑ s, ∑ i : Fin (M + 1), ↑(F s i).natAbs * r' ^ (i : ℕ) :=
      by
      refine' Finset.single_le_sum
        (f := fun s => ∑ i : Fin (M + 1), (↑(F s i).natAbs * r' ^ (i : ℕ) : ℝ≥0))
        (fun _ _ => _) (Finset.mem_univ s)
      exact Finset.sum_nonneg fun _ _ => zero_le _
    _ ≤ c := hF
  refine' mul_le_mul_of_nonneg_left _ (zero_le _)
  cases' le_or_lt r' 1 with hr1 hr1
  · refine' le_trans (min_le_left _ _) _
    exact pow_le_pow_of_le_one h0r.out.le hr1 (Nat.lt_add_one_iff.1 n.2)
  · exact le_trans (min_le_right _ _) (one_le_pow_of_one_le (le_of_lt hr1) _)

/-- An auxiliary function used to prove finiteness of `Lbar_bdd r' S c M`. -/
private def tempMap [Fact (0 < r')] (F : LbarBdd r' S c M) (n : Fin (M + 1)) (s : S) :
    Icc ⌈(-(c / min (r' ^ M) 1) : ℝ)⌉ ⌊(c / min (r' ^ M) 1 : ℝ)⌋ :=
  have h : (-(c / min (r' ^ M) 1) : ℝ) ≤ F s n ∧ (F s n : ℝ) ≤ (c / min (r' ^ M) 1 : ℝ) :=
    by
    rw [← abs_le, ← Real.coe_nnabs, ← Real.cast_natAbs_eq_nnabs_cast]
    exact_mod_cast coeff_bound F F.sum_le n s
  ⟨F s n, Int.ceil_le.2 h.1, Int.le_floor.2 h.2⟩

instance [Fact (0 < r')] : Fintype (LbarBdd r' S c M) :=
  Fintype.ofInjective tempMap
    (by
      rintro ⟨f1, hf1, hf1'⟩ ⟨f2, hf2, hf2'⟩ h
      ext s n
      change (tempMap ⟨f1, hf1, hf1'⟩ n s).1 = (tempMap ⟨f2, hf2, hf2'⟩ n s).1
      rw [h])

/-- The transition map from `Lbar_bdd r' S c N` to `Lbar_bdd r' S c M`, given `M ≤ N`. -/
def transition (r' : ℝ≥0) {S : FintypeCat} {c : ℝ≥0} {M N : ℕ} (h : M ≤ N) (x : LbarBdd r' S c N) :
    LbarBdd r' S c M
    where
  toFun s i := x s (Fin.castLEEmb (add_le_add_right h 1) i)
  coeff_zero' s := x.coeff_zero _
  sum_le' := by
    refine' le_trans _ x.sum_le
    apply Finset.sum_le_sum
    intro s hs
    let I :=
      Finset.map (Fin.castLEEmb (add_le_add_right h 1)).toEmbedding
        (Finset.univ : Finset (Fin (M + 1)))
    refine' le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) _)
    · rw [Finset.sum_map]
      apply le_of_eq
      congr
    · intros; exact Subtype.property (_ : ℝ≥0)

theorem transition_eq {r' : ℝ≥0} {S : FintypeCat} {c : ℝ≥0} {M N : ℕ} (h : M ≤ N)
    (F : LbarBdd r' S c N) (s : S) (i : Fin (M + 1)) :
    (transition r' h F).1 s i = F.1 s (Fin.castLEEmb (add_le_add_right h 1) i) :=
  rfl

theorem transition_transition {r' : ℝ≥0} {S : FintypeCat} {c : ℝ≥0} {M N K : ℕ} (h : M ≤ N)
    (hh : N ≤ K) (x : LbarBdd r' S c K) :
    transition r' h (transition r' hh x) = transition r' (le_trans h hh) x :=
  rfl

theorem transition_castLe {N : ℕ} (h : M ≤ N) [hc : Fact (c₁ ≤ c₂)] (x : LbarBdd r' S c₁ N) :
    transition r' h (LbarBdd.castLe x : LbarBdd r' S c₂ N) = LbarBdd.castLe (transition r' h x) :=
  rfl

/-- The limit of `Lbar_bdd r' S c M` along the `transition` maps as `M` increases. -/
abbrev Limit (r' S c) :=
  { F : ∀ M : ℕ, LbarBdd r' S c M // ∀ (M N : ℕ) (h : M ≤ N), transition r' h (F N) = F M }

/-- The obvious embedding `Lbar_bdd.limit r' S c`
into the product of `Lbar_bdd r' S c M` as `M` varies. -/
def embAux : Limit r' S c → ∀ M : ℕ, LbarBdd r' S c M :=
  Subtype.val

section TopologicalStructure

instance : TopologicalSpace (LbarBdd r' S c M) :=
  ⊥

instance : DiscreteTopology (LbarBdd r' S c M) :=
  ⟨rfl⟩

-- sanity check
example : T2Space (Limit r' S c) := by infer_instance

example : TotallyDisconnectedSpace (Limit r' S c) := by infer_instance

example [Fact (0 < r')] : CompactSpace (LbarBdd r' S c M) := by infer_instance

theorem emb (r' S c) : ClosedEmbedding (@embAux r' S c) :=
  { induced := rfl
    inj := Subtype.coe_injective
    closed_range :=
      by
      have :
        range LbarBdd.embAux =
          ⋂ x : { y : ℕ × ℕ // y.1 ≤ y.2 },
            {F : ∀ M, LbarBdd r' S c M | transition r' x.2 (F x.val.2) = F x.val.1} :=
        by
        ext
        simp only [LbarBdd.embAux, Prod.forall, mem_iInter, Set.mem_setOf_eq, Subtype.range_coe_subtype,
          Subtype.forall]
      rw [this]
      apply isClosed_iInter
      rintro ⟨⟨m, n⟩, h0 : m ≤ n⟩
      exact isClosed_eq
        ((continuous_of_discreteTopology (f := transition r' h0)).comp (continuous_apply n))
        (continuous_apply m) }

instance [Fact (0 < r')] : CompactSpace (Limit r' S c) :=
  by
  exact (emb r' S c).compactSpace

/-- The projection from `Lbar_bdd.limit r' S c M` to `Lbar_bdd r' S c M`.  -/
def proj (M : ℕ) : LbarBdd.Limit r' S c → LbarBdd r' S c M := fun F => F.1 M

theorem continuous_iff {α : Type _} [TopologicalSpace α] (f : α → LbarBdd.Limit r' S c) :
    Continuous f ↔ ∀ M : ℕ, Continuous (proj M ∘ f) :=
  by
  constructor
  · intro hf M
    exact Continuous.comp ((continuous_apply _).comp continuous_subtype_val) hf
  · intro h
    rw [Embedding.continuous_iff (emb r' S c).toEmbedding]
    exact continuous_pi h

end TopologicalStructure

section Addition

/-- The addition on `Lbar_bdd r' S c M`.
It takes a term of type `Lbar_bdd r' S c₁ M` and a term of type `Lbar_bdd r' S c₂ M`
and produces a term of type `Lbar_bdd r' S (c₁ + c₂) M`. -/
def add (F : LbarBdd r' S c₁ M) (G : LbarBdd r' S c₂ M) : LbarBdd r' S (c₁ + c₂) M
    where
  toFun := F + G
  coeff_zero' s := by simp
  sum_le' := by
    refine' le_trans _ (add_le_add F.sum_le G.sum_le)
    rw [← Finset.sum_add_distrib]
    refine' Finset.sum_le_sum _
    rintro s -
    rw [← Finset.sum_add_distrib]
    refine' Finset.sum_le_sum _
    rintro i -
    rw [← add_mul]
    apply mul_le_mul_right'
    norm_cast
    apply Int.natAbs_add_le

/-- Negation on `Lbar_bdd r' S c M` -/
def neg (F : LbarBdd r' S c M) : LbarBdd r' S c M
    where
  toFun := -F
  coeff_zero' s := by simp
  sum_le' := by simp only [abs_neg, Pi.neg_apply, Int.natAbs_neg]; exact F.sum_le

end Addition

section Map

-- To avoid defeq nonsense, we need to use ⟨S⟩ as opposed to S.
-- TODO: Use `Fintype` everywhere?!
/-- TODO -/
def map {S T : Type _} [Fintype S] [Fintype T] (f : S → T) :
    LbarBdd r' (FintypeCat.of S) c M → LbarBdd r' (FintypeCat.of T) c M := fun F =>
  { toFun := fun t i => ∑ s in Finset.univ.filter fun s' => f s' = t, F s i
    coeff_zero' := by simp
    sum_le' :=
      calc
        ∑ t : T, ∑ i : Fin (M + 1),
              ↑(∑ s : S in Finset.univ.filter fun s' => f s' = t, F s i).natAbs * r' ^ (i : ℕ) ≤
            ∑ t : T, ∑ i : Fin (M + 1),
              ∑ s in Finset.univ.filter fun s' => f s' = t, ↑(F s i).natAbs * r' ^ (i : ℕ) :=
          by
          apply Finset.sum_le_sum
          rintro t -
          apply Finset.sum_le_sum
          rintro i -
          rw [← Finset.sum_mul]
          refine' mul_le_mul _ (le_refl _) zero_le' zero_le'
          rw [← Nat.cast_sum]
          rw [Nat.cast_le]
          apply nat_abs_sum_le
        _ ≤ ∑ s : S, ∑ i : Fin (M + 1), ↑(F s i).natAbs * r' ^ (i : ℕ) :=
          by
          rw [Finset.sum_comm]
          conv_rhs => rw [Finset.sum_comm]
          apply Finset.sum_le_sum
          rintro i -
          rw [← Finset.sum_biUnion]
          · apply Finset.sum_le_sum_of_subset
            intro _ _; simp
          · rintro t1 - t2 - h
            -- Porting note: `Set.PairwiseDisjoint` unfolds differently in Lean 4
            rw [Function.onFun, Finset.disjoint_left]
            intro s hs1 hs2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs1 hs2
            exact h (hs1.symm.trans hs2)
        _ ≤ _ := F.sum_le }

end Map

end LbarBdd



