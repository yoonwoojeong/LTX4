import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.ForMathlib.Profinite.Product
import Mathlib.Data.Fintype.Card
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Functor.Currying
import LiquidTensorExperiment.Facts.Default
import LiquidTensorExperiment.HacksAndTricks.TypePow
import LiquidTensorExperiment.Lbar.Basic
import LiquidTensorExperiment.PseudoNormedGroup.ProfinitelyFiltered

#align_import Lbar.Lbar_le

/-!
# $\overline{\mathcal{M}}_{r'}(S)_{≤ c}$

In this file we put a profinite topology on the subspace
`Lbar_le r' S c` of `Lbar r' S` consisting of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ⟦T⟧` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c`.
-/


universe u

noncomputable section

open scoped BigOperators NNReal

open PseudoNormedGroup CategoryTheory CategoryTheory.Limits

attribute [local instance] typePow

variable {r' : ℝ≥0} {S : Type u} [Fintype S] {c c₁ c₂ c₃ : ℝ≥0}

/-- `Lbar_le r' S c` is the set of power series
`F_s = ∑ a_{n,s}T^n ∈ Tℤ[[T]]` such that `∑_{n,s} |a_{n,s}|r'^n ≤ c` -/
def LbarLe (r' : ℝ≥0) (S : Type u) [Fintype S] (c : ℝ≥0) :=
  { F : Lbar r' S // F ∈ filtration (Lbar r' S) c }

namespace LbarLe

instance hasCoe : Coe (LbarLe r' S c) (Lbar r' S) :=
  ⟨Subtype.val⟩

instance hasCoeToFun : CoeFun (LbarLe r' S c) fun F => S → ℕ → ℤ :=
  ⟨fun F => F.1⟩

@[simp]
theorem coe_coe_to_fun (F : LbarLe r' S c) : ⇑(F : Lbar r' S) = F :=
  rfl

@[simp]
theorem coe_mk (x h) : ((⟨x, h⟩ : LbarLe r' S c) : S → ℕ → ℤ) = x :=
  rfl

@[simp]
protected theorem coeff_zero (x : LbarLe r' S c) (s : S) : x s 0 = 0 :=
  x.1.coeff_zero' s

protected theorem summable (x : LbarLe r' S c) (s : S) :
    Summable fun n => ↑(x s n).natAbs * r' ^ n :=
  x.1.summable' s

protected theorem mem_filtration (x : LbarLe r' S c) : x.1 ∈ filtration (Lbar r' S) c :=
  x.property

/-- The inclusion map `Lbar_le r' S c₁ → Lbar_le r' S c₂` for `c₁ ≤ c₂`. -/
protected def castLe [hc : Fact (c₁ ≤ c₂)] (x : LbarLe r' S c₁) : LbarLe r' S c₂ :=
  ⟨⟨x, x.coeff_zero, x.Summable⟩, filtration_mono hc.out x.mem_filtration⟩

@[simp]
theorem coe_castLe [hc : Fact (c₁ ≤ c₂)] (x : LbarLe r' S c₁) :
    ((x.castLEEmb : LbarLe r' S c₂) : Lbar r' S) = x := by ext; rfl

@[simp]
theorem castLe_apply [hc : Fact (c₁ ≤ c₂)] (x : LbarLe r' S c₁) (s : S) (i : ℕ) :
    (x.castLEEmb : LbarLe r' S c₂) s i = x s i :=
  rfl

theorem injective_castLe [Fact (c₁ ≤ c₂)] :
    Function.Injective (LbarLe.castLe : LbarLe r' S c₁ → LbarLe r' S c₂) := fun x y h =>
  by
  ext s n
  change x.cast_le s n = y.cast_le s n
  rw [h]

@[ext]
theorem ext (x y : LbarLe r' S c) (h : (⇑x : S → ℕ → ℤ) = y) : x = y := by ext : 2; exact h

instance : Zero (LbarLe r' S c) :=
  ⟨⟨0, zero_mem_filtration _⟩⟩

instance : Inhabited (LbarLe r' S c) :=
  ⟨0⟩

end LbarLe

variable (c₃)

/-- The addition on `Lbar_le`.
This addition is not homogeneous, but has type
`(Lbar_le r' S c₁) → (Lbar_le r' S c₂) → (Lbar_le r' S c₃)`
for `c₁ + c₂ ≤ c₃`. -/
def LbarLe.add [h : Fact (c₁ + c₂ ≤ c₃)] (F : LbarLe r' S c₁) (G : LbarLe r' S c₂) :
    LbarLe r' S c₃ :=
  Subtype.mk (F + G) <|
    filtration_mono h.out <| add_mem_filtration F.mem_filtration G.mem_filtration

/-- An uncurried version of addition on `Lbar_le`,
meaning that it takes only 1 input, coming from a product type. -/
def LbarLe.add' [Fact (c₁ + c₂ ≤ c₃)] : LbarLe r' S c₁ × LbarLe r' S c₂ → LbarLe r' S c₃ := fun x =>
  LbarLe.add c₃ x.1 x.2

-- TODO: register this as an instance??
/-- The negation on `Lbar_le`. -/
def LbarLe.neg (F : LbarLe r' S c) : LbarLe r' S c :=
  Subtype.mk (-F) <| neg_mem_filtration F.mem_filtration

namespace LbarLe

/-- The truncation map from Lbar_le to `Lbar_bdd`. -/
@[simps]
def truncate (M : ℕ) (F : LbarLe r' S c) : LbarBdd r' ⟨S⟩ c M
    where
  toFun s n := F s n
  coeff_zero' := by simp
  sum_le' := by
    refine' le_trans _ F.mem_filtration
    apply Finset.sum_le_sum
    rintro (s : S) -
    rw [Fin.sum_univ_eq_sum_range (fun i => ↑(F s i).natAbs * r' ^ i) (M + 1)]
    exact sum_le_tsum _ (fun _ _ => Subtype.property (_ : ℝ≥0)) (F.summable s)

theorem truncate_surjective (M : ℕ) :
    Function.Surjective (truncate M : LbarLe r' S c → LbarBdd r' ⟨S⟩ c M) :=
  by
  intro x
  have aux : _ := _
  let F : LbarLe r' S c :=
    ⟨{  toFun := fun s n => if h : n < M + 1 then x s ⟨n, h⟩ else 0
        summable' := aux .. }, _⟩
  · use F; ext s i; simp only [truncate_to_fun]; dsimp
    rw [dif_pos i.is_lt]; simp only [Fin.eta]
  · intro s; rw [dif_pos (Nat.zero_lt_succ _)]; exact x.coeff_zero s
  · apply le_trans _ x.sum_le
    apply Finset.sum_le_sum
    rintro s -
    rw [← sum_add_tsum_nat_add' (M + 1), tsum_eq_zero, add_zero]
    · rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_le_sum
      rintro i -
      simp only [dif_pos i.is_lt, Fin.eta, Lbar.coe_mk]
    · intro i
      dsimp
      rw [dif_neg, Int.natAbs_zero, Nat.cast_zero, MulZeroClass.zero_mul]
      linarith
    · dsimp; apply aux
  · intro s
    apply @summable_of_ne_finset_zero _ _ _ _ _ (Finset.range (M + 1))
    intro i hi
    rw [Finset.mem_range] at hi 
    simp only [hi, MulZeroClass.zero_mul, dif_neg, not_false_iff, Nat.cast_zero, Int.natAbs_zero]

/-- Injectivity of the map `Lbar_le` to the limit of the `Lbar_bdd`. -/
theorem eq_iff_truncate_eq (x y : LbarLe r' S c) (cond : ∀ M, truncate M x = truncate M y) :
    x = y := by
  ext s n
  change (truncate n x).1 s ⟨n, by linarith⟩ = (truncate n y).1 s ⟨n, _⟩
  rw [cond]

theorem truncate_castLe (M : ℕ) [hc : Fact (c₁ ≤ c₂)] (x : LbarLe r' S c₁) :
    truncate M (LbarLe.castLe x : LbarLe r' S c₂) = LbarBdd.castLe (truncate M x) :=
  rfl

/-- Underlying function of the element of `Lbar_le r' S c` associated to a sequence of
  elements of the truncated Lbars. -/
def mkSeq (T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M) : S → ℕ → ℤ := fun s n => (T n).1 s ⟨n, lt_add_one n⟩

@[simp]
theorem mkSeq_zero {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M} (s : S) : mkSeq T s 0 = 0 :=
  (T 0).coeff_zero s

theorem mkSeq_eq_of_compat {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) {s : S} {n : ℕ} {M : ℕ}
    (hnM : n < M + 1) : mkSeq T s n = (T M).1 s ⟨n, hnM⟩ :=
  by
  have hnM : n ≤ M := nat.lt_succ_iff.mp hnM
  unfold mk_seq
  rw [← compat n M hnM]
  apply LbarBdd.transition_eq

theorem mkSeq_sum_range_eq (T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M)
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) (s : S) (n) :
    ∑ i in Finset.range (n + 1), ↑(mkSeq T s i).natAbs * r' ^ i =
      ∑ i : Fin (n + 1), ↑((T n).1 s i).natAbs * r' ^ (i : ℕ) :=
  by
  rw [← Fin.sum_univ_eq_sum_range]
  congr
  ext ⟨i, hi⟩
  congr
  exact mk_seq_eq_of_compat compat _

theorem mkSeq_summable {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) (s : S) :
    Summable fun n : ℕ => ↑(mkSeq T s n).natAbs * r' ^ n :=
  by
  apply @NNReal.summable_of_sum_range_le _ c
  rintro (_ | n)
  · simp only [Finset.sum_empty, Finset.range_zero, zero_le']
  · rw [mk_seq_sum_range_eq T compat s n]
    refine' le_trans _ (T n).sum_le
    refine' Finset.single_le_sum (fun _ _ => _) (Finset.mem_univ s)
    apply zero_le'

open Filter

theorem mkSeq_tendsto {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) :
    Tendsto (fun n : ℕ => ∑ s : S, ∑ i in Finset.range n, ↑(mkSeq T s i).natAbs * r' ^ i) atTop
      (nhds <| ∑ s : S, ∑' n, ↑(mkSeq T s n).natAbs * r' ^ n) :=
  tendsto_finset_sum _ fun s _ =>
    HasSum.tendsto_sum_nat <| Summable.hasSum <| mkSeq_summable compat s

theorem mkSeq_sum_le {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) :
    ∑ s, ∑' n : ℕ, ↑(mkSeq T s n).natAbs * r' ^ n ≤ c :=
  by
  refine' le_of_tendsto (mk_seq_tendsto compat) (eventually_of_forall _)
  rintro (_ | n)
  · simp only [Finset.sum_empty, Finset.range_zero, Finset.sum_const_zero, zero_le']
  · convert (T n).sum_le
    funext
    rw [mk_seq_sum_range_eq T compat s n]
    rfl

theorem truncate_mkSeq {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) (M : ℕ) :
    truncate M ⟨⟨mkSeq T, mkSeq_zero, mkSeq_summable compat⟩, mkSeq_sum_le compat⟩ = T M :=
  by
  ext s ⟨i, hi⟩
  exact mk_seq_eq_of_compat compat _

/-- `of_compat hT` is the limit of a compatible family `T M : Lbar_bdd r' ⟨S⟩ c M`.
This realizes `Lbar_le` as the profinite limit of the spaces `Lbar_bdd`,
see also `Lbar_le.eqv`. -/
def ofCompat {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) : LbarLe r' S c :=
  ⟨⟨mkSeq T, mkSeq_zero, mkSeq_summable compat⟩, mkSeq_sum_le compat⟩

@[simp]
theorem truncate_ofCompat {T : ∀ M : ℕ, LbarBdd r' ⟨S⟩ c M}
    (compat : ∀ (M N : ℕ) (h : M ≤ N), LbarBdd.transition r' h (T N) = T M) (M : ℕ) :
    truncate M (ofCompat compat) = T M := by
  ext s ⟨i, hi⟩
  exact mk_seq_eq_of_compat compat _

/-- The equivalence (as types) between `Lbar_le r' S c`
and the profinite limit of the spaces `Lbar_bdd r' ⟨S⟩ c M`. -/
def eqv : LbarLe r' S c ≃ LbarBdd.Limit r' ⟨S⟩ c
    where
  toFun F := ⟨fun N => truncate _ F, by intros; rfl⟩
  invFun F := ofCompat F.2
  left_inv x := by ext; rfl
  right_inv := by rintro ⟨x, hx⟩; simp only [truncate_of_compat]

section TopologicalStructure

instance : TopologicalSpace (LbarLe r' S c) :=
  TopologicalSpace.induced eqv (by infer_instance)

theorem isOpen_iff {U : Set (LbarBdd.Limit r' ⟨S⟩ c)} : IsOpen (eqv ⁻¹' U) ↔ IsOpen U :=
  by
  rw [isOpen_induced_iff]
  have := Function.Surjective.preimage_injective (Equiv.surjective (eqv : LbarLe r' S c ≃ _))
  simp only [iff_self_iff, this.eq_iff]
  simp only [exists_eq_right]

/-- The homeomorphism between `Lbar_le r' S c`
and the profinite limit of the spaces `Lbar_bdd r' ⟨S⟩ c M`.

This is `Lbar_le.eqv`, lifted to a homeomorphism by transporting
the topology from the profinite limit to `Lbar_le`. -/
def homeo : LbarLe r' S c ≃ₜ LbarBdd.Limit r' ⟨S⟩ c :=
  {
    eqv with
    continuous_toFun := by
      simp only [Equiv.toFun_as_coe, continuous_def]
      intro U hU
      rwa [is_open_iff]
    continuous_invFun := by
      simp only [Equiv.toFun_as_coe, continuous_def]
      intro U hU
      erw [← eqv.image_eq_preimage, ← is_open_iff]
      rwa [eqv.preimage_image U] }

theorem truncate_eq (M : ℕ) :
    (truncate M : LbarLe r' S c → LbarBdd r' ⟨S⟩ c M) = LbarBdd.proj M ∘ homeo :=
  rfl

instance : T2Space (LbarLe r' S c) :=
  ⟨fun x y h => separated_by_continuous homeo.Continuous fun c => h <| homeo.Injective c⟩

instance [Fact (0 < r')] : CompactSpace (LbarLe r' S c) :=
  by
  constructor
  rw [homeo.embedding.is_compact_iff_is_compact_image]
  simp only [Set.image_univ, Homeomorph.range_coe]
  obtain ⟨h⟩ := (by infer_instance : CompactSpace (LbarBdd.Limit r' ⟨S⟩ c))
  exact h

instance : TotallyDisconnectedSpace (LbarLe r' S c)
    where isTotallyDisconnected_univ := by
    rintro A - hA
    suffices subsing : (homeo '' A).Subsingleton
    · intro x hx y hy; apply_rules [homeo.injective, subsing, Set.mem_image_of_mem]
    obtain ⟨h⟩ := (by infer_instance : TotallyDisconnectedSpace (LbarBdd.Limit r' ⟨S⟩ c))
    exact h _ (by tauto) (IsPreconnected.image hA _ homeo.continuous.continuous_on)

theorem continuous_iff {α : Type _} [TopologicalSpace α] (f : α → LbarLe r' S c) :
    Continuous f ↔ ∀ M, Continuous (truncate M ∘ f) :=
  by
  constructor
  · intro hf M
    rw [truncate_eq, Function.comp.assoc]
    revert M
    rw [← LbarBdd.continuous_iff]
    refine' Continuous.comp homeo.continuous hf
  · intro h
    suffices Continuous (homeo ∘ f) by rwa [homeo.comp_continuous_iff] at this 
    rw [LbarBdd.continuous_iff]
    exact h

theorem continuous_truncate {M} : Continuous (@truncate r' S _ c M) :=
  (continuous_iff id).mp continuous_id _

theorem continuous_add' :
    Continuous (LbarLe.add' (c₁ + c₂) : LbarLe r' S c₁ × LbarLe r' S c₂ → LbarLe r' S (c₁ + c₂)) :=
  by
  rw [continuous_iff]
  intro M
  have :
    (truncate M ∘ fun x : LbarLe r' S c₁ × LbarLe r' S c₂ => LbarLe.add _ x.1 x.2) =
      fun x : LbarLe r' S c₁ × LbarLe r' S c₂ => LbarBdd.add (truncate M x.1) (truncate M x.2) :=
    by ext <;> rfl
  erw [this]
  suffices Continuous fun x : LbarBdd r' ⟨S⟩ c₁ M × LbarBdd r' ⟨S⟩ c₂ M => LbarBdd.add x.1 x.2
    by
    have claim :
      (fun x : LbarLe r' S c₁ × LbarLe r' S c₂ => LbarBdd.add (truncate M x.1) (truncate M x.2)) =
        (fun x : LbarBdd r' ⟨S⟩ c₁ M × LbarBdd r' ⟨S⟩ c₂ M => LbarBdd.add x.1 x.2) ∘
          fun x : LbarLe r' S c₁ × LbarLe r' S c₂ => (truncate M x.1, truncate M x.2) :=
      by ext; rfl
    rw [claim]
    refine' Continuous.comp this _
    refine' Continuous.prod_map continuous_truncate continuous_truncate
  exact continuous_of_discreteTopology

theorem continuous_neg : Continuous (LbarLe.neg : LbarLe r' S c → LbarLe r' S c) :=
  by
  rw [continuous_iff]
  intro M
  change Continuous fun x : LbarLe r' S c => LbarBdd.neg (truncate M x)
  exact Continuous.comp continuous_of_discreteTopology continuous_truncate

end TopologicalStructure

theorem continuous_castLe (r' : ℝ≥0) (S : Type u) [Fintype S] (c₁ c₂ : ℝ≥0) [hc : Fact (c₁ ≤ c₂)] :
    Continuous (@LbarLe.castLe r' S _ c₁ c₂ _) :=
  by
  rw [continuous_iff]
  intro M
  simp only [Function.comp, truncate_cast_le]
  exact continuous_bot.comp continuous_truncate

/-! We now prove some scaffolding lemmas
in order to prove that the action of `T⁻¹` is continuous. -/


theorem continuous_of_normed_group_hom (f : Lbar r' S →+ Lbar r' S)
    (g : LbarLe r' S c₁ → LbarLe r' S c₂) (h : ∀ x, ↑(g x) = f x)
    (H :
      ∀ M, ∃ N, ∀ F : Lbar r' S, (∀ s i, i < N + 1 → F s i = 0) → ∀ s i, i < M + 1 → f F s i = 0) :
    Continuous g := by
  rw [continuous_iff]
  intro M
  rcases H M with ⟨N, hN⟩
  let φ : LbarBdd r' ⟨S⟩ c₁ N → LbarLe r' S c₁ :=
    Classical.choose (truncate_surjective N).HasRightInverse
  have hφ : Function.RightInverse φ (truncate N) :=
    Classical.choose_spec (truncate_surjective N).HasRightInverse
  suffices truncate M ∘ g = truncate M ∘ g ∘ φ ∘ truncate N
    by
    rw [this, ← Function.comp.assoc, ← Function.comp.assoc]
    apply continuous_bot.comp continuous_truncate
  ext1 x
  suffices ∀ s i, i < M + 1 → (g x) s i = (g (φ (truncate N x))) s i by ext s i;
    dsimp [Function.comp]; apply this; exact i.property
  intro s i hi
  rw [← coe_coe_to_fun, h, ← coe_coe_to_fun, h, ← sub_eq_zero]
  show (f x - f (φ (truncate N x))) s i = 0
  rw [← f.map_sub]
  apply hN _ _ _ _ hi
  clear hi i s; intro s i hi
  simp only [Lbar.coe_sub, Pi.sub_apply, sub_eq_zero]
  suffices ∀ s i, (truncate N x) s i = truncate N (φ (truncate N x)) s i by exact this s ⟨i, hi⟩
  intro s i; congr 1
  rw [hφ (truncate N x)]

/-- Construct a map between `Lbar_le r' S c₁` and `Lbar_le r' S c₂`
from a bounded group homomorphism `Lbar r' S → Lbar r' S`.

If `f` satisfies a suitable criterion,
then the constructed map is continuous for the profinite topology;
see `continuous_of_normed_group_hom`. -/
def homOfNormedGroupHom {C : ℝ≥0} (c₁ c₂ : ℝ≥0) [hc : Fact (C * c₁ ≤ c₂)]
    (f : Lbar r' S →+ Lbar r' S) (h : f ∈ filtration (Lbar r' S →+ Lbar r' S) C)
    (F : LbarLe r' S c₁) : LbarLe r' S c₂ :=
  ⟨{  toFun := fun s i => f F s i
      coeff_zero' := Lbar.coeff_zero _
      summable' := Lbar.summable _ }, filtration_mono hc.out (h F.mem_filtration)⟩

theorem continuous_homOfNormedGroupHom {C : ℝ≥0} (c₁ c₂ : ℝ≥0) [hc : Fact (C * c₁ ≤ c₂)]
    (f : Lbar r' S →+ Lbar r' S) (h : f ∈ filtration (Lbar r' S →+ Lbar r' S) C)
    (H :
      ∀ M, ∃ N, ∀ F : Lbar r' S, (∀ s i, i < N + 1 → F s i = 0) → ∀ s i, i < M + 1 → f F s i = 0) :
    Continuous (homOfNormedGroupHom c₁ c₂ f h) :=
  continuous_of_normed_group_hom f _ (fun F => by ext; rfl) H

@[simp]
theorem coe_homOfNormedGroupHom_apply {C : ℝ≥0} (c₁ c₂ : ℝ≥0) [hc : Fact (C * c₁ ≤ c₂)]
    (f : Lbar r' S →+ Lbar r' S) (h : f ∈ filtration (Lbar r' S →+ Lbar r' S) C)
    (F : LbarLe r' S c₁) (s : S) (i : ℕ) : (homOfNormedGroupHom c₁ c₂ f h) F s i = f F s i :=
  rfl

section Tinv

/-!
### The action of T⁻¹
-/


/-- The action of `T⁻¹` as map `Lbar_le r S c₁ → Lbar_le r S c₂`.

This action is induced by the action of `T⁻¹` on power series modulo constants: `ℤ⟦T⟧/ℤ`.
So `T⁻¹` sends `T^(n+1)` to `T^n`, but `T^0 = 0`. -/
def tinv {r : ℝ≥0} {S : Type u} [Fintype S] {c₁ c₂ : ℝ≥0} [Fact (0 < r)] [Fact (r⁻¹ * c₁ ≤ c₂)] :
    LbarLe r S c₁ → LbarLe r S c₂ :=
  homOfNormedGroupHom c₁ c₂ Lbar.tinv Lbar.tinv_mem_filtration

@[simp]
theorem tinv_apply {r : ℝ≥0} {S : Type u} [Fintype S] {c₁ c₂ : ℝ≥0} [Fact (0 < r)]
    [Fact (r⁻¹ * c₁ ≤ c₂)] (F : LbarLe r S c₁) (s : S) (i : ℕ) :
    (tinv F : LbarLe r S c₂) s i = Lbar.tinv (F : Lbar r S) s i :=
  rfl

theorem continuous_tinv (r : ℝ≥0) (S : Type u) [Fintype S] (c₁ c₂ : ℝ≥0) [Fact (0 < r)]
    [Fact (r⁻¹ * c₁ ≤ c₂)] : Continuous (@tinv r S _ c₁ c₂ _ _) :=
  continuous_homOfNormedGroupHom c₁ c₂ _ Lbar.tinv_mem_filtration <|
    by
    intro M
    use M + 1
    rintro F hF s (_ | i) hi
    · simp only [Lbar.tinv, AddMonoidHom.mk'_apply, Lbar.coe_mk, Lbar.tinvAux_zero]
    · simp only [Lbar.tinv, Lbar.tinvAux_succ, AddMonoidHom.mk'_apply, Lbar.coe_mk]
      apply hF
      exact Nat.succ_lt_succ hi

end Tinv

/-

section map

/-- TODO -/
def map {S T : Fintype} (f : S ⟶ T) : Lbar_le r' S c → Lbar_le r' T c := λ F,
⟨(F : Lbar r' S).map f, Lbar.nnnorm_map_le_of_nnnorm_le _ _ F.2⟩

lemma map_truncate {S T : Fintype} (f : S ⟶ T) (F : Lbar_le r' S c) (M : ℕ) :
  ((F.truncate M).map f) = (F.map f).truncate M := rfl

lemma map_continuous {S T : Fintype} (f : S ⟶ T) : continuous
  (map f : Lbar_le r' S c → Lbar_le r' T c) :=
begin
  rw continuous_iff,
  intros M,
  have : truncate M ∘ (map f : Lbar_le r' S c → Lbar_le r' T c) =
    Lbar_bdd.map f ∘ truncate M, { ext, refl },
  rw this,
  refine continuous.comp _ continuous_truncate,
  continuity,
end

end map

variables (r' c)

/-- A version of `Lbar_le` which is functorial in `S`. -/
@[simps]
def Fintype_functor [fact (0 < r')] : Fintype.{u} ⥤ Profinite.{u} :=
{ obj := λ S, Profinite.of $ Lbar_le r' S c,
  map := λ S T f,
  { to_fun := map f,
    continuous_to_fun := map_continuous _ },
  map_id' := λ S, begin
    ext1,
    exact subtype.ext x.1.map_id,
  end,
  map_comp' := λ S T U f g, begin
    ext1,
    exact subtype.ext (x.1.map_comp f g),
  end }

variables (c₁ c₂)
/-- The functor sending `S` to the (categorical) product
  of `Lbar_le r' S c₁` and `Lbar_le r' S c₂`. -/
@[simps]
def Fintype_functor_prod [fact (0 < r')] : Fintype.{u} ⥤ Profinite.{u} :=
{ obj := λ S, (S,S),
  map := λ _ _ f, (f,f) } ⋙
    (Fintype_functor r' c₁).prod (Fintype_functor r' c₂) ⋙
    (uncurry.obj prod.functor)

/-- This is a functorial version of `add'`. -/
@[simps]
def Fintype_add_functor [fact (0 < r')] :
  Fintype_functor_prod.{u} r' c₁ c₂ ⟶ Fintype_functor.{u} r' (c₁ + c₂) :=
{ app := λ S, (Profinite.prod_iso _ _).hom ≫ ⟨add' _, continuous_add'⟩,
  naturality' := begin
    intros S T f,
    ext,
    dsimp only [functor.prod, Profinite.prod_iso, Fintype_functor_prod,
      uncurry, prod.functor, functor.comp_map],
    rw [category_theory.limits.prod.map_map, category.comp_id, category.id_comp],
    dsimp [map, Lbar.map, add', add, is_limit.cone_point_unique_up_to_iso,
      is_limit.unique_up_to_iso],
    rw finset.sum_add_distrib,
    -- annoying
    have useful : ∀ {A B C : Profinite} (f : A ⟶ B) (g : B ⟶ C) (a : A),
      (f ≫ g) a = g (f a) := λ _ _ _ _ _ _, rfl,
    congr,
    { have : binary_fan.fst (limit.cone (pair (Profinite.of (Lbar_le r' ↥T c₁))
        (Profinite.of (Lbar_le r' ↥T c₂)))) = category_theory.limits.prod.fst := rfl,
      rw [this, ← useful, category_theory.limits.prod.map_fst],
      refl },
    { have : binary_fan.snd (limit.cone (pair (Profinite.of (Lbar_le r' ↥T c₁))
        (Profinite.of (Lbar_le r' ↥T c₂)))) = category_theory.limits.prod.snd := rfl,
      rw [this, ← useful, category_theory.limits.prod.map_snd],
      refl },
  end}

/-- Negation on `Lbar_le` as a functor in `S`. -/
def Fintype_neg_functor [fact (0 < r')] : Fintype_functor.{u} r' c ⟶ Fintype_functor.{u} r' c :=
{ app := λ S, ⟨Lbar_le.neg, Lbar_le.continuous_neg⟩,
  naturality' := begin
    intros A B f,
    ext,
    dsimp [map, neg],
    simp,
  end }

variables {c₁ c₂}

open category_theory

/-- A bifunctor version of `Fintype_functor`, where `c` can vary. -/
@[simps]
def Fintype_bifunctor [fact (0 < r')] : ℝ≥0 ⥤ Fintype.{u} ⥤ Profinite.{u} :=
{ obj := λ c, Fintype_functor r' c,
  map := λ c₁ c₂ f,
  { app := λ S,
    { to_fun := @Lbar_le.cast_le r' S _ c₁ c₂ ⟨le_of_hom f⟩,
      continuous_to_fun := by apply continuous_cast_le } },
  map_id' := λ c, by { ext, refl },
  map_comp' := λ a b c f g, by { ext, refl } }

/-- The extension of `Fintype_functor` to `Profinite` obtained by taking limits. -/
@[simps]
def functor [fact (0 < r')] : Profinite.{u} ⥤ Profinite.{u} :=
Profinite.extend (Fintype_functor r' c)

variables (c₁ c₂)

/-- The profinite variant of `Fintype_functor_prod`. -/
@[simps]
def functor_prod [fact (0 < r')] : Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ S, (S,S), map := λ _ _ f, (f, f) } ⋙
  (functor r' c₁).prod (functor r' c₂) ⋙
  (uncurry.obj prod.functor)

/-- A cone over `(S.fintype_diagram ⋙ Fintype_functor_prod r' c₁ c₂)` used in the definition
  of `add_functor`. -/
def functor_prod_cone [fact (0 < r')] (S : Profinite) :
  cone (S.fintype_diagram ⋙ Fintype_functor_prod.{u} r' c₁ c₂) :=
{ X := (functor_prod r' c₁ c₂).obj S,
  π :=
  { app := λ I, category_theory.limits.prod.map (limit.π _ I) (limit.π _ I),
    naturality' := begin
      intros I J f,
      dsimp [Fintype_functor_prod],
      simp [← limit.w _ f],
    end } }

-- TODO: this proof is SLOW.
/-- The profinite variant of `Fintype_add_functor`. -/
def add_functor [fact (0 < r')] : functor_prod.{u} r' c₁ c₂ ⟶ functor.{u} r' (c₁ + c₂) :=
-- Why doesn't this work without the "by apply ..."?
{ app := λ S, by apply limit.lift _ (functor_prod_cone r' c₁ c₂ S) ≫
      category_theory.limits.lim.map (whisker_left _ (Fintype_add_functor _ _ _)),
  naturality' := begin
    intros S T f,
    erw [limits.limit.lift_map, limits.limit.lift_map],
    dsimp only [whisker_left, limits.cones.postcompose],
    apply limit.hom_ext,
    intros I,
    dsimp only [nat_trans.comp_app, functor, Profinite.extend, Profinite.change_cone],
    simp_rw [category.assoc, limits.limit.lift_π],
    change _ = _ ≫ limit.π _ _ ≫ _,
    simp_rw [← category.assoc, limits.limit.lift_π],
    dsimp only [nat_trans.comp_app, functor_prod_cone, functor_prod,
      functor.comp_map, uncurry, limits.prod.functor],
    simp only [limits.prod.map_map, category.id_comp, category.comp_id, category.assoc],
    let e : Fintype.of (I.comap f.continuous) ⟶ Fintype.of I := discrete_quotient.map (le_refl _),
    erw ← (Fintype_add_functor r' c₁ c₂).naturality e,
    simp_rw ← category.assoc,
    dsimp only [Fintype_functor_prod, functor.comp_map, uncurry, limits.prod.functor,
      functor.prod, functor, Profinite.extend],
    simp only [limits.prod.map_map, category.id_comp, category.comp_id, limits.limit.lift_π],
    refl,
  end }

/-- The profinite functorial variant of negation on `Lbar_le`. -/
def neg_functor [fact (0 < r')] : functor.{u} r' c ⟶ functor.{u} r' c :=
{ app := λ X, limits.lim.map $ whisker_left _ $ Fintype_neg_functor _ _,
  naturality' := begin
    intros A B f,
    apply limit.hom_ext,
    intros S,
    dsimp,
    simp,
  end }

variables {c₁ c₂}

/-- A bifunctor version of `functor`, where `c` can vary. -/
@[simps]
def bifunctor [fact (0 < r')] : ℝ≥0 ⥤ Profinite.{u} ⥤ Profinite.{u} :=
{ obj := λ c, functor r' c,
  map := λ a b f, Profinite.extend_nat_trans $ (Fintype_bifunctor r').map f,
  map_id' := begin
    intros c,
    rw (Fintype_bifunctor r').map_id,
    exact Profinite.extend_nat_trans_id _,
  end,
  map_comp' := begin
    intros a b c α β,
    rw (Fintype_bifunctor r').map_comp,
    exact Profinite.extend_nat_trans_comp _ _,
  end }

/-- `Lbar_le.functor r' c` is indeed an extension of `Lbar_le.Fintype_functor r' c`. -/
@[simps]
def functor_extends [fact (0 < r')] :
  Fintype.to_Profinite ⋙ functor.{u} r' c ≅ Fintype_functor.{u} r' c :=
Profinite.extend_extends _ .

variables {r' c}

-/
end LbarLe

instance [Fact (0 < r')] : ProfinitelyFilteredPseudoNormedGroup (Lbar r' S) :=
  {
    Lbar.pseudoNormedGroup with
    topology := fun c => show TopologicalSpace (LbarLe r' S c) by infer_instance
    t2 := fun c => show T2Space (LbarLe r' S c) by infer_instance
    td := fun c => show TotallyDisconnectedSpace (LbarLe r' S c) by infer_instance
    compact := fun c => show CompactSpace (LbarLe r' S c) by infer_instance
    continuous_add' := fun c₁ c₂ => LbarLe.continuous_add'
    continuous_neg' := fun c => LbarLe.continuous_neg
    continuous_castLe := fun c₁ c₂ => by
      intro h
      rw [show PseudoNormedGroup.castLe = (LbarLe.castLe : LbarLe r' S c₁ → LbarLe r' S c₂) by ext;
          rfl]
      exact LbarLe.continuous_castLe r' S c₁ c₂ }

/-

namespace Lbar


variable r'

/-- The diagram whose colimit yields `Lbar.profinite`. -/
def profinite_diagram [fact (0 < r')] : ℝ≥0 ⥤ Profinite.{u} ⥤ Type u :=
let E := (whiskering_right Profinite _ _).obj (forget Profinite) in
  ((whiskering_right _ _ _).obj E).obj (Lbar_le.bifunctor.{u} r')

/-- The functor `Lbar : Profinite ⥤ Type*`. -/
@[nolint check_univs] -- TODO remove this
def profinite [fact (0 < r')] : Profinite ⥤ Type* :=
(as_small.down ⋙ profinite_diagram r').flip ⋙ colim

attribute [nolint check_univs] profinite._proof_1

-- TODO: Move this to the condensed folder, once it's more stable!
/-- The representable presheaf associated to a profinite set. -/
def representable : Profinite.{u} ⥤ (as_small.{u+1} Profinite.{u})ᵒᵖ ⥤ Type (u+1) :=
let Y := @yoneda (as_small.{u+1} Profinite.{u}) _ in
((whiskering_right Profinite.{u} _ _).obj Y).obj as_small.up

/-- The diagram whose colimit yields `Lbar.precondensed`. -/
def precondensed_diagram [fact (0 < r')] :
  ℝ≥0 ⥤ Profinite.{u} ⥤ (as_small.{u+1} Profinite.{u})ᵒᵖ ⥤ Type (u+1) :=
let E := (whiskering_right Profinite _ _).obj representable in
((whiskering_right _ _ _).obj E).obj $ Lbar_le.bifunctor.{u} r'

/-- A functor associating to every `S : Profinite` the presheaf associated to the condensed set
`Lbar(S)`. -/
-- TODO: Prove that it is a condensed set!
def precondensed [fact (0 < r')] : Profinite.{u} ⥤ (as_small.{u+1} Profinite.{u})ᵒᵖ ⥤ Type (u+1) :=
(as_small.down.{_ _ (u+1)} ⋙ precondensed_diagram.{u} r').flip  ⋙ colim

end Lbar

-/
#lint

