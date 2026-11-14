import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import LiquidTensorExperiment.SystemOfComplexes.Basic

#align_import SystemOfComplexes.truncate

/-!

# Truncation

In this file we define a truncation functors for (systems of) complexes of seminormed groups.
This operation takes a complex `C` indexed by `ℕ`, and creates a new complex whose objects are
* in degree `0`:   the cokernel of `d : C 0 ⟶ C 1`
* in degree `n+1`: the object `C (n+2)`

Various lemmas are proved about how this construction preserves or reflects
various notions of bounded exactness.

-/


universe u

noncomputable section

open scoped NNReal

open CategoryTheory CategoryTheory.Limits

namespace SemiNormedGroupCat

open quotientAddGroup

namespace Truncate

variable (C : CochainComplex SemiNormedGroupCat.{u} ℕ)

open CategoryTheory.Preadditive

def x : ℕ → SemiNormedGroupCat.{u}
  | 0 => explicitCokernel (C.d 0 1)
  | n + 1 => C.pt (n + 2)

def d : ∀ i j, x C i ⟶ x C j
  | 0, 1 => explicitCokernelDesc (C.d_comp_d 0 1 2)
  | i + 1, j + 1 => C.d (i + 2) (j + 2)
  | _, _ => 0

theorem d_eq_zero : ∀ ⦃i j : ℕ⦄, ¬(ComplexShape.up ℕ).Rel i j → d C i j = 0
  | 0, 0, h => rfl
  | 0, j + 2, h => rfl
  | i + 1, 0, h => rfl
  | 0, 1, h => (h rfl).elim
  | i + 1, j + 1, h => C.shape _ _ fun H => h <| Nat.succ_injective <| H

theorem d_comp_d : ∀ i j k, i + 1 = j → j + 1 = k → d C i j ≫ d C j k = 0
  | 0, 1, 2, rfl, rfl => explicitCokernelDesc_comp_eq_zero _ (C.d_comp_d _ _ _)
  | i + 1, j + 1, k + 1, rfl, rfl => C.d_comp_d _ _ _

@[simps]
def obj : CochainComplex SemiNormedGroupCat ℕ
    where
  pt := x C
  d := d C
  shape' := d_eq_zero C
  d_comp_d' := d_comp_d C

theorem obj_d_add_one (C : CochainComplex SemiNormedGroupCat ℕ) (i j : ℕ) :
    (obj C).d (i + 1) (j + 1) = d C (i + 1) (j + 1) :=
  rfl

def mapF {C₁ C₂ : CochainComplex SemiNormedGroupCat ℕ} (f : C₁ ⟶ C₂) : ∀ i : ℕ, x C₁ i ⟶ x C₂ i
  | 0 => explicitCokernel.map (f.comm 0 1).symm
  | i + 1 => f.f (i + 2)

theorem map_comm {C₁ C₂ : CochainComplex SemiNormedGroupCat.{u} ℕ} (f : C₁ ⟶ C₂) :
    ∀ i j, i + 1 = j → mapF f i ≫ d C₂ i j = d C₁ i j ≫ mapF f j
  | 0, 1, rfl => (ExplicitCoker.map_desc (f.comm 1 2).symm).symm
  | i + 1, j + 1, rfl => f.comm (i + 2) (j + 2)

@[simps]
def map {C₁ C₂ : CochainComplex SemiNormedGroupCat.{u} ℕ} (f : C₁ ⟶ C₂) : obj C₁ ⟶ obj C₂
    where
  f := mapF f
  comm' := map_comm f

end Truncate

@[simps]
def truncate : CochainComplex SemiNormedGroupCat.{u} ℕ ⥤ CochainComplex SemiNormedGroupCat.{u} ℕ
    where
  obj C := Truncate.obj C
  map C₁ C₂ f := Truncate.map f
  map_id C := by ext (n | n) ⟨x⟩ <;> rfl
  map_comp C₁ C₂ C₃ f g := by ext (n | n) ⟨x⟩ <;> rfl

instance truncate.additive : truncate.Additive
    where map_add' := by intros;
    ext (_ | n) ⟨⟩ <;>
      simp only [truncate_map, Truncate.mapF_2, HomologicalComplex.add_f_apply,
        Preadditive.comp_add, Truncate.mapF, explicitCokernel.map, Preadditive.add_comp,
        explicit_cokernel_π_desc]

end SemiNormedGroupCat

namespace SystemOfComplexes

open CategoryTheory

variable (C : SystemOfComplexes.{u})

@[simps]
def truncate : SystemOfComplexes ⥤ SystemOfComplexes :=
  (whiskeringRight _ _ _).obj <| SemiNormedGroupCat.truncate

@[simp]
theorem truncate_obj_d_zero_one (c : ℝ≥0) (y : C c 1) :
    (Truncate.obj C).d 0 1 (SemiNormedGroupCat.explicitCokernelπ _ y) = C.d 1 2 y :=
  rfl

@[simp]
theorem truncate_obj_d_succ_succ (c : ℝ≥0) (i j : ℕ) (x : Truncate.obj C c (i + 1)) :
    (Truncate.obj C).d (i + 1) (j + 1) x = C.d (i + 2) (j + 2) x :=
  rfl

theorem truncateAdmissible (hC : C.Admissible) : (Truncate.obj C).Admissible :=
  { d_norm_noninc' := by
      rintro c (i | i) j rfl
      · apply SemiNormedGroupCat.explicitCokernelDesc_normNoninc
        exact hC.d_normNoninc _ _ 1 2
      · exact hC.d_normNoninc _ _ (i + 2) (i + 3)
    res_normNoninc := by
      rintro c₁ c₂ (i | i) h x
      · apply SemiNormedGroupCat.explicitCokernelDesc_normNoninc _
        exact (SemiNormedGroupCat.normNoninc_explicitCokernelπ _).comp (hC.res_normNoninc _ _ _ _)
      · exact hC.res_normNoninc _ _ _ _ x }

variable {k K : ℝ≥0} (m' m : ℕ) [hk : Fact (1 ≤ k)] (c₀ : ℝ≥0)

theorem truncateIsWeakBoundedExact (hC : C.IsWeakBoundedExact k K (m + 1) c₀) :
    (Truncate.obj C).IsWeakBoundedExact k K m c₀
  | c, hc, 0, hi, x, ε, hε =>
    by
    let π c := SemiNormedGroupCat.explicitCokernelπ (@d C c 0 1)
    obtain ⟨x, rfl⟩ : ∃ x', π _ x' = x := SemiNormedGroupCat.explicitCokernelπ_surjective x
    obtain ⟨i₀, -, hi₀, rfl, y, hy⟩ := hC c hc _ (Nat.succ_le_succ hi) x ε hε
    obtain rfl : i₀ = 0 := by rwa [Nat.sub_self] at hi₀ ; clear hi
    refine' ⟨0, _, rfl, rfl, 0, _⟩
    simp only [map_zero, sub_zero, map_neg, truncate_obj_d_zero_one, norm_neg]
    calc
      _ = ‖(π c (res x - C.d 0 1 y))‖ := _
      _ ≤ ‖res x - C.d 0 1 y‖ := (SemiNormedGroupCat.normNoninc_explicitCokernelπ _ _)
      _ ≤ _ := hy
    have hπy : π c (C.d 0 1 y) = 0 := by show (C.d 0 1 ≫ π c) y = 0;
      rw [SemiNormedGroupCat.comp_explicitCokernelπ]; rfl
    simp only [_root_.map_sub, hπy, sub_zero]; rfl
  | c, hc, i + 1, hi, x, ε, hε =>
    by
    obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc _ (Nat.succ_le_succ hi) x ε hε
    refine' ⟨i, _, rfl, rfl, _⟩
    cases i <;> [exact ⟨SemiNormedGroupCat.explicitCokernelπ _ y, hy⟩; exact ⟨y, hy⟩]

theorem isWeakBoundedExactOfTruncate (IH : C.IsWeakBoundedExact k K m c₀)
    (hC : (Truncate.obj C).IsWeakBoundedExact k K m c₀) : C.IsWeakBoundedExact k K (m + 1) c₀
  | c, hc, 0, hi, x, ε, hε => IH c hc 0 (Nat.zero_le _) x ε hε
  | c, hc, 1, hi, x, ε, hε =>
    by
    let π c := SemiNormedGroupCat.explicitCokernelπ (@d C c 0 1)
    let δ := ε / 2
    have hδε : δ + δ = ε := by dsimp [δ]; rw [← add_div, half_add_self]
    have hδ : 0 < δ := div_pos hε zero_lt_two
    obtain ⟨x', Hxx', Hx'⟩ :
      ∃ x', π c x' = π c (res x) ∧ ‖x'‖ < ‖(π c (res x))‖ + δ :=
      (SemiNormedGroupCat.isQuotient_explicitCokernelπ _).norm_lift hδ _
    obtain ⟨y, hy⟩ : ∃ y : C c 0, C.d 0 1 y = res x - x' :=
      by
      erw [QuotientAddGroup.eq, add_comm, ← sub_eq_add_neg, Set.mem_range] at Hxx' 
      exact Hxx'
    obtain ⟨_, _, rfl, rfl, y', H⟩ := hC c hc _ (Nat.zero_le m) (π _ x) δ hδ
    refine' ⟨0, 2, rfl, rfl, y, _⟩
    simp only [d_self_apply, map_zero, sub_zero, truncate_obj_d_zero_one, norm_neg] at H ⊢
    calc
      ‖(res x - (C.d 0 1) y)‖ ≤ ‖x'‖ := by rw [hy, sub_sub_cancel]
      _ ≤ ‖(π c (res x))‖ + δ := Hx'.le
      _ ≤ ↑K * ‖C.d 1 2 x‖ + δ + δ := (add_le_add_right H _)
      _ ≤ ↑K * ‖C.d 1 2 x‖ + ε := by rw [add_assoc, hδε]
  | c, hc, i + 2, hi, x, ε, hε =>
    by
    obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc (i + 1) (Nat.pred_le_pred hi) x ε hε
    refine' ⟨i + 1, _, rfl, rfl, _⟩
    cases i
    · let π c := SemiNormedGroupCat.explicitCokernelπ (@d C c 0 1)
      obtain ⟨y, rfl⟩ : ∃ y', π _ y' = y := SemiNormedGroupCat.explicitCokernelπ_surjective y
      exact ⟨y, hy⟩
    · exact ⟨y, hy⟩

theorem truncate_isWeakBoundedExact_iff (hC : C.IsWeakBoundedExact k K m c₀) :
    (Truncate.obj C).IsWeakBoundedExact k K m c₀ ↔ C.IsWeakBoundedExact k K (m + 1) c₀ :=
  ⟨isWeakBoundedExactOfTruncate C m c₀ hC, truncateIsWeakBoundedExact C m c₀⟩

end SystemOfComplexes

