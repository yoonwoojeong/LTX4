import Mathlib.LinearAlgebra.Dimension
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.LinearAlgebra.FreeModule.Basic

#align_import for_mathlib.pid

open scoped BigOperators

open Order

section Finset

universe u v w

variable {β : Type u} {α : Type v} {α' : Type w} [CommMonoid β]

@[simp, to_additive]
theorem Finset.prod_comap (s : Finset α') (e : α → α') (f : α' → β) (he : Set.InjOn e (e ⁻¹' ↑s))
    (hs : (s : Set α') ⊆ Set.range e) : ∏ x in s.preimage e he, f (e x) = ∏ x in s, f x :=
  by
  haveI : ∀ x : α', Decidable (x ∈ Set.range e) := fun x => Classical.propDecidable _
  haveI := Classical.typeDecidableEq α'
  have hs : s = Finset.image e (s.preimage e he) :=
    by
    rw [Finset.image_preimage]
    ext
    constructor
    · intro ha
      simp only [Finset.mem_filter, Set.mem_range]
      refine' ⟨ha, _⟩
      exact_mod_cast Set.mem_of_subset_of_mem hs ha
    · simp only [Finset.mem_filter, Set.mem_range, and_imp, forall_exists_index]
      exact fun H _ _ => H
  have hpre : e ⁻¹' ↑s = s.preimage e he := by rw [Finset.coe_preimage]
  have : ∏ x in Finset.image e (s.preimage e he), f x = ∏ x in s.preimage e he, f (e x)
  apply Finset.prod_image
  intro x hx y hy h
  have hx : x ∈ e ⁻¹' ↑s := by rw [hpre] <;> exact hx
  have hy : y ∈ e ⁻¹' ↑s := by rw [hpre] <;> exact hy
  exact he hx hy h
  rw [← this]
  rw [← hs]

end Finset

section Finsupp

variable {α : Type _} {M : Type _} {R : Type _}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {α' : Type _}

theorem Finsupp.total_comap_domain' (v : α' → M) (f : α → α') (l : α' →₀ R)
    (hf : Set.InjOn f (f ⁻¹' ↑l.support)) (hsupp : (l.support : Set α') ⊆ Set.range f) :
    (Finsupp.total α M R (v ∘ f)) (Finsupp.comapDomain f l hf) = ∑ i : α' in l.support, l i • v i :=
  by
  haveI := Classical.typeDecidableEq α'
  rw [Finsupp.total_apply]
  simp [Finsupp.sum, Finsupp.comapDomain]
  exact Finset.sum_comap l.support f (fun x => l x • v x) hf hsupp

end Finsupp

open Submodule.IsPrincipal Set Submodule

universe u

-- Equivalent of lt_of_lt_of_le for unbundled orders. (??)
theorem lt_of_lt_of_le_unbundled {α : Type u} {r : α → α → Prop} [IsStrictTotalOrder α r]
    {a b c : α} (hab : r a b) (hbc : ¬r c b) : r a c :=
  by
  have t : r b c ∨ b = c ∨ r c b := trichotomous b c
  cases t
  exact IsTrans.trans a b c hab t
  cases t
  rw [← t]
  exact hab
  exact False.elim (hbc t)

-- Characterization of le for unbundled orders. (??)
theorem le_unbundled {α : Type u} {r : α → α → Prop} [IsStrictTotalOrder α r] {a b : α} :
    r a b ∨ a = b ↔ ¬r b a := by
  constructor
  intro h
  cases h
  by_contra h'
  exact irrefl a (IsTrans.trans _ _ _ h h')
  rw [h]
  exact irrefl b
  intro h
  have t : r a b ∨ a = b ∨ r b a := trichotomous a b
  cases t
  exact Or.intro_left _ t
  cases t
  exact Or.intro_right _ t
  exact False.elim (h t)

variable {R : Type _} [CommRing R]

variable {M : Type _} [AddCommGroup M] [Module R M]

section AuxLemmas

variable {o : Ordinal} {a : { i // i < o } → R}

theorem support_remove {i : Ordinal} {j_good : { i // a i ≠ 0 }} (hj : succ j_good.1.1 = i)
    {l l' : { i // a i ≠ 0 } →₀ R}
    (hsupp : (l.support : Set { i // a i ≠ 0 }) ⊆ fun x : { i // a i ≠ 0 } => x.1.1 < i)
    (hl' : l' = l + Finsupp.single j_good (-l j_good)) :
    (l'.support : Set { i // a i ≠ 0 }) ⊆ fun x : { i // a i ≠ 0 } => x.1.1 < j_good.1.1 :=
  by
  let good := { i // a i ≠ 0 }
  have hl'j : l' j_good = 0 := by
    simp only [hl', Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_right_neg]
  intro x hx
  have hx₁ : x ∈ l'.support := hx
  have hl' : ∀ x : good, x ≠ j_good → l' x = l x
  intro x hx
  simp only [hl', Finsupp.single_eq_of_ne hx.symm, Finsupp.coe_add, Pi.add_apply, add_zero]
  by_contra
  have h : ¬x.1.1 < j_good.1.1 := h
  have h := eq_or_lt_of_le (not_lt.1 h)
  cases h
  · have h_1 : j_good = x := by simp at H1  <;> ext <;> exact h_1
    rw [← h_1] at hx₁ 
    rw [l'.3 j_good] at hx₁ 
    contradiction
  · have h_1' : j_good.1.1 ≠ x.1.1 := ne_of_lt H1
    have h_1' : j_good ≠ x
    -- todo: can't ext do this?
    simp at h_1' 
    rw [Ne.def]
    apply mt Subtype.ext_iff.1
    apply mt Subtype.ext_iff.1
    exact h_1'
    have : l'.toFun x = l x := hl' x h_1'.symm
    have hx' := hx₁
    rw [l'.3 x] at hx' 
    rw [this] at hx' 
    have hxi : succ j_good.1.1 ≤ x.1.1 := SuccOrder.succ_le_of_lt h_1
    rw [hj] at hxi 
    have := not_mem_subset hsupp (not_lt_of_ge hxi)
    have := mt (l.3 x).2 this
    contradiction

-- Auxiliary lemma for proving linear independence at limit ordinals.
theorem lin_ind_limit {BB : { i // a i ≠ 0 } → M} {i : Ordinal} (hio : i ≤ o)
    (hlim : Ordinal.IsLimit i)
    (H :
      ∀ k : Ordinal,
        k < i →
          k ≤ o →
            ∀ l : { i // a i ≠ 0 } →₀ R,
              ((l.support : Set { i // a i ≠ 0 }) ⊆ fun x : { i // a i ≠ 0 } => x.1.1 < k) →
                Finsupp.total { i // a i ≠ 0 } M R BB l = 0 → l = 0)
    {l : { i // a i ≠ 0 } →₀ R}
    (hsupp : (l.support : Set { i // a i ≠ 0 }) ⊆ fun x : { i // a i ≠ 0 } => x.1.1 < i)
    (hl : Finsupp.total { i // a i ≠ 0 } M R BB l = 0) : l = 0 :=
  by
  let good := { i // a i ≠ 0 }
  by_cases hemp : l.support.Nonempty
  · let m := l.support.max' hemp
    dsimp at hsupp 
    have hm₀ : ↑↑m < i := by
      exact_mod_cast mem_of_subset_of_mem hsupp (Finset.max'_mem l.support hemp)
    have hm : succ m.1.1 < i := (Ordinal.succ_lt_of_isLimit hlim).2 hm₀
    have hmo : succ m.1.1 ≤ o := le_of_lt (lt_of_lt_of_le hm hio)
    have hsub : (l.support : Set good) ⊆ fun x : good => x.1.1 < succ m.1.1
    intro x hx
    have hx : x ∈ l.support := hx
    have : x.1.1 ≤ m.1.1 := Finset.le_max' l.support x hx
    exact Order.lt_succ_iff.2 this
    exact H (succ m.1.1) hm hmo l hsub hl
  · rw [Finset.not_nonempty_iff_eq_empty] at hemp 
    exact Finsupp.support_eq_empty.1 hemp

-- Auxiliary lemma for proving the span property at limit ordinals.
theorem span_limit {N : Submodule R M} {BB : { i // a i ≠ 0 } → M} {i : Ordinal} (hio : i ≤ o)
    (hlim : Ordinal.IsLimit i) {B : Basis { i // i < o } R M}
    (H :
      ∀ k : Ordinal,
        k < i →
          k ≤ o →
            ∀ l : { i // i < o } →₀ R,
              ((l.support : Set { i // i < o }) ⊆ fun x => x.1 < k) →
                Finsupp.total { i // i < o } M R B l ∈ N →
                  Finsupp.total { i // i < o } M R B l ∈ Submodule.span R (range BB))
    {l : { i // i < o } →₀ R} (hsupp : (l.support : Set { i // i < o }) ⊆ fun x => x.1 < i)
    (hl : Finsupp.total { i // i < o } M R B l ∈ N) :
    Finsupp.total { i // i < o } M R B l ∈ Submodule.span R (range BB) :=
  by
  let ords := { i // i < o }
  by_cases hemp : l.support.Nonempty
  · let m := l.support.max' hemp
    dsimp at hsupp 
    have hm₀ : ↑m < i := by
      exact_mod_cast mem_of_subset_of_mem hsupp (Finset.max'_mem l.support hemp)
    have hm : succ m.1 < i := (Ordinal.succ_lt_of_isLimit hlim).2 hm₀
    have hmo : succ m.1 ≤ o := le_of_lt (lt_of_lt_of_le hm hio)
    have hsub : (l.support : Set ords) ⊆ fun x : ords => x.1 < succ m.1
    intro x hx
    have hx : x ∈ l.support := hx
    have : x.1 ≤ m.1 := Finset.le_max' l.support x hx
    exact Order.lt_succ_iff.2 this
    exact H (succ m.1) hm hmo l hsub hl
  · rw [Finset.not_nonempty_iff_eq_empty] at hemp 
    simp only [Finsupp.support_eq_empty.1 hemp, _root_.map_zero, zero_mem]

-- Auxiliary lemma for proving linear independence at successor ordinals.
theorem lin_ind_succ [IsDomain R] {N : Submodule R M} {B : Basis { i // i < o } R M}
    {BB : { i // a i ≠ 0 } → N}
    (hB_BB :
      ∀ i : Ordinal,
        ∀ l : { i // a i ≠ 0 } →₀ R,
          ((l.support : Set { i // a i ≠ 0 }) ⊆ fun x => x.1.1 < i) →
            ∃ lB : { i // i < o } →₀ R,
              ((lB.support : Set { i // i < o }) ⊆ fun x => x.1 < i) ∧
                Finsupp.total { i // i < o } M R B lB = Finsupp.total { i // a i ≠ 0 } N R BB l)
    (hcoordB : ∀ i : { i // a i ≠ 0 }, (B.Coord i) (BB i) ≠ 0) {i : Ordinal} (hio : i ≤ o)
    (hlim : ¬Ordinal.IsLimit i)
    (H :
      ∀ k : Ordinal,
        k < i →
          k ≤ o →
            ∀ l : { i // a i ≠ 0 } →₀ R,
              ((l.support : Set { i // a i ≠ 0 }) ⊆ fun x : { i // a i ≠ 0 } => x.1.1 < k) →
                Finsupp.total { i // a i ≠ 0 } N R BB l = 0 → l = 0)
    {l : { i // a i ≠ 0 } →₀ R}
    (hsupp : (l.support : Set { i // a i ≠ 0 }) ⊆ fun x : { i // a i ≠ 0 } => x.1.1 < i)
    (hl : Finsupp.total { i // a i ≠ 0 } N R BB l = 0) : l = 0 :=
  by
  let ords := { i // i < o }
  let good := { i // a i ≠ 0 }
  dsimp at hsupp 
  dsimp only [Ordinal.IsLimit] at hlim 
  repeat' push_neg at hlim 
  by_cases hi : i ≠ 0
  rcases hlim hi with ⟨j, hj⟩
  have hji : j < i := hj.1
  have hjo : j < o := lt_of_lt_of_le hji hio
  have hj : succ j = i := le_antisymm (succ_le_iff.2 hj.1) hj.2
  have not_j_lt_x : ∀ x : good, ∀ j : Ordinal, x ∈ l.support → j < x.1.1 → succ j = i → False :=
    by
    intro x j hx h_1 hj
    have hi : succ j ≤ x := SuccOrder.succ_le_of_lt h_1
    rw [hj] at hi 
    have hi' := mem_of_subset_of_mem hsupp hx
    have hi' : ↑↑x < i := hi'
    have hi'' := not_le_of_lt hi'
    contradiction
  by_cases hgood : a ⟨j, hjo⟩ ≠ 0
  · -- Case: j is good
    let j_good : good := ⟨⟨j, hjo⟩, hgood⟩
    by_cases hjsupp : j_good ∈ l.support
    · let l' := l + Finsupp.single j_good (-l j_good)
      have hsupp' : (l'.support : Set good) ⊆ fun x : good => x.1.1 < j :=
        haveI : succ j_good.1.1 = i := hj
        support_remove this hsupp rfl
      let lB := Exists.choose (hB_BB j l' hsupp')
      have hlBsupp : (lB.support : Set { i // i < o }) ⊆ fun x : { i // i < o } => x.1 < j :=
        (Exists.choose_spec (hB_BB j l' hsupp')).1
      have hlBtot : Finsupp.total { i // i < o } M R B lB = Finsupp.total good N R BB l' :=
        (Exists.choose_spec (hB_BB j l' hsupp')).2
      have h₁ : (B.coord ⟨j, hjo⟩) (Finsupp.total good N R BB l) = 0 := by
        simp only [hl, LinearMap.map_zero, coe_zero]
      have h₂ : (B.coord ⟨j, hjo⟩) (Finsupp.total good N R BB l') = 0 :=
        by
        rw [← hlBtot]
        simp only [Basis.repr_total, Basis.coord_apply]
        rw [← Finsupp.not_mem_support_iff]
        apply not_mem_subset hlBsupp
        have : ¬(⟨j, hjo⟩ : ords).val < j := by simp <;> exact irrefl j
        exact this
      have h₃ :
        (B.coord ⟨j, hjo⟩) (Finsupp.total good N R BB (Finsupp.single j_good (-l j_good))) ≠ 0
      have hlj : l j_good ≠ 0 := (l.3 j_good).1 hjsupp
      · simp only [hlj, Finsupp.total_single, coe_smul_of_tower, Basis.coord_apply,
          LinearEquiv.map_smulₛₗ, RingHom.id_apply, Finsupp.coe_smul, Pi.smul_apply,
          Algebra.id.smul_eq_mul, Ne.def, neg_eq_zero, mul_eq_zero, false_or_iff]
        have := hcoordB j_good
        rw [Basis.coord_apply] at this 
        exact this
      have hsum :
        (B.coord ⟨j, hjo⟩) (Finsupp.total good N R BB l') =
          (B.coord ⟨j, hjo⟩) (Finsupp.total good N R BB l) +
            (B.coord ⟨j, hjo⟩) (Finsupp.total good N R BB (Finsupp.single j_good (-l j_good))) :=
        by simp [l', Finsupp.single_neg, map_add_neg, map_neg]
      simp only [h₁, h₂, zero_add] at hsum 
      have hsum := Eq.symm hsum
      contradiction
    · have hsub : (l.support : Set good) ⊆ fun x : good => x.1.1 < j
      intro x hx
      have hx : x ∈ l.support := hx
      by_contra
      have h : ¬x.1.1 < j := h
      have h := eq_or_lt_of_le (not_lt.1 h)
      cases h
      · have : j_good = x := by simp [j_good, h_1]
        rw [this] at hjsupp 
        contradiction
      · exact not_j_lt_x x j hx h_1 hj
      exact H j hji (le_of_lt hjo) l hsub hl
  · -- Case: j is not good
    have hsub : (l.support : Set good) ⊆ fun x : good => x.1.1 < j
    intro x hx
    have hx : x ∈ l.support := hx
    by_contra
    have h : ¬x.1.1 < j := h
    have h := eq_or_lt_of_le (not_lt.1 h)
    cases h
    · have hx' := x.2
      have : x.1 = ⟨j, hjo⟩ := by simp [h_1]
      rw [this] at hx' 
      contradiction
    · exact not_j_lt_x x j hx h_1 hj
    exact H j hji (le_of_lt hjo) l hsub hl
  · -- induction base: i = 0
    have hi : i = 0 := Classical.not_not.1 hi
    rw [hi] at hsupp 
    simp only [Ordinal.not_lt_zero] at hsupp 
    have hsupp : (l.support : Set good) ⊆ ∅ := hsupp
    rw [subset_empty_iff, Finset.coe_eq_empty] at hsupp 
    simp only [Finsupp.support_eq_empty.1 hsupp, _root_.map_zero, zero_mem]

-- Auxiliary lemma for proving the span property at successor ordinals.
theorem span_succ {N : Submodule R M} {BB : { i // a i ≠ 0 } → M} {i : Ordinal} (hio : i ≤ o)
    (hlim : ¬Ordinal.IsLimit i) {B : Basis { i // i < o } R M}
    (H :
      ∀ k : Ordinal,
        k < i →
          k ≤ o →
            ∀ l : { i // i < o } →₀ R,
              ((l.support : Set { i // i < o }) ⊆ fun x => x.1 < k) →
                Finsupp.total { i // i < o } M R B l ∈ N →
                  Finsupp.total { i // i < o } M R B l ∈ Submodule.span R (range BB))
    {l : { i // i < o } →₀ R} (hsupp : (l.support : Set { i // i < o }) ⊆ fun x => x.1 < i)
    (hl : Finsupp.total { i // i < o } M R B l ∈ N)
    (hBB : ∀ i, ((B.repr (BB i)).support : Set { i // i < o }) ⊆ fun x => x.1 ≤ i)
    (hc :
      ∀ j : { i // i < o },
        i = succ j.1 → ∃ r : R, (B.coord j) (Finsupp.total { i // i < o } M R B l) = r • a j)
    (hBBN : ∀ i, BB i ∈ N) (hBBa : ∀ j : { i // a i ≠ 0 }, (B.coord j) (BB j) = a j) :
    Finsupp.total { i // i < o } M R B l ∈ Submodule.span R (range BB) :=
  by
  let ords := { i // i < o }
  let good := { i // a i ≠ 0 }
  dsimp at hsupp 
  dsimp only [Ordinal.IsLimit] at hlim 
  repeat' push_neg at hlim 
  by_cases hi : i ≠ 0
  rcases hlim hi with ⟨j, hj⟩
  have hji : j < i := hj.1
  have hjo : j < o := lt_of_lt_of_le hji hio
  have hj : succ j = i := le_antisymm (succ_le_iff.2 hj.1) hj.2
  have not_j_lt_x : ∀ x : ords, ∀ j : Ordinal, x ∈ l.support → j < x.1 → succ j = i → False :=
    by
    intro x j hx h_1 hj
    have hi : succ j ≤ x := SuccOrder.succ_le_of_lt h_1
    rw [hj] at hi 
    have hi' := mem_of_subset_of_mem hsupp hx
    have hi' : ↑x < i := hi'
    have hi'' := not_le_of_lt hi'
    contradiction
  have hc := hc ⟨j, hjo⟩ hj.symm
  by_cases hgood : a ⟨j, hjo⟩ ≠ 0
  · -- Case: j is good
    let j_good : good := ⟨⟨j, hjo⟩, hgood⟩
    by_cases hjsupp : (⟨j, hjo⟩ : { i // i < o }) ∈ l.support
    · let r := Exists.choose hc
      have hr : (B.coord ⟨j, hjo⟩) (Finsupp.total { i // i < o } M R B l) = r • a ⟨j, hjo⟩ :=
        Exists.choose_spec hc
      let l' := l - B.repr (r • BB j_good)
      have hsum :
        Finsupp.total { i // i < o } M R B l' =
          Finsupp.total { i // i < o } M R B l - r • BB j_good :=
        by simp [l']
      have hsum' :
        Finsupp.total { i // i < o } M R B l =
          Finsupp.total { i // i < o } M R B l' + r • BB j_good :=
        by simp only [hsum, sub_add_cancel]
      rw [hsum']
      have hsupp₀ : (l'.support : Set { i // i < o }) ⊆ fun x => x.1 < i :=
        by
        have hBBj := hBB j_good
        have hBBj' : B.repr (BB j_good) ∈ Finsupp.supported R R fun x : ords => x.val < i
        have hx : ∀ x : ords, x.1 ≤ j → x.1 < succ j := fun x p => lt_of_le_of_lt p (lt_succ j)
        rw [hj] at hx 
        intro y hy
        have := mem_of_subset_of_mem hBBj hy
        exact hx y (this : y.val ≤ j_good)
        intro x hx
        let l₀ : Finsupp.supported R R fun x : ords => x.1 < i := ⟨l, hsupp⟩
        let BBj₀ : Finsupp.supported R R fun x : ords => x.1 < i := ⟨B.repr (BB j_good), hBBj'⟩
        let l'₀ : Finsupp.supported R R fun x : ords => x.1 < i := l₀ - r • BBj₀
        have hl' : l' = l'₀ := by
          simp only [l', LinearEquiv.map_smulₛₗ, RingHom.id_apply, Subtype.coe_mk,
            coe_smul_of_tower, AddSubgroupClass.coe_sub, Submodule.coe_mk, sub_left_inj]
        have hl'' := (Finsupp.mem_supported R l'₀.1).1 l'₀.2
        simp only [Subtype.val_eq_coe, ← hl'] at hl'' 
        exact mem_of_subset_of_mem hl'' hx
      have hsupp' : (l'.support : Set { i // i < o }) ⊆ fun x => x.1 < j :=
        by
        intro x hx
        by_contra
        have h : ¬x.1 < j := h
        have h := eq_or_lt_of_le (not_lt.1 h)
        cases h
        have hjx : x = ⟨j, hjo⟩ := by simp [h_1]
        have hx : x ∈ l'.support := hx
        rw [l'.mem_support_toFun] at hx 
        have hl' : l' x = 0
        dsimp [l']
        have hu := hBBa j_good
        simp at hu 
        simp only [hu, hjx, LinearEquiv.map_smulₛₗ, RingHom.id_apply, Finsupp.coe_smul,
          Pi.smul_apply]
        rw [← hr]
        simp
        contradiction
        have hx := mem_of_subset_of_mem hsupp₀ hx
        have hx : x.1 < i := hx
        rw [← hj] at hx 
        have :=
          mt (not_covby_iff (lt_succ j)).2 (Classical.not_not.2 (order.succ_eq_iff_covby.mp rfl))
        push_neg at this 
        have := not_lt_of_ge (this x h_1)
        contradiction
      have hl' : Finsupp.total { i // i < o } M R B l' ∈ N :=
        by
        dsimp [l']
        simp
        rw [sub_eq_add_neg]
        apply N.add_mem' hl
        simp
        apply N.smul_mem' r
        exact hBBN j_good
      have h : Finsupp.total { i // i < o } M R B l' ∈ Submodule.span R (range BB) :=
        H j hji (le_of_lt hjo) l' hsupp' hl'
      have hBBj : r • BB j_good ∈ Submodule.span R (range BB) :=
        Submodule.smul_mem' (Submodule.span R (range BB)) r
          (mem_of_subset_of_mem subset_span (⟨j_good, rfl⟩ : BB j_good ∈ range BB))
      exact Submodule.add_mem' (Submodule.span R (range BB)) h hBBj
    · have hsub : (l.support : Set { i // i < o }) ⊆ fun x => x.1 < j
      intro x hx
      have hx : x ∈ l.support := hx
      by_contra
      have h : ¬x.1 < j := h
      have h := eq_or_lt_of_le (not_lt.1 h)
      cases h
      · have : (⟨j, hjo⟩ : { i // i < o }) = x := by
          simp only [h_1, Subtype.val_eq_coe, Subtype.coe_eta]
        rw [this] at hjsupp 
        contradiction
      · exact not_j_lt_x x j hx h_1 hj
      exact H j hji (le_of_lt hjo) l hsub hl
  · -- Case: j is not good
    have hgood := Classical.not_not.1 hgood
    simp only [hgood, Ideal.submodule_span_eq, singleton_zero, Ideal.span_zero, Ideal.mem_bot] at hc 
    have hsub : (l.support : Set { i // i < o }) ⊆ fun x => x.1 < j
    intro x hx
    have hx : x ∈ l.support := hx
    by_contra
    have h : ¬x.1 < j := h
    have h := eq_or_lt_of_le (not_lt.1 h)
    cases h
    · have : (⟨j, hjo⟩ : { i // i < o }) = x := by
        simp only [h_1, Subtype.val_eq_coe, Subtype.coe_eta]
      simp only [Basis.coord_apply, Basis.repr_total] at hc 
      rw [this] at hc 
      cases hc
      simp only [Algebra.id.smul_eq_mul, MulZeroClass.mul_zero] at hc_h 
      have hx := (Finsupp.mem_support_toFun l x).1 hx
      contradiction
    · exact not_j_lt_x x j hx h_1 hj
    exact H j hji (le_of_lt hjo) l hsub hl
  · -- induction base: i = 0
    have hi : i = 0 := Classical.not_not.1 hi
    rw [hi] at hsupp 
    simp only [Ordinal.not_lt_zero] at hsupp 
    have hsupp : (l.support : Set { i // i < o }) ⊆ ∅ := hsupp
    rw [subset_empty_iff, Finset.coe_eq_empty] at hsupp 
    rw [Finsupp.support_eq_empty.1 hsupp]
    simp only [Finsupp.support_eq_empty.1 hsupp, _root_.map_zero, zero_mem]

end AuxLemmas

-- Auxiliary lemma for comparing a span in a submodule with the span considered in the larger module.
theorem span_restrict (N : Submodule R M) (s : Set M) (hs : s ⊆ N.carrier) :
    ∀ x : N, x ∈ @Submodule.span R N _ _ _ (N.carrier.restrict s) ↔ (x : M) ∈ Submodule.span R s :=
  by
  intro x
  constructor
  · simp only [Submodule.mem_span]
    intro hx p hp
    let s' : Set N := N.carrier.restrict s
    have hp' : s' ⊆ comap N.subtype p
    intro y hy
    exact_mod_cast mem_of_subset_of_mem hp (hy : s y)
    have := hx (Submodule.comap N.subtype p) hp'
    simp only [mem_comap, Submodule.coeSubtype] at this 
    exact this
  · simp only [Submodule.mem_span]
    intro hx p hp
    have hp' : s ⊆ ↑(map N.subtype p)
    intro y hy
    simp only [map_coe, Submodule.coeSubtype, mem_image, SetLike.mem_coe]
    have hy' := mem_of_subset_of_mem hs hy
    refine' ⟨⟨y, hy'⟩, ⟨_, rfl⟩⟩
    have hy'' : N.carrier.restrict s ⟨y, hy'⟩
    simp only [restrict_apply, coe_mk]
    exact hy
    exact_mod_cast mem_of_subset_of_mem hp hy''
    have hx' := hx (Submodule.map N.subtype p) hp'
    simp at hx' 
    exact hx'

-- Auxiliary lemma for comparing a span in a submodule with the span considered in the larger module,
-- in the special case where the spanning set is the range of a map.
theorem span_range_codRestrict (N : Submodule R M) {α : Type _} (f : α → M) (h : ∀ x : α, f x ∈ N) :
    ∀ x : N,
      x ∈ @Submodule.span R N _ _ _ (range (codRestrict f N h)) ↔
        (x : M) ∈ Submodule.span R (range f) :=
  by
  have hr : range (codRestrict f N _) = N.carrier.restrict (range f)
  ext x
  simp
  constructor
  · rintro ⟨y, hy⟩
    use y
    have hy := congr_arg coe hy
    rw [coe_cod_restrict_apply] at hy 
    exact hy
    exact h
  · rintro ⟨y, hy⟩
    use y
    ext
    rw [coe_cod_restrict_apply]
    exact hy
  rw [hr]
  apply span_restrict
  rintro x ⟨a, rfl⟩
  exact h a

-- Equivalent of basis.reindex_apply for sets of indices.
theorem Basis.reindex_apply_image {ι ι' : Type _} (b : Basis ι R M) (e : ι ≃ ι') (s : Set ι') :
    b.reindex e '' s = b ∘ e.symm '' s := by
  ext x
  constructor
  all_goals
    rintro ⟨y, ⟨hy, rfl⟩⟩
    simp only [Basis.reindex_apply, Function.comp_apply, mem_image]
    refine' ⟨y, ⟨hy, rfl⟩⟩

-- Lemma on supports of finsupps, useful for finsupp.induction.
theorem Finsupp.support_single_add {α : Type _} {l : α →₀ M} {b : M} (hb : b ≠ 0) {i : α}
    (hi : i ∉ l.support) {s : Set α} (h : (Finsupp.support (Finsupp.single i b + l) : Set α) ⊆ s) :
    (Finsupp.support l : Set α) ⊆ s :=
  by
  haveI := Classical.typeDecidableEq α
  intro x hx
  by_cases hx' : x = i
  · have H : (Finsupp.single i b + l) i ≠ 0 := by
      simpa only [Finsupp.not_mem_support_iff.1 hi, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same, add_zero, Ne.def]
    -- note: squeeze_simp does not work with field notations
    rw [hx']
    exact mem_of_subset_of_mem h ((Finsupp.mem_support_toFun _ i).2 H)
  · have H : (Finsupp.single i b + l) x ≠ 0
    simp only [Finsupp.single_eq_of_ne (Ne.symm hx'), Finsupp.coe_add, Pi.add_apply, zero_add,
      Ne.def]
    exact (Finsupp.mem_support_toFun _ x).1 hx
    exact mem_of_subset_of_mem h (Finsupp.mem_support_iff.2 H)

-- Lemma on supports of finsupps, useful for finsupp.induction.
theorem Finsupp.mem_support_of_support_single_add {α : Type _} {l : α →₀ M} {b : M} (hb : b ≠ 0)
    {i : α} (hi : i ∉ l.support) {s : Set α}
    (h : (Finsupp.support (Finsupp.single i b + l) : Set α) ⊆ s) : i ∈ s :=
  by
  haveI := Classical.typeDecidableEq α
  have H : (Finsupp.single i b + l) i ≠ 0 := by
    simpa only [Finsupp.not_mem_support_iff.1 hi, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_eq_same, add_zero, Ne.def]
  exact mem_of_subset_of_mem h (Finsupp.mem_support_iff.2 H)

-- Has better def-eqs than `ordinal.enum_iso`. The mathlib fix is at #15454.
@[simps]
noncomputable def Ordinal.enumIso' {α} (r : α → α → Prop) [IsWellOrder α r] :
    Subrel (· < ·) (· < Ordinal.type r) ≃r r
    where
  toFun x := Ordinal.enum r x.1 x.2
  invFun x := ⟨Ordinal.typein r x, Ordinal.typein_lt_type r x⟩
  left_inv := fun ⟨o, h⟩ => Subtype.ext_val (Ordinal.typein_enum _ _)
  right_inv h := Ordinal.enum_typein _ _
  map_rel_iff' := by rintro ⟨a, _⟩ ⟨b, _⟩; apply Ordinal.enum_lt_enum

/-- A submodule of a free module over a principal ideal domain is free. -/
theorem Submodule.nonempty_basis_of_pid' [IsDomain R] [IsPrincipalIdealRing R] {ι : Type u}
    (b : Basis ι R M) (N : Submodule R M) : ∃ B : Type (u + 1), Nonempty (Basis B R N) :=
  by
  haveI : DecidableEq M := Classical.typeDecidableEq M
  -- Set up the data.
  let r := Classical.choose (Cardinal.ord_eq ι)
  haveI := Classical.choose (Classical.choose_spec (Cardinal.ord_eq ι))
  let o := Ordinal.type r
  let ords := { j : Ordinal // j < o }
  let enum : ords → ι := fun i => Ordinal.enum r i.1 i.2
  let seg : ords → Set ι := fun i => fun x => ¬r (enum i) x
  -- i.e. x ≤ i
  let F := fun i : ords => span R (image (coeFn b) (seg i))
  let U i := F i ⊓ N
  let V : ords → Submodule R N := fun i => (F i).comap N.subtype
  let V₁ : Ordinal → Submodule R N := fun i => dite (i < o) (fun p => V ⟨i, p⟩) fun p => 0
  have hU : ∀ i, U i ≤ N := fun i => inf_le_right
  let ideal := fun i : ords => Submodule.map (b.coord (enum i)) (U i)
  let a i := generator (Ideal i)
  let P x := a x ≠ 0
  have a_mem : ∀ i : ords, a i ∈ Ideal i := fun i => generator_mem _
  let u i := Exists.choose (a_mem i)
  have hu := fun i => Exists.choose_spec (a_mem i)
  let B : Basis ords R M := Basis.reindex b (Ordinal.enumIso' r).toEquiv.symm
  let good := { j : ords // a j ≠ 0 }
  let BB : good → N := cod_restrict (fun i => u i.1) N fun i => by apply hU i.1; exact (hu i.1).1
  have hu' : ∀ j : good, (B.coord j) (BB j) = a j.1 := fun j => by simpa using (hu j).2
  -- Prove lemmas about the data which are useful as hypotheses to the auxiliary lemmas above.
  have hc :
    ∀ i : Ordinal,
      ∀ l : ords →₀ R,
        Finsupp.total ords M R B l ∈ N →
          ((l.support : Set ords) ⊆ fun x => x.1 < i) →
            ∀ j : ords,
              i = succ j.1 → ∃ r : R, (B.coord j) (Finsupp.total ords M R B l) = r • a j :=
    by
    intro i l hl hsupp j hij
    have hI : (B.coord j) ((⇑(Finsupp.total ords M R ⇑B)) l) ∈ Ideal j
    refine' ⟨Finsupp.total ords M R B l, ⟨_, _⟩⟩
    dsimp [U]
    refine' ⟨_, hl⟩
    simp only [mem_span_set, Basis.coe_reindex, SetLike.mem_coe]
    use Finsupp.mapDomain B l
    constructor
    rw [Finsupp.mapDomain_support_of_injOn l (Set.injOn_of_injective (Basis.injective B) _)]
    simp only [B, Finset.coe_image, Basis.reindex_apply_image]
    have h : (Ordinal.enumIso' r).symm.toEquiv.symm '' (l.support : Set ords) ⊆ seg j
    simp only [Equiv.subset_image, RelIso.coe_fn_toEquiv]
    intro x hx
    use enum x
    have hxi := mem_of_subset_of_mem hsupp hx
    have hxi : x.1 < i := hxi
    rw [hij] at hxi 
    have hxj : x.1 ≤ j.1 := SuccOrder.le_of_lt_succ hxi
    constructor
    have goal : ¬r (enum j) (enum x)
    rwa [Ordinal.enum_le_enum]
    exact goal
    simp only [Ordinal.enumIso', Ordinal.typein_enum, Subtype.val_eq_coe, Subtype.coe_eta,
      RelIso.coe_fn_symm_mk, Equiv.coe_fn_symm_mk]
    rw [image_comp]
    exact image_subset b h
    simp only [Ordinal.enumIso', Subtype.val_eq_coe, Basis.coe_reindex, Equiv.coe_fn_symm_mk]
    rw [← @Finsupp.total_apply M M R _ _ _ (fun x => x) _]
    rw [Finsupp.total_mapDomain]
    rw [Function.Injective.of_comp_iff (Basis.injective b)]
    exact Equiv.injective (Ordinal.enumIso' r).toEquiv
    simpa [B, Ordinal.enumIso']
    rw [← Submodule.IsPrincipal.span_singleton_generator (Ideal j)] at hI 
    rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hI 
    rw [Submodule.IsPrincipal.span_singleton_generator] at hI 
    exact hI
  have hBBN : ∀ i, (BB i : M) ∈ N := fun i => by apply hU i.1; exact (hu i.1).1
  have hBB : ∀ i, (BB i : M) ∈ F i := by
    intro i
    simp [BB]
    have : U i ≤ F i := inf_le_left
    rw [← SetLike.coe_subset_coe] at this 
    have hi : u i ∈ U i := (hu i).1
    exact_mod_cast mem_of_subset_of_mem this hi
  have hcoordB : ∀ i : good, (B.coord i) (BB i) ≠ 0 := fun i => by rw [hu'] <;> exact i.2
  have hBB' : ∀ i, (Finsupp.support (B.repr (BB i)) : Set ords) ⊆ fun x => x.1 ≤ i :=
    by
    intro i x hx
    have h := hBB i
    rw [mem_span_set] at h 
    rcases h with ⟨l, ⟨hsupp, hl⟩⟩
    simp [B] at hx 
    simp [BB] at hl 
    let l' := Finsupp.comapDomain b l (Set.injOn_of_injective (Basis.injective b) _)
    have hsupp' : (l.support : Set M) ⊆ range ⇑b :=
      subset.trans hsupp (Set.image_subset_range b (seg i))
    have hrepr :=
      Finsupp.total_comap_domain' (fun i => i) b l (Set.injOn_of_injective (Basis.injective b) _)
        hsupp'
    have hrepr : (Finsupp.total ι M R ((fun i => i) ∘ b)) l' = ∑ i : M in l.support, l i • i :=
      hrepr
    dsimp [Finsupp.sum] at hl 
    rw [← hrepr] at hl 
    rw [← hl] at hx 
    simp [Ordinal.enumIso] at hx 
    rw [← Ne.def, ← Finsupp.mem_support_iff] at hx 
    have hx := mem_of_subset_of_mem hsupp hx
    rw [Function.Injective.mem_set_image (Basis.injective b)] at hx 
    apply (Ordinal.enum_le_enum r x.2 i.1.2).1
    assumption
  have hB_BB :
    ∀ i : Ordinal,
      ∀ l : good →₀ R,
        ((l.support : Set good) ⊆ fun x => x.1.1 < i) →
          ∃ lB : ords →₀ R,
            ((lB.support : Set ords) ⊆ fun x => x.1 < i) ∧
              Finsupp.total ords M R B lB = Finsupp.total good N R BB l :=
    by
    intro i l
    apply @Finsupp.induction good R _ _ l
    · intro
      use 0
      simp only [Finsupp.support_zero, Finset.coe_empty, empty_subset, _root_.map_zero, coe_zero,
        eq_self_iff_true, and_self_iff]
    · intro j r l hj hr hl hl'
      have hlsupp := Finsupp.support_single_add hr hj hl'
      have hl := hl hlsupp
      rcases hl with ⟨lB, ⟨hlBsupp, hlBtot⟩⟩
      use lB + r • B.repr (BB j)
      constructor
      have hj' := Finsupp.mem_support_of_support_single_add hr hj hl'
      have hj' : j.1.1 < i := hj'
      have hBBjsupp : (Finsupp.support (B.repr (BB j)) : Set ords) ⊆ fun x => x.1 < i :=
        by
        intro x hx
        have := mem_of_subset_of_mem (hBB' j) hx
        have : x.1 ≤ j := this
        exact lt_of_le_of_lt this hj'
      let lB₀ : Finsupp.supported R R (fun x => x.1 < i : Set ords) := ⟨lB, hlBsupp⟩
      let BBj₀ : Finsupp.supported R R (fun x => x.1 < i : Set ords) := ⟨B.repr (BB j), hBBjsupp⟩
      let l'₀ := lB₀ + r • BBj₀
      exact l'₀.2
      simp only [map_add, LinearMap.map_smulₛₗ, RingHom.id_apply, Finsupp.total_single, coe_add,
        coe_smul_of_tower, Basis.total_repr, hlBtot]
      rw [add_comm]
  -- Prove linear independence.
  have HH₁ :
    ∀ j : Ordinal,
      j ≤ o →
        ∀ l : good →₀ R,
          ((l.support : Set good) ⊆ fun x : good => x.1.1 < j) →
            (Finsupp.total good N R BB) l = 0 → l = 0 :=
    by
    intro j hj
    apply
      @Ordinal.induction fun j =>
        j ≤ o →
          ∀ l : good →₀ R,
            ((l.support : Set good) ⊆ fun x : good => x.1.1 < j) →
              (Finsupp.total good N R BB) l = 0 → l = 0
    dsimp
    intro i H hio l hsupp hl
    by_cases hlim : Ordinal.IsLimit i
    · exact lin_ind_limit hio hlim H hsupp hl
    · exact lin_ind_succ hB_BB hcoordB hio hlim H hsupp hl
    exact hj
  have H₁ : LinearIndependent R BB :=
    by
    rw [linearIndependent_iff]
    intro l hl
    have hsupp : (l.support : Set good) ⊆ fun x : good => x.1.1 < o := fun x _ => x.1.2
    exact HH₁ o (le_refl o) l hsupp hl
  -- Prove the span property.
  have HH₂ :
    ∀ j : Ordinal,
      j ≤ o →
        ∀ l : ords →₀ R,
          ((l.support : Set ords) ⊆ fun x => x.1 < j) →
            Finsupp.total ords M R B l ∈ N →
              Finsupp.total ords M R B l ∈ Submodule.span R (range fun i : good => u i.1) :=
    by
    intro j hj
    apply
      @Ordinal.induction fun k =>
        k ≤ o →
          ∀ l : { i // i < o } →₀ R,
            ((l.support : Set { i // i < o }) ⊆ fun x => x.1 < k) →
              Finsupp.total { i // i < o } M R B l ∈ N →
                Finsupp.total { i // i < o } M R B l ∈
                  Submodule.span R (range fun i : good => u i.1)
    dsimp
    intro i H hio l hsupp hl
    by_cases hlim : Ordinal.IsLimit i
    · exact span_limit hio hlim H hsupp hl
    · exact span_succ hio hlim H hsupp hl hBB' (hc i l hl hsupp) hBBN hu'
    exact hj
  have H₂ : ⊤ ≤ Submodule.span R (range BB) :=
    by
    rintro x -
    let l := B.repr (x : M)
    have hl : Finsupp.total ords M R B l ∈ N := by simp only [l, Basis.total_repr] <;> exact x.2
    have hx := HH₂ o (le_refl o) l _ hl
    simp only [l, Basis.total_repr] at hx 
    rw [span_range_codRestrict N (fun i : good => u i.1) _ x]
    exact hx
    intro y _
    exact y.2
  exact ⟨good, ⟨Basis.mk H₁ H₂⟩⟩

@[instance]
theorem Submodule.free_of_pid_of_free [IsDomain R] [IsPrincipalIdealRing R] {N : Submodule R M}
    [Module.Free R M] : Module.Free R N :=
  by
  have h := (Submodule.nonempty_basis_of_pid' (Module.Free.chooseBasis R M) N).choose_spec
  cases h
  exact Module.Free.of_basis h

