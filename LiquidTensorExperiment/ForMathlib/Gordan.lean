import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness
import Mathlib.Topology.ContinuousFunction.Algebra
import LiquidTensorExperiment.ForMathlib.Nnrat
import LiquidTensorExperiment.ForMathlib.RationalCones

#align_import for_mathlib.Gordan

/-!

# Gordan's Lemma

-/


universe u

variable {Λ : Type u} [AddCommGroup Λ]

variable {ι : Type _}

open scoped BigOperators NNRat

def explicitDualSet (l : ι → Λ) : Submodule ℕ (Λ →+ ℤ)
    where
  carrier := {x | ∀ i, 0 ≤ x (l i)}
  zero_mem' i := le_rfl
  add_mem' x y hx hy i := add_nonneg (hx i) (hy i)
  smul_mem' n x hx i := nsmul_nonneg (hx i) n

theorem mem_explicitDualSet (l : ι → Λ) (x : Λ →+ ℤ) : x ∈ explicitDualSet l ↔ ∀ i, 0 ≤ x (l i) :=
  Iff.rfl

def dualFinset (S : Finset Λ) : Submodule ℕ (Λ →+ ℤ) :=
  explicitDualSet (coe : (S : Set Λ) → Λ)

theorem mem_dualFinset (S : Finset Λ) (l : Λ →+ ℤ) : l ∈ dualFinset S ↔ ∀ x ∈ S, 0 ≤ l x :=
  by
  rw [dualFinset, mem_explicitDualSet]
  simp

theorem dualFinset_antimono {S T : Finset Λ} (hST : S ⊆ T) : dualFinset T ≤ dualFinset S :=
  by
  rintro φ hφ ⟨i, his : i ∈ S⟩
  exact hφ ⟨i, hST his⟩

theorem explicitDualSet_eq_dualFinset [DecidableEq Λ] [Fintype ι] (l : ι → Λ) :
    explicitDualSet l = dualFinset (Finset.image l Finset.univ) :=
  by
  ext φ
  constructor
  · rintro hφ ⟨t, ht : t ∈ Finset.image _ _⟩
    rw [Finset.mem_image] at ht 
    rcases ht with ⟨i, -, rfl⟩
    exact hφ i
  · rintro hφ i
    refine' hφ ⟨l i, (_ : l i ∈ Finset.image _ _)⟩
    rw [Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩

def intersectHalfspaces (l : ι → Λ →+ ℤ) : Submodule ℕ Λ
    where
  carrier := {x | ∀ i, 0 ≤ l i x}
  zero_mem' i := by simp only [AddMonoidHom.map_zero]
  add_mem' x y hx hy i := by
    simp only [AddMonoidHom.map_add]
    apply add_nonneg (hx i) (hy i)
  smul_mem' c x hx i := by
    simp only [nsmul_eq_mul, AddMonoidHom.map_nsmul]
    apply mul_nonneg (Int.ofNat_zero_le c) (hx i)

theorem mem_intersectHalfspaces (l : ι → Λ →+ ℤ) (x : Λ) :
    x ∈ intersectHalfspaces l ↔ ∀ i, 0 ≤ l i x :=
  Iff.rfl

def intersectHalfspacesSet (s : Set (Λ →+ ℤ)) : Submodule ℕ Λ :=
  intersectHalfspaces (coe : (s : Set (Λ →+ ℤ)) → Λ →+ ℤ)

theorem mem_intersectHalfspacesSet (S : Set (Λ →+ ℤ)) (x : Λ) :
    x ∈ intersectHalfspacesSet S ↔ ∀ f : Λ →+ ℤ, f ∈ S → 0 ≤ f x :=
  by
  rw [intersectHalfspacesSet, mem_intersectHalfspaces]
  simp

variable {α : Type _}

def toRationalPoint : (α → ℤ) →ₗ[ℤ] α → ℚ
    where
  toFun f x := f x
  map_add' f g := by ext1 x; simp only [Int.cast_add, Pi.add_apply]
  map_smul' m f := by
    ext1 x;
    simp only [zsmul_eq_mul, Pi.mul_apply, Int.cast_mul, eq_intCast, mul_eq_mul_right_iff,
      Int.cast_eq_zero]
    left; rfl

@[simp]
theorem toRationalPoint_apply (x : α → ℤ) (i : α) : toRationalPoint x i = x i :=
  rfl

theorem toRationalPoint_injective : Function.Injective (toRationalPoint : (α → ℤ) → α → ℚ) :=
  by
  intro x y h
  ext i
  rw [Function.funext_iff] at h 
  specialize h i
  simpa using h

def latticeRestrict (S : Submodule ℚ≥0 (α → ℚ)) : Submodule ℕ (α → ℤ)
    where
  carrier := toRationalPoint ⁻¹' (S : Set (α → ℚ))
  zero_mem' := by
    simp only [LinearMap.map_zero, Set.mem_preimage, SetLike.mem_coe, Submodule.zero_mem]
  add_mem' a b (ha : toRationalPoint a ∈ S) (hb : toRationalPoint b ∈ S) :=
    by
    change toRationalPoint (a + b) ∈ S
    simp only [LinearMap.map_add]
    apply S.add_mem ha hb
  smul_mem' c x (hx : toRationalPoint x ∈ S) :=
    by
    change toRationalPoint (c • x) ∈ S
    rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_of_tower_mem S c hx

theorem mem_latticeRestrict (S : Submodule ℚ≥0 (α → ℚ)) (x : α → ℤ) :
    x ∈ latticeRestrict S ↔ toRationalPoint x ∈ S :=
  Iff.rfl

def IsInteger (x : ℚ) :=
  ∃ z : ℤ, x = z

def IsIntegerPoint (x : α → ℚ) :=
  ∀ a, IsInteger (x a)

def floorPoint (x : α → ℚ) : α → ℤ := fun i => ⌊x i⌋

theorem floorPoint_eq_of_isIntegerPoint (x : α → ℚ) (hx : IsIntegerPoint x) :
    (fun i => floorPoint x i : α → ℚ) = x := by
  ext1 i
  obtain ⟨z, hz⟩ := hx i
  simp [floorPoint, hz]

theorem exists_scalings {ι : Type _} (s : Finset ι) (v : ι → ℚ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i ∈ s, IsInteger (n • v i) := by
  classical
  apply Finset.induction_on s
  · exact ⟨1, by norm_num, by simp⟩
  · rintro x s hx ⟨m, hm₁, hm₂⟩
    refine' ⟨m * (v x).den, mul_pos hm₁ (v x).Pos, _⟩
    simp only [forall_eq_or_imp, nsmul_eq_mul, Finset.mem_insert, Nat.cast_mul]
    refine' ⟨⟨m * (v x).num, _⟩, _⟩
    · push_cast
      rw [mul_assoc]
      norm_cast
      rw [mul_comm ((v x).den : ℚ), Rat.mul_den_eq_num]
      norm_cast
    intro y hy
    obtain ⟨z, hz⟩ := hm₂ y hy
    rw [mul_right_comm]
    refine' ⟨z * (v x).den, _⟩
    push_cast
    rw [← hz]
    simp

theorem point_exists_scaling {α : Type _} [Fintype α] (x : α → ℚ) :
    ∃ n : ℕ, 0 < n ∧ IsIntegerPoint (n • x) :=
  let ⟨m, hm₁, hm₂⟩ := exists_scalings Finset.univ x
  ⟨m, hm₁, fun a => by simpa using hm₂ a⟩

open scoped Classical

noncomputable def scaleFactor {α : Type _} [Fintype α] (x : α → ℚ) : ℕ :=
  Nat.find (point_exists_scaling x)

theorem scaleFactor_pos {α : Type _} [Fintype α] (x : α → ℚ) : 0 < scaleFactor x :=
  (Nat.find_spec (point_exists_scaling x)).1

theorem rat_scaleFactor_ne_zero {α : Type _} [Fintype α] (x : α → ℚ) : (scaleFactor x : ℚ) ≠ 0 :=
  by
  norm_cast
  apply (scaleFactor_pos x).ne'

noncomputable def scaleUp {α : Type _} [Fintype α] (x : α → ℚ) : α → ℤ :=
  floorPoint (scaleFactor x • x)

theorem scaleUp_is {α : Type _} [Fintype α] (x : α → ℚ) :
    (fun i : α => ↑(scaleUp x i)) = scaleFactor x • x :=
  floorPoint_eq_of_isIntegerPoint _ (Nat.find_spec (point_exists_scaling x)).2

theorem scaleUp_coord {α : Type _} [Fintype α] (x : α → ℚ) (a : α) :
    (scaleUp x a : ℚ) = scaleFactor x * x a :=
  by
  suffices (scaleUp x a : ℚ) = (scaleFactor x • x) a by simpa using this
  rw [← scaleUp_is]

theorem toRationalPoint_scaleUp {α : Type _} [Fintype α] (x : α → ℚ) :
    toRationalPoint (scaleUp x) = scaleFactor x • x :=
  by
  ext1 i
  simp only [scaleUp_coord, toRationalPoint_apply, nsmul_eq_mul, Pi.mul_apply, mul_eq_mul_right_iff]
  left; rfl

example {a b : ℤ} : (a : ℚ) = b → a = b := fun h => (Rat.coe_int_inj a b).mp h

noncomputable def upgradeFunctional {α : Type _} [Fintype α] (f : (α → ℤ) →+ ℤ) : (α → ℚ) →ₗ[ℚ] ℚ
    where
  toFun g := (f (scaleUp g) : ℚ) / scaleFactor g
  map_add' g₁ g₂ := by
    field_simp [rat_scaleFactor_ne_zero]
    norm_cast
    suffices
      f ((scaleFactor g₁ * scaleFactor g₂) • scaleUp (g₁ + g₂)) =
        f (scaleFactor (g₁ + g₂) • (scaleFactor g₂ • scaleUp g₁ + scaleFactor g₁ • scaleUp g₂))
      by
      simp only [AddMonoidHom.map_nsmul, AddMonoidHom.map_add] at this 
      simp only [nsmul_eq_mul, mul_comm _ (f _)] at this 
      rw [this]
      apply mul_comm
    congr 1
    ext1 a
    simp only [Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, Int.ofNat_mul, mul_add]
    rw [← Rat.coe_int_inj]
    push_cast
    simp only [scaleUp_coord, Pi.add_apply]
    ring!
  map_smul' m x := by
    simp only [Algebra.id.smul_eq_mul]
    rw [← Rat.num_div_den m]
    field_simp [rat_scaleFactor_ne_zero, m.pos.ne', -Rat.num_div_den]
    simp only [Rat.num_div_den]
    norm_cast
    suffices
      f ((m.denom * scaleFactor x) • scaleUp (m • x)) =
        f ((scaleFactor (m • x) * m.num : ℤ) • scaleUp x)
      by
      simp only [AddMonoidHom.map_zsmul, AddMonoidHom.map_nsmul] at this 
      simp only [Int.ofNat_mul]
      simp only [Algebra.id.smul_eq_mul, Rat.num_div_den, nsmul_eq_mul, Int.ofNat_mul] at this 
      rw [mul_comm (f _), this, mul_comm _ m.num, mul_right_comm]
    congr 1
    ext1 a
    simp only [Pi.smul_apply]
    simp only [Algebra.id.smul_eq_mul, nsmul_eq_mul, Int.ofNat_mul]
    rw [← Rat.coe_int_inj]
    push_cast
    simp only [scaleUp_coord, Pi.smul_apply, Algebra.id.smul_eq_mul, ← Rat.mul_den_eq_num]
    ring!

theorem upgrade_id {α : Type _} [Fintype α] (f : (α → ℤ) →+ ℤ) (g : α → ℤ) :
    upgradeFunctional f (toRationalPoint g) = f g :=
  by
  dsimp [upgradeFunctional, toRationalPoint]
  rw [div_eq_iff (rat_scaleFactor_ne_zero _)]
  norm_cast
  rw [mul_comm, ← nsmul_eq_mul, ← AddMonoidHom.map_nsmul]
  congr 1
  ext a
  simp only [nsmul_eq_mul, Pi.mul_apply]
  rw [← Rat.coe_int_inj]
  rw [scaleUp_coord]
  norm_cast

section

theorem finitely_generated_iff_integrally_generated [Fintype α] (C : Submodule ℚ≥0 (α → ℚ)) :
    C.FG ↔ ∃ S : Finset (α → ℤ), Submodule.span ℚ≥0 (S.image toRationalPoint : Set (α → ℚ)) = C :=
  by
  constructor
  · rintro ⟨S, rfl⟩
    refine' ⟨S.image scaleUp, _⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x
      simp only [toRationalPoint_scaleUp, and_imp, Set.mem_image, Finset.mem_coe,
        exists_exists_and_eq_and, SetLike.mem_coe, exists_imp, Finset.coe_image]
      rintro y hy rfl
      have : y ∈ Submodule.span ℚ≥0 (S : Set (α → ℚ)) := Submodule.subset_span hy
      have z := Submodule.smul_mem _ (scaleFactor y : ℚ≥0) this
      convert z using 1
      ext1 i
      simp only [nsmul_eq_mul, Pi.smul_apply]
      rfl
    · rw [Submodule.span_le]
      intro x
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.coe_image, ← Set.image_comp]
      intro hx
      have : scaleFactor x • x ∈ toRationalPoint ∘ scaleUp '' (S : Set (α → ℚ)) :=
        by
        refine' ⟨_, hx, _⟩
        simp only [nsmul_eq_mul, Function.comp_apply, toRationalPoint_scaleUp]
      have :
        scaleFactor x • x ∈ Submodule.span ℚ≥0 (toRationalPoint ∘ scaleUp '' (S : Set (α → ℚ))) :=
        Submodule.subset_span this
      have hx₂ := Submodule.smul_mem _ ((scaleFactor x)⁻¹ : ℚ≥0) this
      convert hx₂ using 1
      ext1 i
      simp only [nsmul_eq_mul, Pi.mul_apply, Pi.smul_apply]
      change _ = _ * (_ * _)
      simp
      rw [← mul_assoc]
      convert (one_mul (x i)).symm
      convert inv_mul_cancel _
      apply rat_scaleFactor_ne_zero
  · rintro ⟨S, rfl⟩
    refine' ⟨_, rfl⟩

theorem finitely_generated_iff_integrally_generated_type {α : Type u} [Fintype α]
    (C : Submodule ℚ≥0 (α → ℚ)) :
    C.FG ↔
      ∃ (ι : Type u) (s : Finset ι) (v : ι → α → ℤ) (hv : Function.Injective v),
        Submodule.span ℚ≥0 (s.image fun i => toRationalPoint (v i) : Set (α → ℚ)) = C :=
  by
  rw [finitely_generated_iff_integrally_generated]
  constructor
  · rintro ⟨S, rfl⟩
    refine' ⟨_, S, id, fun _ _ h => h, rfl⟩
  · rintro ⟨ι, s, v, _, rfl⟩
    refine' ⟨s.image v, _⟩
    rw [Finset.image_image]

theorem bounded_lattice_thing [Fintype α] {k : α → ℕ} (C : Set (α → ℤ))
    (hC : ∀ (x : α → ℤ) (i), x ∈ C → Int.natAbs (x i) ≤ k i) : C.Finite := by
  classical
  let C' : Finset (α → ℤ) :=
    (finset.univ.pi fun i => Finset.Ico (-(k i : ℤ)) (k i + 1)).image fun f a =>
      f a (Finset.mem_univ _)
  have : C ⊆ C' := by
    intro x hx
    simp only [Set.mem_image, Finset.mem_univ, Finset.mem_pi, forall_true_left, Finset.mem_coe,
      Finset.mem_Ico, Finset.coe_image]
    refine' ⟨fun a _ => x a, fun a => _, _⟩
    · have : abs (x a) ≤ k a := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hC x a hx
      rw [abs_le] at this 
      refine' ⟨this.1, _⟩
      rw [Int.lt_add_one_iff]
      apply this.2
    rfl
  apply Set.Finite.subset _ this
  exact Finset.finite_toSet C'

theorem Finset.sum_natAbs_le {ι : Type _} (s : Finset ι) (f : ι → ℤ) :
    (∑ i in s, f i).natAbs ≤ ∑ i in s, (f i).natAbs :=
  Finset.le_sum_of_subadditive _ rfl Int.natAbs_add_le _ _

theorem floor_add_floor_le {α : Type _} [LinearOrderedRing α] [FloorRing α] (x y : α) :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ := by
  rw [Int.le_floor, Int.cast_add]
  apply add_le_add (Int.floor_le x) (Int.floor_le y)

theorem Finset.floor_le {α : Type _} [LinearOrderedRing α] [FloorRing α] {ι : Type _} (s : Finset ι)
    (f : ι → α) : ∑ i in s, ⌊f i⌋ ≤ ⌊∑ i in s, f i⌋ :=
  by
  apply Finset.induction_on s
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    apply le_trans (add_le_add_left ih _) (floor_add_floor_le _ _)

theorem ceil_add_le {α : Type _} [LinearOrderedRing α] [FloorRing α] (x y : α) :
    ⌈x + y⌉ ≤ ⌈x⌉ + ⌈y⌉ := by
  rw [Int.ceil_le, Int.cast_add]
  apply add_le_add (Int.le_ceil x) (Int.le_ceil y)

theorem Finset.le_ceil {α : Type _} [LinearOrderedRing α] [FloorRing α] {ι : Type _} (s : Finset ι)
    (f : ι → α) : ⌈∑ i in s, f i⌉ ≤ ∑ i in s, ⌈f i⌉ :=
  Finset.le_sum_of_subadditive _ (by simp) ceil_add_le _ _

theorem natAbs_lt_natAbs_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) :
    a.natAbs < b.natAbs := by
  lift b to ℕ using le_trans w₁ (le_of_lt w₂)
  lift a to ℕ using w₁
  simpa using w₂

theorem Int.coe_sum {α : Type _} (f : α → ℕ) (s : Finset α) :
    ∑ x : α in s, (f x : ℤ) = (↑(∑ i in s, f i) : ℤ) :=
  by
  apply Finset.induction_on s
  · simp
  · intro i t hi ih
    simp only [Finset.sum_insert hi, ih]
    simp

theorem Finset.mem_span_iff {R M : Type _} [Ring R] [AddCommMonoid M] [Module R M] (S : Finset M)
    (x : M) : x ∈ Submodule.span R (S : Set M) ↔ ∃ w : M → R, ∑ i in S, w i • i = x :=
  mem_span_finset

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.proofs -/
set_option pp.proofs true

theorem missing [Fintype α] (w : α → ℤ) (n : ℕ) :
    toRationalPoint (n • w) = (n : ℚ≥0) • toRationalPoint w :=
  by
  simp only [nsmul_eq_mul]
  induction n
  · simp
  · simp [add_smul, ← n_ih, add_mul]

theorem my_result [Fintype α] (C : Submodule ℚ≥0 (α → ℚ)) (hC : C.FG) : (latticeRestrict C).FG :=
  by
  rw [finitely_generated_iff_integrally_generated_type] at hC 
  rcases hC with ⟨ι, s, w, hw, rfl⟩
  let B :=
    {x : α → ℤ |
      ∃ w' : ι → ℚ≥0,
        (∀ i ∈ s, w' i < 1) ∧ ∑ i in s, w' i • toRationalPoint (w i) = toRationalPoint x}
  let k : α → ℕ := fun a => ∑ i in s, Int.natAbs (w i a)
  have : ∀ (x : α → ℤ) (a), x ∈ B → Int.natAbs (x a) ≤ k a :=
    by
    rintro x a ⟨w', hw', hw''⟩
    have hw''' : (∑ i : ι in s, w' i • toRationalPoint (w i)) a = toRationalPoint x a := by
      rw [hw'']
    simp only [Finset.sum_apply, Algebra.id.smul_eq_mul, toRationalPoint_apply, Pi.smul_apply] at
      hw''' 
    change ∑ c : ι in s, (w' c : ℚ) * w c a = x a at hw''' 
    clear hw''
    have : abs (∑ c : ι in s, (w' c : ℚ) * w c a) ≤ ∑ c : ι in s, abs (w c a) :=
      by
      apply le_trans (Finset.abs_sum_le_sum_abs _ _) _
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_of_le_one_left
      exact abs_nonneg (w i a)
      rw [abs_le]
      refine' ⟨_, (hw' i hi).le⟩
      apply le_trans (show (-1 : ℚ) ≤ 0 by norm_num) (w' i).2
    rw [hw'''] at this 
    norm_cast at this 
    simp only [Int.abs_eq_natAbs] at this 
    rw [Int.coe_sum] at this 
    norm_cast at this 
    apply this
  let B' := Set.Finite.toFinset (bounded_lattice_thing _ this)
  refine' ⟨B' ∪ s.image w, _⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    simp only [Set.union_subset_iff, Finset.coe_union, Set.Finite.coe_toFinset]
    constructor
    · rintro x ⟨w', hw', hw''⟩
      change toRationalPoint x ∈ _
      rw [← hw'']
      simp only [SetLike.mem_coe]
      refine' Submodule.sum_smul_mem _ _ _
      intro i hi
      apply Submodule.subset_span
      simp only [Set.mem_image, Finset.mem_coe, Finset.coe_image]
      refine' ⟨_, hi, rfl⟩
    · simp only [Set.image_subset_iff, Finset.coe_image]
      intro x hx
      change toRationalPoint (w x) ∈ _
      apply Submodule.subset_span
      refine' ⟨_, hx, rfl⟩
  · rintro x (hx : toRationalPoint _ ∈ _)
    simp only [SetLike.mem_coe, mem_span_finset] at hx 
    rcases hx with ⟨f, hf⟩
    rw [Finset.sum_image] at hf 
    · simp only [Finset.coe_union, Set.Finite.coe_toFinset, Finset.coe_image]
      let f' : ι → ℚ≥0 := fun i => f (toRationalPoint (w i))
      let ns : ι → ℕ := fun i => ⌊(f' i : ℚ)⌋.natAbs
      let g' : ι → ℚ≥0 := fun i => f' i - ns i
      have ns' : ∀ i, (ns i : ℤ) = ⌊(f' i : ℚ)⌋ :=
        by
        intro i
        change (Int.natAbs _ : ℤ) = _
        rw [← Int.abs_eq_natAbs, abs_of_nonneg]
        rw [Int.floor_nonneg]
        apply (f' i).2
      have hg' : ∀ i, (g' i : ℚ) = f' i - ns i :=
        by
        intro i
        change max _ _ = _
        simp only [NNRat.coe_natCast]
        rw [max_eq_left]
        rw [sub_nonneg]
        change (Int.natAbs _ : ℚ) ≤ _
        suffices ((Int.natAbs ⌊(f' i : ℚ)⌋ : ℤ) : ℚ) ≤ f' i by simpa using this
        rw [ns']
        apply Int.floor_le
      change ∑ x in s, f' x • toRationalPoint (w x) = toRationalPoint x at hf 
      -- have :  ≤ ↑(f' i) - ↑(ns i)
      have : ∀ i, (ns i : ℚ≥0) + g' i = f' i := by
        intro i
        apply NNRat.coe_injective
        rw [NNRat.coe_add, hg']
        simp
      simp_rw [← this, add_smul, Finset.sum_add_distrib] at hf 
      let x_floors := ∑ x : ι in s, ns x • w x
      have : x - x_floors ∈ B := by
        refine' ⟨g', _, _⟩
        · intro i hi
          rw [← NNRat.coe_lt_coe]
          rw [hg']
          simp only [NNRat.coe_one]
          suffices (f' i : ℚ) - ((ns i : ℤ) : ℚ) < 1 by simpa using this
          rw [ns']
          apply Int.fract_lt_one
        rw [LinearMap.map_sub]
        rw [map_sum]
        rw [eq_sub_iff_add_eq']
        rw [← hf]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply missing
      · have : x = x - x_floors + x_floors := by simp
        rw [this]
        refine' Submodule.add_mem _ _ _
        · apply Submodule.subset_span
          left
          apply ‹x - x_floors ∈ B›
        apply Submodule.sum_smul_mem _ ns _
        intro i hi
        apply Submodule.subset_span
        right
        refine' ⟨_, hi, rfl⟩
    intro x hx y hy t
    apply hw
    apply toRationalPoint_injective t

end

-- instance {α : Type*} [fintype α] : finite_dimensional ℚ (α → ℚ) :=
-- @is_noetherian_pi _ _ _ _ _ _ _ (λ i, infer_instance)
theorem finset_Gordan_aux_pi {α : Type _} [Fintype α] (S : Finset ((α → ℤ) →+ ℤ)) :
    (intersectHalfspacesSet (S : Set ((α → ℤ) →+ ℤ))).FG := by
  classical
  let S' : Finset ((α → ℚ) →ₗ[ℚ] ℚ) := S.image upgradeFunctional
  suffices
    latticeRestrict (setDownOne (S' : Set ((α → ℚ) →ₗ[ℚ] ℚ))) =
      intersectHalfspacesSet (S : Set ((α → ℤ) →+ ℤ))
    by
    rw [← this]
    apply my_result
    rw [← fG_iff_isPolyhedralCone]
    rw [isPolyhedralCone_iff_finset]
    refine' ⟨_, rfl⟩
  ext x
  simp [mem_latticeRestrict, mem_intersectHalfspacesSet, upgrade_id]

/-- A finset version of Gordan's Lemma. -/
theorem finset_Gordan_aux [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (S : Finset (Λ →+ ℤ)) :
    (intersectHalfspacesSet (S : Set (Λ →+ ℤ))).FG := by
  classical
  have e := LinearEquiv.restrictScalars ℕ (Module.Free.chooseBasis ℤ Λ).equivFun
  -- deliberately forget the data here, it makes the simp at the end easier
  let e' : (Λ →+ ℤ) → (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) →+ ℤ := fun f =>
    f.comp e.symm.to_linear_map.to_add_monoid_hom
  let L :=
    (intersectHalfspacesSet ↑(S.image e')).map
      (e.symm : (Module.Free.ChooseBasisIndex ℤ Λ → ℤ) →ₗ[ℕ] Λ)
  have : L.fg := Submodule.FG.map _ (finset_Gordan_aux_pi (S.image e'))
  suffices L = intersectHalfspacesSet (S : Set (Λ →+ ℤ)) by rwa [← this]
  ext x
  simp [mem_intersectHalfspacesSet, LinearEquiv.symm_apply_eq]

/-- A finset version of Gordan's Lemma. -/
theorem finset_Gordan [Module.Finite ℤ Λ] [Module.Free ℤ Λ] (S : Finset Λ) : (dualFinset S).FG := by
  classical
  let S' : Finset ((Λ →+ ℤ) →+ ℤ) := S.image AddMonoidHom.eval
  letI := Module.Free.addMonoidHom Λ ℤ
  --RB: not sure why this is needed
  have := finset_Gordan_aux S'
  convert this using 1
  ext x
  simp [mem_dualFinset, mem_intersectHalfspacesSet]

/-- A fintype version of Gordan's Lemma. -/
theorem explicit_gordan [Module.Finite ℤ Λ] [Module.Free ℤ Λ] [Fintype ι] (l : ι → Λ) :
    (explicitDualSet l).FG := by
  classical
  rw [explicitDualSet_eq_dualFinset]
  apply finset_Gordan

