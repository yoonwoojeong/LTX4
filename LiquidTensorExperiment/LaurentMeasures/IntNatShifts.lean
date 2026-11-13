import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Analysis.SpecificLimits.Normed

#align_import laurent_measures.int_nat_shifts

/- These are lemmas that are used in the proof of either auxilliary facts for Theorem 6.9 or
for Theorem 6.9 directly. -/
/- These are lemmas that are used in the proof of either auxilliary facts for Theorem 6.9 or
for Theorem 6.9 directly. -/
open Function Metric Finset NNReal NormedField

open scoped NNReal Classical BigOperators TopologicalSpace

namespace AuxThm69

section GroupAddNeg

variable {G : Type _} [Group G]

/-- If `G` is a group and `g ∈ G` is an element, then `equiv.group_mul g` is the self-equivalence
of `G` defined by `h ↦ g * h`. -/
@[to_additive
      "If `G` is an additive group and `g ∈ G` is an element, then `equiv.add_group_add g`\nis the self-equivalence of `G` defined by `h ↦ g + h`."]
def Equiv.groupMul (g : G) : G ≃ G :=
  ⟨fun x => g * x, fun x => g⁻¹ * x, by intro; simp, by intro; simp⟩

@[simp, to_additive]
theorem Equiv.groupMul_apply {g h : G} : Equiv.groupMul g h = g * h :=
  rfl

@[simp, to_additive]
theorem Equiv.groupMul_symm_apply {g h : G} : (Equiv.groupMul g).symm h = g⁻¹ * h :=
  rfl

variable [LE G] [CovariantClass G G (· * ·) (· ≤ ·)]

@[to_additive]
theorem aux_ineq_hMul {d e x : G} (hx : d ≤ x) : e ≤ e * d⁻¹ * x :=
  calc
    e ≤ e * (d⁻¹ * x) := le_mul_of_one_le_right' (le_inv_mul_iff_le.mpr hx)
    _ = e * d⁻¹ * x := (mul_assoc _ _ _).symm

/-- If `G` is a group and `d e : G`. then `mul_inv_fun d e` is the function mapping
`{x // d ≤ x}` to `{x // e ≤ x}` defined by `x ↦ e * d⁻¹ * x`. -/
@[to_additive
      "If `G` is an additive group and `d e : G`. then `add_neg_fun d e` is the function\nmapping `{x // d ≤ x}` to `{x // e ≤ x}` defined by `x ↦ e + (- d) + x`."]
def mulInvFun (d e : G) : { x // d ≤ x } → { x // e ≤ x } := fun ⟨x, hx⟩ => ⟨_, aux_ineq_hMul hx⟩

@[to_additive]
theorem mulInvFun_def (d e : G) (z : { x // d ≤ x }) : mulInvFun d e z = ⟨_, aux_ineq_hMul z.2⟩ :=
  by cases z; simp [mul_inv_fun]

@[simp, to_additive]
theorem mulInvFun_comp (d e f : G) : mulInvFun e f ∘ mulInvFun d e = mulInvFun d f := by funext;
  simp [mul_inv_fun_def, mul_assoc]

@[simp, to_additive]
theorem mulInvFun_comp_id (d e : G) : mulInvFun e d ∘ mulInvFun d e = id := by funext;
  simp [mul_inv_fun_def]

@[simp, to_additive]
theorem mulInvFun_comp_id_apply (d e : G) (z : { x // d ≤ x }) :
    mulInvFun e d (mulInvFun d e z) = z := by simp [mul_inv_fun_def, mul_assoc]

/-- The function `mul_inv_fun d e` bundled as an equivalence `{x // d ≤ x} ≃ {x // e ≤ x}`. -/
@[to_additive
      "The function `add_neg_fun d e` bundled as an equivalence\n`{x // d ≤ x} ≃ {x // e ≤ x}`."]
def Equiv.mulInv (d e : G) : { x // d ≤ x } ≃ { x // e ≤ x }
    where
  toFun := mulInvFun d e
  invFun := mulInvFun e d
  left_inv z := by simp
  right_inv z := by simp

@[simp, to_additive]
theorem Equiv.mulInv_eval (d e : G) (x : { x // d ≤ x }) :
    Equiv.mulInv d e x = ⟨e * d⁻¹ * x, aux_ineq_hMul x.2⟩ := by cases' x with x hx; simpa

@[simp, to_additive]
theorem Equiv.mulInv_rev (d e : G) : (Equiv.mulInv d e).symm = Equiv.mulInv e d :=
  rfl

end GroupAddNeg

/-- The subtype of nonnegative integers is equivalent to the natural numbers. -/
def intSubtypeNonnegEquiv : { x : ℤ // 0 ≤ x } ≃ ℕ
    where
  toFun := by
    rintro ⟨x | y, hx⟩
    · exact x
    · exact ((Int.negSucc_not_nonneg _).mp hx).elim
  invFun x := ⟨x, Int.ofNat_zero_le x⟩
  left_inv := by
    rintro ⟨x | y, hx⟩
    · simp only [Int.ofNat_eq_coe, Subtype.coe_mk]
    · exact ((Int.negSucc_not_nonneg _).mp hx).elim
  right_inv x := rfl

@[simp]
theorem intSubtypeNonnegEquiv_eval {z : { x : ℤ // 0 ≤ x }} :
    intSubtypeNonnegEquiv z = Int.toNat z :=
  by
  rcases z with ⟨x | y, hz⟩
  · rfl
  · exact ((Int.negSucc_not_nonneg _).mp hz).elim

@[simp]
theorem Int.toNat_subtype_nonneg {z : { x : ℤ // 0 ≤ x }} : ((z : ℤ).toNat : ℤ) = z :=
  by
  cases' z with x hz
  simp [Int.toNat_of_nonneg hz]

@[simp]
theorem intSubtypeNonnegEquiv_symm_eval {n : ℕ} : (intSubtypeNonnegEquiv.symm n : ℤ) = n :=
  rfl

/-- The subtype of nonnegative integers is equivalent to the natural number. -/
def Int.nonnegEquivNat (d : ℤ) : { x : ℤ // d ≤ x } ≃ ℕ :=
  (Equiv.addNeg d 0).trans intSubtypeNonnegEquiv

/-- The subtype of nonnegative integers is equivalent to the natural number. -/
def Nat.leEquivNat (d : ℕ) : { x // d ≤ x } ≃ ℕ
    where
  toFun x := x.1 - d
  invFun x := ⟨x + d, le_add_self⟩
  left_inv := by rintro ⟨x, hx⟩; simp only [Nat.sub_add_cancel hx]
  right_inv x := by simp

/-- The "identity" is an equivalence between the complement of the set of non-negative integers
and the negative integers. -/
def complLe : ↥(setOf ((· ≤ ·) (0 : ℤ))ᶜ) ≃ { z : ℤ // z < 0 }
    where
  toFun := by rintro ⟨a, ha⟩; exact ⟨a, by simpa using ha⟩
  invFun := by rintro ⟨a, ha⟩; exact ⟨a, by simpa using ha⟩
  left_inv := by rintro ⟨a, ha⟩; simp
  right_inv := by rintro ⟨a, ha⟩; simp

@[simp]
theorem complLe_symm_eval {x : { z : ℤ // z < 0 }} : (complLe.symm x : ℤ) = x := by
  cases' x with x hx; rfl

section Group

variable (α : Type _)

section OneLt

variable [Group α] [LT α] [CovariantClass α α (· * ·) (· < ·)]

/-- Taking inverses establishes an isomorphism between the elements of a group that are
strictly smaller than `1` with the elements that are strictly larger than `1`. -/
@[to_additive
      "Taking opposites establishes an isomorphism between the elements of an additive\ngroup that are strictly smaller than `0` with the elements that are strictly larger than `0`."]
def Equiv.ltOneGtOne : {z : α | z < 1} ≃ {z : α | 1 < z}
    where
  toFun := by rintro ⟨z, hz⟩; exact ⟨z⁻¹, by simpa⟩
  invFun := by rintro ⟨z, hz⟩; exact ⟨z⁻¹, by simpa⟩
  left_inv := by rintro ⟨z, hz⟩; simp
  right_inv := by rintro ⟨z, hz⟩; simp

variable {α}

@[simp, to_additive]
theorem Equiv.ltOneGtOne_eval {x : {z : α | z < 1}} : ((Equiv.ltOneGtOne α) x : α) = x⁻¹ := by
  cases' x with x hx; rfl

@[simp, to_additive]
theorem Equiv.ltOneGtOne_symm_eval {x : {z : α | 1 < z}} :
    ((Equiv.ltOneGtOne α).symm x : α) = x⁻¹ := by cases' x with x hx; rfl

end OneLt

section one_le

variable [Group α] [LE α] [CovariantClass α α (· * ·) (· ≤ ·)]

/-- Taking inverses establishes an isomorphism between the elements of a group that are
at most `1` with the elements that are at least `1`. -/
@[to_additive
      "Taking opposites establishes an isomorphism between the elements of an additive\ngroup that are strictly at most `0` with the elements that are at least `0`."]
def Equiv.leOneGeOne : {z : α | z ≤ 1} ≃ {z : α | 1 ≤ z}
    where
  toFun := by rintro ⟨z, hz⟩; exact ⟨z⁻¹, by simpa⟩
  invFun := by rintro ⟨z, hz⟩; exact ⟨z⁻¹, by simpa⟩
  left_inv := by rintro ⟨z, hz⟩; simp
  right_inv := by rintro ⟨z, hz⟩; simp

variable {α}

@[simp, to_additive]
theorem Equiv.leOneGeOne_eval {x : {z : α | z ≤ 1}} : ((Equiv.leOneGeOne α) x : α) = x⁻¹ := by
  cases' x with x hx; rfl

@[simp, to_additive]
theorem Equiv.leOneGeOne_symm_eval {x : {z : α | 1 ≤ z}} :
    ((Equiv.leOneGeOne α).symm x : α) = x⁻¹ := by cases' x with x hx; rfl

end one_le

end Group

/-- An equivalence between the complement of the non-negative integers and the natural numbers. -/
def oppo : ({z : ℤ | 0 ≤ z}ᶜ : Set ℤ) ≃ ℕ :=
  complLe.trans <| (Equiv.negGtZero ℤ).trans <| (Equiv.addNeg 1 0).trans intSubtypeNonnegEquiv

@[simp]
theorem oppo_symm_eval {n : ℕ} : (oppo.symm n : ℤ) = -n - 1 := by simp [oppo]

section TopologicalSpace

variable {α : Type _} [TopologicalSpace α]

section AddCommMonoid

variable [AddCommMonoid α] {f : ℤ → α}

theorem my_summable_shift (f : ℤ → α) (N : ℤ) :
    (Summable fun x : ℕ => f (x + N)) ↔ Summable fun x : { x // N ≤ x } => f x :=
  by
  convert (int_subtype_nonneg_equiv.symm.trans (equiv.add_neg 0 N)).summable_iff
  ext
  simp [add_comm]

end AddCommMonoid

end TopologicalSpace

section Uniform

variable {α : Type _} [UniformSpace α] [AddCommGroup α] [UniformAddGroup α] [CompleteSpace α]

variable {f : ℤ → α}

theorem int_summable_iff :
    Summable f ↔ (Summable fun n : ℕ => f n) ∧ Summable fun n : ℕ => f (-n - 1) :=
  by
  refine' (@summable_subtype_and_compl α _ _ _ _ _ _ {z : ℤ | 0 ≤ z}).symm.trans _
  rw [← Equiv.summable_iff int_subtype_nonneg_equiv, ← Equiv.summable_iff oppo.symm]
  refine' ⟨_, _⟩ <;> rintro ⟨h1, h2⟩ <;> refine' ⟨_, _⟩ <;>
        refine' Summable.congr ‹_› fun b => _ <;>
      simp only [oppo_symm_eval, int_subtype_nonneg_equiv_eval, Function.comp_apply] <;>
    · apply congr_arg; simp [b.2]

end Uniform

theorem Summable.smaller_radius {f : ℕ → ℝ} {ρ σ : ℝ≥0} (hf : Summable fun n => f n * ρ ^ n)
    (σρ : σ ≤ ρ) (f0 : ∀ n, 0 ≤ f n) : Summable fun n => f n * σ ^ n :=
  by
  refine' Summable.of_nonneg_of_le (fun b => mul_nonneg (f0 _) (pow_nonneg zero_le_coe _)) _ hf
  exact fun b =>
    mul_le_mul rfl.le (pow_le_pow_of_le_left zero_le_coe σρ b) (pow_nonneg zero_le_coe b) (f0 b)

/-- A technical equivalence, useful in the proof of `prod_nat_summable_1`. -/
def equivNatDiag : { x : ℕ × ℕ // x.2 ≤ x.1 } ≃ ℕ × ℕ
    where
  toFun x := (x.1.1 - x.1.2, x.1.2)
  invFun x := ⟨(x.1 + x.2, x.2), by simp⟩
  left_inv := by rintro ⟨x, hx⟩; simp only [Nat.sub_add_cancel hx, Prod.mk.eta]
  right_inv := by rintro ⟨x, y⟩; simp only [add_tsub_cancel_right]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem Summable.prod_nat {f : ℤ → ℝ} {g : ℕ → ℝ} (hf : Summable f) (f0 : ∀ n, 0 ≤ f n)
    (hg : Summable g) (g0 : ∀ n, 0 ≤ g n) :
    Summable fun lj : ℕ × ℕ => f (lj.fst + lj.snd) * g lj.snd :=
  by
  apply (Equiv.summable_iff equiv_nat_diag).mp
  suffices Summable fun lj : { x : ℕ × ℕ // x.2 ≤ x.1 } => f lj.1.fst * g lj.1.snd
    by
    convert this
    ext ⟨⟨x, y⟩, hx⟩
    suffices f (↑(x - y) + ↑y) * g y = f ↑x * g y by simpa [equiv_nat_diag]
    rw_mod_cast [Nat.sub_add_cancel hx]
  apply Summable.subtype (_ : Summable fun lj : ℕ × ℕ => f lj.fst * g lj.snd)
  convert summable_mul_of_summable_norm (_ : Summable fun i : ℕ => «expr∥ ∥» (f i)) _
  · conv =>
      congr
      ext
      rw [Real.norm_of_nonneg (f0 _)]
    apply (int_summable_iff.mp hf).1
  · conv =>
      congr
      ext
      rw [Real.norm_of_nonneg (g0 _)]
    exact hg

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem prod_nat_summable_aux {f : ℤ → ℝ} {s r : ℝ≥0} (s1 : s < 1)
    (hf : Summable fun n : ℤ => «expr∥ ∥» (f n) * r ^ n) :
    Summable fun lj : ℕ × ℕ =>
      «expr∥ ∥» (f (lj.fst + 1 + lj.snd) * r ^ (lj.fst + 1 + lj.snd)) * s ^ lj.snd :=
  by
  apply Summable.of_norm
  simp_rw [norm_mul, norm_norm]
  convert
    (_ : Summable fun n => «expr∥ ∥» (f (n + 1)) * r ^ (n + 1)).prod_nat _ (by simpa)
      (pow_nonneg s.2)
  · simpa only [norm_pow, norm_eq, val_eq_coe, add_right_comm _ (1 : ℤ), add_right_comm _ 1 _]
  · let add_one : ℤ ≃ ℤ := ⟨fun x => x - 1, fun x => x + 1, fun x => by simp, fun x => by simp⟩
    apply add_one.summable_iff.mp
    convert hf
    ext
    simp
  · exact fun n => mul_nonneg (norm_nonneg _) (zpow_nonneg r.2 _)

end AuxThm69

