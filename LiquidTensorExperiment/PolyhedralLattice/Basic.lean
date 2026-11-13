import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.RingTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Int.Basic

#align_import polyhedral_lattice.basic

/-!

# Polyhedral lattices

A polyhedral lattice is a finite free ℤ-module with a real-valued norm
making it into a normed group, such that the closed unit ball of
the Banach space obtained by tensoring everything up to ℝ is a rational polyhedron.

## Implementation issues

The condition on the norm actually used is `generates_norm` below.

-/


noncomputable section

open scoped BigOperators Classical NNReal

section GeneratesNorm

variable {Λ ι : Type _} [SeminormedAddCommGroup Λ] [Fintype ι]

/-- A finite family `x : ι → Λ` generates the norm on `Λ`
if for every `l : Λ` there exist coefficients `c : ι → ℕ`
such that `l = ∑ i, c i • x i` and `∥l∥ = ∑ i, (c i) * ∥x i∥`.
-/
def GeneratesNorm (x : ι → Λ) :=
  ∀ l : Λ, ∃ c : ι → ℕ, l = ∑ i, c i • x i ∧ ‖l‖ = ∑ i, c i * ‖x i‖

theorem generatesNorm_iff_generates_nnnorm (x : ι → Λ) :
    GeneratesNorm x ↔
      ∀ l : Λ, ∃ c : ι → ℕ, l = ∑ i, c i • x i ∧ ‖l‖₊ = ∑ i, c i * ‖x i‖₊ :=
  by
  apply forall_congr'; intro l
  simp only [← NNReal.eq_iff, NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_nat_cast, coe_nnnorm]

theorem GeneratesNorm.generates_nnnorm {x : ι → Λ} (hl : GeneratesNorm x) :
    ∀ l : Λ, ∃ c : ι → ℕ, l = ∑ i, c i • x i ∧ ‖l‖₊ = ∑ i, c i * ‖x i‖₊ :=
  (generatesNorm_iff_generates_nnnorm x).mp hl

theorem generatesNorm_of_generates_nnnorm {x : ι → Λ}
    (H : ∀ l : Λ, ∃ c : ι → ℕ, l = ∑ i, c i • x i ∧ ‖l‖₊ = ∑ i, c i * ‖x i‖₊) :
    GeneratesNorm x :=
  (generatesNorm_iff_generates_nnnorm x).mpr H

end GeneratesNorm

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`Finite] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`Free] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`polyhedral'] [] -/
class PolyhedralLattice (Λ : Type _) extends NormedAddCommGroup Λ where
  [Finite : Module.Finite ℤ Λ]
  [Free : Module.Free ℤ Λ]
  polyhedral' : ∃ (ι : Type) (_ : Fintype ι) (l : ι → Λ), GeneratesNorm l

namespace PolyhedralLattice

variable (Λ : Type _) [PolyhedralLattice Λ]

attribute [instance] PolyhedralLattice.finite PolyhedralLattice.free

instance noZeroSMulDivisors_int : NoZeroSMulDivisors ℤ Λ :=
  Module.Free.noZeroSMulDivisors ℤ Λ

instance noZeroSMulDivisors_nat : NoZeroSMulDivisors ℕ Λ :=
  ⟨fun n l h => by
    rw [← coe_nat_zsmul, smul_eq_zero] at h 
    refine' h.imp _ id; simp only [imp_self, Int.coe_nat_eq_zero]⟩

theorem polyhedral : ∃ (ι : Type) (_ : Fintype ι) (l : ι → Λ), GeneratesNorm l ∧ ∀ i, l i ≠ 0 :=
  by
  obtain ⟨ι, _ι_inst, l, hl⟩ := PolyhedralLattice.polyhedral' Λ; skip
  refine' ⟨{ i // l i ≠ 0 }, inferInstance, fun i => l i, _, fun i => i.2⟩
  intro x
  obtain ⟨c, h1, h2⟩ := hl x
  refine' ⟨fun i => c i, _, _⟩
  · rw [h1]
    refine' Finset.sum_bij_ne_zero _ (fun _ _ _ => Finset.mem_univ _) _ _ _
    · rintro i - hi; refine' ⟨i, _⟩; contrapose! hi; rw [hi, smul_zero]
    · dsimp; rintro i j - hi - hj; simp only [imp_self]
    · rintro ⟨i, hi⟩ -; dsimp; intro H; refine' ⟨i, Finset.mem_univ _, H, rfl⟩
    · intros; rfl
  · rw [h2]
    refine' Finset.sum_bij_ne_zero _ (fun _ _ _ => Finset.mem_univ _) _ _ _
    · rintro i - hi; refine' ⟨i, _⟩; contrapose! hi; rw [hi, norm_zero, MulZeroClass.mul_zero]
    · dsimp; rintro i j - hi - hj; simp only [imp_self]
    · rintro ⟨i, hi⟩ -; dsimp; intro H; refine' ⟨i, Finset.mem_univ _, H, rfl⟩
    · intros; rfl

end PolyhedralLattice

/-- A morphism of polyhedral lattices is a norm-nonincreasing group homomorphism. -/
structure PolyhedralLatticeHom (Λ₁ Λ₂ : Type _) [PolyhedralLattice Λ₁] [PolyhedralLattice Λ₂] where
  toFun : Λ₁ → Λ₂
  map_add' : ∀ l₁ l₂, toFun (l₁ + l₂) = toFun l₁ + toFun l₂
  strict' : ∀ l, ‖toFun l‖ ≤ ‖l‖

namespace AddMonoidHom

variable {Λ₁ Λ₂ : Type _} [PolyhedralLattice Λ₁] [PolyhedralLattice Λ₂]

variable {f g : PolyhedralLatticeHom Λ₁ Λ₂}

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_polyhedral_lattice_hom'` for a version that uses `ℝ≥0` for the bound. -/
def mkPolyhedralLatticeHom (f : Λ₁ →+ Λ₂) (h : ∀ v, ‖f v‖ ≤ ‖v‖) :
    PolyhedralLatticeHom Λ₁ Λ₂ :=
  { f with strict' := h }

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_polyhedral_lattice_hom` for a version that uses `ℝ` for the bound. -/
def mkPolyhedralLatticeHom' (f : Λ₁ →+ Λ₂) (h : ∀ x, ‖f x‖₊ ≤ ‖x‖₊) :
    PolyhedralLatticeHom Λ₁ Λ₂ :=
  { f with strict' := h }

end AddMonoidHom

namespace PolyhedralLatticeHom

variable {Λ Λ₁ Λ₂ Λ₃ : Type _}

variable [PolyhedralLattice Λ] [PolyhedralLattice Λ₁] [PolyhedralLattice Λ₂] [PolyhedralLattice Λ₃]

variable {f g : PolyhedralLatticeHom Λ₁ Λ₂}

instance : CoeFun (PolyhedralLatticeHom Λ₁ Λ₂) fun _ => Λ₁ → Λ₂ :=
  ⟨PolyhedralLatticeHom.toFun⟩

initialize_simps_projections PolyhedralLatticeHom (toFun → apply)

theorem coe_inj (H : (⇑f : Λ₁ → Λ₂) = g) : f = g := by
  cases f <;> cases g <;> congr <;> exact funext H

theorem coe_injective : @Function.Injective (PolyhedralLatticeHom Λ₁ Λ₂) (Λ₁ → Λ₂) coeFn := by
  apply coe_inj

theorem coe_inj_iff : f = g ↔ (⇑f : Λ₁ → Λ₂) = g :=
  ⟨congr_arg _, coe_inj⟩

@[ext]
theorem ext (H : ∀ x, f x = g x) : f = g :=
  coe_inj <| funext H

theorem ext_iff : f = g ↔ ∀ x, f x = g x :=
  ⟨by rintro rfl x <;> rfl, ext⟩

variable (f g)

@[simp]
theorem toFun_eq_coe : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f) (h₁) (h₂) : ⇑(⟨f, h₁, h₂⟩ : PolyhedralLatticeHom Λ₁ Λ₂) = f :=
  rfl

@[simp]
theorem coe_mkPolyhedralLatticeHom (f : Λ₁ →+ Λ₂) (h) : ⇑(f.mkPolyhedralLatticeHom h) = f :=
  rfl

@[simp]
theorem coe_mkPolyhedralLatticeHom' (f : Λ₁ →+ Λ₂) (h) : ⇑(f.mkPolyhedralLatticeHom' h) = f :=
  rfl

/-- The group homomorphism underlying a bounded group homomorphism. -/
def toAddMonoidHom (f : PolyhedralLatticeHom Λ₁ Λ₂) : Λ₁ →+ Λ₂ :=
  AddMonoidHom.mk' f f.map_add'

@[simp]
theorem coe_toAddMonoidHom : ⇑f.toAddMonoidHom = f :=
  rfl

theorem toAddMonoidHom_injective :
    Function.Injective (@PolyhedralLatticeHom.toAddMonoidHom Λ₁ Λ₂ _ _) := fun f g h =>
  coe_inj <| show ⇑f.toAddMonoidHom = g by rw [h]; rfl

@[simp]
theorem mk_toAddMonoidHom (f) (h₁) (h₂) :
    (⟨f, h₁, h₂⟩ : PolyhedralLatticeHom Λ₁ Λ₂).toAddMonoidHom = AddMonoidHom.mk' f h₁ :=
  rfl

@[simp]
theorem map_zero : f 0 = 0 :=
  f.toAddMonoidHom.map_zero

@[simp]
theorem map_add (x y) : f (x + y) = f x + f y :=
  f.toAddMonoidHom.map_add _ _

@[simp]
theorem map_sum {ι : Type _} (Λ : ι → Λ₁) (s : Finset ι) : f (∑ i in s, Λ i) = ∑ i in s, f (Λ i) :=
  f.toAddMonoidHom.map_sum _ _

@[simp]
theorem map_sub (x y) : f (x - y) = f x - f y :=
  f.toAddMonoidHom.map_sub _ _

@[simp]
theorem map_neg (x) : f (-x) = -f x :=
  f.toAddMonoidHom.map_neg _

@[simp]
theorem map_zsmul (n : ℤ) (x) : f (n • x) = n • f x :=
  f.toAddMonoidHom.map_zsmul _ _

instance : Zero (PolyhedralLatticeHom Λ₁ Λ₂) :=
  ⟨(0 : Λ₁ →+ Λ₂).mkPolyhedralLatticeHom (by simp [le_refl])⟩

theorem strict (l : Λ₁) : ‖f l‖ ≤ ‖l‖ :=
  f.strict' l

theorem strict_nnnorm (l : Λ₁) : ‖f l‖₊ ≤ ‖l‖₊ :=
  f.strict' l

@[simps]
def toNormedGroupHom : NormedAddGroupHom Λ₁ Λ₂ :=
  { f with bound' := ⟨1, by simpa only [one_mul] using f.strict⟩ }

/-- The identity as a polyhedral lattice hom. -/
@[simps]
def id : PolyhedralLatticeHom Λ Λ :=
  (AddMonoidHom.id Λ).mkPolyhedralLatticeHom (by simp [le_refl])

/-- The composition of polyhedral lattice homs. -/
@[simps]
protected def comp (g : PolyhedralLatticeHom Λ₂ Λ₃) (f : PolyhedralLatticeHom Λ₁ Λ₂) :
    PolyhedralLatticeHom Λ₁ Λ₃ :=
  (g.toAddMonoidHom.comp f.toAddMonoidHom).mkPolyhedralLatticeHom fun l =>
    (g.strict' _).trans (f.strict' _)

end PolyhedralLatticeHom

