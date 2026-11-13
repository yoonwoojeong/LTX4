import Mathlib.Topology.Constructions

#align_import hacks_and_tricks.type_pow

/-
In this file, we define notation `X^n` to take powers of types.
By definition, `X^n` is modelled as functions from `fin n` to `X`.
-/
/-- A definition of powers of a type. -/
-- Porting note: `@[reducible]` so that Lean 4 instance search sees `A ^ n = Fin n → A`,
-- as Lean 3 did.
@[reducible]
def typePow : Pow (Type _) ℕ :=
  ⟨fun A n => Fin n → A⟩

namespace TypePowTopology

attribute [local instance] typePow

variable (z : ℤ) (A : Type) [AddCommGroup A] (n : ℕ) (x : A ^ n)

instance topologicalSpace {n : ℕ} {α : Type _} [TopologicalSpace α] : TopologicalSpace (α ^ n) :=
  Pi.topologicalSpace

--instance {n : ℕ} {α : Type*} [topological_space α] [discrete_topology α] : discrete_topology (α^n) := admit
end TypePowTopology

namespace TypePowAlgebra

attribute [local instance] typePow

-- Porting note: Lean 3 found the pi-instance on `A ^ n = Fin n → A` by unfolding `typePow`;
-- Lean 4's instance index does not see through `A ^ n`, so it is registered explicitly
-- (just as LTE already did above for `TopologicalSpace`).
instance addCommGroup {n : ℕ} {A : Type _} [AddCommGroup A] : AddCommGroup (A ^ n) :=
  Pi.addCommGroup

-- Porting note: the `Pi.*_apply` simp lemmas do not match on `A ^ n`; these restate them.
@[simp] theorem zero_apply {n : ℕ} {A : Type _} [AddCommGroup A] (i : Fin n) :
    (0 : A ^ n) i = 0 := rfl

@[simp] theorem add_apply {n : ℕ} {A : Type _} [AddCommGroup A] (x y : A ^ n) (i : Fin n) :
    (x + y) i = x i + y i := rfl

@[simp] theorem neg_apply {n : ℕ} {A : Type _} [AddCommGroup A] (x : A ^ n) (i : Fin n) :
    (-x) i = -x i := rfl

@[simp] theorem sub_apply {n : ℕ} {A : Type _} [AddCommGroup A] (x y : A ^ n) (i : Fin n) :
    (x - y) i = x i - y i := rfl

end TypePowAlgebra

namespace AddMonoidHom

universe u v

attribute [local instance] typePow

/-- The group homomorphism `A^n →+ B^n` induced by a group homomorphism `A →+ B`. -/
def pow {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B] (φ : A →+ B) (n : ℕ) :
    A ^ n →+ B ^ n where
  toFun := (· ∘ ·) φ
  map_zero' := funext fun _ => φ.map_zero
  map_add' _ _ := funext fun _ => φ.map_add _ _

theorem pow_eval {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B] (φ : A →+ B) (n : ℕ)
    (as : A ^ n) (i : Fin n) : φ.pow n as i = φ (as i) :=
  rfl

open scoped BigOperators

/-- The group homomorphism `A^n →+ B` induced by `n` group homs `A →+ B` -/
def powHom {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B] {n : ℕ}
    (φ : Fin n → A →+ B) : A ^ n →+ B
    where
  toFun z := ∑ i : Fin n, φ i (z i)
  map_zero' := by simp only [TypePowAlgebra.zero_apply, Finset.sum_const_zero, map_zero]
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    simp

end AddMonoidHom

attribute [local instance] typePow

/-- The natural bijection `(A^m)^n ≃ (A^n)^m`. -/
def powPow {A : Type _} {m n : ℕ} : (A ^ m) ^ n ≃ (A ^ n) ^ m
    where
  toFun f i j := f j i
  invFun f j i := f i j
  left_inv _ := rfl
  right_inv _ := rfl

/-- The natural bijection `A^n ≃ B^n` induced by a bijection `A ≃ B`.-/
def powEquiv {A B : Type _} (e : A ≃ B) {n : ℕ} : A ^ n ≃ B ^ n
    where
  toFun f i := e (f i)
  invFun g i := e.symm (g i)
  left_inv f := funext fun i => Equiv.symm_apply_apply _ _
  right_inv g := funext fun i => Equiv.apply_symm_apply _ _

#lint

