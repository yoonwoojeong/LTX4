import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.Algebra.BigOperators.Multiset.Lemmas
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.RingEquiv
import Mathlib.Algebra.Module.Pi
import Mathlib.Topology.Basic
import LiquidTensorExperiment.HacksAndTricks.TypePow

#align_import pseudo_normed_group.basic

/-!

# Pseudo-normed groups

This file contains definitions and basic properties of pseudo-normed (abelian additive) groups.
See for example the comments after the proof of Proposition 9.10 of `analytic.pdf`, although we do
not work in an arbitrary topos.

## Main definitions

`pseudo_normed_group` -- a pseudo-normed abelian additive group

## Implementation issues

Right now we let the M_c be subsets of M. An alternative approach would be to have
them all as types; this is more convenient for some parts of the argument.

-/


noncomputable section

open scoped NNReal BigOperators

attribute [local instance] typePow

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`filtration] [] -/
/-- A pseudo-normed group is an abelian group `M`
together with an increasing filtration indexed by `ℝ≥0` of subsets `M_{≤c}`
containing `0` and closed under negation,
and such that if `x₁ ∈ M_{≤c₁}` and `x₂ ∈ M_{c₂}`, then `x₁ + x₂ ∈ M_{≤c₁ + c₂}`.

See also the comments after Proposition 9.10 on p66 in [Analytic].

Implementation details:
* In [Analytic], the filtration is indexed by *positive* real numbers (excluding) `0`,
  whereas this definition includes `0` in the indexing set.
* We do not ask for the filtration to be exhaustive (similar to [Analytic]),
  which is convenient, because it means that `M₁ →+ M₂` is naturally a pseudo-normed group
  if `M₁` and `M₂` are pseudo-normed groups. -/
class PseudoNormedGroup (M : Type _) where
  [toAddCommGroup : AddCommGroup M]
  filtration : ℝ≥0 → Set M
  filtration_mono : ∀ ⦃c₁ c₂⦄, c₁ ≤ c₂ → filtration c₁ ⊆ filtration c₂
  zero_mem_filtration : ∀ c, (0 : M) ∈ filtration c
  neg_mem_filtration : ∀ ⦃c x⦄, x ∈ filtration c → -x ∈ filtration c
  add_mem_filtration :
    ∀ ⦃c₁ c₂ x₁ x₂⦄, x₁ ∈ filtration c₁ → x₂ ∈ filtration c₂ → x₁ + x₂ ∈ filtration (c₁ + c₂)

/-- The additive commutative group instance underlying a pseudo-normed group. -/
add_decl_doc PseudoNormedGroup.toAddCommGroup

open Function

-- An alternative attempt at pseudo-normed groups,
-- that we might want to keep/switch to in the future
-- class pseudo_normed_group' (B_ : ℝ≥0 → Type*) (M : out_param Type*) :=
-- [to_add_comm_group : add_comm_group M]
-- [has_zero : Π r, has_zero (B_ r)]
-- [has_neg : Π r, has_neg (B_ r)]
-- (map : ∀ ⦃c₁ c₂⦄, c₁ ≤ c₂ → B_ c₁ → B_ c₂) -- rename
-- (incl : ∀ c, B_ c → M)
-- (incl_injective : ∀ c, injective (incl c))
-- (incl_zero : ∀ c, incl c 0 = 0)
-- (incl_neg : ∀ {c} (f : B_ c), incl c (-f) = - (incl c f))
-- (incl_map : ∀ {c₁ c₂} (h : c₁ ≤ c₂), (incl c₂) ∘ (map h) = (incl c₁))
-- (B_add {c₁ c₂} : B_ c₁ → B_ c₂ → B_ (c₁ + c₂))
-- (incl_add {c₁ c₂} (f : B_ c₁) (g : B_ c₂) : incl _ (B_add f g) = incl _ f + incl _ g)
-- (map_refl {c} : map (le_refl c) = id)
-- (map_trans {c₁ c₂ c₃} (h1 : c₁ ≤ c₂) (h2 : c₂ ≤ c₃) : map (h1.trans h2) = map h2 ∘ map h1)
/-
class topological_pseudo_normed_group' (B_ : ℝ≥0 → Type*) (M : Type*)
  extends pseudo_normed_group' B_ M :=
[is_top_space : Π r, topological_space (B_ r)]
-/
/-
Thought by Johan:
Maybe we want both defintions above, and write a bit of glue to move between them.
Both seem useful for different bits of what we want to do.
-/
attribute [instance] PseudoNormedGroup.toAddCommGroup

namespace PseudoNormedGroup

variable {M : Type _} [PseudoNormedGroup M]

instance (c : ℝ≥0) : Zero (filtration M c) :=
  ⟨⟨0, zero_mem_filtration _⟩⟩

instance (c : ℝ≥0) : Neg (filtration M c) :=
  ⟨fun x => ⟨-x, neg_mem_filtration x.2⟩⟩

@[simp]
theorem filtration.coe_zero {c : ℝ≥0} : ((0 : filtration M c) : M) = 0 :=
  rfl

@[simp]
theorem filtration.coe_neg {c : ℝ≥0} (x : filtration M c) :
    ((-x : filtration M c) : M) = -(x : M) :=
  rfl

/-- Bounded uncurried addition for pseudo-normed groups. -/
def add' {c₁ c₂} (x : filtration M c₁ × filtration M c₂) : filtration M (c₁ + c₂) :=
  ⟨(x.1 + x.2 : M), add_mem_filtration x.1.2 x.2.2⟩

@[simp]
theorem add'_eq {c₁ c₂ : ℝ≥0} (x : filtration M c₁ × filtration M c₂) : (add' x : M) = x.1 + x.2 :=
  rfl

/-- Bounded negation for pseudo-normed groups. -/
def neg' {c} (x : filtration M c) : filtration M c :=
  ⟨(-x : M), neg_mem_filtration x.2⟩

@[simp]
theorem neg'_eq {c : ℝ≥0} (x : filtration M c) : (neg' x : M) = -x :=
  rfl

theorem sub_mem_filtration ⦃c₁ c₂ x₁ x₂⦄ (h₁ : x₁ ∈ filtration M c₁) (h₂ : x₂ ∈ filtration M c₂) :
    x₁ - x₂ ∈ filtration M (c₁ + c₂) := by rw [sub_eq_add_neg];
  exact add_mem_filtration h₁ (neg_mem_filtration h₂)

theorem neg_mem_filtration_iff (c x) : -x ∈ filtration M c ↔ x ∈ filtration M c :=
  ⟨fun h => by rw [← neg_neg x]; exact neg_mem_filtration h, fun h => neg_mem_filtration h⟩

theorem sum_mem_filtration {ι : Type _} (x : ι → M) (c : ι → ℝ≥0) (s : Finset ι)
    (h : ∀ i ∈ s, x i ∈ filtration M (c i)) : ∑ i in s, x i ∈ filtration M (∑ i in s, c i) := by
  classical
  revert h
  apply Finset.induction_on s <;> clear s
  · intro; simpa only [Finset.sum_empty] using zero_mem_filtration _
  · intro i s his IH h
    rw [Finset.sum_insert his, Finset.sum_insert his]
    apply add_mem_filtration (h _ _) (IH _)
    · exact Finset.mem_insert_self i s
    · intro j hj; apply h; exact Finset.mem_insert_of_mem hj

theorem nat_smul_mem_filtration (n : ℕ) (m : M) (c : ℝ≥0) (h : m ∈ filtration M c) :
    n • m ∈ filtration M (n * c) := by
  induction' n with n ih; · simpa only [zero_smul] using zero_mem_filtration _
  simp only [Nat.succ_eq_add_one, add_smul, one_smul, Nat.cast_succ, add_mul, one_mul]
  exact add_mem_filtration ih h

theorem int_smul_mem_filtration (n : ℤ) (m : M) (c : ℝ≥0) (h : m ∈ filtration M c) :
    n • m ∈ filtration M (n.natAbs * c) :=
  by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simp only [Int.natAbs_ofNat, ← zsmul_eq_smul, coe_nat_zsmul, nsmul_eq_smul]
    exact PseudoNormedGroup.nat_smul_mem_filtration n m c h
  · push_neg at hn ; rw [← neg_pos] at hn 
    lift -n to ℕ using hn.le with k hk
    rw [← neg_neg n, Int.natAbs_neg, ← hk, Int.natAbs_ofNat, neg_smul]
    apply neg_mem_filtration
    simp only [neg_smul, ← zsmul_eq_smul, coe_nat_zsmul, nsmul_eq_smul]
    exact PseudoNormedGroup.nat_smul_mem_filtration k m c h

/-- The map from `filtration M₁ c` to `filtration M₂ c` induced by a strict morphism `M₁ → M₂`. -/
@[simps]
def level {M₁ M₂ : Type _} [PseudoNormedGroup M₁] [PseudoNormedGroup M₂] (f : M₁ → M₂)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ c) (c : ℝ≥0) :
    filtration M₁ c → filtration M₂ c := fun x => ⟨f x, strict x.2⟩

section Pi

variable ()

instance pi {ι : Type _} (M : ι → Type _) [∀ i, PseudoNormedGroup (M i)] :
    PseudoNormedGroup (∀ i, M i)
    where
  filtration c := {x | ∀ i, x i ∈ filtration (M i) c}
  filtration_mono c₁ c₂ h x hx i := filtration_mono h (hx i)
  zero_mem_filtration c i := zero_mem_filtration _
  neg_mem_filtration c x h i := neg_mem_filtration (h i)
  add_mem_filtration c₁ c₂ x₁ x₂ h₁ h₂ i := add_mem_filtration (h₁ i) (h₂ i)

theorem mem_filtration_pi {ι : Type _} (M : ι → Type _) [∀ i, PseudoNormedGroup (M i)] (c : ℝ≥0)
    (x : ∀ i, M i) : x ∈ filtration (∀ i, M i) c ↔ ∀ i, x i ∈ filtration (M i) c :=
  Iff.rfl

/-- The equivalence between `(Π i, M i)_c` and `Π i, (M i)_c`. -/
@[simps]
def filtrationPiEquiv {ι : Type _} (M : ι → Type _) [∀ i, PseudoNormedGroup (M i)] (c : ℝ≥0) :
    filtration (∀ i, M i) c ≃ ∀ i, filtration (M i) c
    where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => x i, fun i => (x i).2⟩
  left_inv := by rintro ⟨x, hx⟩; rfl
  right_inv := by intro x; ext; rfl

end Pi

section Prod

variable (M₁ M₂ : Type _) [PseudoNormedGroup M₁] [PseudoNormedGroup M₂]

instance prod : PseudoNormedGroup (M₁ × M₂)
    where
  filtration c := {x | x.1 ∈ filtration M₁ c ∧ x.2 ∈ filtration M₂ c}
  filtration_mono c₁ c₂ h x hx := ⟨filtration_mono h hx.1, filtration_mono h hx.2⟩
  zero_mem_filtration c := ⟨zero_mem_filtration _, zero_mem_filtration _⟩
  neg_mem_filtration c x h := ⟨neg_mem_filtration h.1, neg_mem_filtration h.2⟩
  add_mem_filtration c₁ c₂ x₁ x₂ h₁ h₂ :=
    ⟨add_mem_filtration h₁.1 h₂.1, add_mem_filtration h₁.2 h₂.2⟩

theorem mem_filtration_prod (c : ℝ≥0) (x : M₁ × M₂) :
    x ∈ filtration (M₁ × M₂) c ↔ x.1 ∈ filtration M₁ c ∧ x.2 ∈ filtration M₂ c :=
  Iff.rfl

/-- The equivalence between `(M₁ × M₂)_c` and `(M₁)_c × (M₂)_c`. -/
@[simps]
def filtrationProdEquiv (c : ℝ≥0) : filtration (M₁ × M₂) c ≃ filtration M₁ c × filtration M₂ c
    where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1, x.2), ⟨x.1.2, x.2.2⟩⟩
  left_inv := by rintro ⟨⟨x₁, x₂⟩, hx⟩; rfl
  right_inv := by rintro ⟨x₁, x₂⟩; ext <;> rfl

end Prod

/-- The natural inclusion `filtration M c₁ → filtration M c₂`,
for a pseudo-normed group `M`, and `c₁ ≤ c₂`. -/
def castLe {c₁ c₂ : ℝ≥0} [h : Fact (c₁ ≤ c₂)] (x : filtration M c₁) : filtration M c₂ :=
  ⟨x, filtration_mono h.out x.2⟩

/-- The natural inclusion `filtration M c₁ → filtration M c₂`,
for a pseudo-normed group `M`, and `c₁ ≤ c₂`. -/
def castLe' {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) : filtration M c₁ → filtration M c₂ := fun x =>
  ⟨x, filtration_mono h x.2⟩

@[simp]
theorem castLe'_eq_castLe {c₁ c₂ : ℝ≥0} [h : Fact (c₁ ≤ c₂)] (x : filtration M c₁) :
    castLe' h.out x = castLe x :=
  rfl

@[simp]
theorem coe_castLe {c₁ c₂ : ℝ≥0} [h : Fact (c₁ ≤ c₂)] (x : filtration M c₁) :
    ((castLe x : filtration M c₂) : M) = x :=
  rfl

@[simp]
theorem coe_castLe' {c₁ c₂ : ℝ≥0} (h : c₁ ≤ c₂) (x : filtration M c₁) : (castLe' h x : M) = x :=
  rfl

theorem injective_castLe (c₁ c₂ : ℝ≥0) [Fact (c₁ ≤ c₂)] :
    Function.Injective (castLe : filtration M c₁ → filtration M c₂) := fun x y h =>
  Subtype.coe_injective <| by simpa only [coe_cast_le] using congr_arg (coe : filtration M c₂ → M) h

variable (M)

end PseudoNormedGroup

open PseudoNormedGroup

namespace AddMonoidHom

variable {M M₁ M₂ M₃ : Type _}

variable [PseudoNormedGroup M] [PseudoNormedGroup M₁]

variable [PseudoNormedGroup M₂] [PseudoNormedGroup M₃]

instance : PseudoNormedGroup (M₁ →+ M₂) :=
  {
    AddMonoidHom.addCommGroup with
    filtration := fun N => {f | ∀ ⦃c⦄ ⦃x : M₁⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ (N * c)}
    filtration_mono := fun N₁ N₂ h f hf c x hx => filtration_mono (mul_le_mul_right' h c) (hf hx)
    zero_mem_filtration := fun N c x hx => zero_mem_filtration _
    neg_mem_filtration := fun N f hf c x hx => neg_mem_filtration <| hf hx
    add_mem_filtration := fun N₁ N₂ f₁ f₂ hf₁ hf₂ c x hx => by rw [add_mul];
      apply add_mem_filtration (hf₁ hx) (hf₂ hx) }

theorem comp_mem_filtration {g f cg cf} (hg : g ∈ filtration (M₂ →+ M₃) cg)
    (hf : f ∈ filtration (M₁ →+ M₂) cf) : g.comp f ∈ filtration (M₁ →+ M₃) (cg * cf) :=
  fun c x hx => by rw [mul_assoc]; exact hg (hf hx)

@[simp]
theorem id_mem_filtration (c : ℝ≥0) (hc : 1 ≤ c) : id M ∈ filtration (M →+ M) c := fun c' x hx => by
  refine' filtration_mono _ hx <;>
    calc
      c' = 1 * c' := by rw [one_mul]
      _ ≤ c * c' := mul_le_mul_right' hc c'

-- move this, maybe it already exists?
/-- The additive monoid homomorphism into a product of additive monoids,
constructed from a family of monoid homomorphisms into the factors. -/
@[simps (config :=
      { rhsMd := semireducible
        fullyApplied := false })]
def mkToPi {M₁} [AddMonoid M₁] {ι : Type _} {M : ι → Type _} [∀ i, AddMonoid (M i)]
    (f : ∀ i, M₁ →+ M i) : M₁ →+ ∀ i, M i
    where
  toFun v i := f i v
  map_zero' := by simp only [map_zero]; rfl
  map_add' := by intros; simp only [map_add]; rfl

theorem mkToPi_mem_filtration {ι : Type _} {M : ι → Type _} [∀ i, PseudoNormedGroup (M i)]
    (f : ∀ i, M₁ →+ M i) {c} (hfc : ∀ i, f i ∈ filtration (M₁ →+ M i) c) :
    mkToPi f ∈ filtration (M₁ →+ ∀ i, M i) c := fun c' x h i => hfc i h

theorem eval_mem_filtration {ι : Type _} (M : ι → Type _) [∀ i, PseudoNormedGroup (M i)] (i : ι)
    (c : ℝ≥0) (hc : 1 ≤ c) : Pi.evalAddMonoidHom M i ∈ filtration ((∀ i, M i) →+ M i) c :=
  fun c' x hx => by
  refine' filtration_mono _ (hx i) <;>
    calc
      c' = 1 * c' := by rw [one_mul]
      _ ≤ c * c' := mul_le_mul_right' hc c'

/-- The additive monoid homomorphism out of a finite product of additive monoids,
constructed from a family of monoid homomorphisms out of the factors. -/
def mkFromPi {ι : Type _} [Fintype ι] {M : ι → Type _} {M₂} [∀ i, AddMonoid (M i)]
    [AddCommMonoid M₂] (f : ∀ i, M i →+ M₂) : (∀ i, M i) →+ M₂ :=
  ∑ i, (f i).comp (Pi.evalAddMonoidHom M i)

@[simp]
theorem mkFromPi_apply {ι : Type _} [Fintype ι] {M : ι → Type _} [∀ i, AddCommMonoid (M i)]
    (f : ∀ i, M i →+ M₂) (x : ∀ i, M i) : mkFromPi f x = ∑ i, f i (x i) :=
  by
  show AddMonoidHom.eval x (AddMonoidHom.mkFromPi f) = _
  simp only [AddMonoidHom.mkFromPi, AddMonoidHom.map_sum]
  rfl

@[simp]
theorem coe_mkFromPi {ι : Type _} [Fintype ι] {M : ι → Type _} [∀ i, AddCommMonoid (M i)]
    (f : ∀ i, M i →+ M₂) : ⇑(mkFromPi f) = ∑ i, f i ∘ Pi.evalAddMonoidHom M i := by ext x;
  rw [@mk_from_pi_apply M₂ _ ι _ M _ f x, Fintype.sum_apply]; rfl

theorem mkFromPi_mem_filtration {ι : Type _} [Fintype ι] {M : ι → Type _}
    [∀ i, PseudoNormedGroup (M i)] (f : ∀ i, M i →+ M₂) {c : ι → ℝ≥0}
    (hfc : ∀ i, f i ∈ filtration (M i →+ M₂) (c i)) :
    mkFromPi f ∈ filtration ((∀ i, M i) →+ M₂) (∑ i, c i) := fun c' x h =>
  by
  rw [Finset.sum_mul, @mk_from_pi_apply M₂ _ ι _ M _ f x]
  refine' sum_mem_filtration _ _ _ _
  rintro i -
  exact hfc i (h i)

theorem const_smul_hom_nat_mem_filtration (n : ℕ) (c : ℝ≥0) (h : ↑n ≤ c) :
    DistribMulAction.toAddMonoidHom M n ∈ filtration (M →+ M) c := fun c' x hx => by
  simpa only [DistribMulAction.toAddMonoidHom_apply] using
    filtration_mono (mul_le_mul_right' h c') (nat_smul_mem_filtration _ _ _ hx)

theorem const_smul_hom_int_mem_filtration (n : ℤ) (c : ℝ≥0) (h : ↑n.natAbs ≤ c) :
    DistribMulAction.toAddMonoidHom M n ∈ filtration (M →+ M) c := fun c' x hx => by
  simpa only [DistribMulAction.toAddMonoidHom_apply] using
    filtration_mono (mul_le_mul_right' h c') (int_smul_mem_filtration _ _ _ hx)

end AddMonoidHom

structure StrictPseudoNormedGroupHom (M N : Type _) [PseudoNormedGroup M]
    [PseudoNormedGroup N] extends M →+ N where
  strict' :
    ∀ c x, x ∈ PseudoNormedGroup.filtration M c → to_fun x ∈ PseudoNormedGroup.filtration N c

namespace StrictPseudoNormedGroupHom

variable {M N : Type _} [PseudoNormedGroup M] [PseudoNormedGroup N]
  (f g : StrictPseudoNormedGroupHom M N)

instance : CoeFun (StrictPseudoNormedGroupHom M N) fun _ => M → N :=
  ⟨fun f => f.toAddMonoidHom⟩

@[simp]
theorem coe_mk (f) (h) : ⇑(⟨f, h⟩ : StrictPseudoNormedGroupHom M N) = f :=
  rfl

@[simp]
theorem mk_to_monoid_hom (f) (h) : (⟨f, h⟩ : StrictPseudoNormedGroupHom M N).toAddMonoidHom = f :=
  rfl

@[simp]
theorem coe_toAddMonoidHom : ⇑f.toAddMonoidHom = f :=
  rfl

@[simp]
theorem map_zero : f 0 = 0 :=
  f.toAddMonoidHom.map_zero

@[simp]
theorem map_add (x y) : f (x + y) = f x + f y :=
  f.toAddMonoidHom.map_add _ _

@[simp]
theorem map_neg (x) : f (-x) = -f x :=
  f.toAddMonoidHom.map_neg _

theorem strict ⦃c x⦄ (h : x ∈ filtration M c) : f x ∈ filtration N c :=
  f.strict' _ _ h

@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g := by cases f; cases g; congr; ext; apply h

def id (M : Type _) [PseudoNormedGroup M] : StrictPseudoNormedGroupHom M M
    where
  toFun := id
  map_zero' := rfl
  map_add' _ _ := rfl
  strict' _ _ h := h

def comp {A B C : Type _} [PseudoNormedGroup A] [PseudoNormedGroup B] [PseudoNormedGroup C]
    (f : StrictPseudoNormedGroupHom A B) (g : StrictPseudoNormedGroupHom B C) :
    StrictPseudoNormedGroupHom A C where
  toFun x := g <| f x
  map_zero' := by simp
  map_add' _ _ := by simp
  strict' c x h := g.strict <| f.strict h

@[simp]
theorem id_apply (A : Type _) [PseudoNormedGroup A] (a : A) :
    StrictPseudoNormedGroupHom.id A a = a :=
  rfl

@[simp]
theorem comp_apply {A B C : Type _} [PseudoNormedGroup A] [PseudoNormedGroup B]
    [PseudoNormedGroup C] (f : StrictPseudoNormedGroupHom A B) (g : StrictPseudoNormedGroupHom B C)
    (a : A) : f.comp g a = g (f a) :=
  rfl

end StrictPseudoNormedGroupHom

-- #lint- only unused_arguments def_lemma doc_blame
