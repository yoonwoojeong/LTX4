import Mathlib.Algebra.PUnitInstances
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Compact
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.HacksAndTricks.TypePow
import LiquidTensorExperiment.Facts.Default

#align_import pseudo_normed_group.profinitely_filtered

/-!

# profinitely_filtered_pseudo_normed_group

The definition of a profinitely_filtered_pseudo_normed_group, and an API for this
definition.

-/


open PseudoNormedGroup

open scoped NNReal BigOperators

attribute [local instance] typePow

-- move this
theorem Int.induction_nonneg_or_nonpos {P : ℤ → Prop} (n : ℤ) (h₁ : ∀ n : ℕ, P n)
    (h₂ : ∀ n : ℕ, P (-n)) : P n :=
  by
  rcases le_or_lt 0 n with (hn | hn)
  · lift n to ℕ using hn; exact h₁ n
  · lift -n to ℕ using neg_nonneg.mpr hn.le with k hk; simpa only [hk, neg_neg] using h₂ k

/-- A *complete Hausdorff filtered pseudo-normed topological group* is
* an abelian group `M` with an increasing filtration `filtration M c, c : ℝ≥0` such that
* `filtration M c` is a compact Hausdorff (or T2) space
* `M` is pseudo-normed, so `0 ∈ filtration M c`, `-(filtration M c) = filtration M c`,
  and `x₁ ∈ filtration M c₁, x₂ ∈ filtration M c₂ → (x₁ + x₂) ∈ filtration M (c₁ + c₂)`
* (bounded) addition and negation are continuous.

Morphisms are continuous and bounded homomorphisms. -/
class ComphausFilteredPseudoNormedGroup (M : Type _) extends PseudoNormedGroup M where
  [topology : ∀ c, TopologicalSpace (filtration M c)]
  [t2 : ∀ c, T2Space (filtration M c)]
  --[td : ∀ c, totally_disconnected_space (filtration M c)]
  [compact : ∀ c, CompactSpace (filtration M c)]
  continuous_add' :
    ∀ c₁ c₂, Continuous (add' : filtration M c₁ × filtration M c₂ → filtration M (c₁ + c₂))
  continuous_neg' : ∀ c, Continuous (neg' : filtration M c → filtration M c)
  continuous_castLe :
    ∀ (c₁ c₂) [h : Fact (c₁ ≤ c₂)], Continuous (castLe : filtration M c₁ → filtration M c₂)

/-- A *profinitely filtered pseudo-normed topological group* is a *complete Hausdorff filtered
pseudo-normed topological group* with the additional requirement that
* `filtration M c` is a profinite set. -/
class ProfinitelyFilteredPseudoNormedGroup (M : Type _) extends
    ComphausFilteredPseudoNormedGroup M where
  -- Porting note: Lean 3 wrote the parent's field `filtration c`; here `filtration M c`
  [td : ∀ c, TotallyDisconnectedSpace (filtration M c)]

namespace ComphausFilteredPseudoNormedGroup

variable {M M₁ M₂ M₃ : Type _}

variable [ComphausFilteredPseudoNormedGroup M]

variable [ComphausFilteredPseudoNormedGroup M₁]

variable [ComphausFilteredPseudoNormedGroup M₂]

variable [ComphausFilteredPseudoNormedGroup M₃]

instance (c : ℝ≥0) : TopologicalSpace (filtration M c) :=
  topology c

instance (c : ℝ≥0) : T2Space (filtration M c) :=
  t2 c

--instance (c : ℝ≥0) : totally_disconnected_space (filtration M c) := td c
instance (c : ℝ≥0) : CompactSpace (filtration M c) :=
  compact c

theorem isClosedMap_castLe (c₁ c₂) [h : Fact (c₁ ≤ c₂)] :
    IsClosedMap (@PseudoNormedGroup.castLe M _ _ _ h) :=
  (continuous_castLe c₁ c₂).isClosedMap

theorem closedEmbedding_castLe (c₁ c₂) [h : Fact (c₁ ≤ c₂)] :
    ClosedEmbedding (@PseudoNormedGroup.castLe M _ _ _ h) :=
  closedEmbedding_of_continuous_injective_closed (continuous_castLe c₁ c₂) (injective_castLe c₁ c₂)
    (isClosedMap_castLe c₁ c₂)

theorem embedding_castLe (c₁ c₂) [h : Fact (c₁ ≤ c₂)] :
    Embedding (@PseudoNormedGroup.castLe M _ _ _ h) :=
  (closedEmbedding_castLe c₁ c₂).toEmbedding

theorem continuous_add {X : Type _} [TopologicalSpace X] (c₁ c₂ : ℝ≥0) (f : X → filtration M c₁)
    (hf : Continuous f) (g : X → filtration M c₂) (hg : Continuous g) :
    Continuous
      (fun x => ⟨f x + g x, add_mem_filtration (f x).2 (g x).2⟩ : X → filtration M (c₁ + c₂)) :=
  haveI : Continuous fun x => (f x, g x) := hf.prod_mk hg
  (continuous_add' c₁ c₂).comp this

theorem continuous_neg {X : Type _} [TopologicalSpace X] (c : ℝ≥0) (f : X → filtration M c)
    (hf : Continuous f) :
    Continuous (fun x => ⟨-f x, neg_mem_filtration (f x).2⟩ : X → filtration M c) :=
  (continuous_neg' c).comp hf

theorem continuous_nsmul {X : Type _} [TopologicalSpace X] (n : ℕ) (c : ℝ≥0)
    (f : X → filtration M c) (hf : Continuous f) :
    Continuous
      (fun x => ⟨n • f x, nat_smul_mem_filtration n _ _ (f x).2⟩ : X → filtration M (n * c)) :=
  by
  induction' n with n ih
  · simp only [Nat.zero_eq, zero_smul]
    -- Porting note: the codomain `filtration M (↑0 * c)` has to be given explicitly
    exact @continuous_const X (filtration M (↑Nat.zero * c)) _ _ ⟨0, zero_mem_filtration (M := M) _⟩
  · simp only [Nat.succ_eq_add_one, succ_nsmul']
    haveI aux1 : Fact (↑n * c ≤ n • c) := ⟨by simp only [le_refl, nsmul_eq_mul]⟩
    haveI aux2 : Fact (n • c + c ≤ ↑n.succ * c) := ⟨by simp [le_refl, nsmul_eq_mul, add_mul]⟩
    exact
      (continuous_castLe (n • c + c) (n.succ * c)).comp
        (continuous_add (n • c) c _ ((continuous_castLe _ _).comp ih) _ hf)

theorem continuous_zsmul {X : Type _} [TopologicalSpace X] (n : ℤ) (c : ℝ≥0)
    (f : X → filtration M c) (hf : Continuous f) :
    Continuous
      (fun x => ⟨n • f x, int_smul_mem_filtration n _ _ (f x).2⟩ :
        X → filtration M (n.natAbs * c)) :=
  by
  -- Porting note: Lean 4 `induction ... using` names the cases
  induction n using Int.induction_nonneg_or_nonpos with
  | h₁ n => simp only [coe_nat_zsmul]; exact continuous_nsmul n c f hf
  | h₂ n =>
    simp only [neg_smul]
    haveI : Fact (↑n * c ≤ (-n : ℤ).natAbs * c) := ⟨by simp only [Int.natAbs_ofNat, Int.natAbs_neg, le_refl]⟩
    convert
      continuous_neg _ _
        ((continuous_castLe (n * c) ((-n : ℤ).natAbs * c)).comp (continuous_nsmul n c f hf)) using
      1
    ext x
    simp only [Function.comp_apply, coe_castLe, coe_nat_zsmul, Subtype.coe_mk]

end ComphausFilteredPseudoNormedGroup

namespace ProfinitelyFilteredPseudoNormedGroup

variable {M : Type _} [ProfinitelyFilteredPseudoNormedGroup M]

instance (c : ℝ≥0) : TotallyDisconnectedSpace (filtration M c) :=
  td c

end ProfinitelyFilteredPseudoNormedGroup

section

/-- A `comphaus_filtered_pseudo_normed_group_hom` is a morphism between compact hausdorff
  filtered pseudo-normed groups. It is an additive group homomorphism which is bounded
  in the sense that there exist some constant `B` such that the filtrand at level `c`
  for the source is mapped into the filtrand at level `B*c` in the target. -/
structure ComphausFilteredPseudoNormedGroupHom (M₁ M₂ : Type _)
    [ComphausFilteredPseudoNormedGroup M₁] [ComphausFilteredPseudoNormedGroup M₂] extends
    M₁ →+ M₂ where
  bound' : ∃ C, ∀ c x, x ∈ filtration M₁ c → toFun x ∈ filtration M₂ (C * c)
  continuous' :
    ∀ ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂) (h : ∀ x : filtration M₁ c₁, toFun ↑x = f₀ x), Continuous f₀

/-- A `strict_comphaus_filtered_pseudo_normed_group_hom` is a strict morphism between compact
  hausdorff filtered pseudo-normed groups. It is an additive group homomorphism which is bounded
  in the strict sense that the filtrand at level `c` for the source is mapped into the filtrand
  at level `c` in the target. -/
structure StrictComphausFilteredPseudoNormedGroupHom (M₁ M₂ : Type _)
    [ComphausFilteredPseudoNormedGroup M₁] [ComphausFilteredPseudoNormedGroup M₂] extends
    M₁ →+ M₂ where
  strict' : ∀ c x, x ∈ filtration M₁ c → toFun x ∈ filtration M₂ c
  continuous' : ∀ c, Continuous (PseudoNormedGroup.level toFun strict' c)

end


namespace ComphausFilteredPseudoNormedGroupHom

open ComphausFilteredPseudoNormedGroup

variable {M M₁ M₂ M₃ : Type _}

variable [ComphausFilteredPseudoNormedGroup M]

variable [ComphausFilteredPseudoNormedGroup M₁]

variable [ComphausFilteredPseudoNormedGroup M₂]

variable [ComphausFilteredPseudoNormedGroup M₃]

variable (f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂)

instance : CoeFun (ComphausFilteredPseudoNormedGroupHom M₁ M₂) fun _ => M₁ → M₂ :=
  -- Porting note: Lean 4 has no projection constant for the inherited field `toFun`
  ⟨fun f => f.toFun⟩

-- Porting note: a custom `simps` projection for the coercion; without it `@[simps]` loops
/-- See Note [custom simps projection]. -/
def Simps.apply (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) : M₁ → M₂ := f

initialize_simps_projections ComphausFilteredPseudoNormedGroupHom (toFun → apply)

@[simp]
theorem coe_mk (f) (h₁) (h₂) (h₃) (h₄) :
    ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : ComphausFilteredPseudoNormedGroupHom M₁ M₂) = f :=
  rfl

@[simp]
theorem mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) :
    (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : ComphausFilteredPseudoNormedGroupHom M₁ M₂).toAddMonoidHom =
      ⟨⟨f, h₁⟩, h₂⟩ :=
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
theorem map_sum {ι : Type _} (x : ι → M₁) (s : Finset ι) : f (∑ i in s, x i) = ∑ i in s, f (x i) :=
  f.toAddMonoidHom.map_sum _ _

@[simp]
theorem map_sub (x y) : f (x - y) = f x - f y :=
  f.toAddMonoidHom.map_sub _ _

@[simp]
theorem map_neg (x) : f (-x) = -f x :=
  f.toAddMonoidHom.map_neg _

@[simp]
theorem map_zsmul (x) (n : ℤ) : f (n • x) = n • f x :=
  f.toAddMonoidHom.map_zsmul _ _

/-- Make a profinitely filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mkOfBound (f : M₁ →+ M₂) (C : ℝ≥0)
    (hC :
      ∀ c,
        ∃ H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c),
          @Continuous (filtration M₁ c) (filtration M₂ (C * c)) _ _ fun x => ⟨f x, H x x.2⟩) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  { f with
    bound' := ⟨C, fun c => (hC c).choose⟩
    continuous' := fun c₁ c₂ f₀ hf₀ => by
      obtain ⟨_, H⟩ := hC c₁
      haveI : Fact (C * c₁ ≤ max (C * c₁) c₂) := ⟨le_max_left _ _⟩
      haveI : Fact (c₂ ≤ max (C * c₁) c₂) := ⟨le_max_right _ _⟩
      rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe c₂ (max (C * c₁) c₂)).continuous_iff]
      rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe (C * c₁) (max (C * c₁) c₂)).continuous_iff] at H 
      convert H using 1
      ext; dsimp; rw [← hf₀]; rfl }

/-- Make a profinitely filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mkOfStrict (f : M₁ →+ M₂)
    (h :
      ∀ c,
        ∃ H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ c,
          @Continuous (filtration M₁ c) (filtration M₂ c) _ _ fun x => ⟨f x, H x x.2⟩) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  mkOfBound f 1 fun c => by
    obtain ⟨w, H⟩ := h c
    refine' ⟨_, _⟩
    · simpa only [one_mul]
    · rwa [(ComphausFilteredPseudoNormedGroup.embedding_castLe (1 * c) c).continuous_iff]

/-- Make a profinitely filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
noncomputable def mk' (f : M₁ →+ M₂)
    (h :
      ∃ C,
        ∀ c,
          ∃ H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c),
            @Continuous (filtration M₁ c) (filtration M₂ (C * c)) _ _ fun x => ⟨f x, H x x.2⟩) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  mkOfBound f h.choose h.choose_spec

@[simp]
theorem coe_mkOfBound (f : M₁ →+ M₂) (C) (h) : ⇑(mkOfBound f C h) = f :=
  rfl

@[simp]
theorem coe_mk' (f : M₁ →+ M₂) (h) : ⇑(mk' f h) = f :=
  rfl

def Strict : Prop :=
  ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ c

/-- If `f : comphaus_filtered_pseudo_normed_group_hom M₁ M₂` and `r : ℝ≥0` then
  `f.bound_by r` is the statement that `f` maps the `c`th filtrand of `M₁` into the `r*c`th
  filtrand of `M₂`. -/
def BoundBy (C : ℝ≥0) : Prop :=
  ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ (C * c)

theorem strict_iff_boundBy_one : f.Strict ↔ f.BoundBy 1 := by simp only [Strict, BoundBy, one_mul]

variable {f}

theorem BoundBy.mono {C₁} (hf : f.BoundBy C₁) (C₂ : ℝ≥0) (H : C₁ ≤ C₂) : f.BoundBy C₂ :=
  fun c x hx => filtration_mono (mul_le_mul' H le_rfl) (hf hx)

theorem Strict.boundByOne (hf : f.Strict) : f.BoundBy 1 :=
  f.strict_iff_boundBy_one.1 hf

theorem BoundBy.strict (hf : f.BoundBy 1) : f.Strict :=
  f.strict_iff_boundBy_one.2 hf

variable (f)

theorem bound : ∃ C, f.BoundBy C :=
  f.bound'

theorem mkOfBoundBoundBy (f : M₁ →+ M₂) (C) (h) : (mkOfBound f C h).BoundBy C := fun c => (h c).choose

theorem mkOfStrictStrict (f : M₁ →+ M₂) (h) : (mkOfStrict f h).Strict := fun c => (h c).choose

protected theorem continuous ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂)
    (h : ∀ x : filtration M₁ c₁, f ↑x = f₀ x) : Continuous f₀ :=
  f.continuous' f₀ h

-- /-- `f.level c` is the function `filtration M₁ c → filtration M₂ c`
-- induced by a `profinitely_filtered_pseudo_normed_group_hom M₁ M₂`. -/
-- @[simps] def level (c : ℝ≥0) (x : filtration M₁ c) : filtration M₂ c := ⟨f x, f.strict x.2⟩
-- lemma level_continuous (c : ℝ≥0) : continuous (f.level c) := f.continuous' c
variable {f g}

@[ext]
-- Porting note: Lean 4 does not flatten the `AddMonoidHom` parent, so use its `ext`
theorem ext (H : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; exact AddMonoidHom.ext H

instance : Zero (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨mkOfBound (0 : M₁ →+ M₂) 0 fun c =>
      ⟨fun _ _ => zero_mem_filtration _, @continuous_const _ _ _ _ 0⟩⟩

instance : Inhabited (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨0⟩

theorem zeroBoundByZero : (0 : ComphausFilteredPseudoNormedGroupHom M₁ M₂).BoundBy 0 :=
  mkOfBoundBoundBy _ _ _

theorem coe_inj ⦃f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂⦄ (h : (f : M₁ → M₂) = g) :
    f = g :=
  ext (congrFun h)

/-- The identity function as `profinitely_filtered_pseudo_normed_group_hom`. -/
@[simps]
def id : ComphausFilteredPseudoNormedGroupHom M M :=
  mkOfBound (AddMonoidHom.id _) 1 <| by
    refine' fun c => ⟨_, _⟩
    · intros; rwa [one_mul]
    haveI : Fact (1 * c ≤ c) := by rw [one_mul]; exact ⟨le_rfl⟩
    rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe (1 * c) c).continuous_iff]
    convert continuous_id

-- Porting note: `@[simps]` must unfold `mk'` (as Lean 3's did), hence `rhsMd := .default`
/-- The composition of `profinitely_filtered_pseudo_normed_group_hom`s. -/
@[simps (config := { rhsMd := .default })]
noncomputable def comp (g : ComphausFilteredPseudoNormedGroupHom M₂ M₃)
    (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) : ComphausFilteredPseudoNormedGroupHom M₁ M₃ :=
  mk' (g.toAddMonoidHom.comp f.toAddMonoidHom) <|
    by
    obtain ⟨Cf, hCf⟩ := f.bound
    obtain ⟨Cg, hCg⟩ := g.bound
    refine' ⟨Cg * Cf, fun c => ⟨_, _⟩⟩
    · intro x hx; rw [mul_assoc]; exact hCg (hCf hx)
    let f₀ : filtration M₁ c → filtration M₂ (Cf * c) := fun x => ⟨f x, hCf x.2⟩
    have hf₀ : Continuous f₀ := f.continuous _ fun x => rfl
    let g₀ : filtration M₂ (Cf * c) → filtration M₃ (Cg * (Cf * c)) := fun x => ⟨g x, hCg x.2⟩
    have hg₀ : Continuous g₀ := g.continuous _ fun x => rfl
    haveI : Fact (Cg * Cf * c ≤ Cg * (Cf * c)) := by rw [mul_assoc]; exact ⟨le_rfl⟩
    rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe (Cg * Cf * c) (Cg * (Cf * c))).continuous_iff]
    exact hg₀.comp hf₀

theorem BoundBy.id : (id : ComphausFilteredPseudoNormedGroupHom M M).BoundBy 1 :=
  by
  intro c x hx
  rwa [one_mul]

theorem BoundBy.comp {f' : ComphausFilteredPseudoNormedGroupHom M₂ M₃} {C₁ C₂ : ℝ≥0}
    (hf : f.BoundBy C₁) (hf' : f'.BoundBy C₂) : (f'.comp f).BoundBy (C₂ * C₁) :=
  by
  intro c x hx
  rw [mul_assoc]
  exact hf' (hf hx)

end ComphausFilteredPseudoNormedGroupHom

namespace StrictComphausFilteredPseudoNormedGroupHom

open ComphausFilteredPseudoNormedGroup

variable {M M₁ M₂ M₃ : Type _}

variable [ComphausFilteredPseudoNormedGroup M]

variable [ComphausFilteredPseudoNormedGroup M₁]

variable [ComphausFilteredPseudoNormedGroup M₂]

variable [ComphausFilteredPseudoNormedGroup M₃]

variable (f g : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂)

instance : CoeFun (StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) fun _ => M₁ → M₂ :=
  -- Porting note: Lean 4 has no projection constant for the inherited field `toFun`
  ⟨fun f => f.toFun⟩

-- Porting note: a custom `simps` projection for the coercion; without it `@[simps]` loops
/-- See Note [custom simps projection]. -/
def Simps.apply (f : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) : M₁ → M₂ := f

initialize_simps_projections StrictComphausFilteredPseudoNormedGroupHom (toFun → apply)

@[simp]
theorem coe_mk (f) (h₁) (h₂) (h₃) (h₄) :
    ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) = f :=
  rfl

@[simp]
theorem mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) :
    (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂).toAddMonoidHom =
      ⟨⟨f, h₁⟩, h₂⟩ :=
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
theorem map_sum {ι : Type _} (x : ι → M₁) (s : Finset ι) : f (∑ i in s, x i) = ∑ i in s, f (x i) :=
  f.toAddMonoidHom.map_sum _ _

@[simp]
theorem map_sub (x y) : f (x - y) = f x - f y :=
  f.toAddMonoidHom.map_sub _ _

@[simp]
theorem map_neg (x) : f (-x) = -f x :=
  f.toAddMonoidHom.map_neg _

@[simp]
theorem map_zsmul (x) (n : ℤ) : f (n • x) = n • f x :=
  f.toAddMonoidHom.map_zsmul _ _

/-- Make a strict comphaus filtered pseudo-normed group hom
from a group hom and a proof that it is bounded and continuous. -/
def mk' (f : M₁ →+ M₂)
    (h :
      ∀ c,
        ∃ H : ∀ x, x ∈ filtration M₁ c → f x ∈ filtration M₂ c,
          @Continuous (filtration M₁ c) (filtration M₂ c) _ _ fun x => ⟨f x, H x x.2⟩) :
    StrictComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  { f with
    strict' := fun c x hh => (h c).choose x hh
    continuous' := fun c => (h c).choose_spec }

@[simp]
theorem coe_mk' (f : M₁ →+ M₂) (h) : ⇑(mk' f h) = f :=
  rfl

theorem strict ⦃c x⦄ : x ∈ filtration M₁ c → f x ∈ filtration M₂ c :=
  f.strict' c x

def level {c} : filtration M₁ c → filtration M₂ c :=
  PseudoNormedGroup.level f f.strict c

protected theorem level_continuous (c) : Continuous (PseudoNormedGroup.level f f.strict c) :=
  f.continuous' _

@[simp]
protected theorem level_castLe' {c₁ c₂} (h : c₁ ≤ c₂) (x : filtration M₁ c₁) :
    f.level (castLe' h x) = castLe' h (f.level x) :=
  rfl

@[simp]
protected theorem level_zero {c} : f.level (0 : filtration M₁ c) = 0 :=
  by
  ext
  dsimp
  rw [← f.map_zero]
  rfl

@[simp]
protected theorem level_neg {c} (x : filtration M₁ c) : f.level (-x) = -f.level x :=
  by
  ext
  dsimp
  erw [← f.map_neg]
  rfl

@[simp]
protected theorem level_add {c₁ c₂} (x : filtration M₁ c₁ × filtration M₁ c₂) :
    f.level (add' x) = add' ⟨f.level x.1, f.level x.2⟩ :=
  by
  ext
  dsimp
  erw [← f.map_add]
  rfl

@[simp]
theorem coe_level {c} (x : filtration M₁ c) : (f.level x : M₂) = f x :=
  rfl

variable {f g}

@[ext]
-- Porting note: Lean 4 does not flatten the `AddMonoidHom` parent, so use its `ext`
theorem ext (H : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; exact AddMonoidHom.ext H

instance : Zero (StrictComphausFilteredPseudoNormedGroupHom M₁ M₂)
    where zero :=
    {
      (0 : M₁ →+
          M₂) with
      strict' := fun c x h => PseudoNormedGroup.zero_mem_filtration _
      continuous' := fun c =>
        by
        let e : filtration M₁ c → filtration M₂ c := fun x =>
          ⟨0, PseudoNormedGroup.zero_mem_filtration _⟩
        exact (continuous_const : Continuous e) }

instance : Inhabited (StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨0⟩

theorem coe_inj ⦃f g : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂⦄ (h : (f : M₁ → M₂) = g) :
    f = g :=
  ext (congrFun h)

/-- The identity function as `profinitely_filtered_pseudo_normed_group_hom`. -/
@[simps]
def id : StrictComphausFilteredPseudoNormedGroupHom M M :=
  -- Porting note: the `AddMonoidHom` parent is given by name instead of as a `with` source
  { toAddMonoidHom := AddMonoidHom.id M
    strict' := fun c x h => h
    continuous' := fun c => by
      convert continuous_id }

/-- The composition of `profinitely_filtered_pseudo_normed_group_hom`s. -/
@[simps (config := { rhsMd := .default })]
def comp (g : StrictComphausFilteredPseudoNormedGroupHom M₂ M₃)
    (f : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    StrictComphausFilteredPseudoNormedGroupHom M₁ M₃ :=
  { toAddMonoidHom := g.toAddMonoidHom.comp f.toAddMonoidHom
    strict' := fun c x h => g.strict <| f.strict h
    continuous' := fun c => (g.level_continuous c).comp (f.level_continuous c) }

/-- If `f` is a strict morphism between compact hausdorff filtered pseudo-normed groups
  then `f.to_chfpsng_hom` is the corresponding morphism where we forget strictness.  -/
def toChfpsngHom (f : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  ComphausFilteredPseudoNormedGroupHom.mkOfStrict f.toAddMonoidHom fun c =>
    ⟨fun x h => f.strict h, f.level_continuous _⟩

-- Porting note: `@[simps]` cannot see through `mkOfStrict` here, so the lemma is stated by hand
@[simp]
theorem toChfpsngHom_apply (f : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) (x : M₁) :
    toChfpsngHom f x = f x :=
  rfl

theorem toChfpsngHom.boundByOne (f : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    (toChfpsngHom f).BoundBy 1 := fun c m hmc =>
  by
  rw [one_mul]
  exact f.strict hmc

end StrictComphausFilteredPseudoNormedGroupHom

namespace ComphausFilteredPseudoNormedGroupHom

variable {M₁ M₂ : Type _}

variable [ComphausFilteredPseudoNormedGroup M₁]

variable [ComphausFilteredPseudoNormedGroup M₂]

def Strict.toSchfpsngHom {f : ComphausFilteredPseudoNormedGroupHom M₁ M₂} (h : f.Strict) :
    StrictComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  { f.toAddMonoidHom with
    strict' := h
    continuous' := fun c => f.continuous _ fun x => rfl }

end ComphausFilteredPseudoNormedGroupHom

namespace PUnit

instance : ProfinitelyFilteredPseudoNormedGroup PUnit
    where
  filtration' _ := Set.univ
  filtration_mono' _ _ _ := Set.subset_univ _
  zero_mem_filtration' _ := Set.mem_univ _
  neg_mem_filtration' _ _ _ := Set.mem_univ _
  add_mem_filtration' _ _ _ _ _ _ := Set.mem_univ _
  continuous_add' _ _ := continuous_of_discreteTopology
  continuous_neg' _ := continuous_of_discreteTopology
  continuous_castLe _ _ _ := continuous_of_discreteTopology

end PUnit

section Continuity

variable {M M₁ M₂ M₃ : Type _}

namespace PseudoNormedGroup

/-- Helper function for pseudo-normed groups.
`pow_incl` is the natural inclusion function `(filtration M c)^n → M^n`.
Note that `(filtration M c)^n` is not the same type as `filtration (M^n) c`,
although they are naturally equivalent. -/
def powIncl {n : ℕ} {c : ℝ≥0} [PseudoNormedGroup M] : (filtration M c : Type _) ^ n → M ^ n :=
  fun x j => x j

theorem powIncl_injective {n : ℕ} {c : ℝ≥0} [PseudoNormedGroup M] :
    Function.Injective (@powIncl M n c _) := fun x y h =>
  funext fun j => Subtype.coe_injective <| congr_fun h j

@[simp]
theorem powIncl_apply {n : ℕ} {c : ℝ≥0} [PseudoNormedGroup M] (x : (filtration M c : Type _) ^ n)
    (j : Fin n) : powIncl x j = x j :=
  rfl

end PseudoNormedGroup

open PseudoNormedGroup ComphausFilteredPseudoNormedGroup

variable [ComphausFilteredPseudoNormedGroup M]

variable [ComphausFilteredPseudoNormedGroup M₁]

variable [ComphausFilteredPseudoNormedGroup M₂]

variable [ComphausFilteredPseudoNormedGroup M₃]

/-- A function `f : M₁ → M₂` between profinitely filtered pseudo-normed groups
is continuous if it is continuous when restricted to the filtration sets.

Implementation detail: to avoid diamonds of topologies on `filtration M c`
we avoid `topological_space M`.
We therefore give a hands on definition of continuity. -/
def PfpngCtu (f : M₁ → M₂) : Prop :=
  ∀ ⦃c₁ c₂⦄ (f₀ : filtration M₁ c₁ → filtration M₂ c₂) (h : ∀ x : filtration M₁ c₁, f ↑x = f₀ x), Continuous f₀

section PfpngCtu

theorem pfpngCtuConst (y : M₂) : PfpngCtu fun x : M₁ => y :=
  by
  intro c₁ c₂ f₀ h
  suffices f₀ = fun x => f₀ ⟨0, zero_mem_filtration _⟩ by rw [this]; exact continuous_const
  ext1 x
  apply Subtype.coe_injective
  dsimp only
  rw [← h, ← h]

theorem PfpngCtu.neg {f : M₁ → M₂} (hf : PfpngCtu f) : PfpngCtu (-f) :=
  by
  intro c₁ c₂ f₀ h
  let g := neg' ∘ f₀
  have hg : f₀ = neg' ∘ g := by ext; simp [neg_neg]
  rw [hg]
  refine' (continuous_neg' c₂).comp (hf g _)
  intro x
  specialize h x
  simp only [g, Function.comp_apply, ← h, neg_neg, Pi.neg_apply, neg'_eq]

theorem PfpngCtu.add {f g : M₁ → M₂} (hf : PfpngCtu f) (hg : PfpngCtu g)
    (H : ∀ c₁, ∃ c₂, ∀ x : filtration M₁ c₁, f x ∈ filtration M₂ c₂) : PfpngCtu (f + g) :=
  by
  intro c₁ c₂ fg₀ hfg₀
  obtain ⟨cf, hcf⟩ := H c₁
  let f₀ : filtration M₁ c₁ → filtration M₂ cf := fun x => ⟨f x, hcf x⟩
  have hf₀ : ∀ x : filtration M₁ c₁, f ↑x = f₀ x := fun x => rfl
  have f₀_ctu : Continuous f₀ := hf f₀ hf₀
  let cg := cf + c₂
  haveI : Fact (c₂ ≤ cf + cg) :=
    ⟨calc
        c₂ ≤ cf + c₂ := self_le_add_left _ _
        _ ≤ cf + (cf + c₂) := self_le_add_left _ _⟩
  have hcg : ∀ x : filtration M₁ c₁, g x ∈ filtration M₂ cg :=
    by
    intro x
    have : g x = -f x + (f + g) x := by simp only [Pi.add_apply, neg_add_cancel_left]
    rw [this]
    refine' add_mem_filtration (neg_mem_filtration <| hcf x) _
    rw [hfg₀]
    exact (fg₀ x).2
  let g₀ : filtration M₁ c₁ → filtration M₂ cg := fun x => ⟨g x, hcg x⟩
  have hg₀ : ∀ x : filtration M₁ c₁, g ↑x = g₀ x := fun x => rfl
  have g₀_ctu : Continuous g₀ := hg g₀ hg₀
  have aux := f₀_ctu.prod_mk g₀_ctu
  rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe c₂ (cf + cg)).continuous_iff]
  convert (continuous_add' cf cg).comp aux using 1
  ext; dsimp; rw [← hfg₀, Pi.add_apply]

theorem PfpngCtu.sub {f g : M₁ → M₂} (hf : PfpngCtu f) (hg : PfpngCtu g)
    (H : ∀ c₁, ∃ c₂, ∀ x : filtration M₁ c₁, f x ∈ filtration M₂ c₂) : PfpngCtu (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg H

variable (M)

theorem pfpngCtuId : PfpngCtu (@id M) := by
  intro c₁ c₂ f₀ h
  haveI : Fact (c₁ ≤ max c₁ c₂) := ⟨le_max_left _ _⟩
  haveI : Fact (c₂ ≤ max c₁ c₂) := ⟨le_max_right _ _⟩
  have : @castLe M _ c₂ (max c₁ c₂) _ ∘ f₀ = castLe := by ext; dsimp; rw [← h]; rfl
  rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe c₂ (max c₁ c₂)).continuous_iff, this]
  exact (ComphausFilteredPseudoNormedGroup.embedding_castLe _ _).continuous

theorem pfpngCtuSmulNat : ∀ n : ℕ, PfpngCtu fun x : M => n • x
  | 0 => by simp only [zero_smul]; exact pfpngCtuConst 0
  | n + 1 => by
    simp only [add_smul, one_smul, add_comm]
    exact (pfpngCtuId M).add (pfpngCtuSmulNat n) fun c => ⟨c, fun x => x.2⟩

theorem pfpngCtuSmulInt : ∀ n : ℤ, PfpngCtu fun x : M => n • x
  | (n : ℕ) => by simpa only [coe_nat_zsmul] using pfpngCtuSmulNat M n
  | .negSucc n => by simpa only [negSucc_zsmul] using (pfpngCtuSmulNat M (n + 1)).neg

end PfpngCtu

end Continuity

namespace ComphausFilteredPseudoNormedGroupHom

variable {M M₁ M₂ : Type _}

variable [ComphausFilteredPseudoNormedGroup M]

variable [ComphausFilteredPseudoNormedGroup M₁]

variable [ComphausFilteredPseudoNormedGroup M₂]

@[simps]
def copy (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) (g : M₁ → M₂) (h : g = f) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  { f.toAddMonoidHom.copy g h with
    toFun := g
    bound' := by cases h; exact f.bound
    continuous' := by cases h; exact f.continuous' }

def add (f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  { f.toAddMonoidHom + g.toAddMonoidHom with
    toFun := f + g
    bound' := by
      obtain ⟨Cf, hCf⟩ := f.bound
      obtain ⟨Cg, hCg⟩ := g.bound
      refine' ⟨Cf + Cg, fun c x hx => _⟩
      rw [add_mul]
      apply add_mem_filtration (hCf hx) (hCg hx)
    continuous' := by
      apply PfpngCtu.add f.continuous g.continuous
      obtain ⟨Cf, hCf⟩ := f.bound
      intro c₁
      refine' ⟨Cf * c₁, fun x => hCf x.2⟩ }

def neg (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  { -f.toAddMonoidHom with
    toFun := -f
    bound' := by
      obtain ⟨Cf, hCf⟩ := f.bound
      refine' ⟨Cf, fun c x hx => _⟩
      apply neg_mem_filtration (hCf hx)
    continuous' := PfpngCtu.neg f.continuous }

def sub (f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  (f.add g.neg).copy (f - g) (sub_eq_add_neg _ _)

def nsmul' :
    ∀ (n : ℕ) (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂),
      ComphausFilteredPseudoNormedGroupHom M₁ M₂
  | 0, f => 0
  | n + 1, f => f.add (nsmul' n f)

def nsmul (n : ℕ) (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  (f.nsmul' n).copy (n • f)
    (by
      induction' n with n ih
      · rw [Nat.zero_eq, zero_smul]; rfl
      · rw [succ_nsmul, ih]; rfl)

def zsmul' :
    ∀ (n : ℤ) (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂),
      ComphausFilteredPseudoNormedGroupHom M₁ M₂
  | (n : ℕ), f => f.nsmul n
  | .negSucc n, f => (f.nsmul n.succ).neg

def zsmul (n : ℤ) (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  (f.zsmul' n).copy (n • f)
    (by
      cases n
      · rw [Int.ofNat_eq_coe, ofNat_zsmul]; rfl
      · rw [negSucc_zsmul]; rfl)

instance : Add (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨add⟩

instance : Neg (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨neg⟩

instance : Sub (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨sub⟩

instance hasNsmul : SMul ℕ (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨nsmul⟩

instance hasZsmul : SMul ℤ (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  ⟨zsmul⟩

instance : AddCommGroup (ComphausFilteredPseudoNormedGroupHom M₁ M₂) :=
  Function.Injective.addCommGroup ComphausFilteredPseudoNormedGroupHom.toAddMonoidHom
    (fun f g h => by ext x; rw [AddMonoidHom.ext_iff] at h ; exact h x) rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

@[simps]
def toAddMonoidHomHom : ComphausFilteredPseudoNormedGroupHom M₁ M₂ →+ M₁ →+ M₂
    where
  toFun := toAddMonoidHom
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toAddMonoidHomHom_injective : Function.Injective (@toAddMonoidHomHom M₁ M₂ _ _) :=
  fun f g h => by ext x; exact AddMonoidHom.congr_fun h x

theorem BoundBy.add {f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂} {Cf Cg : ℝ≥0}
    (hf : f.BoundBy Cf) (hg : g.BoundBy Cg) : (f + g).BoundBy (Cf + Cg) := fun c x hx => by
  rw [add_mul]; exact add_mem_filtration (hf hx) (hg hx)

theorem BoundBy.sub {f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂} {Cf Cg : ℝ≥0}
    (hf : f.BoundBy Cf) (hg : g.BoundBy Cg) : (f - g).BoundBy (Cf + Cg) := fun c x hx => by
  rw [add_mul]; exact sub_mem_filtration (hf hx) (hg hx)

theorem BoundBy.neg {f : ComphausFilteredPseudoNormedGroupHom M₁ M₂} {Cf : ℝ≥0}
    (hf : f.BoundBy Cf) : (-f).BoundBy Cf := fun c x hx => neg_mem_filtration (hf hx)

theorem BoundBy.nsmul {f : ComphausFilteredPseudoNormedGroupHom M₁ M₂} {Cf : ℝ≥0}
    (hf : f.BoundBy Cf) (n : ℕ) : (n • f).BoundBy (n * Cf) := fun c x hx =>
  filtration_mono (mul_assoc _ _ _).ge (nat_smul_mem_filtration n _ _ (hf hx))

theorem BoundBy.zsmul {f : ComphausFilteredPseudoNormedGroupHom M₁ M₂} {Cf : ℝ≥0}
    (hf : f.BoundBy Cf) (n : ℤ) : (n • f).BoundBy (n.natAbs * Cf) := fun c x hx =>
  filtration_mono (mul_assoc _ _ _).ge (int_smul_mem_filtration n _ _ (hf hx))

@[simp]
theorem add_apply (f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂) (x : M₁) :
    (f + g) x = f x + g x :=
  rfl

@[simp]
theorem sub_apply (f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂) (x : M₁) :
    (f - g) x = f x - g x :=
  rfl

@[simp]
theorem sum_apply {ι : Type _} (s : Finset ι) (f : ι → ComphausFilteredPseudoNormedGroupHom M₁ M₂)
    (x : M₁) : (∑ i in s, f i) x = ∑ i in s, f i x := by
  classical
  -- Porting note: `apply Finset.induction_on s` is written with `induction ... using`
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | @insert i s his IH =>
    simp only [Finset.sum_insert his, add_apply, IH]

theorem sumBoundBy {ι : Type _} (s : Finset ι) (f : ι → ComphausFilteredPseudoNormedGroupHom M₁ M₂)
    (C : ι → ℝ≥0) (hf : ∀ i ∈ s, (f i).BoundBy (C i)) : (∑ i in s, f i).BoundBy (∑ i in s, C i) :=
  by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro; simp only [Finset.sum_empty]; exact zeroBoundByZero
  | @insert i s his IH =>
    intro hf
    simp only [Finset.sum_insert his]
    apply (hf _ (s.mem_insert_self i)).add (IH fun j hj => hf _ <| Finset.mem_insert_of_mem hj)

@[simp]
theorem nsmul_apply {M N : Type _} [ComphausFilteredPseudoNormedGroup M]
    [ComphausFilteredPseudoNormedGroup N] (n : ℕ) (f : ComphausFilteredPseudoNormedGroupHom M N)
    (x : M) : (n • f) x = n • f x :=
  rfl

@[simp]
theorem zero_apply (M N : Type _) [ComphausFilteredPseudoNormedGroup M]
    [ComphausFilteredPseudoNormedGroup N] (x : M) :
    (0 : ComphausFilteredPseudoNormedGroupHom M N) x = 0 :=
  rfl

end ComphausFilteredPseudoNormedGroupHom

namespace ComphausFilteredPseudoNormedGroup

/-! ## Products -/


section Pi

variable {ι : Type _} (M : ι → Type _) [∀ i, ComphausFilteredPseudoNormedGroup (M i)]

instance piTopology (c : ℝ≥0) : TopologicalSpace (filtration (∀ i, M i) c) :=
  TopologicalSpace.induced (filtrationPiEquiv M c) <| inferInstance

@[simps apply symm_apply]
def filtrationPiHomeo (c : ℝ≥0) : filtration (∀ i, M i) c ≃ₜ ∀ i, filtration (M i) c
    where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => x i, fun i => (x i).2⟩
  left_inv := by rintro ⟨x, hx⟩; rfl
  right_inv := by intro x; ext; rfl
  continuous_toFun := by
    rw [continuous_def]
    intro U hU
    rw [isOpen_induced_iff]
    refine' ⟨U, hU, _⟩
    rfl
  continuous_invFun := by
    rw [continuous_def]
    rintro s ⟨t, ht, s_eq⟩
    -- Porting note: Lean 3's `continuous_def.1 _` left the continuity of this map (which is
    -- the identity) as a side goal; it is given explicitly
    have : Continuous fun x : (∀ i, filtration (M i) c) =>
        filtrationPiEquiv M c ⟨fun i => x i, fun i => (x i).2⟩ :=
      continuous_id
    simpa [← s_eq] using continuous_def.1 this t ht

instance pi_t2 (c : ℝ≥0) : T2Space (filtration (∀ i, M i) c) :=
  by
  have : T2Space (∀ i, filtration (M i) c) := inferInstance
  apply
    @Embedding.t2Space _ _ _ _ this (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c) (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c).embedding

/-
instance pi_td (c : ℝ≥0) : totally_disconnected_space (filtration (Π i, M i) c) :=
begin
  obtain ⟨H⟩ : totally_disconnected_space (Π i, filtration (M i) c) := infer_instance,
  rw [← homeomorph.range_coe (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c), ← set.image_univ] at H,
  exact ⟨embedding.is_totally_disconnected (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c).embedding H⟩,
end
-/
instance pi_compact (c : ℝ≥0) : CompactSpace (filtration (∀ i, M i) c) :=
  by
  obtain ⟨H⟩ : CompactSpace (∀ i, filtration (M i) c) := inferInstance
  rw [← Homeomorph.isCompact_image (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c).symm, Set.image_univ,
    Homeomorph.range_coe] at H 
  exact ⟨H⟩

def prodPiHomeoPiProd [∀ i, ComphausFilteredPseudoNormedGroup (M i)] (c₁ c₂ : ℝ≥0) :
    filtration (∀ i, M i) c₁ × filtration (∀ i, M i) c₂ ≃ₜ
      ∀ i, filtration (M i) c₁ × filtration (M i) c₂
    where
  toFun x i := ⟨⟨x.1.1 i, x.1.2 i⟩, ⟨x.2.1 i, x.2.2 i⟩⟩
  invFun x := ⟨⟨fun i => (x i).1.1, fun i => (x i).1.2⟩, ⟨fun i => (x i).2.1, fun i => (x i).2.2⟩⟩
  left_inv := by rintro ⟨x, hx⟩; simp only [Subtype.coe_eta]
  right_inv := by intro x; ext <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.prod_mk
    have h₁ := (Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₁)).mpr
      (continuous_fst : Continuous (Prod.fst : filtration (∀ i, M i) c₁ × filtration (∀ i, M i) c₂ → _))
    exact (continuous_apply i).comp h₁
    -- Porting note: the domain of `Prod.snd` has to be given in Lean 4
    have h₂ := (Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₂)).mpr
      (continuous_snd : Continuous (Prod.snd : filtration (∀ i, M i) c₁ × filtration (∀ i, M i) c₂ → _))
    exact (continuous_apply i).comp h₂
  continuous_invFun := by
    apply Continuous.prod_mk
    let f₁ : (∀ i, filtration (M i) c₁ × filtration (M i) c₂) → filtration (∀ i, M i) c₁ := fun x =>
      ⟨fun i : ι => (x i).fst.val, fun i => (x i).fst.prop⟩
    have : Continuous (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₁ ∘ f₁) :=
      by
      apply continuous_pi
      intro i
      dsimp [ComphausFilteredPseudoNormedGroup.filtrationPiHomeo, f₁]
      simp only [Subtype.coe_eta]
      exact continuous_fst.comp (continuous_apply i)
    exact (Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₁)).mp this
    let f₂ : (∀ i, filtration (M i) c₁ × filtration (M i) c₂) → filtration (∀ i, M i) c₂ := fun x =>
      ⟨fun i : ι => (x i).snd.val, fun i => (x i).snd.prop⟩
    have : Continuous (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₂ ∘ f₂) :=
      by
      apply continuous_pi
      intro i
      dsimp [ComphausFilteredPseudoNormedGroup.filtrationPiHomeo, f₂]
      simp only [Subtype.coe_eta]
      exact continuous_snd.comp (continuous_apply i)
    exact (Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₂)).mp this

instance pi : ComphausFilteredPseudoNormedGroup (∀ i, M i) :=
  {
    PseudoNormedGroup.pi
      M with
    continuous_add' := by
      intro c₁ c₂
      rw [← Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M (c₁ + c₂)), ←
        Homeomorph.comp_continuous_iff' (ComphausFilteredPseudoNormedGroup.prodPiHomeoPiProd M c₁ c₂).symm]
      apply continuous_pi
      intro i
      exact (continuous_add' c₁ c₂).comp (continuous_apply i)
    continuous_neg' := by
      intro c
      rw [← Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c), ←
        Homeomorph.comp_continuous_iff' (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c).symm]
      apply continuous_pi
      intro i
      exact (continuous_neg' c).comp (continuous_apply i)
    continuous_castLe := by
      intro c₁ c₂ h
      rw [← Homeomorph.comp_continuous_iff (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₂), ←
        Homeomorph.comp_continuous_iff' (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₁).symm]
      apply continuous_pi
      intro i
      exact (continuous_castLe (M := M i) c₁ c₂).comp (continuous_apply i) }

variable {M}

@[simps]
def piProj (i : ι) : ComphausFilteredPseudoNormedGroupHom (∀ i, M i) (M i) :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBound (Pi.evalAddMonoidHom M i) 1 <|
    by
    refine' fun c => ⟨fun x hx => by rw [one_mul]; exact hx i, _⟩
    have hc := (continuous_apply i).comp (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c).continuous
    haveI : Fact (c ≤ 1 * c) := by rw [one_mul]; exact ⟨le_rfl⟩
    -- Porting note: the continuity hypothesis is named, since `haveI` shadows `this`
    rw [(ComphausFilteredPseudoNormedGroup.embedding_castLe (M := M i) c (1 * c)).continuous_iff] at hc
    convert hc using 0

theorem piProjBoundBy (i : ι) : (@piProj _ M _ i).BoundBy 1 :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ _ _

/-- Universal property of the product of profinitely filtered pseudo-normed groups -/
@[simps (config := { fullyApplied := false })]
def piLift {N : Type _} [ComphausFilteredPseudoNormedGroup N]
    (f : ∀ i, ComphausFilteredPseudoNormedGroupHom N (M i)) (hf : ∃ C, ∀ i, (f i).BoundBy C) :
    ComphausFilteredPseudoNormedGroupHom N (∀ i, M i) :=
  {
    AddMonoidHom.mkToPi fun i =>
      (f i).toAddMonoidHom with
    toFun := AddMonoidHom.mkToPi fun i => (f i).toAddMonoidHom
    bound' := by obtain ⟨C, hC⟩ := hf; refine' ⟨C, fun c x hx i => hC i hx⟩
    continuous' := by
      intro c₁ c₂ f₀ hf₀
      rw [continuous_induced_rng]
      apply continuous_pi
      intro i
      let g := Function.eval i ∘ ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c₂ ∘ f₀
      refine' (f i).continuous g fun x => _
      specialize hf₀ x; rw [Function.funext_iff] at hf₀ 
      exact hf₀ i }

noncomputable def piMap {N : ι → Type _} [∀ i, ComphausFilteredPseudoNormedGroup (N i)]
    (f : ∀ i, ComphausFilteredPseudoNormedGroupHom (M i) (N i)) (hf : ∃ C, ∀ i, (f i).BoundBy C) :
    ComphausFilteredPseudoNormedGroupHom (∀ i, M i) (∀ i, N i) :=
  piLift (fun i => (f i).comp (piProj i))
    (by
      obtain ⟨C, hC⟩ := hf
      refine' ⟨C, fun i c x hx => hC i _⟩
      have := ComphausFilteredPseudoNormedGroup.piProjBoundBy i hx
      rwa [one_mul] at this )

end Pi

end ComphausFilteredPseudoNormedGroup

namespace ProfinitelyFilteredPseudoNormedGroup

/-! ## Products -/


section Pi

open ComphausFilteredPseudoNormedGroup

variable {ι : Type _} (M : ι → Type _) [∀ i, ProfinitelyFilteredPseudoNormedGroup (M i)]

instance pi_td (c : ℝ≥0) : TotallyDisconnectedSpace (filtration (∀ i, M i) c) :=
  by
  obtain ⟨H⟩ : TotallyDisconnectedSpace (∀ i, filtration (M i) c) := inferInstance
  rw [← Homeomorph.range_coe (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c), ← Set.image_univ] at H 
  exact ⟨Embedding.isTotallyDisconnected (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo M c).embedding H⟩

instance pi : ProfinitelyFilteredPseudoNormedGroup (∀ i, M i) :=
  { (inferInstance : ComphausFilteredPseudoNormedGroup _) with }

end Pi

end ProfinitelyFilteredPseudoNormedGroup

