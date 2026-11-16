import LiquidTensorExperiment.PseudoNormedGroup.ProfinitelyFiltered

#align_import pseudo_normed_group.with_Tinv

/-!

# Profinitely filtered pseudo-normed groups with T⁻¹

The definition of `profinitely_filtered_pseudo_normed_group_with_Tinv`,
and morphisms between them.

-/


open PseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup ComphausFilteredPseudoNormedGroup

open scoped NNReal BigOperators

attribute [local instance] typePow

class ComphausFilteredPseudoNormedGroupWithTinv (r' : outParam <| ℝ≥0) (M : Type _) extends
    ComphausFilteredPseudoNormedGroup M where
  tinv : ComphausFilteredPseudoNormedGroupHom M M
  -- Porting note: Lean 3's `filtration c` / `Tinv` (the parent's and this class's fields)
  tinv_mem_filtration : ∀ c x, x ∈ filtration M c → tinv x ∈ filtration M (r'⁻¹ * c)

/-- A *profinitely filtered pseudo-normed topological group with action by `T⁻¹`* is
a profinitely filtered pseudo-normed topological group `M` together with a
nonnegative real `r'` and homomorphism `Tinv : M → M` such that
`Tinv x ∈ filtration M (r'⁻¹ * c)` for all `x ∈ filtration M c`.
-/
class ProfinitelyFilteredPseudoNormedGroupWithTinv (r' : outParam <| ℝ≥0) (M : Type _) extends
    ProfinitelyFilteredPseudoNormedGroup M where
  tinv : ComphausFilteredPseudoNormedGroupHom M M
  -- Porting note: Lean 3's `filtration c` / `Tinv` (the parent's and this class's fields)
  tinv_mem_filtration : ∀ c x, x ∈ filtration M c → tinv x ∈ filtration M (r'⁻¹ * c)

namespace ProfinitelyFilteredPseudoNormedGroupWithTinv

variable {r' : ℝ≥0} {M M₁ M₂ M₃ : Type _}

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M]

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M₁]

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M₂]

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M₃]

theorem aux {r' c c₂ : ℝ≥0} (h : c ≤ r' * c₂) : r'⁻¹ * c ≤ c₂ :=
  by
  by_cases hr' : r' = 0
  · subst r'; rw [inv_zero, MulZeroClass.zero_mul]; exact zero_le'
  · rwa [NNReal.mul_le_iff_le_inv, inv_inv]; exact inv_ne_zero hr'

@[simps]
def tinv₀ (c c₂ : ℝ≥0) [h : Fact (c ≤ r' * c₂)] (x : filtration M c) : filtration M c₂ :=
  ⟨tinv (x : M), filtration_mono (aux h.1) (tinv_mem_filtration _ _ x.2)⟩

theorem tinv₀_continuous (c c₂ : ℝ≥0) [Fact (c ≤ r' * c₂)] : Continuous (@tinv₀ r' M _ c c₂ _) :=
  tinv.continuous _ fun x => rfl

theorem tinvBoundBy : (@tinv _ M _).BoundBy r'⁻¹ :=
  tinv_mem_filtration

instance toComphausFilteredPseudoNormedGroupWithTinv (M : Type _)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    ComphausFilteredPseudoNormedGroupWithTinv r' M :=
  { (inferInstance : ProfinitelyFilteredPseudoNormedGroupWithTinv r' M) with }

end ProfinitelyFilteredPseudoNormedGroupWithTinv

section

open ComphausFilteredPseudoNormedGroupWithTinv

/-- The type of strict morphisms between two compact Hausdorff filtered pseudo-normed groups
with an action of T⁻¹. -/
structure ComphausFilteredPseudoNormedGroupWithTinvHom (r' : ℝ≥0) (M₁ M₂ : Type _)
    [ComphausFilteredPseudoNormedGroupWithTinv r' M₁]
    [ComphausFilteredPseudoNormedGroupWithTinv r' M₂] extends M₁ →+ M₂ where
  strict' : ∀ ⦃c x⦄, x ∈ filtration M₁ c → toFun x ∈ filtration M₂ c
  continuous' : ∀ c, Continuous (PseudoNormedGroup.level toFun strict' c)
  map_Tinv' : ∀ x, toFun (tinv x) = tinv (toFun x)

end


namespace ComphausFilteredPseudoNormedGroupWithTinvHom

open ComphausFilteredPseudoNormedGroupWithTinv

variable {r' : ℝ≥0} {M M₁ M₂ M₃ : Type _}

variable [ComphausFilteredPseudoNormedGroupWithTinv r' M]

variable [ComphausFilteredPseudoNormedGroupWithTinv r' M₁]

variable [ComphausFilteredPseudoNormedGroupWithTinv r' M₂]

variable [ComphausFilteredPseudoNormedGroupWithTinv r' M₃]

variable (f g : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂)

instance : CoeFun (ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) fun _ => M₁ → M₂ :=
  -- Porting note: coerce through the `AddMonoidHom` parent (as `StrictPseudoNormedGroupHom` does),
  -- so that applied homs have the same normal form as mathlib's `AddMonoidHom` coercion
  ⟨fun f => f.toAddMonoidHom⟩

-- Porting note: a custom `simps` projection for the coercion; without it `@[simps]` loops
/-- See Note [custom simps projection]. -/
def Simps.apply (f : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) : M₁ → M₂ := f

initialize_simps_projections ComphausFilteredPseudoNormedGroupWithTinvHom (toFun → apply)

@[simp]
theorem coe_mk (f) (h₁) (h₂) (h₃) (h₄) (h₅) :
    ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄, h₅⟩ : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) = f :=
  rfl

@[simp]
theorem mk_to_monoid_hom (f) (h₁) (h₂) (h₃) (h₄) (h₅) :
    (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄, h₅⟩ :
          ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂).toAddMonoidHom =
      ⟨⟨f, h₁⟩, h₂⟩ :=
  rfl

-- Porting note: not `@[simp]`: Lean 4 expands `⇑f` to `f.toAddMonoidHom.toFun`, which
-- mathlib's simp lemma `AddMonoidHom.toFun_eq_coe` turns back into the left-hand side (loop)
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
theorem map_zsmul (n : ℤ) (x) : f (n • x) = n • f x :=
  f.toAddMonoidHom.map_zsmul _ _

theorem strict : ∀ ⦃c x⦄, x ∈ filtration M₁ c → f x ∈ filtration M₂ c :=
  f.strict'

/-- `f.level c` is the function `filtration M₁ c → filtration M₂ c`
induced by a `comphaus_filtered_pseudo_normed_group_with_Tinv_hom M₁ M₂`. -/
-- Porting note: `rhsMd := .default` as in Lean 3, where `simps` unfolded the definition
@[simps (config := { rhsMd := .default })]
def level : ∀ c : ℝ≥0, filtration M₁ c → filtration M₂ c :=
  PseudoNormedGroup.level f f.strict

theorem level_continuous (c : ℝ≥0) : Continuous (f.level c) :=
  f.continuous' c

theorem map_tinv (x : M₁) : f (tinv x) = tinv (f x) :=
  f.map_Tinv' x

variable {f g}

@[ext]
-- Porting note: Lean 4 does not flatten the `AddMonoidHom` parent, so use its `ext`
theorem ext (H : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; exact AddMonoidHom.ext H

instance : Zero (ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) :=
  -- Porting note: the `AddMonoidHom` parent is given by name instead of as a `with` source
  ⟨{ toAddMonoidHom := 0
     strict' := fun c x h => zero_mem_filtration _
     continuous' := fun c => @continuous_const _ (filtration M₂ c) _ _ 0
     map_Tinv' := fun x => show 0 = tinv (0 : M₂) from tinv.map_zero.symm }⟩

instance : Inhabited (ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) :=
  ⟨0⟩

theorem coe_inj ⦃f g : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂⦄
    (h : (f : M₁ → M₂) = g) : f = g :=
  ext (congrFun h)

/-- The identity function as `comphaus_filtered_pseudo_normed_group_with_Tinv_hom`. -/
@[simps]
def id : ComphausFilteredPseudoNormedGroupWithTinvHom r' M M :=
  { toAddMonoidHom := AddMonoidHom.id _
    strict' := fun c x => _root_.id
    continuous' := fun c => by convert continuous_id
    map_Tinv' := fun x => rfl }

/-- The composition of `comphaus_filtered_pseudo_normed_group_with_Tinv_hom`s. -/
@[simps (config := { rhsMd := .default })]
def comp (g : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₂ M₃)
    (f : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₃ :=
  { toAddMonoidHom := g.toAddMonoidHom.comp f.toAddMonoidHom
    strict' := fun c x hx => g.strict (f.strict hx)
    continuous' := fun c => (g.level_continuous c).comp (f.level_continuous c)
    map_Tinv' := fun x =>
      calc
        g (f (tinv x)) = g (tinv (f x)) := by rw [f.map_tinv]
        _ = tinv (g (f x)) := by rw [g.map_tinv] }

variable (f)

/-- The `comphaus_filtered_pseudo_normed_group_hom` underlying a
`comphaus_filtered_pseudo_normed_group_with_Tinv_hom`. -/
def toComphausFilteredPseudoNormedGroupHom : ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  ComphausFilteredPseudoNormedGroupHom.mkOfStrict f.toAddMonoidHom fun c =>
    ⟨fun x h => f.strict h, f.level_continuous c⟩

theorem toProfinitelyFilteredPseudoNormedGroupHomStrict :
    f.toComphausFilteredPseudoNormedGroupHom.Strict :=
  ComphausFilteredPseudoNormedGroupHom.mkOfStrictStrict _ _

variable {f}

-- Porting note: the type of `hfT` (inferred in Lean 3) is stated
def mk' (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) (hf1 : f.BoundBy 1)
    (hfT : ∀ x, f (tinv x) = tinv (f x)) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂ :=
  { f with
    toFun := f
    strict' := fun c x hx => by simpa only [one_mul] using hf1 hx
    continuous' := fun c => f.continuous _ fun x => rfl
    map_Tinv' := hfT }

@[simp]
theorem mk'_apply (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) (hf1 : f.BoundBy 1)
    (hfT : ∀ x, f (tinv x) = tinv (f x)) (x : M₁) :
    @mk' r' _ _ _ _ f hf1 hfT x = f x :=
  rfl

/-- If the inverse of `comphaus_filtered_pseudo_normed_group_with_Tinv_hom` is strict, then it
is a `comphaus_filtered_pseudo_normed_group_with_Tinv_hom`. -/
def invOfEquivOfStrict (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' M₂ M₁ :=
  { e.symm.toAddMonoidHom with
    strict' := strict
    continuous' := fun c =>
      by
      simp only [AddEquiv.coe_toAddMonoidHom, AddMonoidHom.toFun_eq_coe]
      have hcont := f.continuous' c
      let g : filtration M₁ c ≃ filtration M₂ c :=
        ⟨fun x => ⟨f x, f.strict x.2⟩, fun x => ⟨e.symm x, strict x.2⟩, fun x => by simp [he],
          fun x => by simp [he]⟩
      change Continuous g.symm
      rw [continuous_iff_isClosed]
      intro U hU
      rw [← g.image_eq_preimage]
      exact (hcont.closedEmbedding g.injective).isClosedMap U hU
    map_Tinv' := fun x => by
      apply e.injective
      simp only [AddEquiv.coe_toAddMonoidHom, AddMonoidHom.toFun_eq_coe]
      -- Porting note: `erw` because the coercions are unfolded differently after `simp only`
      erw [e.apply_symm_apply, ← he, map_tinv, he, e.apply_symm_apply] }

@[simp]
theorem invOfEquivOfStrict.apply (x : M₁) (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
    (invOfEquivOfStrict e he strict) (f x) = x := by simp [ComphausFilteredPseudoNormedGroupWithTinvHom.invOfEquivOfStrict, he]

@[simp]
theorem InvOfEquivOfStrictSymm.apply (x : M₂) (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) :
    f (invOfEquivOfStrict e he strict x) = x := by simp [ComphausFilteredPseudoNormedGroupWithTinvHom.invOfEquivOfStrict, he]

end ComphausFilteredPseudoNormedGroupWithTinvHom

namespace PUnit

-- Porting note: Lean 4 rejects this as an instance because the out-parameter `r'` is not
-- determined by `PUnit`; it is only ever used by name, so it is a `def`.
def profinitelyFilteredPseudoNormedGroupWithTinv (r' : ℝ≥0) :
    ProfinitelyFilteredPseudoNormedGroupWithTinv r' PUnit :=
  {
    PUnit.profinitelyFilteredPseudoNormedGroup with
    tinv := ComphausFilteredPseudoNormedGroupHom.id
    tinv_mem_filtration := fun c x h => Set.mem_univ _ }

end PUnit

namespace ProfinitelyFilteredPseudoNormedGroupWithTinv

section

/-! ## Powers -/


-- TODO: Generalize this section to `comphaus_filtered...` as needed.
noncomputable section

variable (r' : ℝ≥0) {ι : Type _} (M M₁ M₂ : ι → Type _)

variable [∀ i, ProfinitelyFilteredPseudoNormedGroupWithTinv r' (M i)]

variable [∀ i, ProfinitelyFilteredPseudoNormedGroupWithTinv r' (M₁ i)]

variable [∀ i, ProfinitelyFilteredPseudoNormedGroupWithTinv r' (M₂ i)]

instance pi : ProfinitelyFilteredPseudoNormedGroupWithTinv r' (∀ i, M i) :=
  {
    ProfinitelyFilteredPseudoNormedGroup.pi
      _ with
    tinv := ComphausFilteredPseudoNormedGroup.piMap (fun i => tinv) ⟨r'⁻¹, fun i => tinvBoundBy⟩
    tinv_mem_filtration := fun c x hx i => tinv_mem_filtration _ _ (hx i) }

instance pi' (M : Type _) [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] (N : ℕ) :
    ProfinitelyFilteredPseudoNormedGroupWithTinv r' (M ^ N) :=
  ProfinitelyFilteredPseudoNormedGroupWithTinv.pi r' fun i => M

@[simp]
theorem pi_tinv_apply (x : ∀ i, M i) (i : ι) : tinv x i = tinv (x i) :=
  rfl

@[simps (config := { fullyApplied := false })]
def piProj (i : ι) : ComphausFilteredPseudoNormedGroupWithTinvHom r' (∀ i, M i) (M i) :=
  { Pi.evalAddMonoidHom M i with
    toFun := Pi.evalAddMonoidHom M i
    strict' := fun c x hx => hx i
    continuous' := fun c => (continuous_apply i).comp (filtrationPiHomeo M c).continuous
    map_Tinv' := fun x => rfl }

/-- Universal property of the product of
profinitely filtered pseudo-normed groups with `T⁻¹`-action -/
@[simps (config := { fullyApplied := false })]
def piLift {N : Type _} [ProfinitelyFilteredPseudoNormedGroupWithTinv r' N]
    (f : ∀ i, ComphausFilteredPseudoNormedGroupWithTinvHom r' N (M i)) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' N (∀ i, M i) :=
  {
    AddMonoidHom.mkToPi fun i =>
      (f i).toAddMonoidHom with
    toFun := AddMonoidHom.mkToPi fun i => (f i).toAddMonoidHom
    strict' := fun c x hx i => (f i).strict hx
    continuous' := by
      intro c
      rw [continuous_induced_rng]
      apply continuous_pi
      intro i
      exact (f i).continuous' c
    map_Tinv' := fun x => by ext i; exact (f i).map_tinv x }

@[simps (config := { fullyApplied := false, rhsMd := .default })]
def piMap (f : ∀ i, ComphausFilteredPseudoNormedGroupWithTinvHom r' (M₁ i) (M₂ i)) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' (∀ i, M₁ i) (∀ i, M₂ i) :=
  piLift r' _ fun i => (f i).comp (piProj r' _ i)

end

end

end ProfinitelyFilteredPseudoNormedGroupWithTinv

