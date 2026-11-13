import Mathlib.Analysis.NormedSpace.Banach
import Mathlib.Analysis.MeanInequalitiesPow
import LiquidTensorExperiment.NormedGroup.NormedWithAut

#align_import banach

/-!
# p-Banach spaces

A `p`-Banach space is just like an ordinary Banach space,
except that the axiom `∥c • v∥ = ∥c∥ * ∥v∥` is replaced by `∥c • v∥ = ∥c∥^p * ∥v∥`.

In other words, a `p`-Banach space is a complete topological vector space
whose topology is induced by a `p`-norm.


In this file, we define `p`-normed spaces, called `normed_space'`,
and we prove that every `p`-normed space is also `p'`-normed, for `0 < p' ≤ p`.

-/


noncomputable section

open scoped NNReal

section

structure HasPNorm (V : Type _) (p : ℝ) [AddCommGroup V] [Module ℝ V] [UniformSpace V] extends
    Norm V where
  norm_smul : ∀ (α : ℝ) (v : V), ‖α • v‖ = |α| ^ p • ‖v‖
  triangle : ∀ v w : V, ‖v + w‖ ≤ ‖v‖ + ‖w‖
  uniformity :
    uniformity V =
      ⨅ (ε : ℝ) (H : ε > 0), Filter.principal {p : V × V | ‖p.fst - p.snd‖ < ε}

variable (V : Type _) (p : ℝ) [AddCommGroup V] [Module ℝ V] [UniformSpace V]

def HasPNorm.seminormedAddCommGroup [Fact (0 < p)] (h : HasPNorm V p) : SeminormedAddCommGroup V :=
  {
    @seminormed_add_comm_group.of_core V _ h.toHasNorm <|
      have hp0 : p ≠ 0 := (Fact.out _ : 0 < p).ne'
      { norm_zero := by simpa only [zero_smul, abs_zero, Real.zero_rpow hp0] using h.norm_smul 0 0
        triangle := h.triangle
        norm_neg := fun v => by
          simpa only [neg_smul, one_smul, abs_neg, abs_one, Real.one_rpow] using
            h.norm_smul (-1)
              v } with
    toUniformSpace := by infer_instance
    uniformity_dist := h.uniformity
    toAddCommGroup := by infer_instance }

structure PBanach : Prop where
  exists_p_norm : Nonempty (HasPNorm V p)
  [TopologicalAddGroup : TopologicalAddGroup V]
  [continuous_smul : ContinuousSMul ℝ V]
  [complete : CompleteSpace V]
  [separated : SeparatedSpace V]

end

structure PBanachCat (p : ℝ) where
  V : Type _
  [addCommGroup' : AddCommGroup V]
  [module' : Module ℝ V]
  [uniformSpace' : UniformSpace V]
  pBanach' : PBanach V p

namespace PBanachCat

variable (p : ℝ) (V : PBanachCat p)

instance : CoeSort (PBanachCat p) (Type _) :=
  ⟨fun X => X.V⟩

instance : AddCommGroup V :=
  V.addCommGroup'

instance : Module ℝ V :=
  V.module'

instance : UniformSpace V :=
  V.uniformSpace'

instance : TopologicalAddGroup V :=
  V.pBanach'.TopologicalAddGroup

instance : ContinuousSMul ℝ V :=
  V.pBanach'.continuous_smul

instance : CompleteSpace V :=
  V.pBanach'.complete

instance : SeparatedSpace V :=
  V.pBanach'.separated

variable {p}

/-- Highly non-canonical! -/
def chooseSeminormedAddCommGroup [Fact (0 < p)] : SeminormedAddCommGroup V :=
  (Classical.choice V.pBanach'.exists_p_norm).SeminormedAddCommGroup V p

@[simps]
def smulNormedHom [Fact (0 < p)] (x : ℝ) :
    @NormedAddGroupHom V V V.chooseSeminormedAddCommGroup V.chooseSeminormedAddCommGroup
    where
  toFun v := x • v
  map_add' v₁ v₂ := smul_add _ _ _
  bound' := ⟨|x| ^ p, fun v => by rw [HasPNorm.norm_smul, smul_eq_mul]⟩

/-- Highly non-canonical! -/
def chooseNormedWithAut [Fact (0 < p)] (x : ℝ≥0) [Fact (0 < x)] :
    NormedWithAut (x ^ p) ⟨V, chooseSeminormedAddCommGroup V⟩
    where
  t :=
    { hom := smulNormedHom V x
      inv := smulNormedHom V x⁻¹
      hom_inv_id' := by
        ext v; dsimp; rw [← mul_smul, inv_mul_cancel, one_smul]
        exact_mod_cast (Fact.out _ : 0 < x).ne'
      inv_hom_id' := by
        ext v; dsimp; rw [← mul_smul, mul_inv_cancel, one_smul]
        exact_mod_cast (Fact.out _ : 0 < x).ne' }
  norm_t v := by
    dsimp; rw [HasPNorm.norm_smul, smul_eq_mul]; congr 2
    rw [abs_eq_self]; exact x.coe_nonneg

@[simp]
theorem chooseNormedWithAut_t_hom [Fact (0 < p)] (x : ℝ≥0) [Fact (0 < x)] (v : V) :
    (@NormedWithAut.t (x ^ p) ⟨V, chooseSeminormedAddCommGroup V⟩ (V.chooseNormedWithAut x)).hom v =
      x • v :=
  rfl

@[simp]
theorem chooseNormedWithAut_t_inv [Fact (0 < p)] (x : ℝ≥0) [Fact (0 < x)] (v : V) :
    (@NormedWithAut.t (x ^ p) ⟨V, chooseSeminormedAddCommGroup V⟩ (V.chooseNormedWithAut x)).inv v =
      x⁻¹ • v :=
  rfl

end PBanachCat

-- noncomputable
-- def pBanach'_is_qBanach' (V: Type*) (p : ℝ) [fact (0 < p)] [fact (p ≤ 1)] (q : ℝ) [fact (0 < q)]
--   [fact (q ≤ 1)] [add_comm_group V] [module ℝ V] [uniform_space V] [has_continuous_smul ℝ V]
--   [topological_add_group V] [complete_space V] (hp : pBanach' V p) : pBanach' V q :=
-- begin
--   cases hp,
--   let Hp_norm := hp.some,
--   let ψ := Hp_norm.norm,
--   use λ v : V, (ψ v)^(q/p),--[FAE] Why λ v, ((h_p_norm.norm) v)^(q/p) does not work?
--   intros α v,
--   dsimp only [ψ],
--   admit,
--   admit,
-- rw [Hp_norm.p_norm α v, smul_eq_mul, real.mul_rpow, ← real.rpow_mul, mul_div_cancel'],
-- exacts [refl _, ne_of_gt (fact.out _), abs_nonneg α,
--   (real.rpow_nonneg_of_nonneg (abs_nonneg α) p), hp_nonneg_norm v,
--   (λ _, (real.rpow_nonneg_of_nonneg (hp_nonneg_norm _) _))],
-- end
section Obsolete

-- move this
theorem Real.add_rpow_le {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h0r : 0 ≤ r) (hr1 : r ≤ 1) :
    (x + y) ^ r ≤ x ^ r + y ^ r := by
  by_cases hr : 0 = r
  · subst r; simp only [zero_le_one, Real.rpow_zero, le_add_iff_nonneg_left]
  let x' : ℝ≥0 := ⟨x, hx⟩
  let y' : ℝ≥0 := ⟨y, hy⟩
  exact_mod_cast ENNReal.rpow_add_le_add_rpow x' y' h0r hr1

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option extends_priority -/
set_option extends_priority 920

-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class NormedSpace' (𝕜 : Type _) (p : outParam ℝ) (V : Type _) [NormedField 𝕜] [NormedAddCommGroup V]
    [Module 𝕜 V] where
  norm_smul : ∀ (c : 𝕜) (v : V), ‖c • v‖ = ‖c‖ ^ p * ‖v‖

instance (priority := 100) NormedSpace.normedSpace' (𝕜 : Type _) (V : Type _) [NormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] : NormedSpace' 𝕜 1 V
    where norm_smul c k := by simp only [Real.rpow_one, norm_smul]

/-- A type alias: `as_normed_space' p' V` is a `p'`-normed space over `𝕜`,
when `V` is a `p`-normed space over `𝕜` and `0 < p' ≤ p`. -/
@[nolint unused_arguments]
def AsNormedSpace' (p' : ℝ) (V : Type _) :=
  V

namespace AsNormedSpace'

instance (p' : ℝ) (V : Type _) [i : Inhabited V] : Inhabited (AsNormedSpace' p' V) :=
  i

/-- The identity map `V → as_normed_space' p' V`. -/
def up (p' : ℝ) {V : Type _} (v : V) : AsNormedSpace' p' V :=
  v

/-- The identity map `as_normed_space' p' V → V`. -/
def down {p' : ℝ} {V : Type _} (v : AsNormedSpace' p' V) : V :=
  v

instance (p' : ℝ) (V : Type _) [i : AddCommGroup V] : AddCommGroup (AsNormedSpace' p' V) :=
  i

instance (p' : ℝ) (𝕜 V : Type _) [Ring 𝕜] [AddCommGroup V] [i : Module 𝕜 V] :
    Module 𝕜 (AsNormedSpace' p' V) :=
  i

@[simp]
theorem down_add {p' : ℝ} {V : Type _} [AddCommGroup V] (v w : AsNormedSpace' p' V) :
    (v + w).down = v.down + w.down :=
  rfl

@[simp]
theorem down_neg {p' : ℝ} {V : Type _} [AddCommGroup V] (v : AsNormedSpace' p' V) :
    (-v).down = -v.down :=
  rfl

@[simp]
theorem down_smul {p' : ℝ} {𝕜 V : Type _} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V] (c : 𝕜)
    (v : AsNormedSpace' p' V) : (c • v).down = c • v.down :=
  rfl

/-- The natural `p'`-norm on `as_normed_space' p' V` induced by a `p`-norm on `V`. -/
protected def hasNorm (p' p : ℝ) (V : Type _) [Norm V] : Norm (AsNormedSpace' p' V) :=
  ⟨fun v => ‖v.down‖ ^ (p' / p)⟩

theorem norm_def {V : Type _} [Norm V] (p' p : ℝ) (v : AsNormedSpace' p' V) :
    @Norm.norm _ (AsNormedSpace'.hasNorm p' p V) v = ‖v.down‖ ^ (p' / p) :=
  rfl

/-- The natural `p'`-normed group structure on `as_normed_space' p' V`
induced by a `p`-normed group structure on `V` -/
protected def normedAddCommGroup (V : Type _) [NormedAddCommGroup V] (p' p : ℝ) [Fact (0 < p')]
    [Fact (p' ≤ p)] : NormedAddCommGroup (AsNormedSpace' p' V) :=
  @normed_add_comm_group.of_core _ _ (AsNormedSpace'.hasNorm p' p V) <|
    have hp' : 0 < p' := Fact.out _
    have hp : 0 < p := lt_of_lt_of_le hp' (Fact.out _)
    have H : 0 < p' / p := div_pos hp' hp
    { norm_eq_zero_iff := fun v =>
        show ‖v.down‖ ^ (p' / p) = 0 ↔ v = 0 by
          simpa only [Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg v.down), norm_eq_zero, H.ne',
            and_true_iff, Ne.def, not_false_iff]
      triangle := fun v w =>
        show
          ‖v + w‖.down ^ (p' / p) ≤
            ‖v.down‖ ^ (p' / p) + ‖w.down‖ ^ (p' / p)
          by
          rw [down_add]
          calc
            ‖v.down + w.down‖ ^ (p' / p) ≤
                (‖v.down‖ + ‖w.down‖) ^ (p' / p) :=
              Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) H.le
            _ ≤ ‖v.down‖ ^ (p' / p) + ‖w.down‖ ^ (p' / p) :=
              Real.add_rpow_le (norm_nonneg _) (norm_nonneg _) H.le _
          rw [div_le_iff hp, one_mul]
          exact Fact.out _
      norm_neg := fun v =>
        show ‖-v‖.down ^ (p' / p) = ‖v.down‖ ^ (p' / p) by
          rw [down_neg, norm_neg] }

attribute [local instance] AsNormedSpace'.normedAddCommGroup

instance (𝕜 : Type _) (V : Type _) [NormedField 𝕜] [NormedAddCommGroup V] [Module 𝕜 V] (p' p : ℝ)
    [Fact (0 < p')] [Fact (p' ≤ p)] [NormedSpace' 𝕜 p V] : NormedSpace' 𝕜 p' (AsNormedSpace' p' V)
    where norm_smul c v := by
    have hp' : 0 < p' := Fact.out _
    have hp : 0 < p := lt_of_lt_of_le hp' (Fact.out _)
    rw [norm_def, norm_def, down_smul, NormedSpace'.norm_smul, Real.mul_rpow, ← Real.rpow_mul,
      mul_div_cancel' _ hp.ne']
    · exact norm_nonneg _
    · exact Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
    · exact norm_nonneg _

end AsNormedSpace'

end Obsolete

