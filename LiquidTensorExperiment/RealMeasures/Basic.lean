import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.CategoryTheory.FintypeCat
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.ForMathlib.Nnreal
import LiquidTensorExperiment.ForMathlib.Real

#align_import real_measures.basic

/-

# Real measures

If `p : ℝ≥0` and `S : Fintype` then `real_measures p S` is just the functions
from `S` to `ℝ`, equipped with its `ℓᵖ` norm.
-/
/-

# Real measures

If `p : ℝ≥0` and `S : Fintype` then `real_measures p S` is just the functions
from `S` to `ℝ`, equipped with its `ℓᵖ` norm.
-/
universe u

noncomputable section

open scoped BigOperators NNReal Classical

/-- `real_measures p S` is the vector space of maps `S → ℝ` equipped with the `ℓᵖ` norm,
which gives it the structure of a `CompHausl`y-filtered normed group.  -/
@[nolint unused_arguments]
def RealMeasures (p : ℝ≥0) (S : FintypeCat) :=
  S → ℝ
deriving AddCommGroup

variable {p : ℝ≥0} {S S' : FintypeCat.{u}}

local notation "ℳ" => RealMeasures

local notation "ϖ" => FintypeCat.of PUnit

namespace RealMeasures

@[simp]
theorem zero_apply (s : S) : (0 : ℳ p S) s = 0 :=
  rfl

@[simp]
theorem add_apply (F G : ℳ p S) (s : S) : (F + G) s = F s + G s :=
  rfl

@[simp]
theorem neg_apply (F : ℳ p S) (s : S) : (-F) s = -F s :=
  rfl

@[simp]
theorem sub_apply (F G : ℳ p S) (s : S) : (F - G) s = F s - G s :=
  rfl

instance : Norm (ℳ p S) :=
  ⟨fun F => ∑ s, ‖F s‖ ^ (p : ℝ)⟩

theorem norm_def (F : ℳ p S) : ‖F‖ = ∑ s, ‖F s‖ ^ (p : ℝ) :=
  rfl

instance : NNNorm (ℳ p S) :=
  ⟨fun F => ∑ s, ‖F s‖₊ ^ (p : ℝ)⟩

theorem nnnorm_def (F : ℳ p S) : ‖F‖₊ = ∑ s, ‖F s‖₊ ^ (p : ℝ) :=
  rfl

@[simp]
protected theorem coe_nnnorm (F : ℳ p S) : (‖F‖₊ : ℝ) = ‖F‖ := by
  simp only [norm_def, nnnorm_def, NNReal.coe_sum, NNReal.coe_rpow, coe_nnnorm]

theorem RealMeasures.norm_nonneg (F : ℳ p S) : 0 ≤ ‖F‖ := by rw [← F.coe_nnnorm];
  exact (‖F‖₊).2

@[simp]
protected theorem nnnorm_zero [hp : Fact (0 < p)] : ‖0 : ℳ p S‖₊ = 0 :=
  by
  rw [nnnorm_def, Finset.sum_eq_zero]
  rintro s -
  rw [zero_apply, nnnorm_zero, NNReal.zero_rpow]
  exact_mod_cast hp.out.ne'

protected theorem nnnorm_add [h0p : Fact (0 ≤ p)] [hp1 : Fact (p ≤ 1)] (F G : ℳ p S) :
    ‖F + G‖₊ ≤ ‖F‖₊ + ‖G‖₊ :=
  by
  dsimp [nnnorm_def]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s hs
  have h0p' : (0 : ℝ) ≤ p; exact_mod_cast h0p.out
  have hp1' : (p : ℝ) ≤ 1; exact_mod_cast hp1.out
  exact
    (NNReal.rpow_le_rpow (nnnorm_add_le _ _) h0p').trans
      (@NNReal.rpow_add_le_add_rpow p (‖F s‖₊) (‖G s‖₊) h0p' hp1')

--needed? [FAE] Yes!
instance pngRealMeasures [Fact (0 < p)] [Fact (p ≤ 1)] : PseudoNormedGroup (ℳ p S)
    where
  filtration' c := {F | ‖F‖₊ ≤ c}
  filtration_mono' c₁ c₂ h F hF := by dsimp at *; exact le_trans hF h
  zero_mem_filtration' c := by simp only [RealMeasures.nnnorm_zero, zero_le', Set.mem_setOf_eq]
  neg_mem_filtration' c F h := by dsimp [nnnorm_def] at *; simp only [h, nnnorm_neg]
  add_mem_filtration' c₁ c₂ F₁ F₂ h₁ h₂ := (RealMeasures.nnnorm_add _ _).trans (add_le_add h₁ h₂)

theorem mem_filtration_iff [Fact (0 < p)] [Fact (p ≤ 1)] (F : ℳ p S) (c : ℝ≥0) :
    F ∈ PseudoNormedGroup.filtration (ℳ p S) c ↔ ‖F‖₊ ≤ c :=
  Iff.rfl

def map (f : S ⟶ S') : ℳ p S → ℳ p S' := fun F s' =>
  ∑ s in Finset.univ.filterₓ fun t => f t = s', F s

@[simp]
theorem map_apply (f : S ⟶ S') (F : ℳ p S) (s' : S') :
    map f F s' = ∑ s in Finset.univ.filterₓ fun t => f t = s', F s :=
  rfl

@[simp]
theorem map_id : (map (𝟙 S) : ℳ p S → ℳ p S) = id :=
  by
  ext F s
  rw [map_apply, Finset.sum_filter, id.def]
  simp only [FintypeCat.id_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

@[simp]
theorem map_comp {S'' : FintypeCat.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    (map (f ≫ g) : ℳ p S → ℳ p S'') = map g ∘ map f :=
  by
  ext F s
  simp only [Function.comp_apply, map_apply]
  convert Finset.sum_biUnion _ using 1; swap; · classical infer_instance
  · apply Finset.sum_congr
    · change (finset.univ.filter fun t => g (f t) = s) = _
      ext i
      simp only [true_and_iff, exists_prop, Finset.mem_univ, Finset.mem_biUnion, exists_eq_right',
        Finset.mem_filter]
    · intros; rfl
  · intro i hi j hj h k hk
    refine' h _
    simp only [true_and_iff, Finset.inf_eq_inter, Finset.mem_univ, Finset.mem_filter,
      Finset.mem_inter] at hk 
    rw [← hk.1, ← hk.2]

theorem map_bound [h0p : Fact (0 < p)] [hp1 : Fact (p ≤ 1)] (f : S ⟶ S') (F : ℳ p S) :
    ‖map f F‖₊ ≤ ‖F‖₊ :=
  by
  calc
    ∑ s', ‖∑ s in finset.univ.filter fun t => f t = s', F s‖₊ ^ (p : ℝ) ≤
        ∑ s' : S', ∑ s in finset.univ.filter fun t => f t = s', ‖F s‖₊ ^ (p : ℝ) :=
      _
    _ = ∑ s, ‖F s‖₊ ^ (p : ℝ) := _
  · apply Finset.sum_le_sum
    rintro s' -
    have h0p' : (0 : ℝ) < p; exact_mod_cast h0p.out
    have hp1' : (p : ℝ) ≤ 1; exact_mod_cast hp1.out
    exact
      (NNReal.rpow_le_rpow (nnnorm_sum_le _ _) h0p'.le).trans
        (NNReal.rpow_sum_le_sum_rpow _ _ h0p' hp1')
  · rw [← Finset.sum_biUnion]
    · refine' Finset.sum_congr _ _
      · ext s
        simp only [true_and_iff, Finset.mem_univ, Finset.mem_biUnion, iff_true_iff,
          exists_true_left, Finset.mem_filter]
        refine' ⟨_, rfl⟩
      · intros; rfl
    · rintro x - y - h i hi
      apply h
      simp only [true_and_iff, Finset.inf_eq_inter, Finset.mem_univ, Finset.mem_filter,
        Finset.mem_inter] at hi 
      rw [← hi.1, ← hi.2]

def sevalℳ {r : ℝ≥0} (S : FintypeCat) (s : S) :
    RealMeasures r S → RealMeasures r (FintypeCat.of PUnit) := fun F => fun _ => F s

variable [Fact (0 < p)] [Fact (p ≤ 1)]

open PseudoNormedGroup (filtration)

instance topologicalSpace (c : ℝ≥0) : TopologicalSpace (filtration (ℳ p S) c) :=
  @Subtype.topologicalSpace _ _ Pi.topologicalSpace

instance t2Space (c : ℝ≥0) : T2Space (filtration (ℳ p S) c) :=
  @Subtype.t2Space _ _ Pi.topologicalSpace _

theorem nnnorm_apply_le_of_nnnorm_le (F : ℳ p S) (s : S) (c : ℝ≥0) (h : ‖F‖₊ ≤ c) :
    ‖F s‖₊ ≤ c ^ (p⁻¹ : ℝ) :=
  by
  calc
    ‖F s‖₊ = (‖F s‖₊ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) := _
    _ ≤ c ^ (p⁻¹ : ℝ) := _
  · rw_mod_cast [← NNReal.rpow_mul, mul_inv_cancel, NNReal.rpow_one]
    exact ne_of_gt ‹Fact (0 < p)›.out
  · apply NNReal.rpow_le_rpow _ (inv_pos.mpr _).le
    · refine' le_trans _ h
      have aux := Finset.sum_pi_single' s (‖F s‖₊ ^ (p : ℝ)) Finset.univ
      simp only [Finset.mem_univ, if_true] at aux 
      rw [← aux]
      apply Finset.sum_le_sum
      rintro t -
      split_ifs; · subst t; · exact zero_le'
    · norm_cast; exact ‹Fact (0 < p)›.out

theorem apply_mem_Icc_of_nnnorm_le (F : ℳ p S) (s : S) (c : ℝ≥0) (h : ‖F‖₊ ≤ c) :
    F s ∈ Set.Icc (-c ^ (p⁻¹ : ℝ) : ℝ) (c ^ (p⁻¹ : ℝ) : ℝ) :=
  by
  have := @Set.mem_Icc_iff_abs_le ℝ _ 0 (F s) (c ^ (p : ℝ)⁻¹)
  simp only [zero_sub, abs_neg, zero_add, ← Real.norm_eq_abs, ← coe_nnnorm, nnnorm_neg] at this 
  rw [← this]
  norm_cast
  exact nnnorm_apply_le_of_nnnorm_le F s c h

-- move me
theorem Continuous.sum {ι X A : Type _} [TopologicalSpace X] [TopologicalSpace A] [AddCommMonoid A]
    [ContinuousAdd A] (s : Finset ι) (f : ι → X → A) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (∑ i in s, f i) :=
  by
  induction' s using Finset.induction_on with i s his IH
  · simp only [Finset.sum_empty]; exact @continuous_zero X A _ _ _
  · simp only [his, Finset.sum_insert, not_false_iff]
    refine' (hf i <| s.mem_insert_self i).add (IH fun i hi => hf i <| Finset.mem_insert_of_mem hi)

-- move me
theorem Continuous.sum' {ι X A : Type _} [TopologicalSpace X] [TopologicalSpace A] [AddCommMonoid A]
    [ContinuousAdd A] (s : Finset ι) (f : ι → X → A) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous fun x => ∑ i in s, f i x :=
  by
  induction' s using Finset.induction_on with i s his IH
  · simp only [Finset.sum_empty]; exact @continuous_zero X A _ _ _
  · simp only [his, Finset.sum_insert, not_false_iff]
    refine' (hf i <| s.mem_insert_self i).add (IH fun i hi => hf i <| Finset.mem_insert_of_mem hi)

instance compactSpace (c : ℝ≥0) : CompactSpace (filtration (ℳ p S) c) :=
  by
  constructor
  rw [← embedding_subtype_coe.toInducing.isCompact_iff]
  simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  let d : ℝ := c ^ (p⁻¹ : ℝ)
  let T : Set (S → ℝ) := {x | ∀ s, x s ∈ Set.Icc (-d) d}
  have hT : IsCompact T := isCompact_pi_infinite fun s => is_compact_Icc
  refine' compact_of_is_closed_subset hT _ fun F hF s => apply_mem_Icc_of_nnnorm_le F s c hF
  refine' isClosed_le (Continuous.sum' _ _ _) continuous_const
  rintro s -
  have h0p : 0 ≤ (p : ℝ) := by norm_cast; exact Fact.out _
  exact (NNReal.continuous_rpow_const h0p).comp (continuous_nnnorm.comp (continuous_apply s))

open Metric

def equivFiltrationϖBall (c : ℝ≥0) : filtration (ℳ p ϖ) c ≃ closedBall (0 : ℝ) (c ^ (p⁻¹ : ℝ) : ℝ≥0)
    where
  toFun f :=
    ⟨f.1 PUnit.unit, by
      simp only [mem_closedBall_zero_iff]
      have hf := (mem_filtration_iff f.1 c).mp f.2
      simp only [← NNReal.coe_le_coe, RealMeasures.coe_nnnorm, nnnorm_def, Fintype.univ_punit,
        Finset.sum_singleton, norm_def] at hf 
      have := @NNReal.rpow_le_rpow_iff (‖f.1 PUnit.unit‖₊) (c ^ (p⁻¹ : ℝ)) p _
      rw [← NNReal.rpow_mul, inv_mul_cancel, NNReal.rpow_one] at this 
      exact this.mp hf
      exact nnreal.coe_ne_zero.mpr (ne_of_gt (Fact.out _))
      rw [← NNReal.coe_zero]
      exact nnreal.coe_lt_coe.mpr (Fact.out _)⟩
  invFun x :=
    ⟨fun _ => x, by
      have := @Real.rpow_le_rpow_iff (|↑x| : ℝ) (c ^ (p⁻¹ : ℝ)) p _ _ _
      rw [← Real.rpow_mul, inv_mul_cancel, Real.rpow_one] at this 
      have hx := x.2
      simp only [mem_filtration_iff, Subtype.val_eq_coe, nnnorm, Fintype.univ_punit,
        Finset.sum_singleton, ← NNReal.coe_le_coe, NNReal.coe_rpow, Subtype.coe_mk,
        Real.norm_eq_abs, this, abs_le, mem_closedBall_zero_iff] at hx ⊢
      exact hx
      · rw [NNReal.coe_ne_zero]
        exact ne_of_gt (Fact.out _)
      · exact c.2
      · exact abs_nonneg x
      · rw [← NNReal.coe_rpow]
        exact (c ^ (p⁻¹ : ℝ)).2
      · rw [← NNReal.coe_zero, NNReal.coe_lt_coe]
        exact Fact.out _⟩
  left_inv := by
    intro
    ext
    simp only [Subtype.val_eq_coe, Subtype.coe_mk]
    apply congr_arg
    simp only [eq_iff_true_of_subsingleton]
  right_inv := by
    intro
    simp only [Subtype.coe_eta]

def homeoFiltrationϖBall (c : ℝ≥0) :
    filtration (ℳ p ϖ) c ≃ₜ closedBall (0 : ℝ) (c ^ (p⁻¹ : ℝ) : ℝ≥0)
    where
  toEquiv := equivFiltrationϖBall c
  continuous_toFun := by
    refine' Continuous.subtype_mk _ _
    exact Continuous.comp (continuous_apply PUnit.unit) continuous_subtype_val
  continuous_invFun := by
    simp only [equiv_filtration_ϖ_ball]
    continuity

theorem RealMeasures.dist_eq {c : ℝ≥0} (F G : filtration (ℳ p ϖ) c) :
    ‖F.1 - G.1‖ ^ (p⁻¹ : ℝ) =
      |(homeoFiltrationϖBall c F - homeoFiltrationϖBall c G : ℝ)| :=
  by
  have hp : (p : ℝ) ≠ 0 := by
    rw [← NNReal.coe_zero]
    exact ne_of_gt (nnreal.coe_lt_coe.mpr (Fact.out _))
  simp only [norm_def, Fintype.univ_punit, Subtype.val_eq_coe, sub_apply, Finset.sum_singleton, ←
    Real.rpow_mul (norm_nonneg _), mul_inv_cancel hp]
  simpa only [Real.rpow_one, Real.norm_eq_abs]

instance {c : ℝ≥0} : Zero (closedBall (0 : ℝ) c)
    where zero := ⟨0, by simp only [mem_closedBall_zero_iff, norm_zero, NNReal.zero_le_coe]⟩

theorem homeoFiltrationϖBall_preimage {c ε : ℝ≥0} (h : ε ^ (p : ℝ) ≤ c) :
    homeoFiltrationϖBall c ⁻¹' closedBall 0 ε =
      Set.range (Set.inclusion (@PseudoNormedGroup.filtration_mono (ℳ p ϖ) _ _ _ h)) :=
  by
  ext ⟨x, hx⟩
  simp only [homeo_filtration_ϖ_ball, equiv_filtration_ϖ_ball, Subtype.val_eq_coe, Subtype.coe_mk,
    Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Set.mem_preimage, mem_closed_ball, dist_le_coe,
    Set.range_inclusion, Set.mem_setOf_eq]
  change _ ↔ ∑ s : PUnit, ‖x s‖₊ ^ (p : ℝ) ≤ _
  simp only [Fintype.univ_punit, Finset.sum_singleton]
  rw [NNReal.rpow_le_rpow_iff]
  · convert Iff.rfl
    convert (sub_zero _).symm
  · norm_cast; exact Fact.elim inferInstance

-- **[FAE]** The following ones with `_Icc_` might be useless
-- def equiv_filtration_ϖ_Icc (c : ℝ≥0) : filtration (ℳ p ϖ) c ≃ set.Icc ((- c ^ (p⁻¹ : ℝ)) : ℝ)
--   (c ^ (p⁻¹ : ℝ)):=
-- begin
--   fconstructor,
--   { intro f,
--     exact ⟨f.1 punit.star, apply_mem_Icc_of_nnnorm_le _ _ _ f.2⟩ },
--   { intro x,
--     use (λ _, x),
--     have := @real.rpow_le_rpow_iff (|↑x| : ℝ) (c ^ (p⁻¹ : ℝ)) p _ _ _,
--     rw [← real.rpow_mul, inv_mul_cancel, real.rpow_one] at this,
--     have hx := x.2,
--     simpa only [mem_filtration_iff, subtype.val_eq_coe, set.mem_Icc, nnnorm, fintype.univ_punit,
--       finset.sum_singleton, ← nnreal.coe_le_coe, nnreal.coe_rpow, subtype.coe_mk, real.norm_eq_abs,
--       this, abs_le],
--     { rw nnreal.coe_ne_zero,
--       exact ne_of_gt (fact.out _) },
--     { exact c.2 },
--     { exact abs_nonneg x },
--     { rw ← nnreal.coe_rpow,
--      exact (c ^ (p⁻¹ : ℝ)).2 },
--     { rw [← nnreal.coe_zero, nnreal.coe_lt_coe],
--       exact fact.out _ } },
--     { intro f,
--       ext s,
--       simp only [subtype.val_eq_coe, subtype.coe_mk],
--       apply congr_arg,
--       simp only [eq_iff_true_of_subsingleton] },
--     { intro x,
--       simp only [subtype.coe_eta] },
-- end
-- def homeo_filtration_ϖ_Icc (c : ℝ≥0) : filtration (ℳ p ϖ) c ≃ₜ set.Icc ((- c ^ (p⁻¹ : ℝ)) : ℝ)
--   (c ^ (p⁻¹ : ℝ)) :=
-- { to_equiv := equiv_filtration_ϖ_Icc c,
--   continuous_to_fun := admit,
--   continuous_inv_fun := admit
-- }
-- lemma homeo_filtration_ϖ_Icc_apply (c c': ℝ≥0) (h : c ≤ c') :
-- (homeo_filtration_ϖ_Icc c').toFun '' (set.range (set.inclusion (@pseudo_normed_group.filtration_mono (ℳ p ϖ) _ _ _ h)))
--   = ⊥ := --set.Icc ((- c ^ (p⁻¹ : ℝ)) : ℝ) ((c ^ (p⁻¹ : ℝ) : ℝ)) :=
-- begin
--   admit,
-- end
instance chpngRealMeasures : ComphausFilteredPseudoNormedGroup (ℳ p S) :=
  {
    (inferInstance :
      PseudoNormedGroup
        (ℳ p
          S)) with
    continuous_add' := by
      intro c₁ c₂
      rw [continuous_induced_rng]
      simp only [Function.comp, PseudoNormedGroup.add'_eq]
      exact
        (continuous_subtype_val.comp continuous_fst).add
          (continuous_subtype_val.comp continuous_snd)
    continuous_neg' := by
      intro c
      rw [continuous_induced_rng]
      simp only [Function.comp, PseudoNormedGroup.neg'_eq]
      exact continuous_subtype_val.neg
    continuous_castLe := by
      intro c₁ c₂ h
      rw [continuous_induced_rng]
      simp only [Function.comp, PseudoNormedGroup.coe_castLe]
      exact continuous_subtype_val }

variable {α : Type _}

open PseudoNormedGroup ComphausFilteredPseudoNormedGroup

@[simps]
def mapHom [Fact (0 < p)] (f : S ⟶ S') : StrictComphausFilteredPseudoNormedGroupHom (ℳ p S) (ℳ p S')
    where
  toFun := map f
  map_zero' := by ext F s i; simp only [map_apply, Finset.sum_const_zero, zero_apply]
  map_add' F G := by ext s i; simp only [Finset.sum_add_distrib, add_apply, map_apply]
  strict' c F hF := (map_bound _ _).trans hF
  continuous' c := by
    rw [continuous_induced_rng]
    apply continuous_pi _
    intro s'
    simp only [Function.comp, map_apply]
    refine' Continuous.sum' _ _ _
    rintro s -
    exact (continuous_apply s).comp continuous_subtype_val

@[simps]
def functor (p : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)] : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}
    where
  obj S := ⟨ℳ p S, fun F => ⟨‖F‖₊, (mem_filtration_iff _ _).mpr le_rfl⟩⟩
  map S T f := mapHom f
  map_id S := by ext1; rw [map_hom_to_fun, map_id]; rfl
  map_comp S S' S'' f g := by ext1; simp only [map_hom_to_fun, map_comp]; rfl

end RealMeasures

