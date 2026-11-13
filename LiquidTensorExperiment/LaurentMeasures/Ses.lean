-- import laurent_measures.functor
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LiquidTensorExperiment.ForMathlib.PiInduced
import LiquidTensorExperiment.LaurentMeasures.Thm69

#align_import laurent_measures.ses

/-!
This files introduces the maps `Θ`, `Φ` (***and `Ψ` ???***), which are the "measurifications" of
`θ`, `ϕ` (*** and `ψ` ???***)
`laurent_measures.thm69`, they are morphisms in the right category.

We then prove in **???** that `θ_ϕ_exact` of `laurent_measures.thm69` becomes a short exact sequence
in the category **???**.
-/


-- import data.real.basic
-- import data.real.basic
noncomputable section

universe u

namespace LaurentMeasuresSes

open LaurentMeasures PseudoNormedGroup ComphausFilteredPseudoNormedGroup

open ComphausFilteredPseudoNormedGroupHom

open scoped BigOperators NNReal

section PhiToHom

-- parameter {p : ℝ≥0}
-- variables [fact(0 < p)] [fact (p < 1)]
-- local notation `r` := @r p
-- local notation `ℳ` := real_measures p
variable {r : ℝ≥0}

variable [Fact (0 < r)]

variable {S : FintypeCat}

local notation "ℒ" => LaurentMeasures r

local notation "ϖ" => (FintypeCat.of PUnit : Type u)

variable {M₁ M₂ : Type u} [ComphausFilteredPseudoNormedGroup M₁]
  [ComphausFilteredPseudoNormedGroup M₂]

def cfpngHomAdd (f g : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  by
  apply mk_of_bound (f.to_add_monoid_hom + g.to_add_monoid_hom) (f.bound.some + g.bound.some)
  intro c
  refine' ⟨_, _⟩
  · intro x hx
    simp only [ComphausFilteredPseudoNormedGroupHom.coe_mk]
    simp only [AddMonoidHom.add_apply, coe_to_add_monoid_hom]
    convert PseudoNormedGroup.add_mem_filtration (f.bound.some_spec hx) (g.bound.some_spec hx)
    rw [add_mul]
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := fun x =>
    ⟨f x, f.bound.some_spec x.2⟩
  have hf₀ : Continuous f₀ := f.continuous _ fun x => rfl
  let g₀ : filtration M₁ c → filtration M₂ (g.bound.some * c) := fun x =>
    ⟨g x, g.bound.some_spec x.2⟩
  have hg₀ : Continuous g₀ := g.continuous _ fun x => rfl
  simp only [AddMonoidHom.add_apply, coe_to_add_monoid_hom]
  haveI : Fact (f.bound.some * c + g.bound.some * c ≤ (f.bound.some + g.bound.some) * c) :=
    Fact.mk (le_of_eq (add_mul _ _ _).symm)
  let ι :
    filtration M₂ (f.bound.some * c + g.bound.some * c) →
      filtration M₂ ((f.bound.some + g.bound.some) * c) :=
    cast_le
  have hι : Continuous ι := continuous_cast_le _ _
  let S₀ :
    filtration M₂ (f.bound.some * c) × filtration M₂ (g.bound.some * c) →
      filtration M₂ (f.bound.some * c + g.bound.some * c) :=
    fun x => ⟨x.fst + x.snd, add_mem_filtration x.fst.2 x.snd.2⟩
  have hS₀ := continuous_add' (f.bound.some * c) (g.bound.some * c)
  exact hι.comp (hS₀.comp (Continuous.prod_mk hf₀ hg₀))

def cfpngHomNeg (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom M₁ M₂ :=
  by
  apply mk_of_bound (-f.to_add_monoid_hom) f.bound.some
  intro c
  refine' ⟨_, _⟩
  · intro x hx
    simp only [ComphausFilteredPseudoNormedGroupHom.coe_mk]
    convert PseudoNormedGroup.neg_mem_filtration (f.bound.some_spec hx)
  let f₀ : filtration M₁ c → filtration M₂ (f.bound.some * c) := fun x =>
    ⟨f x, f.bound.some_spec x.2⟩
  have hf₀ : Continuous f₀ := f.continuous _ fun x => rfl
  exact (continuous_neg' _).comp hf₀

instance : AddCommGroup (ComphausFilteredPseudoNormedGroupHom M₁ M₂)
    where
  add := cfpngHomAdd
  add_assoc := by intros; ext; apply add_assoc
  zero := 0
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  neg := cfpngHomNeg
  add_left_neg := by intros; ext; apply add_left_neg
  add_comm := by intros; ext; apply add_comm

variable (S)

/-- The map on Laurent measures induced by multiplication by `T⁻¹ - 2` on `ℤ((T))ᵣ`. -/
def Φ : ComphausFilteredPseudoNormedGroupHom (ℒ S) (ℒ S) :=
  shift 1 - 2 • id

-- variable {S}
theorem Φ_eq_ϕ (F : ℒ S) : Φ S F = ϕ F :=
  rfl

-- after the Φ refactor the below lemma is no longer true
-- lemma Φ_bound_by_3 [fact (r ≤ 1)] :
--   (Φ S : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S)).bound_by 3 :=
-- begin
--   let sh : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := shift (-1),
--   let shup : comphaus_filtered_pseudo_normed_group_hom (ℒ S) (ℒ S) := shift (1),
--   have Hsh : sh.bound_by 1,
--   { refine (mk_of_bound_bound_by _ _ _).mono 1 _,
--     rw [neg_neg], exact (pow_one r).le.trans (fact.out _) },
--   have Hshup : shup.bound_by 1,
--   { refine (mk_of_bound_bound_by _ _ _).mono (1) _,
--   }
--   suffices : (sh + sh + (-id)).bound_by (1 + 1 + 1),
--   { convert this using 1, ext1, dsimp only [Φ_eq_ϕ, ϕ], erw two_nsmul, }, -- was refl
--   refine (Hsh.add Hsh).add (mk_of_bound_bound_by _ _ _).neg,
-- end
theorem Φ_natural (S T : FintypeCat) (f : S ⟶ T) (F : ℒ S) (t : T) (n : ℤ) :
    Φ T (map f F) t n = LaurentMeasures.map f (Φ S F) t n := by simp [Φ_eq_ϕ, ϕ, Finset.mul_sum]

end PhiToHom

section Theta

open Theta RealMeasures

parameter (p : ℝ≥0)

local notation "r" => @r p

local notation "ℳ" => RealMeasures p

local notation "ℒ" => LaurentMeasures r

variable {S : FintypeCat.{u}}

local notation "ϖ" => FintypeCat.of (PUnit : Type u)

def sevalℒC (c : ℝ≥0) (s : S) : filtration (ℒ S) c → filtration (ℒ ϖ) c := fun F =>
  by
  refine' ⟨seval_ℒ S s F, _⟩
  have hF := F.2
  simp only [filtration, Set.mem_setOf_eq, seval_ℒ, nnnorm, LaurentMeasures.coe_mk,
    Fintype.univ_punit, Finset.sum_singleton] at hF ⊢
  have := Finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr <| Finset.mem_univ_val _)
  rw [Finset.sum_singleton] at this 
  apply le_trans this hF

variable [Fact (0 < p)]

theorem θ_zero : θ (0 : ℒ S) = 0 := by
  dsimp only [θ, Theta.ϑ]
  funext
  simp only [LaurentMeasures.zero_apply, Int.cast_zero, MulZeroClass.zero_mul, tsum_zero,
    RealMeasures.zero_apply]

variable [Fact (p < 1)]

theorem θ_add (F G : ℒ S) : θ (F + G) = θ F + θ G :=
  by
  dsimp only [θ, Theta.ϑ]
  funext
  simp only [LaurentMeasures.add_apply, Int.cast_add, one_div, inv_zpow', zpow_neg,
    RealMeasures.add_apply, tsum_add]
  rw [← tsum_add]
  · congr
    funext
    rw [add_mul]
  all_goals apply Summable.of_norm;
    simp_rw [← inv_zpow, norm_mul, norm_zpow, norm_inv, Real.norm_two]
  exact
    AuxThm69.summable_smaller_radius_norm F.d half_lt_r (F.summable s) fun n => lt_d_eq_zero _ _ _
  exact
    AuxThm69.summable_smaller_radius_norm G.d half_lt_r (G.summable s) fun n => lt_d_eq_zero _ _ _

--for mathlib
theorem Nnreal.rpow_int_cast (x : ℝ≥0) (n : ℤ) : x ^ n = x ^ (n : ℝ) := by
  rw [← NNReal.coe_eq, NNReal.coe_zpow, ← Real.rpow_int_cast, ← NNReal.coe_rpow]

theorem Nnreal.rpow_le_rpow_of_exponent_le {x : ℝ≥0} (x1 : 1 ≤ x) {y z : ℝ} (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by cases' x with x hx; exact Real.rpow_le_rpow_of_exponent_le x1 hyz

theorem Nnreal.tsum_geom_arit_inequality (f : ℤ → ℝ) {r' : ℝ} (hr'1 : 0 < r') (hr'2 : r' ≤ 1)
    (hs1 : Summable fun n => f n) (hs2 : Summable fun n => ‖f n‖₊ ^ r') :
    ‖tsum fun n => f n‖₊ ^ r' ≤ tsum fun n => ‖f n‖₊ ^ r' :=
  by
  rw [← summable_norm_iff] at hs1 
  simp_rw [← _root_.coe_nnnorm] at hs1 
  rw [NNReal.summable_coe] at hs1 
  refine' le_trans (NNReal.rpow_le_rpow (nnnorm_tsum_le hs1) hr'1.le) _
  have := fun s : Finset ℤ => NNReal.rpow_sum_le_sum_rpow s (fun i => ‖f i‖₊) hr'1 hr'2
  dsimp only at this 
  have s1' :=
    Filter.Tendsto.comp (Continuous.tendsto (NNReal.continuous_rpow_const hr'1.le) _) hs1.has_sum
  dsimp [Function.comp] at s1' 
  apply tendsto_le_of_eventuallyLE s1' hs2.has_sum
  delta Filter.EventuallyLE
  convert Filter.univ_sets _
  ext x
  simp [this]

theorem aux_bound (F : ℒ S) (s : S) :
    ∀ b : ℤ,
      ‖F s b : ℝ‖₊ ^ (p : ℝ) * (2⁻¹ ^ (p : ℝ)) ^ (b : ℝ) ≤ ‖F s b‖₊ * r ^ b :=
  by
  intro b
  rw [NNReal.rpow_int_cast]
  refine' mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg_of_nonneg (NNReal.coe_nonneg _) _)
  have p_le_one : (p : ℝ) ≤ 1 := by
    rw [← NNReal.coe_one]
    exact (nnreal.coe_lt_coe.mpr <| Fact.out _).le
  by_cases hF_nz : F s b = 0
  · rw [hF_nz, Int.cast_zero, nnnorm_zero, nnnorm_zero, NNReal.zero_rpow]
    rw [Ne.def, ← NNReal.coe_zero, NNReal.coe_eq, ← Ne.def]
    exact ne_of_gt (Fact.out _)
  · convert NNReal.rpow_le_rpow_of_exponent_le _ p_le_one
    · rw [NNReal.rpow_one]
      rfl
    · refine' not_lt.mp fun hf => hF_nz (int.abs_lt_one_iff.mp _)
      suffices : (|F s b| : ℝ) < 1; exact_mod_cast this
      rw [← Int.norm_eq_abs]
      rwa [← NNReal.coe_lt_coe, ← nnnorm_norm, Real.nnnorm_of_nonneg (norm_nonneg _)] at hf 

theorem θ_bound : ∀ c : ℝ≥0, ∀ F : ℒ S, F ∈ filtration (ℒ S) c → θ F ∈ filtration (ℳ S) (1 * c) :=
  by
  intro c F hF
  rw [LaurentMeasures.mem_filtration_iff] at hF 
  dsimp only [LaurentMeasures.hasNnnorm] at hF 
  rw [one_mul, RealMeasures.mem_filtration_iff]
  dsimp only [RealMeasures.hasNnnorm, θ, Theta.ϑ]
  let T := S.2.1
  have ineq :
    ∀ s ∈ T,
      ‖(∑' n : ℤ, (F s n : ℝ) * 2⁻¹ ^ n)‖₊ ^ (p : ℝ) ≤
        ∑' n : ℤ, ‖((F s n : ℝ) * 2⁻¹ ^ n)‖₊ ^ (p : ℝ) :=
    by
    intro s hs
    apply nnreal.tsum_geom_arit_inequality fun n => F s n * 2⁻¹ ^ n
    · norm_num; exact Fact.out _
    · suffices : p ≤ 1; assumption_mod_cast; exact Fact.out _
    · dsimp only
      obtain ⟨d, hd⟩ := exists_bdd_filtration r_pos r_lt_one F
      apply AuxThm69.summable_smaller_radius d (F.summable s) (hd s) half_lt_r
    · dsimp only
      simp_rw [nnnorm_mul, NNReal.mul_rpow]
      have := F.summable s
      rw [← NNReal.summable_coe]
      apply Summable.of_nonneg_of_le (fun i => _) _ this; apply NNReal.zero_le_coe
      intro n
      push_cast
      apply mul_le_mul
      · -- true because ∥integer∥ is either 0 or >= 1
        norm_cast
        by_cases h : F s n = 0
        · simp only [h, norm_zero]
          refine' le_of_eq (Real.zero_rpow _)
          norm_cast
          exact ne_of_gt (Fact.out _)
        · nth_rw 2 [(Real.rpow_one (‖F s n‖)).symm]
          apply Real.rpow_le_rpow_of_exponent_le
          · rw [Int.norm_eq_abs, le_abs']
            norm_cast
            rcases lt_trichotomy 0 (F s n) with (hF | hF | hF)
            · right; linarith
            · exact False.elim (h hF.symm)
            · left; change _ ≤ -(1 : ℤ); linarith
          · norm_cast; exact Fact.out _
      · apply le_of_eq
        rw [← r_coe]
        rw [Real.norm_of_nonneg]
        · -- can't use pow_mul yet because one is int one is real
          rw [← Real.rpow_int_cast, ← Real.rpow_int_cast]
          rw [← Real.rpow_mul, mul_comm, Real.rpow_mul] <;> norm_num
        · apply zpow_nonneg
          norm_num
      · refine' (Real.rpow_pos_of_pos _ _).le
        rw [norm_pos_iff]
        apply zpow_ne_zero
        norm_num
      · apply norm_nonneg
  apply (Finset.sum_le_sum ineq).trans
  simp_rw [nnnorm_mul, nnnorm_zpow, nnnorm_inv, NNReal.mul_rpow, Real.nnnorm_two,
    NNReal.rpow_int_cast, ← NNReal.rpow_mul (2 : ℝ≥0)⁻¹, mul_comm, NNReal.rpow_mul (2 : ℝ≥0)⁻¹]
  apply le_trans _ hF
  apply Finset.sum_le_sum
  intro s hs
  apply tsum_le_tsum
  exact aux_bound p F s
  refine' NNReal.summable_of_le _ (F.2 s)
  exacts [aux_bound p F s, F.2 s]

theorem θ_bound' : ∀ c : ℝ≥0, ∀ F : ℒ S, F ∈ filtration (ℒ S) c → θ F ∈ filtration (ℳ S) c := by
  simpa [one_mul] using θ_bound p

def θToAdd : ℒ S →+ ℳ S where
  toFun F := θ F
  map_zero' := θ_zero
  map_add' := θ_add

variable (S)

open Theta Metric RealMeasures

def sevalℳC (c : ℝ≥0) (s : S) : filtration (ℳ S) c → filtration (ℳ ϖ) c := fun x =>
  by
  refine' ⟨fun _ => x.1 s, _⟩
  have hx := x.2
  simp only [filtration, Set.mem_setOf_eq, nnnorm, LaurentMeasures.coe_mk, Fintype.univ_punit,
    Finset.sum_singleton] at hx ⊢
  have := Finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr <| Finset.mem_univ_val _)
  rw [Finset.sum_singleton] at this 
  apply le_trans this hx

-- **[FAE]** From here everything might be useless until `lemma inducing_cast_ℳ`: check
-- also the `variable (c : ℝ≥0)` issue; the idea is to replace cast_ℳ_c with α, for which
-- everything seems to work
variable (c : ℝ≥0)

def Box :=
  { F : ℳ S // ∀ s, ‖F s‖₊ ^ (p : ℝ) ≤ c }

instance : Coe (box S c) (ℳ S) := by dsimp only [box]; infer_instance

instance : TopologicalSpace (ℳ S) := by dsimp only [RealMeasures]; infer_instance

instance : TopologicalSpace (box S c) := by dsimp only [box]; infer_instance

def equivBoxϖ : box S c ≃ ∀ s : S, filtration (ℳ ϖ) c :=
  by
  fconstructor
  · intro F s
    use seval_ℳ S s F.1
    simp only [RealMeasures.mem_filtration_iff, nnnorm, Fintype.univ_punit, Finset.sum_singleton,
      seval_ℳ]
    exact F.2 s
  · intro G
    use fun s => (G s).1 PUnit.unit
    intro s
    simpa only [RealMeasures.mem_filtration_iff, nnnorm, Fintype.univ_punit, Finset.sum_singleton,
      seval_ℳ] using (G s).2
  · intro
    ext s
    simpa only [seval_ℳ]
  · intro G
    ext s
    simp only [seval_ℳ, Subtype.val_eq_coe, Subtype.coe_mk]
    induction x
    rfl

def homeoBoxϖ : box S c ≃ₜ ∀ s : S, filtration (ℳ ϖ) c
    where
  toEquiv := equiv_box_ϖ S c
  continuous_toFun := by
    apply continuous_pi
    intro s
    dsimp only [equiv_box_ϖ, seval_ℳ]
    refine' Continuous.subtype_mk (continuous_pi fun i => _) _
    exact continuous_pi_iff.mp continuous_induced_dom s
  continuous_invFun := by
    dsimp only [equiv_box_ϖ, seval_ℳ]
    refine' Continuous.subtype_mk _ _
    apply continuous_pi
    intro s
    have h : Continuous fun a : S → filtration (ℳ ϖ) c => (a s).val :=
      Continuous.subtype_val (continuous_apply s)
    have H := continuous_apply PUnit.unit
    exact H.comp h

def α : filtration (ℳ S) c → box S c := by
  intro x
  use x
  have hx := x.2
  intro s
  simp only [filtration, Set.mem_setOf_eq, nnnorm, LaurentMeasures.coe_mk, Fintype.univ_punit,
    Finset.sum_singleton] at hx 
  have := Finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr <| Finset.mem_univ_val _)
  rw [Finset.sum_singleton] at this 
  apply le_trans this hx

theorem coe_α_coe : (coe : box S c → ℳ S) ∘ α S c = coe := by funext _; rfl

theorem inducing_α : Inducing (α S c) :=
  by
  have ind_ind := @induced_compose _ _ (ℳ S) _ (α p S c) coe
  rw [coe_α_coe p S c] at ind_ind 
  exact { induced := Eq.symm ind_ind }

theorem seval_ℳ_α_commute (c : ℝ≥0) (s : S) :
    (fun F => (homeo_box_ϖ S c ∘ α S c) F s) = fun F => seval_ℳ_c S c s F :=
  rfl

theorem seval_ℳ_α_commute' {X : Type _} (c : ℝ≥0) {f : X → filtration (ℳ S) c} (s : S) :
    (fun x => (homeo_box_ϖ S c ∘ α S c) (f x) s) = fun x => seval_ℳ_c S c s (f x) :=
  by
  ext z
  have h_commute := @seval_ℳ_α_commute p S _ _ c s
  have := congr_fun h_commute (f z)
  simp only at this 
  rw [this]

@[nolint unused_arguments]
def sevalℒBddC (c : ℝ≥0) (S : FintypeCat) (A : Finset ℤ) (s : S) :
    LaurentMeasuresBdd r S A c → LaurentMeasuresBdd r ϖ A c :=
  by
  intro F
  use fun _ => F s
  have hF := F.2
  simp only [filtration, Set.mem_setOf_eq, seval_ℒ, nnnorm, LaurentMeasures.coe_mk,
    Fintype.univ_punit, Finset.sum_singleton] at hF ⊢
  have := Finset.sum_le_sum_of_subset (finset.singleton_subset_iff.mpr <| Finset.mem_univ_val _)
  rw [Finset.sum_singleton] at this 
  apply le_trans this hF

theorem continuous_sevalℒC (c : ℝ≥0) (s : S) : Continuous (seval_ℒ_c c s) :=
  by
  rw [LaurentMeasures.continuous_iff]
  intro A
  let this.1 := seval_ℒ_bdd_c p c S A s
  have h_trunc :
    @truncate r ϖ c A ∘ seval_ℒ_c p c s = seval_ℒ_bdd_c p c S A s ∘ @truncate r S c A :=
    by
    ext ⟨F, hF⟩ π k
    dsimp only [seval_ℒ_bdd_c, seval_ℒ_c]
    rfl
  rw [h_trunc]
  apply Continuous.comp
  apply continuous_of_discreteTopology
  apply truncate_continuous

section TopologicalGeneralities

open Metric Set

variable {X : Type _} [TopologicalSpace X]

theorem reduction_balls {c : ℝ≥0} (f : X → closedBall (0 : ℝ) c)
    (H : ∀ y : closedBall 0 c, ∀ ε : ℝ, IsOpen (f ⁻¹' ball y ε)) : Continuous f :=
  by
  rw [continuous_def]
  intro _ hU
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨ε, h₀, hε⟩ := (is_open_iff.mp hU) (f x) (mem_preimage.mp hx)
  use f ⁻¹' ball (f x) ε
  exact ⟨preimage_mono hε, H (f x) ε, mem_ball_self h₀⟩

theorem mem_filtration_le_monomial (F : filtration (ℒ ϖ) c) (n : ℕ) :
    ‖F.1 PUnit.unit n : ℝ‖ ≤ c * r⁻¹ ^ n :=
  by
  have h_le : ∑' n : ℤ, ‖F.1 PUnit.unit n : ℝ‖ * r ^ n ≤ c :=
    by
    have := (LaurentMeasures.mem_filtration_iff F.1 c).mp F.2
    rw [LaurentMeasures.nnnorm_def] at this 
    simp only [Fintype.univ_punit, Finset.sum_singleton, ← NNReal.coe_le_coe, NNReal.coe_tsum,
      NNReal.coe_mul, NNReal.coe_zpow, LaurentMeasures.coe_nnnorm] at this 
    exact this
  have :=
    @sum_le_tsum ℝ _ _ _ _ (fun n => ‖F.1 PUnit.unit n : ℝ‖ * r ^ n) {n} _
      (F.1.Summable PUnit.unit)
  simp only [Finset.sum_singleton, zpow_ofNat] at this 
  replace h_le := this.trans h_le
  rwa [← inv_mul_le_iff', inv_pow, inv_inv ((r : ℝ) ^ n), mul_comm]
  · apply pow_pos; rw [inv_pos]; apply r_pos
  · rintro b -
    simp only [Subtype.val_eq_coe]
    exact mul_nonneg (norm_nonneg _) (zpow_nonneg (le_of_lt (nnreal.coe_pos.mpr r_pos)) b)

theorem mem_filtration_sum_le_geom (F : filtration (ℒ ϖ) c) (B : ℕ) :
    ‖(∑' n : { x : ℕ // B ≤ x }, (F.1 PUnit.unit n : ℝ) * 2⁻¹ ^ n.1)‖ ≤
      ‖((c : ℝ) * ∑' n : { x : ℕ // B ≤ x }, (2⁻¹ * r⁻¹) ^ n.1)‖ :=
  by
  have two_r_nonneg : 0 ≤ (2⁻¹ * r⁻¹ : ℝ) := by
    refine' mul_nonneg (inv_nonneg.2 two_pos.le) (inv_nonneg.2 r.2)
  have h_inj : Function.Injective (coe : { x : ℕ // B ≤ x } → ℕ) := Subtype.coe_injective
  have geom_pos : (0 : ℝ) ≤ c * ∑' n : { x // B ≤ x }, (2⁻¹ * r⁻¹) ^ n.1 :=
    by
    apply mul_nonneg c.2 (tsum_nonneg _)
    intro b
    apply pow_nonneg two_r_nonneg
  nth_rw 2 [Real.norm_eq_abs]
  rw [abs_eq_self.mpr geom_pos]
  apply (norm_tsum_le_tsum_norm _).trans
  rw [← tsum_mul_left]
  apply tsum_le_tsum
  · intro b
    rw [norm_mul, mul_pow, mul_comm ((2⁻¹ : ℝ) ^ b.1) _, ← mul_assoc]
    rw [norm_pow, norm_inv, Real.norm_two]
    refine' (mul_le_mul_right _).mpr _
    · simp only [one_div, inv_pos, pow_pos, zero_lt_bit0, zero_lt_one]
    · apply mem_filtration_le_monomial p c F
  swap
  · by_cases hc : (c : ℝ) ≠ 0
    · rw [← summable_mul_left_iff hc]
      have two_r_lt : (2⁻¹ * r⁻¹ : ℝ) < 1 :=
        by
        have := (div_lt_one (nnreal.coe_lt_coe.mpr r_pos)).mpr half_lt_r
        simp only [← inv_eq_one_div] at this ⊢
        rw [div_eq_mul_inv, NNReal.coe_inv] at this 
        convert this
        assumption'
      exact (summable_geometric_of_lt_1 two_r_nonneg two_r_lt).comp_injective h_inj
    · rw [not_ne_iff] at hc 
      simp_rw [hc, MulZeroClass.zero_mul]
      exact summable_zero
  all_goals
    simp_rw [norm_mul, norm_pow, norm_inv, Real.norm_two, Subtype.val_eq_coe]
    refine'
      ((AuxThm69.summable_iff_on_nat_less F.1.d _).mp
            (AuxThm69.summable_smaller_radius_norm F.1.d half_lt_r (F.1.Summable PUnit.unit)
              fun n => lt_d_eq_zero F.1 PUnit.unit n)).comp_injective
        h_inj
    intro n hn
    rw [lt_d_eq_zero F.1 PUnit.unit n hn, norm_zero, MulZeroClass.zero_mul]

def geomBNat (ε : ℝ) (hε : 0 < ε) :
    { B : ℕ //
      ∀ F : filtration (ℒ ϖ) c,
        ‖(tsum fun b : { n : ℕ // B ≤ n } => (F.1 PUnit.unit b.1 : ℝ) * 2⁻¹ ^ b.1)‖ <
          ε ^ (p⁻¹ : ℝ) } :=
  by
  let g := fun n : ℕ => (c : ℝ) * (2⁻¹ * r⁻¹) ^ n
  have := tendsto_tsum_compl_atTop_zero g
  rw [tendsto_at_top] at this 
  have h_pos : 0 < ε ^ (p⁻¹ : ℝ) := Real.rpow_pos_of_pos hε _
  specialize this (ε ^ (p⁻¹ : ℝ)) h_pos
  let A := this.some
  let B₀ : Option ℕ → ℕ := fun a : Option ℕ => Option.recOn a (0 : ℕ) fun n => n
  set B := (B₀ A.max).succ with hB
  use B
  have h_incl : A ≤ Finset.range B
  rw [Finset.le_eq_subset]
  · by_cases H : A.nonempty
    · intro a ha
      obtain ⟨s, hs⟩ := Finset.max_of_nonempty H
      replace hB : s.succ = B; · simp only [*, Option.mem_def]; rfl
      have h_mem := finset.mem_range_succ_iff.mpr (finset.le_max_of_mem ha hs)
      rwa [hB] at h_mem 
    · intro a ha
      rw [Finset.not_nonempty_iff_eq_empty] at H 
      finish
  let hA := this.some_spec
  specialize hA (Finset.range B) h_incl
  rw [Real.dist_0_eq_abs, ← Real.norm_eq_abs] at hA 
  intro F
  apply lt_of_le_of_lt (mem_filtration_sum_le_geom p c F B)
  convert hA using 1
  apply congr_arg
  simp_rw [Subtype.val_eq_coe, ← tsum_mul_left]
  have set_eq : {n : ℕ | B ≤ n} = {n : ℕ | n ∉ Finset.range B} := by
    simp only [Finset.mem_range, not_lt]
  exact tsum_congr_subtype g set_eq

def eqLeIntNat (B : ℕ) : { n : ℤ // (B : ℤ) ≤ n } ≃ { n : ℕ // B ≤ n }
    where
  toFun := by
    intro b
    use(Int.eq_ofNat_of_zero_le ((Int.coe_nat_nonneg B).trans b.2)).some
    rw [← Int.ofNat_le]
    convert b.2
    exact (Exists.choose_spec (Int.eq_ofNat_of_zero_le ((Int.coe_nat_nonneg B).trans b.2))).symm
  invFun n := ⟨n, by simp only [coe_coe, Int.ofNat_le]; exact n.2⟩
  left_inv := by
    rintro ⟨_, h⟩
    simp only [coe_coe, Subtype.coe_mk]
    exact (Exists.choose_spec (Int.eq_ofNat_of_zero_le ((Int.coe_nat_nonneg B).trans h))).symm
  right_inv := by
    rintro ⟨_, h⟩
    simp only [coe_coe, Subtype.coe_mk, Int.coe_nat_inj']
    exact (@exists_eq' _ _).choose_spec.symm

def geomBInt (ε : ℝ) (hε : 0 < ε) :
    { B : ℤ //
      ∀ F : filtration (ℒ ϖ) c,
        ‖(tsum fun b : { n : ℤ // B ≤ n } => (F.1 PUnit.unit b.1 : ℝ) * 2⁻¹ ^ b.1)‖ <
          ε ^ (p⁻¹ : ℝ) } :=
  by
  let ℬ := geom_B_nat p c ε hε
  let B := ℬ.1
  let hB := ℬ.2
  use B
  intro F
  specialize hB F
  convert hB using 1
  apply congr_arg
  exact
    ((eq_le_int_nat B).symm.tsum_eq fun b : { n : ℤ // ↑B ≤ n } =>
        (F.1 PUnit.unit b.1 : ℝ) * 2⁻¹ ^ b.1).symm

def geomB (ε : ℝ) (hε : 0 < ε) : ℤ :=
  (geom_B_int c ε hε).1

theorem tail_B (ε : ℝ) (hε : 0 < ε) :
    ∀ F : filtration (ℒ ϖ) c,
      ‖(tsum fun b : { n : ℤ // geom_B c ε hε ≤ n } => (F.1 PUnit.unit b.1 : ℝ) * 2⁻¹ ^ b.1)‖ <
        ε ^ (p⁻¹ : ℝ) :=
  by
  intro F
  have := (geom_B_int p c ε hε).2 F
  exact this

def u (F : filtration (ℒ ϖ) c) (B : ℤ) : Set (filtration (ℒ ϖ) c) := fun G =>
  ∀ s n, n < B → F s n = G s n

theorem mem_u (F : filtration (ℒ ϖ) c) (B : ℤ) : F ∈ U c F B := fun _ _ _ => rfl

theorem explodes_pow_r (ρ : ℝ≥0) (h₀ : 0 < ρ.1) (h₁ : ρ.1 < 1) (c : ℝ≥0) :
    ∃ n₀ : ℤ, ∀ m : ℤ, m < n₀ → c < ρ ^ m :=
  by
  convert_to ∃ n₀ : ℕ, ∀ m : ℕ, (-m : ℤ) < -n₀ → (c : ℝ) < ρ ^ (-m : ℤ) using 0
  · simp only [neg_lt_neg_iff, Int.ofNat_lt, zpow_neg, zpow_ofNat, eq_iff_iff]
    constructor
    · rintro ⟨n₀, hn₀⟩
      induction n₀
      · use n₀
        intro m hm
        rw [← Int.ofNat_lt] at hm 
        replace hm := neg_lt.mpr (lt_of_le_of_lt (neg_le_self (Int.coe_nat_nonneg _)) hm)
        specialize hn₀ (-m) hm
        rwa [← NNReal.coe_lt_coe, NNReal.coe_zpow, zpow_neg] at hn₀ 
      · use n₀ + 1
        intro m hm
        rw [← Int.ofNat_lt, ← neg_lt_neg_iff, ← Int.negSucc_coe] at hm 
        specialize hn₀ (-m) hm
        rwa [← NNReal.coe_lt_coe, NNReal.coe_zpow, zpow_neg] at hn₀ 
    · rintro ⟨n₀, hn₀⟩
      use-n₀
      rintro ⟨m⟩ hm
      · have := right.neg_nonpos_iff.mpr (Int.ofNat_nonneg n₀)
        rw [Int.ofNat_eq_coe] at this 
        replace := ne_of_lt (lt_of_lt_of_le (lt_of_le_of_lt (Int.ofNat_nonneg m) hm) this)
        finish
      · rw [Int.negSucc_coe, neg_lt_neg_iff, Int.ofNat_lt] at hm 
        specialize hn₀ (m + 1) hm
        rwa [Int.negSucc_coe, ← NNReal.coe_lt_coe, zpow_neg, zpow_ofNat, NNReal.coe_inv,
          NNReal.coe_pow]
  have h := (tendsto_pow_atTop_nhdsWithin_0_of_lt_1 h₀ h₁).inv_tendsto_zero
  simp_rw [← zpow_ofNat] at h 
  have : (fun n : ℕ => ρ.1 ^ (n : ℤ))⁻¹ = fun n : ℕ => ρ.1 ^ (-n : ℤ) :=
    by
    ext
    simp only [Pi.inv_apply, zpow_neg]
  rw [this, Filter.tendsto_atTop] at h 
  specialize h (c + 1)
  rw [NNReal.val_eq_coe] at h 
  simp_rw [← NNReal.coe_zpow] at h 
  obtain ⟨n₀, hn₀⟩ := Filter.Eventually.exists_forall_of_atTop h
  use n₀
  intro m hm
  rw [neg_lt_neg_iff, Int.ofNat_lt] at hm 
  replace hm := le_of_lt hm
  specialize hn₀ m hm
  rw [NNReal.coe_zpow] at hn₀ 
  refine' lt_of_lt_of_le _ hn₀
  exact lt_add_one _

theorem isOpen_u (F : filtration (ℒ ϖ) c) (B : ℤ) : IsOpen (U c F B) :=
  by
  let ι : filtration (ℒ ϖ) c → ∀ i : ℤ, ℤ := fun t i => truncate {i} t PUnit.unit ⟨i, by simp⟩
  have hι : Continuous ι := by
    rw [continuous_pi_iff]; intro i
    dsimp [ι]
    change
      Continuous
        ((fun t : LaurentMeasuresBdd r ϖ {i} c => t PUnit.unit ⟨i, by simp⟩) ∘ truncate {i})
    refine' Continuous.comp continuous_bot (truncate_continuous r (FintypeCat.of PUnit) c {i})
  obtain ⟨n₀, h₀⟩ :
    ∃ n₀ : ℤ, ∀ (m : ℤ) (H : ℒ ϖ) (hH : H ∈ filtration (ℒ ϖ) c), m < n₀ → H PUnit.unit m = 0 :=
    by
    obtain ⟨n₀, h₀⟩ : ∃ n₀ : ℤ, ∀ m : ℤ, m < n₀ → c < r ^ m := explodes_pow_r r r_pos r_lt_one c
    use n₀; intro m H hH hm
    exact eq_zero_of_filtration H _ hH PUnit.unit m (h₀ m hm)
  classical
  let UU : Set (∀ i : ℤ, ℤ) :=
    Set.pi (Set.Ico n₀ B) fun i => if i ∈ Set.Ico n₀ B then {F PUnit.unit i} else ⊤
  have hUU : IsOpen UU := by
    apply isOpen_set_pi; exact finite_Ico n₀ B
    intro a ha; trivial
  convert hUU.preimage hι
  ext G
  constructor
  · intro hG; dsimp [U, UU, ι] at hG ⊢
    intro i hi; rw [if_pos hi]
    simp only [mem_singleton_iff]
    symm
    apply hG; exact hi.2
  · intro hG; dsimp [U, UU, ι] at hG ⊢
    rintro ⟨⟩ n hn
    symm
    by_cases hn' : n < n₀
    · erw [h₀ n G.1 G.2 hn', h₀ n F.1 F.2 hn']
    push_neg at hn' 
    specialize hG n; simpa [hn', hn] using hG

end TopologicalGeneralities

def θC (c : ℝ≥0) (T : FintypeCat) :
    filtration (LaurentMeasures r T) c → filtration (RealMeasures p T) c :=
  by
  intro f
  rw [← one_mul c]
  use⟨θ f, θ_bound p c f f.2⟩

theorem commute_seval_ℒ_ℳ (c : ℝ≥0) (s : S) :
    θ_c c (FintypeCat.of PUnit) ∘ seval_ℒ_c c s = seval_ℳ_c S c s ∘ θ_c c S := by
  simpa only [seval_ℳ_c, seval_ℒ_c, seval_ℒ, θ_c, one_mul, Subtype.coe_mk, eq_mpr_eq_cast,
    set_coe_cast]

theorem continuous_of_seval_ℳ_comp_continuous (c : ℝ≥0) {X : Type _} [TopologicalSpace X]
    {f : X → filtration (ℳ S) c} : (∀ s, Continuous (seval_ℳ_c S c s ∘ f)) → Continuous f :=
  by
  intro H
  replace H : ∀ s : S, Continuous fun x : X => (homeo_box_ϖ p S c ∘ α p S c) (f x) s
  · intro
    rw [seval_ℳ_α_commute' p S c s]
    exact H s
  rw [← continuous_pi_iff] at H 
  convert_to Continuous fun x => (homeo_box_ϖ p S c) (α p S c (f x)) using 0
  · apply eq_iff_iff.mpr
    rw [Homeomorph.comp_continuous_iff, (inducing_α p S c).continuous_iff]
  exact H

theorem tsum_subtype_sub {f g : ℤ → ℝ} {B : ℤ}
    (hf : Summable fun b : { x // B ≤ x } => f b * 2⁻¹ ^ b.1)
    (hg : Summable fun b : { x // B ≤ x } => g b * 2⁻¹ ^ b.1) :
    ‖(tsum ((fun b : ℤ => ((g b : ℝ) - f b) * 2⁻¹ ^ b) ∘ (coe : {b | B ≤ b} → ℤ)))‖ =
      ‖(∑' b : { x // B ≤ x }, (g b : ℝ) * 2⁻¹ ^ b.1 -
          ∑' b : { x // B ≤ x }, (f b : ℝ) * 2⁻¹ ^ b.1)‖ :=
  by
  rw [← tsum_sub hg hf, tsum_eq_tsum_of_hasSum_iff_hasSum]
  intro
  simp_rw [sub_mul, iff_eq_eq]
  rfl

theorem aux_summability_no_norm (F : filtration (ℒ ϖ) c) :
    Summable fun b : ℤ => (F PUnit.unit b : ℝ) * 2⁻¹ ^ b :=
  AuxThm69.summable_smaller_radius F.1.d (F.1.Summable PUnit.unit)
    (fun n => lt_d_eq_zero F.1 PUnit.unit n) half_lt_r

theorem aux_summability_subtype (F : filtration (ℒ ϖ) c) (B : ℤ) :
    Summable fun b : { x : ℤ // B ≤ x } => (F PUnit.unit b : ℝ) * 2⁻¹ ^ b.1 :=
  (aux_summability_no_norm p c F).comp_injective Subtype.coe_injective

theorem pos_ε_pow (ε : ℝ) (hε : 0 < ε) : 0 < ε / (2 : ℝ) ^ p.1 :=
  by
  apply div_pos hε (Real.rpow_pos_of_pos _ _)
  simp only [zero_lt_bit0, zero_lt_one]

theorem dist_lt_of_mem_u (ε : ℝ≥0) (hε : 0 < ε) (F G : filtration (ℒ ϖ) c) :
    G ∈ U c F (geom_B c (ε / (2 : ℝ) ^ p.1) (pos_ε_pow ε hε)) →
      ‖((θ_c c ϖ G : ℳ ϖ) - (θ_c c ϖ) F)‖ < ε :=
  by
  intro h_mem_G
  rw [RealMeasures.norm_def]
  simp only [Fintype.univ_punit, RealMeasures.sub_apply, Finset.sum_singleton]
  rw [← Real.rpow_lt_rpow_iff _ _ _, ← Real.rpow_mul, mul_inv_cancel, Real.rpow_one]
  rotate_left
  · rw [← NNReal.coe_zero]
    exact ne_of_gt (nnreal.coe_lt_coe.mpr (Fact.out _))
  · apply norm_nonneg
  · apply Real.rpow_nonneg_of_nonneg (norm_nonneg _)
  · rw [← NNReal.coe_zero]
    exact ε.2
  · rw [inv_pos, ← NNReal.coe_zero]
    exact nnreal.coe_lt_coe.mpr (Fact.out _)
  simp only [θ_c, one_mul, eq_mpr_eq_cast, set_coe_cast, Subtype.coe_mk]
  dsimp only [θ, ϑ]
  have h_B :
    ∀ b : ℤ,
      b < geom_B p c (ε / 2 ^ p.1) (pos_ε_pow p ε hε) → (G PUnit.unit b : ℝ) - F PUnit.unit b = 0 :=
    by
    intro b hb
    simp only [h_mem_G PUnit.unit b hb, sub_self]
  rw [← tsum_sub]
  rotate_left
  · exact aux_summability_no_norm p c G
  · exact aux_summability_no_norm p c F
  simp_rw [← sub_mul]
  set B := geom_B p c (ε / 2 ^ p.1) (pos_ε_pow p ε hε) with def_B
  let f := fun b : ℤ => ((G : ℒ ϖ) PUnit.unit b - (F : ℒ ϖ) PUnit.unit b : ℝ) * 2⁻¹ ^ b
  let g : {b : ℤ | B ≤ b} → ℝ := f ∘ coe
  let i : Function.support g → ℤ :=
    (coe : {b : ℤ | B ≤ b} → ℤ) ∘ (coe : Function.support g → {b : ℤ | B ≤ b})
  have hi : ∀ ⦃x y : ↥(Function.support g)⦄, i x = i y → ↑x = ↑y :=
    by
    intro _ _ h
    simp only [Subtype.coe_inj] at h 
    rwa [Subtype.coe_inj]
  have hf : Function.support f ⊆ Set.range i :=
    by
    intro a ha
    simp only [f, Function.mem_support, Ne.def] at ha 
    have ha' : B ≤ a := by
      by_contra'
      specialize h_B a this
      simp only [one_div, inv_zpow', zpow_neg, mul_eq_zero, inv_eq_zero, not_or] at ha 
      replace ha := ha.1
      simpa only
    simp only [Set.mem_setOf_eq, Function.mem_support, Ne.def, Set.mem_range, SetCoe.exists]
    use a, ha', ha, refl _
  have hF := tail_B p c (ε.1 / 2 ^ p.1) (pos_ε_pow p ε hε) F
  have hG := tail_B p c (ε.1 / 2 ^ p.1) (pos_ε_pow p ε hε) G
  have h02 : (0 : ℝ) ≤ 2 := two_pos.le
  have h02p : (0 : ℝ) ≤ 2 ^ p.val := Real.rpow_nonneg_of_nonneg h02 _
  rw [Real.div_rpow ε.2 h02p, ← Real.rpow_mul h02] at hF hG 
  simp_rw [@Subtype.val_eq_coe _ _ p] at hF hG 
  have hp0 : (p : ℝ) ≠ 0 := nnreal.coe_ne_zero.mpr (ne_of_gt (Fact.out _))
  rw [mul_inv_cancel hp0, Real.rpow_one] at hF hG 
  rw [tsum_eq_tsum_of_ne_zero_bij i hi hf fun _ => refl _]
  dsimp only [f, g]
  rw [tsum_subtype_sub]
  rotate_left
  · exact aux_summability_subtype p c F B
  · exact aux_summability_subtype p c G B
  apply lt_of_le_of_lt (norm_sub_le _ _)
  convert add_lt_add hG hF
  simp only [NNReal.val_eq_coe, add_halves']

theorem coe_pow_half (η : ℝ) (η_pos' : 0 < η) (η₀ : ℝ≥0) (hη₀ : η₀ = ⟨η, le_of_lt η_pos'⟩) :
    (η / 2) ^ (p : ℝ) = (η₀ ^ (p : ℝ) : ℝ) / 2 ^ p.1 :=
  by
  rw [Real.div_rpow (le_of_lt η_pos') _, NNReal.val_eq_coe, hη₀, Subtype.coe_mk]
  simp only [zero_le_bit0, zero_le_one]

section

variable {c}

def ξ (F : filtration (ℒ ϖ) c) : ℝ :=
  (homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F)

def hξ (F : filtration (ℒ ϖ) c) : ξ F = (homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F) :=
  rfl

theorem speed_aux' (ε η : ℝ) (η₀ : ℝ≥0) (hη₀ : η = η₀) (y : closedBall (0 : ℝ) (c ^ (p : ℝ)⁻¹))
    (F G : filtration (ℒ (FintypeCat.of PUnit)) c)
    (hF : |((homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F) : ℝ) - y| < ε)
    (hη : η = ε - |homeoFiltrationϖBall c (θ_c c ϖ F) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
    (h_pos : 0 < (η / 2) ^ (p : ℝ)) (hp : 0 < (p : ℝ)) (η_pos' : 0 < η)
    (h_η_η₀ : (η / 2) ^ (p : ℝ) = ↑η₀ ^ (p : ℝ) / 2 ^ p.val) (h_pos'')
    (hG : G ∈ U c F (geom_B c (↑η₀ ^ (p : ℝ) / 2 ^ p.val) h_pos'')) :
    ‖((θ_c c (FintypeCat.of PUnit) G).val - (θ_c c (FintypeCat.of PUnit) F).val)‖ <
      η ^ (p : ℝ) :=
  by
  have foo : 0 < η₀ ^ (p : ℝ) := by apply Real.rpow_pos_of_pos; rw [← hη₀]; exact η_pos'
  -- exact dist_lt_of_mem_U p c (η₀ ^ (p : ℝ)) (real.rpow_pos_of_pos η_pos' _) F G hG
  have := dist_lt_of_mem_U p c (η₀ ^ (p : ℝ)) foo F G hG
  convert this

theorem speed_aux (ε η : ℝ) (η₀ : ℝ≥0) (hη₀ : η = η₀) (y : closedBall (0 : ℝ) (c ^ (p : ℝ)⁻¹))
    (F G : filtration (ℒ (FintypeCat.of PUnit)) c)
    (hF : |((homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F) : ℝ) - y| < ε)
    (hη : η = ε - |homeoFiltrationϖBall c (θ_c c ϖ F) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
    (h_pos : 0 < (η / 2) ^ (p : ℝ)) (hp : 0 < (p : ℝ)) (η_pos' : 0 < η)
    (h_η_η₀ : (η / 2) ^ (p : ℝ) = ↑η₀ ^ (p : ℝ) / 2 ^ p.val) (h_pos'')
    (hG : G ∈ U c F (geom_B c (↑η₀ ^ (p : ℝ) / 2 ^ p.val) h_pos'')) : |ξ G - ξ F| < ε - |ξ F - y| :=
  by
  repeat' rw [hξ]
  rw [← real_measures.dist_eq, ←
    Real.rpow_lt_rpow_iff (Real.rpow_nonneg_of_nonneg (real_measures.norm_nonneg _) _)
      (sub_nonneg.mpr (le_of_lt hF)) hp,
    ← Real.rpow_mul (real_measures.norm_nonneg _), inv_mul_cancel (ne_of_gt hp), Real.rpow_one, ←
    hη]
  apply speed_aux'; assumption'

theorem speed (ε η : ℝ) (y : closedBall (0 : ℝ) (c ^ (p⁻¹ : ℝ))) (F G : filtration (ℒ ϖ) c)
    (hF : |((homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F) : ℝ) - y| < ε)
    (hη : η = ε - |homeoFiltrationϖBall c (θ_c c ϖ F) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
    (hG : G ∈ U c F (geom_B c ((η / 2) ^ (p : ℝ)) h_pos)) :
    |ξ G - ξ F| + |ξ F - y| < ε - |ξ F - y| + |ξ F - y| :=
  by
  have hp : 0 < (p : ℝ) := by rw [← NNReal.coe_zero, NNReal.coe_lt_coe]; exact Fact.out _
  have η_pos' : 0 < η := by rw [hη]; exact sub_pos.mpr hF
  set η₀ : ℝ≥0 := ⟨η, le_of_lt η_pos'⟩ with hη₀
  have h_η_η₀ := @coe_pow_half p _ _ η η_pos' η₀ hη₀
  simp_rw [h_η_η₀] at hG 
  apply add_lt_add_right
  apply @speed_aux p _ _ c ε η η₀ _ y F G
  assumption'
  rw [hη₀]; rfl

end

theorem u_subset_preimage' (ε η : ℝ) (y : closedBall (0 : ℝ) (c ^ (p⁻¹ : ℝ)))
    (F : filtration (ℒ ϖ) c)
    (hF : |((homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F) : ℝ) - y| < ε)
    (hη : η = ε - |homeoFiltrationϖBall c (θ_c c ϖ F) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ))
    (G : filtration (ℒ (FintypeCat.of PUnit)) c)
    (hG : G ∈ U c F (geom_B c ((η / 2) ^ (p : ℝ)) h_pos)) : |ξ G - y| < ε :=
  by
  have aux : |ξ p G - ξ p F| + |ξ p F - y| < ε - |ξ p F - y| + |ξ p F - y| := by
    apply speed <;> assumption
  replace aux : |ξ p G - ξ p F| + |ξ p F - y| < ε
  · rwa [sub_add_cancel ε |ξ p F - y|] at aux 
  have := lt_of_le_of_lt (abs_sub_le (ξ p G) (ξ p F) y) aux
  rw [← Real.norm_eq_abs] at this ⊢
  exact this

theorem u_subset_preimage (ε η : ℝ) (y : closedBall (0 : ℝ) (c ^ (p⁻¹ : ℝ)))
    (F : filtration (ℒ ϖ) c)
    (hF : |((homeoFiltrationϖBall c) (θ_c c (FintypeCat.of PUnit) F) : ℝ) - y| < ε)
    (hη : η = ε - |homeoFiltrationϖBall c (θ_c c ϖ F) - y|) (h_pos : 0 < (η / 2) ^ (p : ℝ)) :
    U c F (geom_B c ((η / 2) ^ (p : ℝ)) h_pos) ⊆ homeoFiltrationϖBall c ∘ θ_c c ϖ ⁻¹' ball y ε :=
  by
  intro G hG
  simp only [Set.mem_preimage, one_mul, eq_self_iff_true, eq_mpr_eq_cast, set_coe_cast,
    Function.comp_apply, mem_ball, Subtype.dist_eq, Real.dist_eq]
  apply U_subset_preimage' <;> assumption

-- This is the main continuity property needed in `ses2.lean`
theorem continuous_θC (c : ℝ≥0) : Continuous (θ_c c S) :=
  by
  apply continuous_of_seval_ℳ_comp_continuous
  intro s
  rw [← commute_seval_ℒ_ℳ]
  refine' Continuous.comp _ (continuous_seval_ℒ_c p S c s)
  apply (homeo_filtration_ϖ_ball c).comp_continuous_iff.mp
  apply reduction_balls
  intro y ε
  rw [isOpen_iff_forall_mem_open]
  intro F hF
  simp only [Set.mem_preimage, one_mul, eq_self_iff_true, eq_mpr_eq_cast, set_coe_cast,
    Function.comp_apply, mem_ball, Subtype.dist_eq, Real.dist_eq] at hF 
  set η := ε - |homeo_filtration_ϖ_ball c (θ_c p c ϖ F) - y| with hη
  have η_pos' : 0 < η := by rw [hη]; exact sub_pos.mpr hF
  have η_pos : 0 < (η / 2) ^ (p : ℝ) := Real.rpow_pos_of_pos (half_pos η_pos') _
  set V := U p c F (geom_B p c ((η / 2) ^ (p : ℝ)) η_pos) with hV
  simp_rw [Real.div_rpow (le_of_lt η_pos') (le_of_lt (@two_pos ℝ _ _))] at hV 
  use V
  exact
    And.intro (U_subset_preimage p c ε η y F hF hη η_pos)
      (And.intro (is_open_U p c F _) (mem_U p c F _))

end Theta

end LaurentMeasuresSes

