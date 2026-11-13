import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Intervals.Disjoint
import Mathlib.Data.Set.Intervals.Group
import Mathlib.Data.Set.Intervals.Infinite
import Mathlib.Data.Set.Intervals.Instances
import Mathlib.Data.Set.Intervals.IsoIoo
import Mathlib.Data.Set.Intervals.Monoid
import Mathlib.Data.Set.Intervals.Monotone
import Mathlib.Data.Set.Intervals.OrdConnected
import Mathlib.Data.Set.Intervals.OrdConnectedComponent
import Mathlib.Data.Set.Intervals.OrderIso
import Mathlib.Data.Set.Intervals.Pi
import Mathlib.Data.Set.Intervals.ProjIcc
import Mathlib.Data.Set.Intervals.SurjOn
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.Data.Set.Intervals.WithBotTop
import Mathlib.Analysis.MeanInequalitiesPow
import LiquidTensorExperiment.ForMathlib.Nnreal
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.Condensed.Ab

#align_import normed_free_pfpng.basic

open scoped BigOperators NNReal

universe u

variable (p : ℝ≥0) (S : FintypeCat.{u})

/-- The functor represented by ℤ, i.e., sending a finite type `S` to `S → ℤ`,
  equipped with the "p-norm" sending `s ↦ f(s)` to `∑ₛ∥f(s)∥₊ᵖ`. This is the
  construction defined as a bare function. -/
def NormedFreePfpng (p : ℝ≥0) (S : FintypeCat.{u}) :=
  S → ℤ
deriving AddCommGroup

noncomputable section

open scoped Classical

instance : NNNorm (NormedFreePfpng p S) :=
  ⟨fun f => ∑ s, ‖f s‖₊ ^ (p : ℝ)⟩

namespace NormedFreePfpng

protected theorem nnnorm_def (f : NormedFreePfpng p S) :
    ‖f‖₊ = ∑ s, ‖f s‖₊ ^ (p : ℝ) :=
  rfl

@[simp]
theorem nnnorm_zero [Fact (0 < p)] : ‖0 : NormedFreePfpng p S‖₊ = 0 :=
  by
  change ∑ _, _ = _;
  simp only [Pi.zero_apply, nnnorm_zero, Finset.sum_const, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, Finset.card_eq_zero, NNReal.rpow_eq_zero_iff, eq_self_iff_true, Ne.def,
    NNReal.coe_eq_zero, true_and_iff]
  right; have : 0 < p := Fact.out _; exact this.ne'

@[simp]
theorem nnnorm_neg (f : NormedFreePfpng p S) : ‖-f‖₊ = ‖f‖₊ := by
  change ∑ _, _ = _; simpa

theorem nnnorm_add [Fact (0 ≤ p)] [Fact (p ≤ 1)] (f₁ f₂ : NormedFreePfpng p S) :
    ‖f₁ + f₂‖₊ ≤ ‖f₁‖₊ + ‖f₂‖₊ :=
  by
  change ∑ _, _ ≤ ∑ _, _ + ∑ _, _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have h0p : 0 ≤ p := Fact.out _
  have hp1 : p ≤ 1 := Fact.out _
  calc
    ‖((f₁ + f₂) s)‖₊ ^ ↑p ≤ (‖f₁ s‖₊ + ‖f₂ s‖₊) ^ ↑p :=
      NNReal.rpow_le_rpow (nnnorm_add_le _ _) h0p
    _ ≤ ‖f₁ s‖₊ ^ ↑p + ‖f₂ s‖₊ ^ ↑p := NNReal.rpow_add_le_add_rpow _ _ h0p hp1

instance (c) : TopologicalSpace {f : NormedFreePfpng p S | ‖f‖₊ ≤ c} :=
  ⊥

instance (c) : DiscreteTopology {f : NormedFreePfpng p S | ‖f‖₊ ≤ c} :=
  ⟨rfl⟩

theorem norm_eval_le {c : NNReal} (s : S) (f : NormedFreePfpng p S) (hf : ‖f‖₊ ≤ c) :
    ‖f s‖₊ ^ (p : ℝ) ≤ c :=
  le_trans
    (by
      apply @Finset.single_le_sum S NNReal _ (fun t => ‖f t‖₊ ^ (p : ℝ)) Finset.univ
      · intro _ _; apply zero_le
      · exact Finset.mem_univ s)
    hf

instance [Fact (0 < p)] (c) : Fintype {f : NormedFreePfpng p S | ‖f‖₊ ≤ c} :=
  by
  let A := {f : NormedFreePfpng p S | ‖f‖₊ ≤ c}
  let N := ⌈c ^ (p⁻¹ : ℝ)⌉₊
  have hN := @Nat.le_ceil ℝ≥0 _ _ (c ^ (p⁻¹ : ℝ))
  have h0p : 0 < p := Fact.out _
  have h0pinv : 0 ≤ p⁻¹ := by rw [← nnreal.inv_pos] at h0p ; exact h0p.le
  let ι : A → S → Set.Icc (-(N : ℤ)) N := fun a s => ⟨a.1 s, _⟩
  swap
  · have := (NNReal.rpow_le_rpow (norm_eval_le p S s a.val a.2) h0pinv).trans hN
    rw [← NNReal.coe_le_coe, ← NNReal.rpow_mul, ← NNReal.coe_mul, mul_inv_cancel h0p.ne',
      NNReal.coe_one, NNReal.rpow_one, NNReal.coe_nat_cast] at this 
    constructor
    · rw [← neg_le_neg_iff] at this 
      exact_mod_cast this.trans (neg_abs_le_self (a.val s))
    · exact_mod_cast (le_abs_self _).trans this
  have : Function.Injective ι := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    ext s
    apply_fun fun e => (e s).1 at h 
    assumption
  apply Fintype.ofInjective ι this

variable [Fact (0 < p)] [Fact (p ≤ 1)]

instance : ProfinitelyFilteredPseudoNormedGroup (NormedFreePfpng p S) :=
  {
    (inferInstance :
      AddCommGroup
        (NormedFreePfpng p
          S)) with
    filtration := fun c => {f | ‖f‖₊ ≤ c}
    filtration_mono := fun c₁ c₂ h f hf => le_trans hf h
    zero_mem_filtration := fun c => by simp
    neg_mem_filtration := fun c f hf => by simpa
    add_mem_filtration := fun c₁ c₂ f₁ f₂ h₁ h₂ => le_trans (nnnorm_add _ _ _ _) (add_le_add h₁ h₂)
    continuous_add' := fun c₁ c₂ => continuous_of_discreteTopology
    continuous_neg' := fun c => continuous_of_discreteTopology
    continuous_castLe := fun _ _ _ => continuous_of_discreteTopology }

def map {S₁ S₂ : FintypeCat.{u}} (g : S₁ ⟶ S₂) :
    StrictComphausFilteredPseudoNormedGroupHom (NormedFreePfpng p S₁) (NormedFreePfpng p S₂)
    where
  toFun f s := ∑ t in Finset.univ.filterₓ fun w => g w = s, f t
  map_zero' := by simpa
  map_add' f g := by simpa [Finset.sum_add_distrib]
  strict' := by
    have h0p : 0 < p := Fact.out _
    have hp1 : p ≤ 1 := Fact.out _
    intro c f hf
    refine' le_trans _ hf
    simp only [NormedFreePfpng.nnnorm_def]
    have :
      ∑ s₂, ‖∑ t in finset.univ.filter fun w => g w = s₂, f t‖₊ ^ (p : ℝ) ≤
        ∑ s₂ : S₂, ∑ t in finset.univ.filter fun w => g w = s₂, ‖f t‖₊ ^ (p : ℝ) :=
      by
      apply Finset.sum_le_sum
      intro i _
      refine' le_trans _ (NNReal.rpow_sum_le_sum_rpow _ _ h0p hp1)
      refine' NNReal.rpow_le_rpow _ h0p.le
      apply nnnorm_sum_le
    refine' le_trans this _
    rw [← Finset.sum_biUnion]
    apply le_of_eq
    apply Finset.sum_congr
    · rw [Finset.eq_univ_iff_forall]
      intro x
      rw [Finset.mem_biUnion]
      use g x, by simp
    · intro s₁ _; rfl
    · intro x _ y _ h
      rintro a hh
      apply h
      simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and_iff] at hh 
      rw [← hh.1, ← hh.2]
  Continuous' c := continuous_of_discreteTopology

@[simp]
theorem map_id : map p (𝟙 S) = StrictComphausFilteredPseudoNormedGroupHom.id :=
  by
  ext s
  dsimp [map]
  simp [Finset.filter_congr_decidable, Finset.sum_filter]

@[simp]
theorem map_comp {S₁ S₂ S₃ : FintypeCat.{u}} (g₁ : S₁ ⟶ S₂) (g₂ : S₂ ⟶ S₃) :
    map p (g₁ ≫ g₂) = (map p g₂).comp (map p g₁) :=
  by
  ext s₃
  dsimp [map]
  erw [← Finset.sum_biUnion]
  apply Finset.sum_congr
  · ext s
    constructor
    · intro h; simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff] at h 
      rw [Finset.mem_biUnion]
      use g₁ s, by simpa
    · intro h;
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and_iff, exists_prop,
        exists_eq_right'] at h 
      simpa
  · intro s₁ h
    rw [Finset.mem_biUnion] at h 
  · intro x hx y hy
    simp only [Finset.coe_filter, Finset.coe_univ, Set.sep_univ, Set.mem_setOf_eq] at hx hy 
    intro h a ha
    simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and_iff] at ha 
    apply h; rw [← ha.1, ← ha.2]

end NormedFreePfpng

variable [Fact (0 < p)] [Fact (p ≤ 1)]

/-- The functor represented by ℤ, i.e., sending a finite type `S` to
  `normed_free_pfpng p S`, otherwise known as `S → ℤ`,
  equipped with the "p-norm" sending `s ↦ f(s)` to `∑ₛ∥f(s)∥₊ᵖ`. This norm
  makes `S → ℤ` into a `profinitely_filtered_pseudo_normed_group`. -/
@[simps]
def normedFreePfpngFunctor : FintypeCat ⥤ ProFiltPseuNormGrp₁
    where
  obj S :=
    { M := NormedFreePfpng p S
      exhaustive' := fun f => ⟨‖f‖₊, le_refl _⟩ }
  map S₁ S₂ f := NormedFreePfpng.map p f
  map_id' S := NormedFreePfpng.map_id p S
  map_comp' _ _ _ g₁ g₂ := NormedFreePfpng.map_comp p g₁ g₂

def FintypeCat.normedFreePfpng (T : FintypeCat) : ProFiltPseuNormGrp₁ :=
  (normedFreePfpngFunctor p).obj T

def FintypeCat.normedFreePfpngUnit :
    FintypeCat.toProfinite ⟶ normedFreePfpngFunctor p ⋙ ProFiltPseuNormGrp₁.level.obj 1
    where
  app S :=
    { toFun := fun s =>
        { val := fun t => if s = t then 1 else 0
          property := by
            show Finset.sum _ _ ≤ _
            rw [Finset.sum_eq_single_of_mem]
            pick_goal 4; · exact s; swap; · apply Finset.mem_univ
            · dsimp; rw [if_pos rfl, nnnorm_one, NNReal.one_rpow]
            rintro t - ht; dsimp; rw [if_neg ht.symm, nnnorm_zero, NNReal.zero_rpow]
            have h0p : 0 < p := Fact.out _; exact_mod_cast h0p.ne' }
      continuous_toFun := continuous_bot }
  naturality' S T f := by
    ext s t
    delta ProFiltPseuNormGrp₁.level
    simp only [FintypeCat.toProfinite_map_apply, Profinite.coe_comp, ContinuousMap.coe_mk,
      Function.comp_apply, Subtype.coe_mk, CategoryTheory.Functor.comp_map,
      normedFreePfpngFunctor_map, PseudoNormedGroup.level_coe, Subtype.coe_mk, NormedFreePfpng.map,
      Finset.mem_filter, true_and_iff, Finset.mem_univ,
      StrictComphausFilteredPseudoNormedGroupHom.coe_mk, Finset.sum_ite_eq]

def Profinite.normedFreePfpng (S : Profinite) : ProFiltPseuNormGrp₁ :=
  (Profinite.extend <| normedFreePfpngFunctor p).obj S

open CategoryTheory

open CategoryTheory.Limits

def Profinite.normedFreePfpngLevelIso (S : Profinite.{u}) (r) :
    (ProFiltPseuNormGrp₁.level.obj r).obj (S.NormedFreePfpng p) ≅
      Limits.limit
        (S.fintypeDiagram ⋙ normedFreePfpngFunctor p ⋙ ProFiltPseuNormGrp₁.level.obj r) :=
  (isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj r) (limit.isLimit _)).conePointUniqueUpToIso <|
    limit.isLimit _

def Profinite.toNormedFreePfpng (S : Profinite.{u}) :
    S ⟶ (ProFiltPseuNormGrp₁.level.obj 1).obj (S.NormedFreePfpng p) :=
  (limit.isLimit _).map S.asLimitCone (whiskerLeft _ <| FintypeCat.normedFreePfpngUnit.{u, u} p) ≫
    (S.normedFreePfpngLevelIso p 1).inv

--(limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1) (limits.limit.is_limit _)).map
--  S.as_limit_cone $ whisker_left _ (Fintype.normed_free_pfpng_unit) ≫ (functor.associator _ _ _).inv
def Profinite.normedFreePfpngπ (S : Profinite) (T : DiscreteQuotient S) :
    S.NormedFreePfpng p ⟶ (FintypeCat.of T).NormedFreePfpng p :=
  CategoryTheory.Limits.limit.π _ _

theorem Profinite.normedFreePfpngπ_w (S : Profinite) {T₁ T₂ : DiscreteQuotient S} (f : T₁ ⟶ T₂) :
    Profinite.normedFreePfpngπ p S T₁ ≫ (S.fintypeDiagram ⋙ normedFreePfpngFunctor p).map f =
      Profinite.normedFreePfpngπ p S T₂ :=
  CategoryTheory.Limits.limit.w (S.fintypeDiagram ⋙ normedFreePfpngFunctor p) _

