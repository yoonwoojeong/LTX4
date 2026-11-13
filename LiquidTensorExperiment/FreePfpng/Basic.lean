import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
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
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.Condensed.Ab

#align_import free_pfpng.basic

open scoped BigOperators

universe u

variable (S : FintypeCat.{u})

def FreePfpng :=
  S → ℤ
deriving AddCommGroup

noncomputable section

open scoped Classical

instance : NNNorm (FreePfpng S) :=
  ⟨fun f => ∑ s, ‖f s‖₊⟩

namespace FreePfpng

@[simp]
theorem nnnorm_zero : ‖0 : FreePfpng S‖₊ = 0 := by change ∑ _, _ = _; simp

@[simp]
theorem nnnorm_neg (f : FreePfpng S) : ‖-f‖₊ = ‖f‖₊ := by change ∑ _, _ = _; simpa

theorem nnnorm_add (f₁ f₂ : FreePfpng S) : ‖f₁ + f₂‖₊ ≤ ‖f₁‖₊ + ‖f₂‖₊ :=
  by
  change ∑ _, _ ≤ ∑ _, _ + ∑ _, _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  apply nnnorm_add_le

instance (c) : TopologicalSpace {f : FreePfpng S | ‖f‖₊ ≤ c} :=
  ⊥

instance (c) : DiscreteTopology {f : FreePfpng S | ‖f‖₊ ≤ c} :=
  ⟨rfl⟩

theorem norm_eval_le {c : NNReal} {s : S} (f : FreePfpng S) (hf : ‖f‖₊ ≤ c) :
    ‖f s‖₊ ≤ c :=
  le_trans
    (by
      apply @Finset.single_le_sum S NNReal _ (fun t => ‖f t‖₊) Finset.univ
      · intro _ _; apply zero_le
      · exact Finset.mem_univ s)
    hf

instance (c) : Fintype {f : FreePfpng S | ‖f‖₊ ≤ c} :=
  by
  let A := {f : FreePfpng S | ‖f‖₊ ≤ c}
  have h : ∃ N : ℕ, c ≤ N := ⟨Nat.ceil c, Nat.le_ceil c⟩
  let N := h.some; let hN : c ≤ N := h.some_spec
  let ι : A → S → Set.Icc (-(N : ℤ)) N := fun a s => ⟨a.1 s, _, _⟩
  rotate_left
  · -- I'm sure there is a more efficient way to do this...
    have : -‖a.val s‖ ≤ a.val s := neg_abs_le_self ↑(a.val s)
    replace this : -(c : ℝ) ≤ a.val s := le_trans _ this
    swap
    · simp only [Subtype.val_eq_coe, neg_le_neg_iff]
      exact_mod_cast norm_eval_le S a.val a.2
    replace this : -(N : ℝ) ≤ _ := le_trans _ this
    swap
    · rw [neg_le_neg_iff]; exact_mod_cast hN
    exact_mod_cast this
  · have : ↑(a.val s) ≤ ‖a.val s‖ := le_max_left _ _
    replace this : ↑(a.val s) ≤ (c : ℝ) := le_trans this _
    swap; · exact_mod_cast norm_eval_le S a.val a.2
    replace this := le_trans this hN
    push_cast at this 
    exact_mod_cast this
  have : Function.Injective ι := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    ext s
    apply_fun fun e => (e s).1 at h 
    assumption
  apply Fintype.ofInjective ι this

instance : ProfinitelyFilteredPseudoNormedGroup (FreePfpng S) :=
  {
    (inferInstance :
      AddCommGroup
        (FreePfpng S)) with
    filtration := fun c => {f | ‖f‖₊ ≤ c}
    filtration_mono := fun c₁ c₂ h f hf => le_trans hf h
    zero_mem_filtration := fun c => by simp
    neg_mem_filtration := fun c f hf => by simpa
    add_mem_filtration := fun c₁ c₂ f₁ f₂ h₁ h₂ => le_trans (nnnorm_add _ _ _) (add_le_add h₁ h₂)
    continuous_add' := fun c₁ c₂ => continuous_of_discreteTopology
    continuous_neg' := fun c => continuous_of_discreteTopology
    continuous_castLe := fun _ _ _ => continuous_of_discreteTopology }

def map {S₁ S₂ : FintypeCat.{u}} (g : S₁ ⟶ S₂) :
    StrictComphausFilteredPseudoNormedGroupHom (FreePfpng S₁) (FreePfpng S₂)
    where
  toFun f s := ∑ t in Finset.univ.filterₓ fun w => g w = s, f t
  map_zero' := by simpa
  map_add' f g := by simpa [Finset.sum_add_distrib]
  strict' := by
    intro c f hf
    refine' le_trans _ hf
    change ∑ s₂, ‖∑ t in finset.univ.filter fun w => g w = s₂, f t‖₊ ≤ ∑ s₁, _
    have :
      ∑ s₂, ‖∑ t in finset.univ.filter fun w => g w = s₂, f t‖₊ ≤
        ∑ s₂ : S₂, ∑ t in finset.univ.filter fun w => g w = s₂, ‖f t‖₊ :=
      by
      apply Finset.sum_le_sum
      intro i _
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
  continuous' c := continuous_of_discreteTopology

@[simp]
theorem map_id : map (𝟙 S) = StrictComphausFilteredPseudoNormedGroupHom.id :=
  by
  ext s
  dsimp [map]
  simp [Finset.filter_congr_decidable, Finset.sum_filter]

@[simp]
theorem map_comp {S₁ S₂ S₃ : FintypeCat.{u}} (g₁ : S₁ ⟶ S₂) (g₂ : S₂ ⟶ S₃) :
    map (g₁ ≫ g₂) = (map g₂).comp (map g₁) := by
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

end FreePfpng

@[simps]
def freePfpngFunctor : FintypeCat ⥤ ProFiltPseuNormGrp₁
    where
  obj S :=
    { M := FreePfpng S
      exhaustive' := fun f => ⟨‖f‖₊, le_refl _⟩ }
  map S₁ S₂ f := FreePfpng.map f
  map_id' := FreePfpng.map_id
  map_comp' _ _ _ g₁ g₂ := FreePfpng.map_comp g₁ g₂

def FintypeCat.freePfpng (T : FintypeCat) : ProFiltPseuNormGrp₁ :=
  freePfpngFunctor.obj T

def FintypeCat.freePfpngUnit :
    FintypeCat.toProfinite ⟶ freePfpngFunctor ⋙ ProFiltPseuNormGrp₁.level.obj 1
    where
  app S :=
    { toFun := fun s =>
        { val := fun t => if s = t then 1 else 0
          property := by
            show Finset.sum _ _ ≤ _
            rw [Finset.sum_eq_single_of_mem]
            pick_goal 4; · exact s; swap; · apply Finset.mem_univ
            · dsimp; rw [if_pos rfl, nnnorm_one]
            rintro t - ht; dsimp; rw [if_neg ht.symm, nnnorm_zero] }
      continuous_toFun := continuous_bot }
  naturality' S T f := by
    ext s t
    delta ProFiltPseuNormGrp₁.level
    simp only [FintypeCat.toProfinite_map_apply, Profinite.coe_comp, ContinuousMap.coe_mk,
      Function.comp_apply, Subtype.coe_mk, CategoryTheory.Functor.comp_map, freePfpngFunctor_map,
      PseudoNormedGroup.level_coe, Subtype.coe_mk, FreePfpng.map, Finset.mem_filter, true_and_iff,
      Finset.mem_univ, StrictComphausFilteredPseudoNormedGroupHom.coe_mk, Finset.sum_ite_eq]

def Profinite.freePfpng (S : Profinite) : ProFiltPseuNormGrp₁ :=
  (Profinite.extend freePfpngFunctor).obj S

open CategoryTheory

open CategoryTheory.Limits

def Profinite.freePfpngLevelIso (S : Profinite.{u}) (r) :
    (ProFiltPseuNormGrp₁.level.obj r).obj S.FreePfpng ≅
      Limits.limit (S.fintypeDiagram ⋙ freePfpngFunctor ⋙ ProFiltPseuNormGrp₁.level.obj r) :=
  (isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj r) (limit.isLimit _)).conePointUniqueUpToIso <|
    limit.isLimit _

def Profinite.toFreePfpng (S : Profinite.{u}) :
    S ⟶ (ProFiltPseuNormGrp₁.level.obj 1).obj S.FreePfpng :=
  (limit.isLimit _).map S.asLimitCone (whiskerLeft _ <| FintypeCat.freePfpngUnit.{u, u}) ≫
    (S.freePfpngLevelIso 1).inv

--(limits.is_limit_of_preserves (ProFiltPseuNormGrp₁.level.obj 1) (limits.limit.is_limit _)).map
--  S.as_limit_cone $ whisker_left _ (Fintype.free_pfpng_unit) ≫ (functor.associator _ _ _).inv
def Profinite.freePfpngπ (S : Profinite) (T : DiscreteQuotient S) :
    S.FreePfpng ⟶ (FintypeCat.of T).FreePfpng :=
  CategoryTheory.Limits.limit.π _ _

theorem Profinite.freePfpngπ_w (S : Profinite) {T₁ T₂ : DiscreteQuotient S} (f : T₁ ⟶ T₂) :
    Profinite.freePfpngπ S T₁ ≫ (S.fintypeDiagram ⋙ freePfpngFunctor).map f =
      Profinite.freePfpngπ S T₂ :=
  CategoryTheory.Limits.limit.w (S.fintypeDiagram ⋙ freePfpngFunctor) _

