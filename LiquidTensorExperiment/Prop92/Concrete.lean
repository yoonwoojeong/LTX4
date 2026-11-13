import LiquidTensorExperiment.PseudoNormedGroup.ProfinitelyFiltered
import LiquidTensorExperiment.Prop92.ExtensionProfinite
import LiquidTensorExperiment.NormedGroup.NormedWithAut
import Mathlib.Analysis.Normed.Group.HomCompletion
import LiquidTensorExperiment.LocallyConstant.Analysis
import Mathlib.Tactic.Ring
import LiquidTensorExperiment.ForMathlib.Nnreal

#align_import prop_92.concrete

/-!
This file builds a concrete version of Proposition 9.2, with almost no category.
The exception is that `SemiNormedGroup` is used because this is expected in
`normed_with_aut` (we could easily get rid of this but this is very mild category theory hell).
There are two independent parts. The first one is all about locally constant maps from
compact spaces to seminormed groups. The next one forgets about locally constant functions
and does abstract normed space stuff.
-/


noncomputable section

section

open Finset

open scoped BigOperators

-- Why can't I find this in mathlib?!?
theorem partial_sum_geom {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (n : ℕ) :
    ∑ k in range n, r ^ k = (1 - r ^ n) / (1 - r) :=
  by
  refine' (eq_div_iff (sub_ne_zero.mpr hr'.ne')).mpr _
  induction' n with n ih
  · simp
  · rw [sum_range_succ, add_mul, ih]
    ring

-- Why can't I find this in mathlib?!?
theorem partial_sum_geom_le {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (n : ℕ) :
    ∑ k in range n, r ^ k ≤ 1 / (1 - r) :=
  by
  rw [partial_sum_geom hr hr']
  exact div_le_div zero_le_one (sub_le_self _ (pow_nonneg hr n)) (sub_pos.mpr hr') rfl.le

theorem norm_sum_le_of_le_geom {α : Type _} [SeminormedAddCommGroup α] {r C : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) {f : ℕ → α} (h : ∀ n, ‖f n‖ ≤ C * r ^ n) {n : ℕ} :
    ‖∑ k in range n, f k‖ ≤ C / (1 - r) := by
  calc
    ‖∑ k in range n, f k‖ ≤ ∑ k in range n, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ k in range n, C * r ^ k := (sum_le_sum fun k hk => h k)
    _ = C * ∑ k in range n, r ^ k := by rw [mul_sum]
    _ ≤ C * (1 / (1 - r)) := (mul_le_mul_of_nonneg_left (partial_sum_geom_le hr₀ hr₁ n) hC)
    _ = C / (1 - r) := mul_one_div C (1 - r)

end

open Set

@[simp]
theorem Real.iSup_zero (ι : Type _) : (⨆ i : ι, (0 : ℝ)) = 0 :=
  by
  rw [iSup]
  cases isEmpty_or_nonempty ι
  · rw [Set.range_eq_empty, Real.sSup_empty]
  · rw [Set.range_const, csSup_singleton]

-- Move me
theorem Real.sSup_eq {s : Set ℝ} (hs : s.Nonempty) (hs' : ∃ x, ∀ y ∈ s, y ≤ x) {x : ℝ} :
    sSup s = x ↔ ∀ y, x ≤ y ↔ ∀ z ∈ s, z ≤ y := by
  classical
  rw [Real.sSup_def]
  rw [dif_pos]
  · let x₀ := Classical.choose (Real.exists_isLUB s hs hs')
    change x₀ = x ↔ _
    have H : ∀ y, x₀ ≤ y ↔ ∀ z ∈ s, z ≤ y := by
      intro y
      exact isLUB_le_iff (Classical.choose_spec (Real.exists_isLUB s hs hs'))
    constructor
    · dsimp [x₀]
      rintro rfl
      exact H
    · intro h
      replace H : ∀ y, x₀ ≤ y ↔ x ≤ y
      · intro y
        rw [h, H]
      apply le_antisymm
      · exact (H _).mpr (le_refl _)
      · exact (H _).mp (le_refl _)
  · exact ⟨hs, hs'⟩

-- Move me
theorem isLUB_iff {α : Type _} [Preorder α] {s : Set α} {x : α} :
    IsLUB s x ↔ ∀ y, x ≤ y ↔ ∀ z ∈ s, z ≤ y :=
  by
  constructor
  · rintro ⟨h₁, h₂⟩ y
    exact ⟨fun hxy z z_in => (h₁ z_in).trans hxy, fun h => h₂ h⟩
  · intro H
    exact ⟨fun y y_in => (H x).mp (le_refl x) y y_in, fun z hz => by rwa [H]⟩

-- Move me
theorem Real.sSup_eq' {s : Set ℝ} (hs : s.Nonempty) (hs' : ∃ x, ∀ y ∈ s, y ≤ x) {x : ℝ} :
    sSup s = x ↔ (∀ y ∈ s, y ≤ x) ∧ ∀ z, (∀ y ∈ s, y ≤ z) → x ≤ z :=
  by
  rw [Real.sSup_eq hs hs']
  change _ ↔ IsLUB _ _
  rw [isLUB_iff]

theorem Real.iSup_comp {α β : Type _} (f : β → α) (g : α → ℝ) :
    (⨆ b, g (f b)) = sSup (g '' range f) :=
  by
  change Sup _ = _
  congr
  ext x
  simp

instance SeminormedAddCommGroup.inhabited (G : Type _) [SeminormedAddCommGroup G] : Inhabited G :=
  ⟨0⟩

section GeneralCompletionStuff

open Filter UniformSpace

open scoped TopologicalSpace

-- Now we want an abstract machine where we can plug the sequence g from the previous section.
variable {M₁ : Type _} [SeminormedAddCommGroup M₁] {M₂ : Type _} [SeminormedAddCommGroup M₂]
  (f : NormedAddGroupHom M₁ M₂)

-- PR very close to the definition of cauchy_seq
theorem CauchySeq.map {β : Type _} [SemilatticeSup β] {α : Type _} [UniformSpace α] {γ : Type _}
    [UniformSpace γ] {u : β → α} {f : α → γ} (hu : CauchySeq u) (hf : UniformContinuous f) :
    CauchySeq (f ∘ u) := by
  change Cauchy _
  rw [← map_map]
  exact Cauchy.map hu hf

-- actually not used here, but should go somewhere
theorem NormedAddGroupHom.coe_range : (f.range : Set M₂) = Set.range f := by
  erw [AddMonoidHom.coe_range]; rfl

open NormedAddCommGroup

theorem bar {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (h :
      ∀ m₂ : M₂,
        ∃ g : ℕ → M₁,
          CauchySeq g ∧ Tendsto (f ∘ g) atTop (𝓝 m₂) ∧ ∀ n, ‖g n‖ ≤ C * ‖m₂‖) :
    ∀ hatm₂ : Completion M₂,
      ∃ m₁, f.Completion m₁ = hatm₂ ∧ ‖m₁‖ ≤ (C + ε) * ‖hatm₂‖ :=
  by
  intro hatm₂
  refine'
    controlled_closure_range_of_complete NormedAddCommGroup.norm_toCompl hC hε _ _
      (NormedAddCommGroup.denseRange_toCompl _)
  intro m₂
  rcases h m₂ with ⟨g, cauchy_g, lim_g, bound_g⟩
  have : CauchySeq (to_compl ∘ g) := cauchy_g.map to_compl.uniform_continuous
  rcases cauchySeq_tendsto_of_complete this with ⟨y, hy⟩
  refine' ⟨y, _, _⟩
  · have lim : tendsto (f.completion.comp to_compl ∘ g) at_top (𝓝 (f.completion y)) :=
      (f.completion.continuous.tendsto _).comp hy
    rw [f.completion_to_compl] at lim 
    have : tendsto ((to_compl ∘ f) ∘ g) at_top (𝓝 (to_compl m₂)) :=
      (to_compl.continuous.tendsto _).comp lim_g
    exact tendsto_nhds_unique limUnder this
  · refine'
      le_of_tendsto' (tendsto_norm.comp hy) (_ : ∀ n, ‖(to_compl (g n))‖ ≤ C * ‖m₂‖)
    intro n
    rw [NormedAddCommGroup.norm_toCompl]
    apply bound_g

end GeneralCompletionStuff

section LocallyConstantStuff

open TopologicalSpace NormedWithAut Set

open scoped NNReal BigOperators

attribute [local instance] LocallyConstant.seminormedAddCommGroup

-- Comment below indicate how this will be applied to Prop 9.2
variable
  -- this will be M_{≤ r'c}^a
  {X : Type _}
  [TopologicalSpace X] [CompactSpace X]
  -- this will be M_{≤ c}^a
  {Y : Type _}
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
  -- This will be inclusion
  {e : X → Y}
  (he : Embedding e)
  -- This is used only for premilinary lemma not need the T action on V
  {G : Type _}
  [SeminormedAddCommGroup G]

@[simp]
theorem LocallyConstant.norm_of_isEmpty [IsEmpty X] (f : LocallyConstant X G) : ‖f‖ = 0 :=
  by rw [LocallyConstant.norm_def, iSup, range_eq_empty, Real.sSup_empty]

@[simp]
theorem Embedding.locallyConstantExtend_of_empty (hX : ¬Nonempty X) (f : LocallyConstant X G) :
    he.locallyConstantExtend f = 0 := by
  ext y; dsimp [Embedding.locallyConstantExtend, Embedding.extend]
  rw [dif_neg]
  · rfl
  · intro h; exact hX h.2

@[simp]
theorem LocallyConstant.map_zero {Z : Type _} (g : G → Z) :
    (0 : LocallyConstant X G).map g = LocallyConstant.const X (g 0) :=
  by
  ext x
  simp only [Function.comp_apply, LocallyConstant.map_apply, LocallyConstant.zero_apply]
  rfl

@[simp]
theorem LocallyConstant.norm_const [h : Nonempty X] (g : G) :
    ‖LocallyConstant.const X g‖ = ‖g‖ := by
  simp only [LocallyConstant.norm_def, LocallyConstant.const, ciSup_const, Function.const_apply,
    LocallyConstant.coe_mk]

@[simp]
theorem LocallyConstant.norm_zero : ‖0 : LocallyConstant X G‖ = 0 := by
  simp only [LocallyConstant.norm_def, norm_zero, Real.iSup_zero, LocallyConstant.zero_apply]

@[simp]
theorem LocallyConstant.norm_const_zero : ‖(LocallyConstant.const X (0 : G))‖ = 0 :=
  LocallyConstant.norm_zero

-- Should go in mathlib topology/algebra/ordered, next to is_compast.exists_Sup_image_eq
theorem Continuous.exists_forall_le_of_compact {X : Type _} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {β : Type _} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {f : X → β} (hf : Continuous f) : ∃ x, sSup (range f) = f x := by
  simpa using compact_univ.exists_Sup_image_eq univ_nonempty hf.continuous_on

theorem LocallyConstant.exists_norm_eq [Nonempty X] (f : LocallyConstant X G) :
    ∃ x, ‖f‖ = ‖f x‖ :=
  (continuous_norm.comp f.Continuous).exists_forall_le_of_compact

theorem LocallyConstant.norm_eq_iff (f : LocallyConstant X G) {x : X} :
    ‖f‖ = ‖f x‖ ↔ ∀ x', ‖f x'‖ ≤ ‖f x‖ :=
  by
  have fin_range : (range fun x : X => ‖f x‖).Finite :=
    by
    rw [range_comp]
    apply finite.image
    exact f.range_finite
  have bound : ∃ b, ∀ y ∈ range fun x : X => ‖f x‖, y ≤ b :=
    exists_upper_bound_image _ _ fin_range
  rw [LocallyConstant.norm_def]
  constructor
  · intro h x'
    rw [← h]
    exact le_csSup bound (mem_range_self _)
  · intro h
    erw [Real.sSup_eq _ bound]
    · intro y
      rw [forall_range_iff]
      constructor
      · intro h' x'
        exact (h x').trans h'
      · exact fun i => i x
    · exact ⟨‖f x‖, mem_range_self _⟩

theorem LocallyConstant.norm_eq_iff' (f : LocallyConstant X G) {x : X} :
    ‖f‖ = ‖f x‖ ↔ ∀ g ∈ range f, ‖g‖ ≤ ‖f x‖ := by
  rw [forall_range_iff, LocallyConstant.norm_eq_iff]

theorem LocallyConstant.norm_comap_le {α : Type _} [TopologicalSpace α] [CompactSpace α]
    (f : LocallyConstant X G) {g : α → X} (h : Continuous g) :
    ‖f.comap g‖ ≤ ‖f‖ :=
  LocallyConstant.comapHom_normNoninc g h f

theorem LocallyConstant.comap_map {W X Y Z : Type _} [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace Y] (f : LocallyConstant X Y) (g : W → X) (h : Y → Z) (hg : Continuous g) :
    (f.comap g).map h = (f.map h).comap g := by ext; simp [hg]

theorem LocallyConstant.map_comp' {W X Y Z : Type _} [TopologicalSpace W] (f : LocallyConstant W X)
    (g : X → Y) (h : Y → Z) : (f.map g).map h = f.map (h ∘ g) :=
  rfl

theorem Embedding.norm_extend (f : LocallyConstant X G) :
    ‖he.locallyConstantExtend f‖ = ‖f‖ :=
  by
  cases isEmpty_or_nonempty X
  · rw [f.norm_of_is_empty]
    dsimp [Embedding.locallyConstantExtend, Embedding.extend]
    have hX : ¬Nonempty X := by rwa [not_nonempty_iff]
    suffices (⨆ y : Y, ‖0 : G‖) = 0 by
      simpa only [hX, dif_neg, not_false_iff, and_false_iff]
    simp only [norm_zero, Real.iSup_zero]
  · change (⨆ y : Y, _) = ⨆ x : X, _
    rw [Real.iSup_comp, Real.iSup_comp, he.range_locally_constant_extend f]

variable (φ : X → Y)
  -- this will be φ is T⁻¹ : M_{≤ r'c}^a → M_{≤ c}^a
  {r : ℝ≥0}
  {V : SemiNormedGroupCat} [NormedWithAut r V]

-- this is indeed V!
theorem LocallyConstant.norm_map_aut (g : LocallyConstant Y V) :
    ‖g.map t.hom‖ = r * ‖g‖ :=
  by
  cases isEmpty_or_nonempty Y
  · simp only [MulZeroClass.mul_zero, LocallyConstant.norm_of_isEmpty]
  · cases' g.exists_norm_eq with y hy
    erw [hy, ← norm_T, LocallyConstant.norm_eq_iff]
    intro y'
    erw [norm_T, norm_T]
    cases' (eq_zero_or_pos : r = 0 ∨ 0 < r) with hr hr
    · simp only [hr, NNReal.coe_zero, MulZeroClass.zero_mul]
    · simp only [hr, ← hy, g.norm_apply_le, mul_le_mul_left, NNReal.coe_pos]

@[simp]
theorem NormedWithAut.t_inv_t_hom : (t.inv : V → V) ∘ t.hom = id :=
  by
  ext
  simp

open LocallyConstant

variable {φ} (hφ : Continuous φ)

noncomputable def Embedding.h (f : LocallyConstant X V) : ℕ → LocallyConstant Y V
  | 0 => mapHom t.hom (he.locallyConstantExtend f)
  | i + 1 => mapHom t.hom (he.locallyConstantExtend <| comapHom φ hφ <| Embedding.h i)

variable (f : LocallyConstant X V)

theorem norm_h (i : ℕ) : ‖he.h hφ f i‖ ≤ r ^ (i + 1) * ‖f‖ :=
  by
  induction' i with i ih <;> dsimp [Embedding.h]
  · rw [LocallyConstant.norm_map_aut, he.norm_extend, zero_add, pow_one]
  · rw [LocallyConstant.norm_map_aut, he.norm_extend, pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left (((he.h hφ f i).norm_comap_le hφ).trans ih) r.coe_nonneg

open Finset

def Embedding.g (f : LocallyConstant X V) (N : ℕ) : LocallyConstant Y V :=
  ∑ i in range (N + 1), he.h hφ f i

/-- T⁻¹ g_N e - g_N φ = f - h_N φ-/
theorem one (hφ : Continuous φ) (N : ℕ) :
    mapHom t.inv (comapHom e he.Continuous (he.g hφ f N)) - comapHom φ hφ (he.g hφ f N) =
      f - comapHom φ hφ (he.h hφ f N) :=
  by
  induction' N with N ih
  · dsimp [Embedding.g]
    simp only [Embedding.h, Finset.sum_singleton, sub_left_inj]
    ext x
    simp [he.continuous, he.locally_constant_extend_extends]
  · set c_φ : NormedAddGroupHom (LocallyConstant Y V) (LocallyConstant X V) := comap_hom φ hφ
    set c_e : NormedAddGroupHom (LocallyConstant Y V) (LocallyConstant X V) :=
      comap_hom e he.continuous
    set m_T : NormedAddGroupHom (LocallyConstant X V) (LocallyConstant X V) := map_hom T.inv
    set G := he.g hφ f
    set H := he.h hφ f
    change m_T _ - _ = _
    rw [sub_eq_iff_eq_add] at ih 
    dsimp [Embedding.g, Embedding.h]
    change m_T (c_e (∑ i in range (N.succ + 1), H i)) - c_φ (∑ i in range (N.succ + 1), H i) = _
    erw [Finset.sum_range_succ, map_add, map_add, map_add, ih]
    change
      f - c_φ (H N) + c_φ (G N) + m_T (c_e (H N.succ)) - (c_φ (G N) + c_φ (H N.succ)) =
        f - comap φ (H N.succ)
    dsimp [H, Embedding.h]
    rw [← (he.locally_constant_extend <| comap φ <| H N).comap_map e T.hom he.continuous,
      he.comap_locally_constant_extend, LocallyConstant.map_comp', NormedWithAut.t_inv_t_hom]
    simp [H]
    abel

open Filter

open scoped TopologicalSpace

variable [Fact ((r : ℝ) < 1)]

theorem limit :
    Tendsto
      (fun N => mapHom t.inv (comapHom e he.Continuous (he.g hφ f N)) - comapHom φ hφ (he.g hφ f N))
      atTop (𝓝 f) :=
  by
  simp_rw [one]
  rw [show 𝓝 f = 𝓝 (f - 0) by simp]
  refine' tendsto_const_nhds.sub _
  apply squeeze_zero_norm
  intro n
  apply ((he.h hφ f n).norm_comap_le hφ).trans (norm_h he hφ _ _)
  rw [← MulZeroClass.zero_mul (‖f‖)]
  apply tendsto.mul_const
  rw [tendsto_add_at_top_iff_nat]
  exact tendsto_pow_atTop_nhds_0_of_lt_1 r.coe_nonneg (Fact.out _)

theorem cauchySeq_g : CauchySeq (he.g hφ f) :=
  by
  apply cauchySeq_of_le_geometric r (r ^ 2 * ‖f‖) (Fact.out _)
  intro n
  dsimp [Embedding.g]
  rw [dist_eq_norm, sum_range_succ _ (n + 1), sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  convert norm_h he hφ f (n + 1) using 1
  ring

theorem norm_g_le (N : ℕ) : ‖he.g hφ f N‖ ≤ r / (1 - r) * ‖f‖ :=
  by
  have : ∀ n : ℕ, ‖he.h hφ f n‖ ≤ r * ‖f‖ * r ^ n :=
    by
    intro n
    convert norm_h he hφ f n using 1
    ring
  convert
    norm_sum_le_of_le_geom (mul_nonneg r.coe_nonneg <| norm_nonneg f) r.coe_nonneg (Fact.out _)
      this using
    1
  exact div_mul_eq_mul_div _ _ _

open UniformSpace

theorem concrete_92 [Fact (0 < r)] (f : Completion (LocallyConstant X V)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Completion (LocallyConstant Y V),
      ((mapHom t.inv).comp (comapHom e he.Continuous) - comapHom φ hφ).Completion g = f ∧
        ‖g‖ ≤ (r / (1 - r) + ε) * ‖f‖ :=
  by
  have : (0 : ℝ) < r / (1 - r) := by
    have : 0 < r := Fact.out _
    apply div_pos
    · exact_mod_cast this
    · exact sub_pos.mpr (Fact.out _)
  apply bar _ this hε
  intro m₂
  exact ⟨he.g hφ m₂, cauchySeq_g he hφ m₂, limit he hφ m₂, norm_g_le he hφ m₂⟩

end LocallyConstantStuff

