import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FreeModule.Basic
import LiquidTensorExperiment.ForMathlib.Nnrat

#align_import for_mathlib.rational_cones

universe u

variable {Λ : Type u} [AddCommGroup Λ]

variable {ι : Type _}

open scoped BigOperators

open scoped NNRat

variable {α : Type _}

def nnratModule {Λ : Type _} [AddCommGroup Λ] [Module ℚ Λ] : Module ℚ≥0 Λ :=
  RestrictScalars.module ℚ≥0 ℚ Λ

attribute [local instance] nnratModule

instance nNRat_tower [Module ℚ Λ] : IsScalarTower ℚ≥0 ℚ Λ
    where smul_assoc x y z := by
    rcases x with ⟨x, hx⟩
    change (x • y) • z = x • _
    simp [mul_smul]

variable [Module ℚ Λ]

open Module

def indexUpOne (l : ι → Λ) : Submodule ℚ≥0 (Dual ℚ Λ)
    where
  carrier := {x | ∀ i, 0 ≤ x (l i)}
  zero_mem' i := le_rfl
  add_mem' x y hx hy i := by simpa only [LinearMap.add_apply] using add_nonneg (hx _) (hy _)
  smul_mem' c x hx i := mul_nonneg c.2 (hx i)

@[simp]
theorem mem_indexUpOne (l : ι → Λ) (x : Dual ℚ Λ) : x ∈ indexUpOne l ↔ ∀ i, 0 ≤ x (l i) :=
  Iff.rfl

def setUpOne (s : Set Λ) : Submodule ℚ≥0 (Dual ℚ Λ) :=
  indexUpOne (coe : s → Λ)

theorem setUpOne_def (s : Set Λ) : setUpOne s = indexUpOne (coe : s → Λ) :=
  rfl

theorem indexUpOne_eq_setUpOne_range (l : ι → Λ) : indexUpOne l = setUpOne (Set.range l) :=
  by
  ext φ
  constructor
  · rintro hφ ⟨_, i, rfl⟩
    apply hφ i
  · rintro hφ i
    apply hφ ⟨_, i, rfl⟩

@[simp]
theorem mem_setUpOne (s : Set Λ) (x : Dual ℚ Λ) : x ∈ setUpOne s ↔ ∀ i ∈ s, 0 ≤ x i :=
  by
  change x ∈ indexUpOne _ ↔ _
  simp

theorem setUpOne_antitone (s t : Set Λ) : s ≤ t → setUpOne t ≤ setUpOne s :=
  by
  rintro h f hf ⟨i, hi⟩
  apply hf ⟨_, h hi⟩

/-- The submodule given by the intersection of the given functionals -/
def indexDownOne (l : ι → Λ →ₗ[ℚ] ℚ) : Submodule ℚ≥0 Λ
    where
  carrier := {x | ∀ i, 0 ≤ l i x}
  zero_mem' i := by simp only [LinearMap.map_zero]
  add_mem' x y hx hy i := by simpa only [LinearMap.map_add] using add_nonneg (hx i) (hy i)
  smul_mem' c x (hx : ∀ i, 0 ≤ l i x) i :=
    by
    rw [LinearMap.map_smul_of_tower]
    apply mul_nonneg c.2 (hx i)

@[simp]
theorem mem_indexDownOne (l : ι → Dual ℚ Λ) (x : Λ) : x ∈ indexDownOne l ↔ ∀ i, 0 ≤ l i x :=
  Iff.rfl

def setDownOne (s : Set (Dual ℚ Λ)) : Submodule ℚ≥0 Λ :=
  indexDownOne (coe : s → Dual ℚ Λ)

theorem setDownOne_def (s : Set (Dual ℚ Λ)) : setDownOne s = indexDownOne (coe : s → Dual ℚ Λ) :=
  rfl

theorem indexDownOne_eq_setDownOne_range (l : ι → Dual ℚ Λ) :
    indexDownOne l = setDownOne (Set.range l) :=
  by
  ext φ
  constructor
  · rintro hφ ⟨_, i, rfl⟩
    apply hφ i
  · rintro hφ i
    apply hφ ⟨_, i, rfl⟩

@[simp]
theorem mem_setDownOne (s : Set (Dual ℚ Λ)) (x : Λ) :
    x ∈ setDownOne s ↔ ∀ i : Dual ℚ Λ, i ∈ s → 0 ≤ i x :=
  by
  change x ∈ indexDownOne _ ↔ _
  simp

theorem setDownOne_antitone (s t : Set (Dual ℚ Λ)) : s ≤ t → setDownOne t ≤ setDownOne s :=
  by
  rintro h f hf ⟨i, hi⟩
  apply hf ⟨_, h hi⟩

theorem setUpOne_span (s : Set Λ) : setUpOne (Submodule.span ℚ≥0 s : Set Λ) = setUpOne s :=
  by
  ext f
  simp only [mem_setUpOne, SetLike.mem_coe]
  constructor
  · intro t y hy
    apply t _ (Submodule.subset_span hy)
  · intro hf y hy
    apply Submodule.span_induction hy hf (by simp)
    · intro l₁ l₂ hl₁ hl₂
      simp only [LinearMap.map_add]
      apply add_nonneg hl₁ hl₂
    · intro q y hy
      simp only [LinearMap.map_smul_of_tower]
      apply mul_nonneg q.2 hy

theorem setDownOne_span (s : Set (Dual ℚ Λ)) :
    setDownOne (Submodule.span ℚ≥0 s : Set (Dual ℚ Λ)) = setDownOne s :=
  by
  ext x
  simp only [mem_setDownOne, SetLike.mem_coe]
  constructor
  · intro t y hy
    apply t _ (Submodule.subset_span hy)
  · intro hx y hy
    apply Submodule.span_induction hy hx (by simp)
    · intro l₁ l₂ hl₁ hl₂
      apply add_nonneg hl₁ hl₂
    · intro q f hf
      simp only [LinearMap.smul_apply]
      apply mul_nonneg q.2 hf

theorem le_up_down (l : Set (Dual ℚ Λ)) : l ≤ setUpOne (setDownOne l : Set Λ) :=
  by
  rintro x hx ⟨i, hi⟩
  apply hi ⟨_, hx⟩

theorem le_down_up (l : Set Λ) : l ≤ setDownOne (setUpOne l : Set (Dual ℚ Λ)) :=
  by
  rintro x hx ⟨i, hi⟩
  apply hi ⟨_, hx⟩

noncomputable def downTwo [FiniteDimensional ℚ Λ] :
    Submodule ℚ≥0 (Dual ℚ (Dual ℚ Λ)) → Submodule ℚ≥0 Λ :=
  Submodule.comap (LinearEquiv.restrictScalars ℚ≥0 (evalEquiv ℚ Λ) : Λ →ₗ[ℚ≥0] Dual ℚ (Dual ℚ Λ))

theorem downTwo_def [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 (Dual ℚ (Dual ℚ Λ))) :
    downTwo C =
      C.comap (LinearEquiv.restrictScalars ℚ≥0 (evalEquiv ℚ Λ) : Λ →ₗ[ℚ≥0] Dual ℚ (Dual ℚ Λ)) :=
  rfl

noncomputable def upTwo [FiniteDimensional ℚ Λ] :
    Submodule ℚ≥0 Λ → Submodule ℚ≥0 (Dual ℚ (Dual ℚ Λ)) :=
  Submodule.map (LinearEquiv.restrictScalars ℚ≥0 (evalEquiv ℚ Λ) : Λ →ₗ[ℚ≥0] Dual ℚ (Dual ℚ Λ))

theorem downTwo_up [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ) : downTwo (upTwo C) = C :=
  by
  dsimp only [upTwo, downTwo]
  rw [LinearEquiv.map_eq_comap]
  rw [← Submodule.comap_comp]
  simp only [LinearEquiv.refl_toLinearMap, LinearEquiv.self_trans_symm, LinearEquiv.comp_coe,
    Submodule.comap_id]

theorem upTwo_down [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 (Dual ℚ (Dual ℚ Λ))) :
    upTwo (downTwo C) = C := by
  dsimp only [upTwo, downTwo]
  rw [LinearEquiv.map_eq_comap]
  rw [← Submodule.comap_comp]
  simp [Submodule.comap_id]

theorem downTwo_indexUpOne [FiniteDimensional ℚ Λ] (l : ι → Dual ℚ Λ) :
    downTwo (indexUpOne l) = indexDownOne l := by
  ext x
  simp only [downTwo, Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    mem_indexUpOne, mem_indexDownOne]
  rfl

theorem downTwo_setUpOne [FiniteDimensional ℚ Λ] (l : Set (Dual ℚ Λ)) :
    downTwo (setUpOne l) = setDownOne l :=
  downTwo_indexUpOne _

theorem upTwo_indexDownOne [FiniteDimensional ℚ Λ] (l : ι → Dual ℚ Λ) :
    upTwo (indexDownOne l) = indexUpOne l :=
  by
  rw [← downTwo_indexUpOne]
  simp only [upTwo_down]

theorem upTwo_setDownOne [FiniteDimensional ℚ Λ] (l : Set (Dual ℚ Λ)) :
    upTwo (setDownOne l) = setUpOne l :=
  upTwo_indexDownOne _

theorem down_up_down_eq (l : Set (Dual ℚ Λ)) :
    setDownOne (setUpOne (setDownOne l : Set Λ) : Set (Dual ℚ Λ)) = setDownOne l :=
  by
  apply le_antisymm
  · apply setDownOne_antitone
    apply le_up_down
  · apply le_down_up

theorem up_down_up_eq (l : Set Λ) :
    setUpOne (setDownOne (setUpOne l : Set (Dual ℚ Λ)) : Set Λ) = setUpOne l :=
  by
  apply le_antisymm
  · apply setUpOne_antitone
    apply le_down_up
  · apply le_up_down

theorem downTwo_up_one_up_one [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ)
    (hC : ∃ l : Set (Dual ℚ Λ), C = setDownOne l) :
    downTwo (setUpOne (setUpOne (C : Set Λ) : Set (Dual ℚ Λ))) = C :=
  by
  rw [downTwo_setUpOne]
  rcases hC with ⟨l, rfl⟩
  rw [down_up_down_eq]

theorem down_eval_eq [FiniteDimensional ℚ Λ] (C : Set Λ) :
    setDownOne (evalEquiv ℚ Λ '' C) = setUpOne C :=
  by
  ext x
  simp only [and_imp, Set.mem_image, mem_setDownOne, mem_setUpOne, forall_apply_eq_imp_iff₂,
    exists_imp]
  rfl

theorem down_one_upTwo [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ) :
    setDownOne (upTwo C : Set (Dual ℚ (Dual ℚ Λ))) = setUpOne C :=
  down_eval_eq _

theorem up_one_downTwo [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 (Dual ℚ (Dual ℚ Λ))) :
    setUpOne (downTwo C : Set Λ) = setDownOne C :=
  by
  simp only [← down_one_upTwo]
  simp only [upTwo_down]

theorem up_one_down_one [FiniteDimensional ℚ Λ] (C : Set (Dual ℚ Λ)) :
    setUpOne (setDownOne C : Set Λ) = setDownOne (setUpOne C) :=
  by
  rw [← downTwo_setUpOne]
  simp only [up_one_downTwo]

/-- A submodule is polyhedral if it is the intersection of finitely many half spaces. -/
def IsPolyhedralCone (C : Submodule ℚ≥0 Λ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (l : ι → Λ →ₗ[ℚ] ℚ), C = indexDownOne l

theorem isPolyhedralCone_iff_finset (C : Submodule ℚ≥0 Λ) :
    IsPolyhedralCone C ↔ ∃ s : Finset (Dual ℚ Λ), C = setDownOne s := by
  classical
  constructor
  · rintro ⟨ι, hι, l, rfl⟩
    skip
    refine' ⟨finset.univ.image l, _⟩
    rw [indexDownOne_eq_setDownOne_range l]
    simp
  · rintro ⟨s, rfl⟩
    exact ⟨(s : Set (dual ℚ Λ)), inferInstance, _, setDownOne_def _⟩

theorem downTwo_up_one_up_one_cone [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ)
    (hC : IsPolyhedralCone C) : downTwo (setUpOne (setUpOne (C : Set Λ) : Set (Dual ℚ Λ))) = C :=
  by
  apply downTwo_up_one_up_one
  rw [isPolyhedralCone_iff_finset] at hC 
  rcases hC with ⟨_, rfl⟩
  refine' ⟨_, rfl⟩

theorem isPolyhedralCone_of_equiv {Λ' : Type u} [AddCommGroup Λ'] [Module ℚ Λ'] (e : Λ ≃ₗ[ℚ] Λ')
    (C : Submodule ℚ≥0 Λ) (hC : IsPolyhedralCone C) :
    IsPolyhedralCone (Submodule.map (e.toLinearMap.restrictScalars ℚ≥0) C) :=
  by
  rcases hC with ⟨ι, hι, l, rfl⟩
  refine' ⟨ι, hι, fun i => _, _⟩
  apply (l i).comp e.symm.to_linear_map
  ext x
  simp only [Submodule.mem_map, Function.comp_apply, LinearMap.coe_comp, mem_indexDownOne,
    LinearEquiv.coe_toLinearMap, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa
  · intro t
    refine' ⟨e.symm x, t, by simp⟩

theorem isPolyhedralCone_bot_aux [Fintype α] : IsPolyhedralCone (⊥ : Submodule ℚ≥0 (α → ℚ)) :=
  ⟨Sum α α, Sum.fintype α α,
    Sum.elim (fun i => ⟨fun f => f i, fun x y => rfl, fun _ _ => rfl⟩) fun i =>
      -⟨fun f => f i, fun x y => rfl, fun _ _ => rfl⟩,
    by
    ext
    simp only [LinearMap.coe_proj, Sum.elim_inl, Function.eval_apply, LinearMap.neg_apply,
      Sum.elim_inr, mem_indexDownOne, Sum.forall, Submodule.mem_bot, neg_nonneg]
    constructor
    · rintro rfl
      simp only [LinearMap.map_zero, and_self_iff]
      intro a
      apply le_rfl
    · rintro ⟨h₁, h₂⟩
      ext1 i
      apply le_antisymm
      · apply h₂ i
      · apply h₁ i⟩

theorem isPolyhedralCone_bot [FiniteDimensional ℚ Λ] : IsPolyhedralCone (⊥ : Submodule ℚ≥0 Λ) :=
  by
  let l := (Basis.ofVectorSpace ℚ Λ).equivFun
  have := isPolyhedralCone_of_equiv l.symm ⊥ isPolyhedralCone_bot_aux
  simpa using this

theorem coe_min' (s : Finset ℚ≥0) (hs : s.Nonempty) :
    (coe (s.min' hs) : ℚ) = (s.image coe).min' (hs.image _) :=
  by
  induction' s using Finset.induction_on with x s hx ih t generalizing hs
  · revert hs; simp only [Finset.not_nonempty_empty, IsEmpty.forall_iff]
  · rcases Finset.eq_empty_or_nonempty s with (rfl | hs')
    · simp only [insert_emptyc_eq, Finset.min'_singleton, Finset.image_singleton]
    have aux := Finset.min'_insert x s hs'
    apply_fun (coe : ℚ≥0 → ℚ) at aux 
    convert aux using 1; · congr
    simp only [Finset.image_insert, ih hs', NNRat.coe_min]
    simp only [← Finset.min'_insert]

def ExtendedHalfSpacesIndex {ι : Type _} (s : ι → Λ →ₗ[ℚ] ℚ) (x : Λ) : Type _ :=
  Sum { i : ι // 0 ≤ s i x } ({ i : ι // 0 < s i x } × { i : ι // s i x < 0 })

instance {ι : Type _} [Fintype ι] (s : ι → Λ →ₗ[ℚ] ℚ) (x : Λ) :
    Fintype (ExtendedHalfSpacesIndex s x) :=
  by
  rw [ExtendedHalfSpacesIndex]
  infer_instance

def extendedHalfSpaces {ι : Type _} (s : ι → Λ →ₗ[ℚ] ℚ) (x : Λ) :
    ExtendedHalfSpacesIndex s x → Λ →ₗ[ℚ] ℚ :=
  Sum.elim (s ∘ coe) fun ij => s ij.1 x • s ij.2 - s ij.2 x • s ij.1

theorem span_le_extended [DecidableEq Λ] {ι : Type _} {s : ι → Λ →ₗ[ℚ] ℚ} {l : Finset Λ}
    (hs : Submodule.span ℚ≥0 (l : Set Λ) = indexDownOne s) {x : Λ} (hx : x ∉ l) :
    Submodule.span ℚ≥0 ↑(insert x l) ≤ indexDownOne (extendedHalfSpaces s x) :=
  by
  rw [Submodule.span_le]
  intro f hf
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hf 
  simp only [SetLike.mem_coe, mem_indexDownOne, extendedHalfSpaces]
  rcases hf with (rfl | hf)
  · rintro (⟨i, hi⟩ | ⟨⟨i, hi⟩, j, hj⟩)
    · simpa
    · simp [mul_comm]
  · have f_mem : f ∈ indexDownOne s := by
      rw [← hs]
      exact Submodule.subset_span hf
    rintro (⟨i, hi⟩ | ⟨⟨i, hi⟩, j, hj⟩)
    · simpa using f_mem i
    · have : 0 ≤ s i f := by apply f_mem
      have : 0 ≤ s j f := by apply f_mem
      simp only [Algebra.id.smul_eq_mul, sub_nonneg, LinearMap.smul_apply, Sum.elim_inr,
        Subtype.coe_mk, LinearMap.sub_apply]
      nlinarith

theorem extended_le_span [DecidableEq Λ] {ι : Type _} [Fintype ι] {s : ι → Λ →ₗ[ℚ] ℚ} {l : Finset Λ}
    (hs : Submodule.span ℚ≥0 (l : Set Λ) = indexDownOne s) {x : Λ} (hx : x ∉ l) :
    indexDownOne (extendedHalfSpaces s x) ≤ Submodule.span ℚ≥0 ↑(insert x l) :=
  by
  intro y hy
  simp only [Finset.coe_insert, Submodule.mem_span_insert, exists_prop, hs]
  suffices ∃ t : ℚ≥0, y - t • x ∈ indexDownOne s
    by
    rcases this with ⟨a, ha⟩
    refine' ⟨a, _, ha, by simp⟩
  simp only [mem_indexDownOne] at hy 
  have y_nonneg : ∀ i, 0 ≤ s i x → 0 ≤ s i y :=
    by
    intro i hi
    apply hy (Sum.inl ⟨i, hi⟩)
  have y_neg : ∀ i j, 0 < s i x → s j x < 0 → s j x * s i y ≤ s i x * s j y :=
    by
    intro i j hi hj
    simpa [extendedHalfSpaces] using hy (Sum.inr ⟨⟨i, hi⟩, ⟨j, hj⟩⟩)
  let a : { i // 0 < s i x } → ℚ≥0 := fun i => ⟨s i.1 y, y_nonneg _ i.2.le⟩ / ⟨s i.1 x, i.2.le⟩
  let as : Finset ℚ≥0 := finset.univ.image a
  let b : { i // s i x < 0 } → ℚ := fun i => s i.1 y / s i.1 x
  let bs : Finset ℚ := finset.univ.image b
  by_cases h : Nonempty { i // 0 < s i x }
  · have : as.nonempty := by rwa [Finset.Nonempty.image_iff, Finset.univ_nonempty_iff]
    refine' ⟨as.min' ‹as.nonempty›, _⟩
    rw [mem_indexDownOne]
    intro i
    rw [LinearMap.map_sub, sub_nonneg]
    simp only [LinearMap.map_smul_of_tower, Subtype.val_eq_coe]
    change coe (_ : ℚ≥0) * s i x ≤ s i y
    rcases lt_trichotomy 0 (s i x) with (lt | eq | gt)
    · rw [coe_min', ← le_div_iff lt]
      apply Finset.min'_le
      simp only [Finset.mem_univ, Finset.mem_image, exists_prop]
      refine' ⟨_, ⟨⟨i, lt⟩, ⟨⟩, rfl⟩, _⟩
      simp
    · rw [← Eq, MulZeroClass.mul_zero]
      apply y_nonneg _ Eq.le
    · rw [coe_min', ← div_le_iff_of_neg GT.gt]
      apply Finset.le_min'
      simp only [and_imp, exists_prop, Finset.mem_univ, bex_imp, Finset.mem_image, exists_true_left,
        Subtype.exists, exists_imp]
      rintro _ _ j hj ⟨⟨⟩, rfl⟩ rfl
      simp only [NNRat.coe_div, Subtype.coe_mk]
      have := y_neg _ _ hj GT.gt
      rwa [div_le_iff_of_neg GT.gt, div_mul_eq_mul_div, mul_comm (s j y), div_le_iff' hj]
  by_cases h' : Nonempty { i // s i x < 0 }
  · have : bs.nonempty := by rwa [Finset.Nonempty.image_iff, Finset.univ_nonempty_iff]
    refine' ⟨(bs.max' ‹bs.nonempty›).toNNRat, fun i => _⟩
    rw [LinearMap.map_sub, sub_nonneg]
    simp only [LinearMap.map_smul_of_tower, Subtype.val_eq_coe]
    rcases lt_trichotomy 0 (s i x) with (lt | eq | gt)
    · exfalso
      apply h
      refine' ⟨⟨_, lt⟩⟩
    · rw [← Eq, smul_zero]
      apply y_nonneg
      apply Eq.le
    change max _ _ * _ ≤ _
    rw [← div_le_iff_of_neg GT.gt]
    rw [le_max_iff]
    left
    apply Finset.le_max'
    simp only [Finset.mem_univ, Finset.mem_image, exists_true_left, Subtype.exists]
    refine' ⟨i, GT.gt, rfl⟩
  refine' ⟨0, _⟩
  intro i
  rw [LinearMap.map_sub, sub_nonneg, zero_smul, LinearMap.map_zero]
  simp only [LinearMap.map_smul_of_tower, Subtype.val_eq_coe]
  rcases le_or_lt 0 (s i x) with (lt | lt)
  · apply y_nonneg _ lt
  · exfalso
    apply h'
    refine' ⟨⟨_, lt⟩⟩

theorem eliminate_inductive_step [DecidableEq Λ] (ι : Type u) [Fintype ι] (s : ι → Λ →ₗ[ℚ] ℚ)
    {l : Finset Λ} (hs : Submodule.span ℚ≥0 (l : Set Λ) = indexDownOne s) (x : Λ) (hx : x ∉ l) :
    IsPolyhedralCone (Submodule.span ℚ≥0 (coe (insert x l) : Set Λ)) :=
  by
  refine' ⟨ExtendedHalfSpacesIndex s x, inferInstance, extendedHalfSpaces _ _, _⟩
  apply le_antisymm
  apply span_le_extended hs hx
  apply extended_le_span hs hx

theorem elimination_aux [FiniteDimensional ℚ Λ] (l : Finset Λ) :
    IsPolyhedralCone (Submodule.span ℚ≥0 (l : Set Λ)) := by
  classical
  apply Finset.induction_on l
  · simp only [Finset.coe_empty, Submodule.span_empty]
    apply isPolyhedralCone_bot
  · clear l
    rintro x l hx ⟨ι, hι, s, hs⟩
    skip
    convert eliminate_inductive_step ι s hs x hx

theorem isPolyhedralCone_of_fG [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ) (hC : C.FG) :
    IsPolyhedralCone C := by
  rcases hC with ⟨l, rfl⟩
  apply elimination_aux

theorem one_sixteen_c [FiniteDimensional ℚ Λ] (ι : Type u) [Fintype ι] (l : ι → Λ →ₗ[ℚ] ℚ) :
    setUpOne (indexDownOne l : Set Λ) = Submodule.span ℚ≥0 (Set.range l) :=
  by
  set C : Submodule ℚ≥0 Λ := indexDownOne l
  set C_star := setUpOne (C : Set Λ)
  set C' : Submodule _ (dual ℚ Λ) := Submodule.span ℚ≥0 (Set.range l)
  let C'_star := downTwo (setUpOne (C' : Set (dual ℚ Λ)))
  have C_eq : C = C'_star :=
    by
    change C = downTwo (setUpOne (C' : Set (dual ℚ Λ)))
    rw [downTwo_setUpOne]
    rw [setDownOne_span]
    apply indexDownOne_eq_setDownOne_range
  have C'pc : IsPolyhedralCone C' :=
    by
    apply isPolyhedralCone_of_fG
    classical
    refine' ⟨finset.univ.image l, _⟩
    simp
  change setUpOne (C : Set Λ) = _
  rw [C_eq]
  change setUpOne (downTwo (setUpOne (C' : Set (dual ℚ Λ))) : Set Λ) = _
  rw [downTwo_setUpOne]
  rw [isPolyhedralCone_iff_finset] at C'pc 
  clear_value C'; clear C C_star C'_star C_eq l
  rcases C'pc with ⟨s, rfl⟩
  simp_rw [up_one_down_one (setDownOne (s : Set (dual ℚ (dual ℚ Λ))) : Set (dual ℚ Λ))]
  rw [down_up_down_eq]

theorem dual_fG_of_cone [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ) (hC : IsPolyhedralCone C) :
    (setUpOne (C : Set Λ) : Submodule ℚ≥0 (Dual ℚ Λ)).FG :=
  by
  rcases hC with ⟨ι, hι, l, rfl⟩
  skip
  simp only [one_sixteen_c]
  classical refine' ⟨finset.univ.image l, by simp⟩

theorem fG_of_isPolyhedralCone [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ)
    (hC : IsPolyhedralCone C) : C.FG :=
  by
  have t := dual_fG_of_cone _ (isPolyhedralCone_of_fG _ (dual_fG_of_cone _ hC))
  have t2 :
    (Submodule.map (((eval_equiv ℚ Λ).restrictScalars ℚ≥0).symm : dual ℚ (dual ℚ Λ) →ₗ[ℚ≥0] Λ)
        _).FG :=
    by refine' Submodule.FG.map _ t
  rwa [LinearEquiv.map_eq_comap, LinearEquiv.symm_symm, ← downTwo_def,
    downTwo_up_one_up_one_cone _ hC] at t2 

theorem fG_iff_isPolyhedralCone [FiniteDimensional ℚ Λ] (C : Submodule ℚ≥0 Λ) :
    IsPolyhedralCone C ↔ C.FG :=
  ⟨fG_of_isPolyhedralCone C, isPolyhedralCone_of_fG C⟩

