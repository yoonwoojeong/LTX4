import LiquidTensorExperiment.ForMathlib.Pid
import LiquidTensorExperiment.ForMathlib.Projectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact

#align_import for_mathlib.two_step_resolution

noncomputable section

open ModuleCat CategoryTheory CategoryTheory.Limits

open scoped ZeroObject

theorem Nat.eq_zero_or_exists_eq_add_of_ne_one {i : ℕ} (h : i ≠ 1) : i = 0 ∨ ∃ k : ℕ, i = k + 2 :=
  by
  by_cases hi : i = 0
  exact Or.intro_left _ hi
  simp at h 
  have : 2 ≤ i := Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hi, h⟩
  have := Or.intro_right _ (Nat.exists_eq_add_of_le this)
  simpa [add_comm]

universe u v

variable (R : Type u) [CommRing R] (M : Type max u v) [AddCommGroup M] [Module R M]

@[instance]
theorem ModuleCat.projective_of_of_projective [h : Module.Projective.{u, v} R M] :
    CategoryTheory.Projective (of R M) :=
  IsProjective.iff_projective.1 h

/-- The objects of the two step ""resolution" of a module over a commutative ring. -/
def twoStepResolutionX : ℕ → ModuleCat.{max v u} R
  | 0 => ModuleCat.of R (M →₀ R)
  | 1 => ModuleCat.of R (Finsupp.total M M R id).ker
  | n + 2 => 0

/-- The objects of the two step projective resolution of an Abelian group .-/
def twoStepResolutionAbX (M : Type v) [AddCommGroup M] : ℕ → AddCommGroupCat.{v}
  | 0 => AddCommGroupCat.of (M →₀ ℤ)
  | 1 => AddCommGroupCat.of (Finsupp.total M M ℤ id).ker
  | n + 2 => 0

/-- The boundary maps of the two step "resolution" of a module over a commutative ring. -/
def twoStepResolutionD (i j : ℕ) : twoStepResolutionX R M i ⟶ twoStepResolutionX R M j :=
  match i, j with
  | 1, 0 => ModuleCat.asHom (Submodule.subtype (Finsupp.total M M R id).ker)
  | _, _ => 0

/-- The boundary maps of the two step projective resolution of an Abelian group. -/
def twoStepResolutionAbD (M : Type v) [AddCommGroup M] (i j : ℕ) :
    twoStepResolutionAbX M i ⟶ twoStepResolutionAbX M j :=
  match i, j with
  | 1, 0 => AddCommGroupCat.ofHom (AddSubgroup.subtype (Finsupp.total M M ℤ id).toAddMonoidHom.ker)
  | _, _ => 0

/-- The two step "resolution" of a module over a commutative ring. It is a projective resolution
    if the ring is a principal ideal domain. -/
def twoStepResolution : ChainComplex (ModuleCat.{max v u} R) ℕ
    where
  pt := twoStepResolutionX R M
  d := twoStepResolutionD R M
  shape' := by
    simp
    rintro i j hij
    by_cases h : i = 1 ∧ j = 0
    · rw [h.1, h.2] at hij 
      simp only [eq_self_iff_true, not_true] at hij 
      contradiction
    · push_neg at h 
      by_cases hi : i = 1
      · have hj := h hi
        have hj : ∃ k : ℕ, j = k + 1 :=
          by
          have h : 1 ≤ j := nat.one_le_iff_ne_zero.mpr hj
          have h := Nat.exists_eq_add_of_le h
          simp only [add_comm] at h 
          exact h
        rcases hj with ⟨k, rfl⟩
        rw [hi]
        rfl
      · have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := Nat.eq_zero_or_exists_eq_add_of_ne_one hi
        cases' hi with hi hi
        · rw [hi]; rfl
        · rcases hi with ⟨k, rfl⟩; rfl
  d_comp_d' := by
    intro i j k hij hjk
    by_cases hi : i = 1
    · simp only [hi, ComplexShape.down_Rel, add_left_eq_self] at hij 
      simp only [hij, ComplexShape.down_Rel, Nat.succ_ne_zero] at hjk 
      contradiction
    · have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := Nat.eq_zero_or_exists_eq_add_of_ne_one hi
      cases' hi with hi hi
      · rw [hi]; simp only [twoStepResolutionD, zero_comp]
      · rcases hi with ⟨k, rfl⟩; simp only [twoStepResolutionD, zero_comp]

/-- The two step projective resolution of an abelian group M by the free abelian group M →₀ ℤ over M
    and the kernel of the natural map (M →₀ ℤ) → M. -/
def twoStepResolutionAb (M : Type v) [AddCommGroup M] : ChainComplex AddCommGroupCat.{v} ℕ
    where
  pt := twoStepResolutionAbX M
  d := twoStepResolutionAbD M
  shape' := by
    simp
    rintro i j hij
    by_cases h : i = 1 ∧ j = 0
    · rw [h.1, h.2] at hij 
      simp only [eq_self_iff_true, not_true] at hij 
      contradiction
    · push_neg at h 
      by_cases hi : i = 1
      · have hj := h hi
        have hj : ∃ k : ℕ, j = k + 1 :=
          by
          have h : 1 ≤ j := nat.one_le_iff_ne_zero.mpr hj
          have h := Nat.exists_eq_add_of_le h
          simp only [add_comm] at h 
          exact h
        rcases hj with ⟨k, rfl⟩
        rw [hi]
        rfl
      · have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := Nat.eq_zero_or_exists_eq_add_of_ne_one hi
        cases' hi with hi hi
        · rw [hi]; rfl
        · rcases hi with ⟨k, rfl⟩; rfl
  d_comp_d' := by
    intro i j k hij hjk
    by_cases hi : i = 1
    · simp only [hi, ComplexShape.down_Rel, add_left_eq_self] at hij 
      simp only [hij, ComplexShape.down_Rel, Nat.succ_ne_zero] at hjk 
      contradiction
    · have hi : i = 0 ∨ ∃ k : ℕ, i = k + 2 := Nat.eq_zero_or_exists_eq_add_of_ne_one hi
      cases' hi with hi hi
      · rw [hi]; simp only [twoStepResolutionAbD, zero_comp]
      · rcases hi with ⟨k, rfl⟩; simp only [twoStepResolutionAbD, zero_comp]

/-- The surjective homomorphism from the two step "resolution" of a module over a commutative ring
    to the module. -/
def twoStepResolutionHom :
    twoStepResolution R M ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} R)).obj (of R M) :=
  by
  apply (ChainComplex.toSingle₀Equiv (twoStepResolution R M) (of R M)).invFun
  refine' ⟨Finsupp.total M M R id, _⟩
  ext
  rw [CategoryTheory.comp_apply]
  dsimp only [twoStepResolution]
  simp [twoStepResolutionD, ModuleCat.asHom]

/-- The surjective homomorphism from the two step projective resolution of an Abelian group to the
    group. -/
def twoStepResolutionHomAb (M : Type v) [AddCommGroup M] :
    twoStepResolutionAb M ⟶ (ChainComplex.single₀ AddCommGroupCat.{v}).obj (AddCommGroupCat.of M) :=
  by
  apply (ChainComplex.toSingle₀Equiv (twoStepResolutionAb M) (AddCommGroupCat.of M)).invFun
  refine' ⟨(Finsupp.total M M ℤ id).toAddMonoidHom, _⟩
  ext
  rw [CategoryTheory.comp_apply]
  dsimp only [twoStepResolutionAb]
  simp [twoStepResolutionAbD, AddCommGroupCat.ofHom]

/-- The two step resolution of a module over a principal ideal domain is a projective resolution. -/
theorem twoStepResolutionProjectivePid [IsDomain R] [IsPrincipalIdealRing R] :
    (twoStepResolution R M).IsProjectiveResolution (of R M) (twoStepResolutionHom R M) :=
  by
  refine' ⟨_, _, _, _⟩
  · -- Projectivity.
    intro n
    by_cases hn : n = 0
    simp only [hn, twoStepResolution, twoStepResolutionX]
    infer_instance
    by_cases hn' : n = 1
    simp only [hn']
    dsimp only [twoStepResolution, twoStepResolutionX]
    -- apply_instance,  -- fails because of universe unification issues
    apply ModuleCat.projective_of_of_projective.{u, v}
    have hn : ∃ m : ℕ, n = m + 2 :=
      by
      have := Nat.eq_zero_or_exists_eq_add_of_ne_one hn'
      simp only [hn, false_or_iff] at this 
      exact this
    rcases hn with ⟨m, rfl⟩
    dsimp only [twoStepResolution, twoStepResolutionX]
    infer_instance
  · -- Exactness at degree zero.
    dsimp [twoStepResolution, twoStepResolutionHom, ModuleCat.asHom, ChainComplex.toSingle₀Equiv,
      twoStepResolutionD]
    rw [ModuleCat.exact_iff]
    simp only [Submodule.range_subtype]
  · -- Exactness at positive degrees.
    dsimp only [twoStepResolution, ModuleCat.asHom, autoParam_eq]
    intro n
    by_cases hn : n = 0
    · -- Exactness at degree one.
      rw [hn, zero_add 2, zero_add 1]
      dsimp only [twoStepResolutionD, ModuleCat.asHom]
      have : mono (ModuleCat.asHom (Finsupp.total M M R id).ker.Subtype) :=
        by
        rw [ModuleCat.mono_iff_injective]
        dsimp only [ModuleCat.asHom]
        exact Submodule.injective_subtype (Finsupp.total M M R id).ker
      exact_mod_cast
        CategoryTheory.exact_zero_mono (ModuleCat.asHom (Finsupp.total M M R id).ker.Subtype)
    · -- Exactness at degrees greater than one.
      have hn : ∃ k : ℕ, n = k + 1 :=
        by
        have := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.2 hn)
        simpa only [add_comm]
      rcases hn with ⟨k, rfl⟩
      dsimp only [twoStepResolutionD]
      apply CategoryTheory.exact_of_zero
  · -- Surjectivity.
    dsimp only [twoStepResolutionHom, ChainComplex.toSingle₀Equiv, autoParam_eq]
    have : epi (ModuleCat.asHom (Finsupp.total M M R id))
    rw [ModuleCat.epi_iff_surjective]
    dsimp only [ModuleCat.asHom]
    exact Finsupp.total_surjective R Function.surjective_id
    exact this

-- lemma coe_of' : (of R M : Type (max u v)) = M := rfl
theorem ModuleCat.coe_of'' (M : ModuleCat.{v} R) : of R M = M :=
  by
  cases M
  dsimp [of, coeSort, CoeSort.coe]
  rfl

theorem AddCommGroupCat.coe_of' (M : AddCommGroupCat.{v}) : AddCommGroupCat.of M = M := by
  cases M <;> rfl

theorem AddSubmonoid.injective_subtype {M : Type v} [AddCommMonoid M] (p : AddSubmonoid M) :
    Function.Injective p.Subtype :=
  Subtype.coe_injective

/-- An ℤ-module considered as an Abelian group  is projective if it is projective as a ℤ-module. -/
@[instance]
theorem AddCommGroupCat.projective_of_Z_moduleCat_projective (M : ModuleCat.{v} ℤ) [Projective M] :
    Projective (AddCommGroupCat.of M) := by
  refine' ⟨_⟩
  intros
  let e' :
    (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).obj (ModuleCat.of ℤ E) ⟶
      (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).obj (ModuleCat.of ℤ X) :=
    e
  let eM := full.preimage e'
  let f' :
    (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).obj (ModuleCat.of ℤ M) ⟶
      (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).obj (ModuleCat.of ℤ X) :=
    f
  let fM := full.preimage f'
  have : epi eM :=
    by
    apply functor.epi_of_epi_map (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat.{v}) _
    rw [full.witness]
    apply epi.mk
    intro Z g h H
    let g' : X ⟶ Z := g
    let h' : X ⟶ Z := h
    have H : e ≫ g' = e ≫ h' := H
    --rw cancel_epi at H,    -- "failed to synthesize type class instance for epi e"
    rw [@cancel_epi _ _ _ _ _ _ _inst_2 _ _] at H 
    exact H
  haveI : projective (of ℤ M) := by rw [ModuleCat.coe_of'' ℤ M] <;> infer_instance
  let pM := projective.factor_thru fM eM
  use(forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).map pM
  have hpM := projective.factor_thru_comp fM eM
  have h :
    (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).map (projective.factor_thru fM eM ≫ eM) =
      (forget₂ (ModuleCat.{v} ℤ) AddCommGroupCat).map fM :=
    by simp only [hpM]
  rw [functor.map_comp] at h 
  simp only [full.witness] at h 
  exact h

/-- The two step resolution of an Abelian group is a projective resolution. -/
theorem twoStepResolutionAbProjective (M : Type v) [AddCommGroup M] :
    (twoStepResolutionAb M).IsProjectiveResolution (AddCommGroupCat.of M)
      (twoStepResolutionHomAb M) :=
  by
  refine' ⟨_, _, _, _⟩
  · -- Projectivity.
    intro n
    by_cases hn : n = 0
    simp only [hn, twoStepResolutionAb, twoStepResolutionAbX]
    exact AddCommGroupCat.projective_of_Z_moduleCat_projective (ModuleCat.of.{v} ℤ (M →₀ ℤ))
    -- apply_instance,  -- fails
    by_cases hn' : n = 1
    simp only [hn']
    dsimp only [twoStepResolutionAb, twoStepResolutionAbX]
    exact
      AddCommGroupCat.projective_of_Z_moduleCat_projective
        (ModuleCat.of.{v} ℤ (Finsupp.total M M ℤ id).ker)
    -- apply_instance,  -- fails
    have hn : ∃ m : ℕ, n = m + 2 :=
      by
      have := Nat.eq_zero_or_exists_eq_add_of_ne_one hn'
      simp only [hn, false_or_iff] at this 
      exact this
    rcases hn with ⟨m, rfl⟩
    dsimp only [twoStepResolutionAb, twoStepResolutionAbX]
    infer_instance
  · -- Exactness at degree zero.
    dsimp [twoStepResolutionAb, twoStepResolutionHomAb, AddCommGroupCat.ofHom,
      ChainComplex.toSingle₀Equiv, twoStepResolutionAbD]
    rw [AddCommGroupCat.exact_iff]
    simp only [AddSubgroup.subtype_range]
  · -- Exactness at positive degrees.
    dsimp only [twoStepResolution, ModuleCat.asHom, autoParam_eq]
    intro n
    by_cases hn : n = 0
    · -- Exactness at degree one.
      rw [hn, zero_add 2, zero_add 1]
      dsimp only [twoStepResolutionAb, twoStepResolutionAbD, AddCommGroupCat.ofHom]
      have :
        mono
          (AddCommGroupCat.ofHom
            (AddSubgroup.subtype (Finsupp.total M M ℤ id).toAddMonoidHom.ker)) :=
        by
        rw [AddCommGroupCat.mono_iff_injective]
        dsimp only [AddCommGroupCat.ofHom]
        exact AddSubmonoid.injective_subtype _
      exact_mod_cast
        CategoryTheory.exact_zero_mono
          (AddCommGroupCat.ofHom (AddSubgroup.subtype (Finsupp.total M M ℤ id).toAddMonoidHom.ker))
    · -- Exactness at degrees greater than one.
      have hn : ∃ k : ℕ, n = k + 1 :=
        by
        have := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.2 hn)
        simpa only [add_comm]
      rcases hn with ⟨k, rfl⟩
      dsimp only [twoStepResolutionAb, twoStepResolutionAbD]
      apply CategoryTheory.exact_of_zero
  · -- Surjectivity.
    dsimp only [twoStepResolutionHom, ChainComplex.toSingle₀Equiv, autoParam_eq]
    have : epi (AddCommGroupCat.ofHom (Finsupp.total M M ℤ id).toAddMonoidHom)
    rw [AddCommGroupCat.epi_iff_surjective]
    dsimp only [AddCommGroupCat.ofHom]
    exact Finsupp.total_surjective ℤ Function.surjective_id
    exact this

