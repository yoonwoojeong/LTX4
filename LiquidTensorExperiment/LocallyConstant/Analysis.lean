import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Analysis.Normed.Group.Hom

#align_import locally_constant.analysis

/-!
# Analysis of locally constant maps

This file defines the normed group of locally constant maps from a compact topological
space into a normed group (with the sup norm).

## Main construction

* The instance `locally_constant.normed_add_comm_group`
* `locally_constant.map_hom`: push-forward of locally constant maps as a normed group hom
* `locally_constant.comap_hom`: pull-back of locally constant maps as a normed group hom
-/


noncomputable section

open scoped NNReal

open Set

-- move this
section ForMathlib

theorem Real.sSup_hMul (r : ℝ) (s : Set ℝ) (hr : 0 < r) :
    sSup {x | ∃ y ∈ s, r * y = x} = r * sSup s :=
  by
  by_cases hs : s.Nonempty; swap
  · rw [not_nonempty_iff_eq_empty] at hs ; simp [hs]
  have H : Set.Nonempty {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), r * y = x} := by obtain ⟨x, hx⟩ := hs;
    exact ⟨r * x, x, hx, rfl⟩
  have aux : BddAbove {x : ℝ | ∃ (y : ℝ) (H : y ∈ s), r * y = x} ↔ BddAbove s :=
    by
    constructor <;> rintro ⟨x, hx⟩
    · refine' ⟨x / r, fun y hy => _⟩
      rw [le_div_iff' hr]
      exact hx ⟨_, hy, rfl⟩
    · refine' ⟨r * x, _⟩; rintro _ ⟨y, hy, rfl⟩
      apply mul_le_mul_of_nonneg_left _ hr.le
      exact hx hy
  by_cases s_bdd : BddAbove s; swap
  ·
    simp only [Real.sSup_of_not_bddAbove s_bdd, MulZeroClass.mul_zero,
      Real.sSup_of_not_bddAbove ((not_congr aux).mpr s_bdd)]
  apply le_antisymm
  · apply csSup_le H
    rintro _ ⟨x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup s_bdd hx) hr.le
  · rw [← le_div_iff' hr]
    refine' csSup_le hs _
    intro x hx
    rw [le_div_iff' hr]
    exact le_csSup (aux.mpr s_bdd) ⟨_, hx, rfl⟩

end ForMathlib

open Set

namespace LocallyConstant

variable {X Y Z V V₁ V₂ V₃ : Type _} [TopologicalSpace X]

/-- The sup norm on locally constant function -/
protected def hasNorm [Norm Y] : Norm (LocallyConstant X Y) where norm f := ⨆ x, ‖f x‖

/-- The sup edist on locally constant function -/
protected def hasEdist [EDist Y] : EDist (LocallyConstant X Y)
    where edist f g := ⨆ x, edist (f x) (g x)

/-- The sup edist on locally constant function -/
protected def hasDist [Dist Y] : Dist (LocallyConstant X Y) where dist f g := ⨆ x, dist (f x) (g x)

attribute [local instance] LocallyConstant.hasNorm LocallyConstant.hasEdist LocallyConstant.hasDist

theorem edist_apply_le [EDist Y] (f g : LocallyConstant X Y) (x : X) :
    edist (f x) (g x) ≤ edist f g :=
  le_sSup (Set.mem_range_self x)

theorem norm_def [Norm Y] (f : LocallyConstant X Y) : ‖f‖ = ⨆ x, ‖f x‖ :=
  rfl

theorem edist_def [EDist Y] (f g : LocallyConstant X Y) : edist f g = ⨆ x, edist (f x) (g x) :=
  rfl

theorem dist_def [Dist Y] (f g : LocallyConstant X Y) : dist f g = ⨆ x, dist (f x) (g x) :=
  rfl

section CompactDomain

variable [CompactSpace X]

theorem norm_apply_le [Norm Y] (f : LocallyConstant X Y) (x : X) : ‖f x‖ ≤ ‖f‖ :=
  by
  refine' le_csSup _ (Set.mem_range_self _)
  apply exists_upper_bound_image
  rw [range_comp]
  exact f.range_finite.image _

theorem exists_ub_range_dist [Dist Y] (f g : LocallyConstant X Y) :
    ∃ x : ℝ, ∀ y : ℝ, (y ∈ Set.range fun x : X => dist (f x) (g x)) → y ≤ x :=
  by
  apply exists_upper_bound_image
  simp only [← Function.uncurry_apply_pair dist]
  rw [range_comp]
  apply finite.image
  apply (f.range_finite.prod g.range_finite).Subset
  apply range_pair_subset

theorem dist_apply_le [Dist Y] (f g : LocallyConstant X Y) (x : X) : dist (f x) (g x) ≤ dist f g :=
  le_csSup (exists_ub_range_dist _ _) (Set.mem_range_self x)

-- consider giving the `edist` and the `uniform_space` explicitly
/-- The metric space on locally constant functions on a compact space, with sup distance. -/
protected def pseudoMetricSpace [PseudoMetricSpace Y] : PseudoMetricSpace (LocallyConstant X Y) :=
  {
    LocallyConstant.hasDist with
    dist_self := fun f =>
      show (⨆ x, dist (f x) (f x)) = 0 by
        simp only [dist_self, iSup]
        cases isEmpty_or_nonempty X
        · rw [Set.range_eq_empty, Real.sSup_empty]
        · simp only [Set.range_const, csSup_singleton]
    dist_comm := fun f g => show sSup _ = sSup _ by simp only [dist_comm]
    dist_triangle := by
      intro f g h
      cases isEmpty_or_nonempty X
      · show Sup _ ≤ Sup _ + Sup _; simp only [Set.range_eq_empty, Real.sSup_empty, add_zero]
      refine' csSup_le _ _
      · inhabit X; exact ⟨_, Set.mem_range_self default⟩
      rintro r ⟨x, rfl⟩
      calc
        dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) := dist_triangle _ _ _
        _ ≤ dist f g + dist g h := add_le_add (dist_apply_le _ _ _) (dist_apply_le _ _ _) }

-- consider giving the `edist` and the `uniform_space` explicitly
/-- The metric space on locally constant functions on a compact space, with sup distance. -/
protected def metricSpace [MetricSpace Y] : MetricSpace (LocallyConstant X Y) :=
  {
    LocallyConstant.hasDist with
    dist_self := fun f =>
      show (⨆ x, dist (f x) (f x)) = 0 by
        simp only [dist_self, iSup]
        cases isEmpty_or_nonempty X
        · rwa [Set.range_eq_empty, Real.sSup_empty]
        · simp only [Set.range_const, csSup_singleton]
    eq_of_dist_eq_zero := by
      intro f g h
      ext x
      apply eq_of_dist_eq_zero
      apply le_antisymm _ dist_nonneg
      rw [← h]
      exact dist_apply_le _ _ _
    dist_comm := fun f g => show sSup _ = sSup _ by simp only [dist_comm]
    dist_triangle := by
      intro f g h
      cases isEmpty_or_nonempty X
      · show Sup _ ≤ Sup _ + Sup _; simp only [Set.range_eq_empty, Real.sSup_empty, add_zero]
      refine' csSup_le _ _
      · inhabit X; exact ⟨_, Set.mem_range_self default⟩
      rintro r ⟨x, rfl⟩
      calc
        dist (f x) (h x) ≤ dist (f x) (g x) + dist (g x) (h x) := dist_triangle _ _ _
        _ ≤ dist f g + dist g h := add_le_add (dist_apply_le _ _ _) (dist_apply_le _ _ _) }

/-- The seminormed group of locally constant functions from a compact space to a seminormed group.
-/
protected def seminormedAddCommGroup {G : Type _} [SeminormedAddCommGroup G] :
    SeminormedAddCommGroup (LocallyConstant X G) :=
  { LocallyConstant.hasNorm, LocallyConstant.addCommGroup, LocallyConstant.pseudoMetricSpace with
    dist_eq := fun f g =>
      show sSup _ = sSup _ by
        simp only [SeminormedAddCommGroup.dist_eq, LocallyConstant.sub_apply] }

/-- The normed group of locally constant functions from a compact space to a normed group. -/
protected def normedAddCommGroup {G : Type _} [NormedAddCommGroup G] :
    NormedAddCommGroup (LocallyConstant X G) :=
  { LocallyConstant.seminormedAddCommGroup, LocallyConstant.metricSpace with }

attribute [local instance] LocallyConstant.seminormedAddCommGroup

section MapHom

variable [SeminormedAddCommGroup V] [SeminormedAddCommGroup V₁] [SeminormedAddCommGroup V₂]
  [SeminormedAddCommGroup V₃]

/-- Push-forward of locally constant maps under a normed group hom, as a normed
group hom between types of locally constant functions. -/
@[simps]
def mapHom (f : NormedAddGroupHom V₁ V₂) :
    NormedAddGroupHom (LocallyConstant X V₁) (LocallyConstant X V₂)
    where
  toFun := LocallyConstant.map f
  map_add' := by intro x y; ext s; apply f.map_add'
  bound' := by
    obtain ⟨C, C_pos, hC⟩ := f.bound
    use C
    rintro (g : LocallyConstant _ _)
    calc
      Sup (Set.range fun x => ‖(f (g x))‖) ≤ Sup (Set.range fun x => C * ‖g x‖) :=
        _
      _ = C * Sup (Set.range fun x => ‖g x‖) := _
    · cases isEmpty_or_nonempty X
      · simp only [Set.range_eq_empty, Real.sSup_empty]
      refine' csSup_le _ _
      · inhabit X; exact ⟨_, Set.mem_range_self default⟩
      rintro _ ⟨x, rfl⟩
      calc
        ‖(f (g x))‖ ≤ C * ‖g x‖ := hC _
        _ ≤ Sup _ := le_csSup _ _
      · apply exists_upper_bound_image
        rw [Set.range_comp, Set.range_comp]
        exact (g.range_finite.image _).image _
      · exact Set.mem_range_self _
    · convert Real.sSup_hMul C _ C_pos using 2
      ext x
      simp only [Set.mem_range, exists_prop, Set.setOf_mem_eq, exists_exists_eq_and]
      simp only [Set.mem_setOf_eq]

@[simp]
theorem mapHom_id : @mapHom X _ _ _ _ _ _ (@NormedAddGroupHom.id V _) = NormedAddGroupHom.id _ := by
  ext; rfl

@[simp]
theorem mapHom_comp (g : NormedAddGroupHom V₂ V₃) (f : NormedAddGroupHom V₁ V₂) :
    (@mapHom X _ _ _ _ _ _ g).comp (mapHom f) = mapHom (g.comp f) := by ext; rfl

end MapHom

section ComapHom

/-!
### comapping as normed_add_group_hom
-/


variable [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace Z] [CompactSpace Z]

variable [SeminormedAddCommGroup V]

/-- Pull-back of locally constant maps under a normed group hom, as a normed
group hom between types of locally constant functions. -/
@[simps]
def comapHom (f : X → Y) (hf : Continuous f) :
    NormedAddGroupHom (LocallyConstant Y V) (LocallyConstant X V) :=
  AddMonoidHom.mkNormedAddGroupHom
    (AddMonoidHom.mk' (LocallyConstant.comap f)
      (by intros; ext; simp only [hf, add_apply, Function.comp_apply, coe_comap]))
    1
    (by
      intro g
      rw [one_mul]
      show Sup _ ≤ Sup _
      simp only [hf, Function.comp_apply, coe_comap, AddMonoidHom.mk'_apply]
      cases isEmpty_or_nonempty X
      · simp only [Set.range_eq_empty, Real.sSup_empty]
        cases isEmpty_or_nonempty Y
        · simp only [Set.range_eq_empty, Real.sSup_empty]
        inhabit Y
        calc
          0 ≤ ‖g default‖ := norm_nonneg _
          _ ≤ _ := _
        apply le_csSup
        · apply exists_upper_bound_image
          rw [Set.range_comp]
          exact g.range_finite.image _
        · exact Set.mem_range_self _
      skip
      refine' csSup_le (range_nonempty _) _
      · rintro _ ⟨x, rfl⟩
        apply le_csSup
        · apply exists_upper_bound_image
          rw [Set.range_comp]
          exact g.range_finite.image _
        · exact Set.mem_range_self _)

@[simp]
theorem comapHom_id : @comapHom X X V _ _ _ _ _ id continuous_id = NormedAddGroupHom.id _ :=
  by
  ext
  simp only [comap_id, comap_hom_apply, id.def, NormedAddGroupHom.id_apply,
    AddMonoidHom.toFun_eq_coe, AddMonoidHom.id_apply]

@[simp]
theorem comapHom_comp (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
    (@comapHom _ _ V _ _ _ _ _ f hf).comp (comapHom g hg) = comapHom (g ∘ f) (hg.comp hf) :=
  by
  ext φ x
  -- `[simps]` is producing bad lemmas... I don't know how to trick it into creating good ones
  -- so we use `show` instead, to get into a defeq shape that is usable
  show (comap_hom f hf) ((comap_hom g hg) φ) x = _
  simp only [hg.comp hf, hf, hg, comap_hom_apply, coe_comap]

theorem comapHom_normNoninc (f : X → Y) (hf : Continuous f) :
    (@comapHom _ _ V _ _ _ _ _ f hf).NormNoninc :=
  NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 <|
    NormedAddGroupHom.mkNormedAddGroupHom_norm_le _ zero_le_one _

end ComapHom

end CompactDomain

end LocallyConstant

#lint

