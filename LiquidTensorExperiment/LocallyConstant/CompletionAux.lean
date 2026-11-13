/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Topology.ContinuousFunction.LocallyConstant

#align_import locally_constant.completion_aux

/-!
# p-adic measure theory

This file defines p-adic distributions and measure on the space of locally constant functions
from a profinite space to a normed ring. We then use the measure to construct the p-adic integral.
In fact, we prove that this integral is linearly and continuously extended on `C(X, A`.

## Main definitions and theorems
 * `exists_finset_clopen`
 * `measures`
 * `integral`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12)

## Tags
p-adic L-function, p-adic integral, measure, totally disconnected, locally constant, compact,
Hausdorff


###############
Note (jmc): this file was copied with permission of Ashvni Narayan from
https://github.com/leanprover-community/mathlib/blob/f2fd1fb4507431cf2f2a873db4b97d360633fb69/src/number_theory/L_functions.lean#L453
and subsequently mildly modified.
###############


-/


variable (X : Type _) [TopologicalSpace X]

variable (A : Type _) [NormedAddCommGroup A]

variable {X}

variable [CompactSpace X]

namespace Set

theorem diff_inter_eq_empty {α : Type _} (a : Set α) {b c : Set α} (h : c ⊆ b) : a \ b ∩ c = ∅ :=
  by
  ext x
  simp only [and_imp, not_and, mem_diff, iff_false_iff, mem_inter_iff, mem_empty_iff_false]
  intro
  exact mt (@h x)

theorem diff_inter_mem_sUnion {α : Type _} {s : Set (Set α)} (a y : Set α) (h : y ∈ s) :
    a \ ⋃₀ s ∩ y = ∅ :=
  diff_inter_eq_empty a <| subset_sUnion_of_mem h

end Set

namespace IsClopen

theorem isClosed_sUnion {H : Type _} [TopologicalSpace H] {s : Finset (Set H)}
    (hs : ∀ x ∈ s, IsClosed x) : IsClosed (⋃₀ (s : Set (Set H))) :=
  by
  simpa only [← isOpen_compl_iff, Set.compl_sUnion, Set.sInter_image] using
    Set.Finite.isOpen_biInter (Finset.finite_toSet s) fun i hi => _
  apply isOpen_compl_iff.2 (hs i hi)

theorem isClopen_sUnion {H : Type _} [TopologicalSpace H] (s : Finset (Set H))
    (hs : ∀ x ∈ s, IsClopen x) : IsClopen (⋃₀ (s : Set (Set H))) :=
  ⟨isOpen_sUnion fun t ht => (hs t ht).1, isClosed_sUnion fun t ht => (hs t ht).2⟩

/-- The finite union of clopen sets is clopen. -/
theorem clopen_finite_Union {H : Type _} [TopologicalSpace H] (s : Finset (Set H))
    (hs : ∀ x ∈ s, IsClopen x) : IsClopen (⋃₀ (s : Set (Set H))) := by rw [Set.sUnion_eq_biUnion];
  apply Set.Finite.isClopen_biUnion s.finite_to_set hs

/-- Given a finite set of clopens, one can find a finite disjoint set of clopens contained in
  it. -/
theorem clopen_Union_disjoint {H : Type _} [TopologicalSpace H] (s : Finset (Set H))
    (hs : ∀ x ∈ s, IsClopen x) :
    ∃ t : Finset (Set H),
      (∀ x ∈ (t : Set (Set H)), IsClopen x) ∧
        ⋃₀ (s : Set (Set H)) = ⋃₀ (t : Set (Set H)) ∧
          (∀ (x : Set H) (hx : x ∈ t), ∃ z ∈ s, x ⊆ z) ∧
            ∀ (x y : Set H) (hx : x ∈ t) (hy : y ∈ t) (h : x ≠ y), x ∩ y = ∅ :=
  by
  classical
  apply Finset.induction_on' s
  · use∅;
    simp only [Finset.coe_empty, Set.mem_empty_iff_false, IsEmpty.forall_iff, forall_const,
      eq_self_iff_true, Finset.not_mem_empty, and_self_iff]
  · rintro a S h's hS aS ⟨t, clo, union, sub, disj⟩
    set b := a \ ⋃₀ S with hb
    refine' ⟨insert b t, _, _, ⟨fun x hx => _, fun x y hx hy ne => _⟩⟩
    · rintro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx 
      cases hx
      · rw [hx]; apply IsClopen.diff (hs a h's) (clopen_finite_Union _ fun y hy => hs y (hS hy))
      · apply clo x hx
    · simp only [Finset.coe_insert, Set.sUnion_insert]; rw [← union, Set.diff_union_self]
    · simp only [Finset.mem_insert] at hx ; cases hx
      · use a; rw [hx]; simp only [true_and_iff, true_or_iff, eq_self_iff_true, Finset.mem_insert]
        apply Set.diff_subset
      · rcases sub x hx with ⟨z, hz, xz⟩; refine' ⟨z, _, xz⟩
        rw [Finset.mem_insert]; right; assumption
    · rw [Finset.mem_insert] at hx ; rw [Finset.mem_insert] at hy 
      have : ∀ y ∈ t, b ∩ y = ∅ := by rintro y hy; rw [hb, union]; apply Set.diff_inter_mem_sUnion;
        assumption
      cases hx
      · cases hy
        · exfalso; apply Ne; rw [hx, hy]
        · rw [hx]; apply this y hy
      · cases hy
        · rw [Set.inter_comm]; rw [hy]; apply this x hx
        · apply disj x y hx hy Ne

end IsClopen

namespace LocallyConstant.Density

variable (ε : ℝ)

/-- Takes an element of `A` to an `ε/4`-ball centered around it. -/
abbrev h {A : Type _} [NormedAddCommGroup A] : A → Set A := fun x : A => Metric.ball x (ε / 4)

/-- The set of (ε/4)-balls. -/
abbrev s {A : Type _} [NormedAddCommGroup A] : Set (Set A) :=
  Set.range (h ε)

variable {A} (f : C(X, A))

/-- Preimage of (ε/4)-balls. -/
abbrev b : Set (Set X) :=
  {j : Set X | ∃ U ∈ (s ε : Set (Set A)), j = f ⁻¹' U}

theorem opens {j : Set X} (hj : j ∈ b ε f) : IsOpen j :=
  by
  rcases hj with ⟨hj_w, ⟨hj_h_w_w, rfl⟩, rfl⟩
  exact Continuous.isOpen_preimage f.2 _ Metric.isOpen_ball

variable [Fact (0 < ε)]

/-- `X` is covered by a union of preimage of finitely many elements of `S` under `f` -/
theorem exists_finset_univ_sub :
    ∃ t : Finset (Set A),
      Set.univ ⊆ ⨆ (i : Set A) (H : i ∈ t) (H : i ∈ (s ε : Set (Set A))), f ⁻¹' i :=
  by
  have g : ⋃₀ S ε = (Set.univ : Set A) :=
    by
    rw [Set.sUnion_eq_univ_iff]; rintro; refine' ⟨Metric.ball a (ε / 4), _, _⟩
    · simp only [Set.mem_range, exists_apply_eq_apply]
    · simp only [Metric.mem_ball, dist_self]
      refine' div_pos (Fact.out _) zero_lt_four
  have g' : Set.preimage f (⋃₀ S ε) = Set.univ := by rw [g]; exact Set.preimage_univ
  rw [Set.preimage_sUnion, Set.Subset.antisymm_iff] at g' 
  refine'
    IsCompact.elim_finite_subcover compact_univ _
      (fun i => isOpen_iUnion fun hi => Continuous.isOpen_preimage (ContinuousMap.continuous f) i _)
      g'.2
  cases' hi with y hy; rw [← hy]; refine' @Metric.isOpen_ball A _ y (ε / 4)

/-- Choosing a finset as given in `exists_finset_univ_sub` -/
noncomputable abbrev t : Finset (Set A) :=
  Classical.choose (exists_finset_univ_sub ε f)

theorem exists_finset_univ_sub_prop :
    Set.univ ⊆ ⨆ (i : Set A) (H : i ∈ t ε f) (H : i ∈ (s ε : Set (Set A))), f ⁻¹' i :=
  Classical.choose_spec (exists_finset_univ_sub ε f)

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then the union of the preimages of all the sets from `S` also forms a cover. -/
theorem sUnion_sub_of_finset_sub : Set.univ ⊆ Set.sUnion (b ε f) :=
  by
  rintro x hx
  obtain ⟨-, ⟨j, rfl⟩, -, ⟨hj, rfl⟩, -, ⟨⟨a, jS⟩, rfl⟩, fj⟩ := (exists_finset_univ_sub_prop ε f) hx
  exact ⟨f ⁻¹' j, ⟨j, ⟨_, jS⟩, rfl⟩, fj⟩

variable [T2Space X] [TotallyDisconnectedSpace X]

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then there is a cover of `X` by clopen sets, with the image of each set being
  contained in an element of `S`. -/
def setClopen : Set (Set X) :=
  {j : Set X |
    ∃ (U : Set X) (hU : U ∈ b ε f),
      j ∈
        Classical.choose
          (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
            (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU))}

theorem mem_setClopen {x : Set X} :
    x ∈ setClopen ε f ↔
      ∃ (U : Set X) (hU : U ∈ b ε f),
        x ∈
          Classical.choose
            (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
              (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU)) :=
  Iff.rfl

/-- Elements of `set_clopen` are clopen. -/
theorem setClopen_sub_clopen_set : setClopen ε f ⊆ {s : Set X | IsClopen s} :=
  by
  intro j hj
  obtain ⟨W, hW, hj⟩ := (LocallyConstant.Density.mem_setClopen ε f).1 hj
  obtain ⟨H, -⟩ :=
    Classical.choose_spec
      (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
        (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hW))
  exact H hj

/-- `set_clopen` covers X. -/
theorem univ_sub_sUnion_setClopen : Set.univ ⊆ ⋃₀ setClopen ε f :=
  by
  rintro x hx; rw [Set.mem_sUnion]
  have f' := @loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _
  have sUnion_sub_of_finset_sub := sUnion_sub_of_finset_sub ε f
  -- writing `f⁻¹' U` as a union of basis elements (clopen sets)
  conv at sUnion_sub_of_finset_sub =>
    congr
    skip
    rw [Set.sUnion_eq_iUnion]
    congr
    ext
    apply_congr
      Classical.choose_spec
        (Classical.choose_spec
          (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion f' (opens ε f i.prop)))
  rw [Set.iUnion] at sUnion_sub_of_finset_sub 
  have g3 := sUnion_sub_of_finset_sub hx
  simp only [exists_prop, Set.mem_iUnion, Set.mem_range, SetCoe.exists, exists_exists_eq_and,
    Set.iSup_eq_iUnion, Set.mem_setOf_eq, Subtype.coe_mk] at g3 
  rcases g3 with ⟨U, hU, a, ha, xa⟩
  refine' ⟨a, _, xa⟩
  rw [mem_set_clopen]
  simp only [exists_prop, Set.mem_range, exists_exists_eq_and, Set.mem_setOf_eq]
  refine' ⟨U, hU, ha⟩

/-- The image of each element of `set_clopen` is contained in an element of `S`. -/
theorem exists_b_of_mem_clopen {x : Set X} (hx : x ∈ setClopen ε f) :
    ∃ (U : Set X) (H : U ∈ b ε f), x ⊆ U :=
  by
  rcases hx with ⟨U, hU, xU⟩; refine' ⟨U, hU, _⟩
  obtain ⟨H, H1⟩ :=
    Classical.choose_spec
      (TopologicalSpace.IsTopologicalBasis.open_eq_sUnion
        (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _) (opens ε f hU))
  rw [H1]; intro u hu; simp only [exists_prop, Set.mem_setOf_eq]
  refine' ⟨x, _, hu⟩
  convert xU
  ext; simp only [exists_prop, iff_self_iff]

/-- Every element of `set_clopen` is open. -/
theorem mem_setClopen_isOpen (i : setClopen ε f) : IsOpen (i : Set X) :=
  TopologicalSpace.IsTopologicalBasis.isOpen (@loc_compact_Haus_tot_disc_of_zero_dim X _ _ _ _)
    ((setClopen_sub_clopen_set ε f) i.2)

/-- A restatement of `univ_sub_sUnion_set_clopen`. -/
theorem cover : (Set.univ : Set X) ⊆ ⋃ i : setClopen ε f, ↑i := by
  convert LocallyConstant.Density.univ_sub_sUnion_setClopen ε f; rw [Set.sUnion_eq_iUnion]

/-- Obtain a finite subcover of `set_clopen` using the compactness of `X`. -/
noncomputable abbrev s' :=
  Classical.choose
    (IsCompact.elim_finite_subcover (@compact_univ X _ _) _ (mem_setClopen_isOpen ε f) (cover ε f))

/-- Coercing a subset of `set_clopen` in `s'` to `set X`. -/
abbrev s1 := fun x : s' ε f => (x.1 : Set X)

/-- The range of `s1` is finite. -/
theorem fin : (Set.range (s1 ε f)).Finite := by apply Set.finite_range _;
  exact Finite.of_fintype ↥(s' ε f)

/-- Any element in the range of `s1` is clopen. -/
theorem isClopen_x {x : Set X} (hx : x ∈ (fin ε f).toFinset) : IsClopen x :=
  by
  simp only [Set.mem_range, SetCoe.exists, Set.Finite.mem_toFinset, Finset.mem_coe] at hx 
  rcases hx with ⟨⟨⟨v, hv⟩, hw⟩, hU⟩
  convert (LocallyConstant.Density.setClopen_sub_clopen_set ε f) hv
  rw [← hU]
  delta s1
  simp

/-- If there is a finite set of sets from `S` whose preimage forms a cover for `X`,
  then there is a finset of `sets X` containing clopen sets, with the image of each set being
  contained in an element of `S`. We use `s'` to get a finite disjoint clopen cover of `X`;
  note : it is not a partition -/
noncomputable def finsetClopen : Finset (Set X) :=
  Classical.choose
    (IsClopen.clopen_Union_disjoint (Set.Finite.toFinset (fin ε f)) fun x hx => isClopen_x ε f hx)

/-- Elements of `finset_clopen` are clopen. -/
theorem finsetClopen_isClopen {x : Set X} (hx : x ∈ finsetClopen ε f) : IsClopen x :=
  (Classical.choose_spec
        (IsClopen.clopen_Union_disjoint (Set.Finite.toFinset (fin ε f)) fun x hx =>
          isClopen_x ε f hx)).1
    x hx

/-- The image of every element of `finset_clopen` is contained in some element of `S`. -/
theorem exists_sub_s {x : Set X} (hx : x ∈ finsetClopen ε f) :
    ∃ U ∈ (s ε : Set (Set A)), (Set.image f x : Set A) ⊆ U :=
  by
  rcases(Classical.choose_spec
              (IsClopen.clopen_Union_disjoint (Set.Finite.toFinset (Fin ε f)) fun x hx =>
                LocallyConstant.Density.isClopen_x ε f hx)).2.2.1
      x hx with
    ⟨z, hz, wz⟩
  simp only [Set.mem_range, SetCoe.exists, Set.Finite.mem_toFinset, Finset.mem_coe] at hz 
  -- `z'` is a lift of `x` in `V`
  rcases hz with ⟨⟨⟨z', h1⟩, h2⟩, h3⟩
  rcases LocallyConstant.Density.exists_b_of_mem_clopen ε f h1 with ⟨U, BU, xU⟩
  simp only [exists_prop, exists_exists_eq_and, Set.mem_setOf_eq] at BU 
  cases' BU with U' h4
  refine' ⟨U', h4.1, _⟩; trans Set.image f z
  · apply Set.image_subset _ wz
  · simp only [Set.image_subset_iff]; rw [← h4.2, ← h3]
    delta s1
    simp only [xU, Subtype.coe_mk]

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (b «expr ∈ » finset_clopen[locally_constant.density.finset_clopen] ε f) -/
/-- Showing that `finset_clopen` is a disjoint cover of `X`. -/
theorem finsetClopen_prop (a : X) : ∃! (b : _) (_ : b ∈ finsetClopen ε f), a ∈ b :=
  by
  -- proving that every element `a : X` is contained in a unique element `j` of `s`
  obtain ⟨j, hj, aj⟩ : ∃ j ∈ LocallyConstant.Density.finsetClopen ε f, a ∈ j :=
    by
    -- `s'` covers `X`
    have ha :=
      Classical.choose_spec
        (IsCompact.elim_finite_subcover (@compact_univ X _ _) _ (LocallyConstant.Density.mem_setClopen_isOpen ε f)
          (cover ε f))
        (Set.mem_univ a)
    have hs :=
      (Classical.choose_spec
            (IsClopen.clopen_Union_disjoint (Set.Finite.toFinset (Fin ε f)) fun x hx =>
              LocallyConstant.Density.isClopen_x ε f hx)).2.1
    delta s1 at hs 
    suffices a ∈ ⋃₀ (finset_clopen ε f : Set (Set X))
      by
      simp only [Set.mem_sUnion, Finset.mem_coe, exists_prop] at this 
      cases' this with j hj; refine' ⟨j, hj.1, hj.2⟩
    · rw [finset_clopen]
      rw [← hs]
      simp only [Set.mem_iUnion, Set.Finite.coe_toFinset, Subtype.val_eq_coe, Set.sUnion_range]
      simp only [exists_prop, Set.mem_iUnion, SetCoe.exists, exists_and_right, Subtype.coe_mk] at ha 
      -- have the element `U` of `V`, now translate it to `s`
      rcases ha with ⟨U, ⟨hU, s'U⟩, aU⟩
      delta s'
      refine' ⟨⟨⟨U, hU⟩, s'U⟩, aU⟩
  refine' ⟨j, _, fun y hy => _⟩
  · -- existence
    simp only [exists_prop, Set.image_subset_iff, Set.mem_range, exists_exists_eq_and,
      exists_unique_iff_exists]
    refine' ⟨hj, aj⟩
  · -- uniqueness, coming from the disjointness of the clopen cover, `disj`
    simp only [exists_prop, exists_unique_iff_exists] at hy 
    cases' hy with h1 h2
    have disj :=
      (Classical.choose_spec
                (IsClopen.clopen_Union_disjoint (Set.Finite.toFinset (Fin ε f)) fun x hx =>
                  LocallyConstant.Density.isClopen_x ε f hx)).2.2.2
        j y hj h1
    by_cases h : j = y
    · rw [h.symm]
    · exfalso; specialize disj h; rw [← Set.mem_empty_iff_false]; rw [← disj]
      apply Set.mem_inter aj _
      simp only [and_true_iff, imp_true_iff, eq_iff_true_of_subsingleton] at h2 
      exact h2

/-- Takes a nonempty `s` in `finset_clopen` and returns an element of it. -/
noncomputable abbrev c' := fun (s : Set X) (H : s ∈ finsetClopen ε f ∧ Nonempty s) =>
  Classical.choice H.2

/-- Any `x` in `X` must belong to a unique `s` in `finset_clopen`. `c2` takes `x` to the image of
  any element of `s` under `f`, which is the same `f x`. -/
noncomputable abbrev c2 (f : C(X, A)) : X → A := fun x =>
  f
    (c' ε f (Classical.choose (ExistsUnique.exists (finsetClopen_prop ε f x)))
      (by
        have :=
          exists_prop.1
            (ExistsUnique.exists
              (Classical.choose_spec (ExistsUnique.exists (LocallyConstant.Density.finsetClopen_prop ε f x))))
        constructor
        refine' Finset.mem_coe.1 this.1
        apply Set.Nonempty.to_subtype
        refine' ⟨x, this.2⟩))

/-- Any element of `finset_clopen` is open. -/
theorem mem_finsetClopen_isOpen {U : Set X} (hU : U ∈ finsetClopen ε f) : IsOpen U := by
  rw [LocallyConstant.Density.finsetClopen] at hU ; apply (LocallyConstant.Density.finsetClopen_isClopen ε f hU).1

/-- An equivalent version of `disj`. -/
theorem mem_finsetClopen_unique' {U V : Set X} {y : X} (hU : U ∈ finsetClopen ε f) (hUy : y ∈ U)
    (hVy : y ∈ V) (hV : V ∈ finsetClopen ε f) : V = U :=
  by
  by_contra
  have :=
    (Classical.choose_spec
              (IsClopen.clopen_Union_disjoint (Set.Finite.toFinset (Fin ε f)) fun x hx =>
                LocallyConstant.Density.isClopen_x ε f hx)).2.2.2
      _ _ hV hU h
  revert this
  --change (V ∩ U) ≠ ∅,
  refine' Set.Nonempty.ne_empty ⟨y, Set.mem_inter hVy hUy⟩

/-- Given `x` in `X`, there is a unique element `U` of `finset_clopen` such that `x ∈ U`. For any
  `y ∈ U`, `y` is contained in any other element `V` of `finset_clopen` containing `x`. -/
theorem mem_finsetClopen_unique {U V : Set X} {x y : X}
    (U_prop : (U ∈ finsetClopen ε f ∧ x ∈ U) ∧ ∀ y : Set X, y ∈ finsetClopen ε f → x ∈ y → y = U)
    (hy : y ∈ U) (hV : V ∈ finsetClopen ε f) : x ∈ V ↔ y ∈ V :=
  by
  obtain ⟨W, hW⟩ := LocallyConstant.Density.finsetClopen_prop ε f y
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hW 
  constructor <;> intro h
  · rw [U_prop.2 V hV h]; assumption
  · rw [hW.2 V hV h]; rw [← hW.2 U U_prop.1.1 hy]; apply U_prop.1.2

/-- `c2` is locally constant -/
theorem loc_const : IsLocallyConstant (c2 ε f) :=
  by
  rw [IsLocallyConstant.iff_exists_open]; rintro x
  obtain ⟨U, hU⟩ := LocallyConstant.Density.finsetClopen_prop ε f x
  simp only [and_imp, exists_prop, exists_unique_iff_exists] at hU 
  refine' ⟨U, LocallyConstant.Density.mem_finsetClopen_isOpen ε f hU.1.1, hU.1.2, fun x' hx' => _⟩
  delta c2
  congr
  pick_goal 4; ext y; revert y; rw [← Set.ext_iff]; congr
  -- is there a better way to do this?
  any_goals
    ext y; simp only [exists_prop, and_congr_right_iff, exists_unique_iff_exists]
    intro hy; symm; apply mem_finset_clopen_unique ε f hU hx' hy

/-- Given an `f ∈ C(X, A)` and an `ε > 0`, one can find a locally constant function `b` which is in
  an ε-ball with center `f`, `b` is precisely `c2`. -/
theorem loc_const_dense' :
    ∃ (b : C(X, A)) (H : b ∈ Set.range (@LocallyConstant.toContinuousMap X A _ _)), dist f b < ε :=
  ⟨@LocallyConstant.toContinuousMap X A _ _ ⟨c2 ε f, loc_const ε f⟩, ⟨⟨c2 ε f, loc_const ε f⟩, rfl⟩,
    gt_of_gt_of_ge (half_lt_self (Fact.out _))
      (by
        -- showing that the distance between `f` and `c2` is less than or equal to `ε/2`
        rw [dist_eq_norm, ContinuousMap.norm_eq_iSup_norm]
        -- empty type is special case
        cases' isEmpty_or_nonempty X with hempty hnonempty
        · change _ ≥ dite _ _ _
          split_ifs with h
          · rcases h with ⟨⟨_, x, _⟩, _⟩
            exact (@IsEmpty.false _ hempty x).elim
          exact le_of_lt (half_pos (Fact.out _))
        -- writing the distance in terms of the sup norm
        refine' csSup_le _ fun m hm => _
        · rw [Set.range_nonempty_iff_nonempty]; assumption
        -- this is where `nonempty X` is needed
        · cases' hm with y hy
          simp only [ContinuousMap.coe_sub, LocallyConstant.coe_mk,
            LocallyConstant.toContinuousMapLinearMap_apply, Pi.sub_apply,
            LocallyConstant.coe_continuousMap] at hy 
          rw [← hy]
          -- reduced to proving ∥f(y) - c2(y)∥ ≤ ε/2
          obtain ⟨w, wT, hw⟩ := LocallyConstant.Density.finsetClopen_prop ε f y
          -- `w` is the unique element of `finset_clopen` to which `y` belongs
          simp only [exists_prop, exists_unique_iff_exists] at wT 
          simp only [and_imp, exists_prop, exists_unique_iff_exists] at hw 
          have : c2 ε f y = f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩) :=
            by
            -- showing that `w` is the same as the `classical.some _` used in `c2`
            delta c2;
            congr
            any_goals
              have := Classical.choose_spec (ExistsUnique.exists (finset_clopen_prop ε f y))
              simp only [exists_prop, exists_unique_iff_exists] at *
              apply hw _ this.1 this.2
          dsimp
          rw [this]
          obtain ⟨U, hU, wU⟩ := exists_sub_S ε f wT.1
          -- `U` is a set of `A` which is an element of `S` and contains `f(w)`
          cases' hU with z hz
          -- `U` is the `ε/4`-ball centered at `z`
          have mem_U : f (c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩) ∈ U :=
            wU ⟨c' ε f w ⟨wT.1, ⟨⟨y, wT.2⟩⟩⟩, Subtype.coe_prop _, rfl⟩
          have tS : f y ∈ U := wU ⟨y, wT.2, rfl⟩
          rw [hz.symm, mem_ball_iff_norm] at *
          conv_lhs => rw [sub_eq_sub_add_sub _ _ z]
          -- unfolding everything in terms of `z`, and then using `mem_U` and `tS`
          have : ε / 2 = ε / 4 + ε / 4 := by rw [div_add_div_same]; linarith
          rw [this]; apply norm_add_le_of_le (le_of_lt _) (le_of_lt tS)
          rw [← norm_neg _]; simp only [mem_U, neg_sub])⟩

variable (X)

/-- The locally constant functions from `X` to `A` (viewed as a subset of C(X, A)) are dense
  in C(X, A). -/
theorem loc_const_dense : Dense (Set.range (@LocallyConstant.toContinuousMap X A _ _)) := fun f =>
  by
  rw [Metric.mem_closure_iff]
  rintro ε hε
  haveI : Fact (0 < ε) := Fact.mk hε
  -- we have all the ingredients from `loc_const_dense'`, only need `exists_finset_univ_sub_prop`
  apply loc_const_dense' ε f

end LocallyConstant.Density

