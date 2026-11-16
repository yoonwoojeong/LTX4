import LiquidTensorExperiment.ForMathlib.IsLocallyConstant
import LiquidTensorExperiment.LocallyConstant.Analysis

#align_import prop_92.extension_profinite

/-!
# Extending a locally constant map to larger profinite sets

In this file, we prove that, given a topological embedding `e : X → Y` from a non-empty
compact topological space to a profinite set (ie. compact Hausdorff totally disconnected space),
every locally constant map `f` from `X` to any type `Z` "extends" to a locally constant map
from `Y` to `Z`, ie. there exists `g : Y → Z` locally constant such that `f = g ∘ e`.

     e
  X ↪-→ Y
  |    /
f |   / h
  ↓ ↙
  Z

Notes:
* this wouldn't work if `X` and `Z` were empty and `Y` weren't. The minimal assumption
  would be assuming `Z` isn't empty, I'll refactor this soon.
* Everything is stated assuming only `X` is compact but the existence of `f` ensures `X` is
  profinite, we're just saving type-class search (and nothing in the construction or proofs
  directly use `X` is profinite).

The main definition is `embedding.extend {e : X → Y} (he : embedding e) (f : X → Z) : Y → Z`
It assumes `X` is compact (and non-empty) and assumes `Y` is profinite but doesn't
assume `f` is locally constant, it is simply defined as a constant map if `f` isn't.

The announced properties of this extension are `embedding.extend_extends` and
`embedding.is_locally_constant_extend`.
-/


variable {X : Type _} [TopologicalSpace X]

noncomputable section

open Set

variable [CompactSpace X] {Y : Type _} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [TotallyDisconnectedSpace Y]

theorem Embedding.preimage_clopen {f : X → Y} (hf : Embedding f) {U : Set X} (hU : IsClopen U) :
    ∃ V : Set Y, IsClopen V ∧ U = f ⁻¹' V :=
  by
  cases' hU with hU hU'
  have hfU : IsCompact (f '' U) := hU'.is_compact.image hf.continuous
  obtain ⟨W, W_op, hfW⟩ : ∃ W : Set Y, IsOpen W ∧ f ⁻¹' W = U :=
    by
    rw [hf.toInducing.induced] at hU 
    exact is_open_induced_iff.mp hU
  obtain ⟨ι, Z : ι → Set Y, hWZ : W = ⋃ i, Z i, hZ : ∀ i, IsClopen <| Z i⟩ :=
    is_topological_basis_clopen.open_eq_iUnion W_op
  have : f '' U ⊆ ⋃ i, Z i := by rw [image_subset_iff, ← hWZ, hfW]
  obtain ⟨I, hI⟩ : ∃ I : Finset ι, f '' U ⊆ ⋃ i ∈ I, Z i
  exact hfU.elim_finite_subcover _ (fun i => (hZ i).1) this
  refine' ⟨⋃ i ∈ I, Z i, _, _⟩
  · apply Set.Finite.isClopen_biUnion; apply Finset.finite_toSet
    tauto
  · apply subset.antisymm
    exact image_subset_iff.mp hI
    have : (⋃ i ∈ I, Z i) ⊆ ⋃ i, Z i := Union₂_subset_Union _ _
    rw [← hfW, hWZ]
    mono

theorem Embedding.ex_discreteQuotient [Nonempty X] {f : X → Y} (hf : Embedding f)
    (S : DiscreteQuotient X) : ∃ (S' : DiscreteQuotient Y) (g : S ≃ S'), S'.proj ∘ f = g ∘ S.proj :=
  by
  classical
  inhabit X
  haveI : Fintype S := discrete_quotient.fintype S
  have : ∀ s : S, ∃ V : Set Y, IsClopen V ∧ S.proj ⁻¹' {s} = f ⁻¹' V := fun s =>
    hf.preimage_clopen (S.fiber_clopen {s})
  choose V hV using this
  rw [forall_and] at hV 
  cases' hV with V_cl hV
  let s₀ := S.proj default
  let W : S → Set Y := fun s => V s \ ⋃ (s') (h : s' ≠ s), V s'
  have W_dis : ∀ {s s'}, s ≠ s' → Disjoint (W s) (W s') :=
    by
    rintro s s' hss x ⟨⟨hxs_in, hxs_out⟩, ⟨hxs'_in, hxs'_out⟩⟩
    apply hxs'_out
    rw [mem_Union₂]
    exact ⟨s, hss, hxs_in⟩
  have hfW : ∀ x, f x ∈ W (S.proj x) := by
    intro x
    constructor
    · change x ∈ f ⁻¹' (V <| S.proj x)
      rw [← hV (S.proj x)]
      exact mem_singleton _
    · intro h
      rcases mem_Union₂.mp h with ⟨s', hss', hfx : x ∈ f ⁻¹' V s'⟩
      rw [← hV s'] at hfx 
      exact hss' hfx.symm
  have W_nonempty : ∀ s, (W s).Nonempty := by
    intro s
    obtain ⟨x, hx : S.proj x = s⟩ := S.proj_surjective s
    use f x
    rw [← hx]
    apply hfW
  let R : S → Set Y := fun s => if s = s₀ then W s₀ ∪ (⋃ s, W s)ᶜ else W s
  have W_cl : ∀ s, IsClopen (W s) := by
    intro s
    apply (V_cl s).diffₓ
    apply isClopen_iUnion_of_finite
    intro s'
    by_cases h : s' = s
    simp [h, isClopen_empty]
    simp [h, V_cl s']
  have R_cl : ∀ s, IsClopen (R s) := by
    intro s
    dsimp [R]
    split_ifs
    · apply (W_cl s₀).union
      apply IsClopen.compl
      exact isClopen_iUnion_of_finite W_cl
    · exact W_cl _
  let R_part : IndexedPartition R := by
    apply IndexedPartition.mk'
    · rintro s s' hss x ⟨hxs, hxs'⟩
      dsimp [R] at hxs hxs' 
      split_ifs at hxs hxs'  with hs hs'
      · exact (hss (hs.symm ▸ hs' : s = s')).elim
      · cases' hxs' with hx hx
        · exact W_dis hs' ⟨hxs, hx⟩
        · apply hx
          rw [mem_Union]
          exact ⟨s, hxs⟩
      · cases' hxs with hx hx
        · exact W_dis hs ⟨hxs', hx⟩
        · apply hx
          rw [mem_Union]
          exact ⟨s', hxs'⟩
      · exact W_dis hss ⟨hxs, hxs'⟩
    · intro s
      dsimp [R]
      split_ifs
      · use(W_nonempty s₀).some
        left
        exact (W_nonempty s₀).some_mem
      · apply W_nonempty
    · intro y
      by_cases hy : ∃ s, y ∈ W s
      · cases' hy with s hys
        use s
        dsimp [R]
        split_ifs
        · left
          rwa [h] at hys 
        · exact hys
      · use s₀
        simp only [R, if_pos rfl]
        right
        rwa [mem_compl_iff, mem_Union]
  let S' := R_part.discrete_quotient R_cl
  let g := R_part.discrete_quotient_equiv R_cl
  have hR : ∀ x, f x ∈ R (S.proj x) := by
    intro x
    by_cases hx : S.proj x = s₀
    · simp only [hx, R, if_pos rfl]
      left
      rw [← hx]
      apply hfW
    · simp only [R, if_neg hx]
      apply hfW
  use S', g
  ext x
  change f x ∈ S'.proj ⁻¹' {g (S.proj x)}
  rw [R_part.discrete_quotient_fiber R_cl]
  simpa using hR x

def Embedding.discreteQuotientMap [Nonempty X] {f : X → Y} (hf : Embedding f)
    (S : DiscreteQuotient X) : DiscreteQuotient Y :=
  (hf.ex_discreteQuotient S).some

def Embedding.discreteQuotientEquiv [Nonempty X] {f : X → Y} (hf : Embedding f)
    (S : DiscreteQuotient X) : S ≃ hf.discreteQuotientMap S :=
  (hf.ex_discreteQuotient S).choose_spec.some

theorem Embedding.discreteQuotient_spec [Nonempty X] {f : X → Y} (hf : Embedding f)
    (S : DiscreteQuotient X) :
    (hf.discreteQuotientMap S).proj ∘ f = hf.discreteQuotientEquiv S ∘ S.proj :=
  (hf.ex_discreteQuotient S).choose_spec.choose_spec

variable {Z : Type _} [Inhabited Z]

open scoped Classical

def Embedding.extend {e : X → Y} (he : Embedding e) (f : X → Z) : Y → Z :=
  if h : IsLocallyConstant f ∧ Nonempty X then
    by
    haveI := h.2
    let ff : LocallyConstant X Z := ⟨f, h.1⟩
    let T := he.discreteQuotientMap ff.discreteQuotient
    let ee : ff.discreteQuotient ≃ T := he.discreteQuotientEquiv ff.discreteQuotient
    exact ff.lift ∘ ee.symm ∘ T.proj
  else fun y => default

/- lemma embedding.extend_eq {e : X → Y} (he : embedding e) {f : X → Z} (hf : is_locally_constant f) :
  he.extend f = (hf.discrete_quotient_map) ∘ (he.discrete_quotient_equiv hf.discrete_quotient).symm ∘ (he.discrete_quotient_map hf.discrete_quotient).proj
  := dif_pos hf -/
theorem Embedding.extend_extends {e : X → Y} (he : Embedding e) {f : X → Z}
    (hf : IsLocallyConstant f) : ∀ x, he.extend f (e x) = f x :=
  by
  intro x
  haveI : Nonempty X := ⟨x⟩
  let ff : LocallyConstant X Z := ⟨f, hf⟩
  let S := ff.discreteQuotient
  let S' := he.discreteQuotientMap S
  let barf : S → Z := ff.lift
  let g : S ≃ S' := he.discreteQuotientEquiv S
  unfold Embedding.extend
  have h : IsLocallyConstant f ∧ Nonempty X := ⟨hf, ⟨x⟩⟩
  rw [dif_pos h]
  change (barf ∘ g.symm ∘ S'.proj ∘ e) x = f x
  suffices (barf ∘ S.proj) x = f x by simpa [he.discreteQuotient_spec]
  simpa

theorem Embedding.isLocallyConstant_extend {e : X → Y} (he : Embedding e) {f : X → Z} :
    IsLocallyConstant (he.extend f) :=
  by
  unfold Embedding.extend
  split_ifs
  · apply IsLocallyConstant.comp
    apply IsLocallyConstant.comp
    exact DiscreteQuotient.proj_isLocallyConstant _
  · apply IsLocallyConstant.const

theorem Embedding.range_extend {e : X → Y} (he : Embedding e) [Nonempty X] {Z : Type _}
    [Inhabited Z] {f : X → Z} (hf : IsLocallyConstant f) : range (he.extend f) = range f :=
  by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    let ff : LocallyConstant _ _ := ⟨f, hf⟩
    let T := he.discreteQuotientMap ff.discreteQuotient
    let ee : ff.discreteQuotient ≃ T := he.discreteQuotientEquiv ff.discreteQuotient
    dsimp only [Embedding.extend]
    rw [dif_pos]
    swap; · exact ⟨hf, ‹_›⟩
    change ff.lift (ee.symm (T.proj y)) ∈ _
    rcases ff.discreteQuotient.proj_surjective (ee.symm (T.proj y)) with ⟨w, hz⟩
    use w
    rw [← hz]
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨e x, he.extend_extends hf _⟩

def Embedding.locallyConstantExtend {e : X → Y} (he : Embedding e) (f : LocallyConstant X Z) :
    LocallyConstant Y Z :=
  ⟨he.extend f, he.isLocallyConstant_extend⟩

@[simp]
theorem Embedding.locallyConstantExtend_extends {e : X → Y} (he : Embedding e)
    (f : LocallyConstant X Z) (x : X) : he.locallyConstantExtend f (e x) = f x :=
  he.extend_extends f.2 x

theorem Embedding.comap_locallyConstantExtend {e : X → Y} (he : Embedding e)
    (f : LocallyConstant X Z) : (he.locallyConstantExtend f).comap e = f :=
  by
  ext x
  rw [LocallyConstant.coe_comap _ _ he.continuous]
  exact he.locallyConstantExtend_extends f x

theorem Embedding.range_locallyConstantExtend {e : X → Y} (he : Embedding e) [Nonempty X]
    {Z : Type _} [Inhabited Z] (f : LocallyConstant X Z) :
    range (he.locallyConstantExtend f) = range f :=
  he.range_extend f.2

-- version avec comap_hom pour Z normed group ?
