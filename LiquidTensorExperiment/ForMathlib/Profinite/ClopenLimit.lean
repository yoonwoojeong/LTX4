import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.DiscreteQuotient
import LiquidTensorExperiment.ForMathlib.Order

#align_import for_mathlib.Profinite.clopen_limit

noncomputable section

open scoped Classical

namespace Profinite

open CategoryTheory

open CategoryTheory.Limits

universe u

variable {J : Type u} [SemilatticeInf J] (F : J ⥤ Profinite.{u}) (C : Cone F)

theorem image_eq (hC : IsLimit C) (i : J) :
    Set.range (C.π.app i) = ⋂ (j : J) (h : j ≤ i), Set.range (F.map (homOfLE h)) :=
  by
  refine' le_antisymm _ _
  · apply Set.subset_iInter
    intro j
    apply Set.subset_iInter
    intro hj
    rw [← C.w (hom_of_le hj)]
    apply Set.range_comp_subset_range
  · rintro x hx
    have cond : ∀ (j : J) (hj : j ≤ i), ∃ y : F.obj j, (F.map (hom_of_le hj)) y = x :=
      by
      intro j hj
      exact hx _ ⟨j, rfl⟩ _ ⟨hj, rfl⟩
    let Js := Σ' a b : J, a ≤ b
    let P := ∀ j : J, F.obj j
    let Us : Js → Set P := fun e => {p | F.map (hom_of_le e.2.2) (p e.1) = p e.2.1 ∧ p i = x}
    have hP : _root_.is_compact (Set.univ : Set P) := compact_univ
    have hh := hP.inter_iInter_nonempty Us _ _
    · rcases hh with ⟨z, hz⟩
      let IC : limit_cone F ≅ C := (limit_cone_is_limit F).uniqueUpToIso hC
      let ICX : (limit_cone F).pt ≅ C.X := (Cones.forget _).mapIso IC
      let z : (limit_cone F).pt := ⟨z, _⟩
      swap
      · intro a b h
        convert (hz.2 _ ⟨⟨a, b, le_of_hom h⟩, rfl⟩).1
      use ICX.hom z
      change (hC.lift _ ≫ _) _ = _
      rw [hC.fac]
      exact (hz.2 _ ⟨⟨i, i, le_refl _⟩, rfl⟩).2
    · intro i
      refine' IsClosed.inter (isClosed_eq _ _) (isClosed_eq _ _) <;> continuity
    · have : ∀ e : J, Nonempty (F.obj e) := by
        intro e
        rcases cond (e ⊓ i) inf_le_right with ⟨y, rfl⟩
        use F.map (hom_of_le inf_le_left) y
      haveI : ∀ j : J, Inhabited (F.obj j) := by intro j; refine' ⟨Nonempty.some (this j)⟩
      intro G
      let GG := G.image fun e : Js => e.1
      haveI : Inhabited J := ⟨i⟩
      have := exists_le_finset (insert i GG)
      obtain ⟨j0, hj0⟩ := this
      obtain ⟨x0, rfl⟩ := cond j0 (hj0 _ (Finset.mem_insert_self _ _))
      let z : P := fun e => if h : j0 ≤ e then F.map (hom_of_le h) x0 else default
      use z
      refine' ⟨trivial, _⟩
      rintro S ⟨e, rfl⟩
      rintro T ⟨k, rfl⟩
      dsimp [z]
      refine' ⟨_, by erw [dif_pos]⟩
      have : j0 ≤ e.fst := by
        apply hj0
        apply Finset.mem_insert_of_mem
        rw [Finset.mem_image]
        refine' ⟨e, k, rfl⟩
      erw [dif_pos this, dif_pos (le_trans this e.2.2)]
      change (F.map _ ≫ F.map _) _ = _
      rw [← F.map_comp]
      rfl

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.proofs -/
set_option pp.proofs true

theorem image_stabilizes [Inhabited J] [∀ i, Fintype (F.obj i)] (i : J) :
    ∃ (j : J) (hj : j ≤ i),
      ∀ (k : J) (hk : k ≤ j),
        Set.range (F.map (homOfLE <| le_trans hk hj)) = Set.range (F.map (homOfLE hj)) :=
  by
  have := eventually_constant i (fun e he => Set.range (F.map (hom_of_le he))) _
  swap
  · intro a b ha hb h
    dsimp
    have : hom_of_le ha = hom_of_le h ≫ hom_of_le hb := rfl
    rw [this, F.map_comp, Profinite.coe_comp]
    apply Set.range_comp_subset_range
  obtain ⟨j0, hj0, hh⟩ := this
  use j0; use hj0
  exact hh

/-- The images of the transition maps stabilize, in which case they agree with
the image of the cone point. -/
theorem exists_image [Inhabited J] [∀ i, Fintype (F.obj i)] (hC : IsLimit C) (i : J) :
    ∃ (j : J) (hj : j ≤ i), Set.range (C.π.app i) = Set.range (F.map <| homOfLE <| hj) :=
  by
  have := iInter_eq i (fun e he => Set.range (F.map (hom_of_le he))) _
  swap
  · intro a b ha hb hh
    dsimp
    have : hom_of_le ha = hom_of_le hh ≫ hom_of_le hb; rfl
    rw [this, F.map_comp, Profinite.coe_comp]
    apply Set.range_comp_subset_range
  obtain ⟨j0, hj0, hh⟩ := this
  dsimp at hh 
  use j0; use hj0
  rw [image_eq _ _ hC, ← hh]

end Profinite

