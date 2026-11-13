import Mathlib.Data.Fintype.Basic

#align_import for_mathlib.order

open scoped Classical

theorem exists_le_finset {α : Type _} [Inhabited α] [SemilatticeInf α] (G : Finset α) :
    ∃ j : α, ∀ g ∈ G, j ≤ g := by
  by_cases h : G.nonempty
  · exact ⟨Finset.inf' G h id, fun g => Finset.inf'_le _⟩
  · exact ⟨default, fun g hg => False.elim <| h ⟨_, hg⟩⟩

theorem iInter_eq {α β : Type _} [Inhabited α] [Fintype β] [SemilatticeInf α] (i : α)
    (f : ∀ (a : α) (ha : a ≤ i), Set β)
    (hf : ∀ (a b : α) (ha : a ≤ i) (hb : b ≤ i) (h : a ≤ b), f a ha ≤ f b hb) :
    ∃ (j : α) (hj : j ≤ i), (⋂ (k : α) (hk : k ≤ i), f k hk) = f j hj :=
  by
  suffices ∃ (j : α) (hj : j ≤ i), ∀ (k : α) (hk : k ≤ i), f j hj ≤ f k hk
    by
    rcases this with ⟨j, hj, h⟩
    use j
    use hj
    refine' le_antisymm _ _
    · refine' Set.sInter_subset_of_mem ⟨j, _⟩
      tidy
    · rintro x hx _ ⟨k, rfl⟩
      rintro _ ⟨hk, rfl⟩
      apply h _ _ hx
  let BB := {S : Set β | ∃ (e : α) (he : e ≤ i), S = f e he}
  let FF : BB → α := fun ee => Classical.choose ee.2
  have hFF : ∀ S : BB, FF S ≤ i := fun S => (Classical.choose_spec S.2).some
  have hFF' : ∀ S : BB, (S : Set β) = f (FF S) (hFF S) := fun S =>
    (Classical.choose_spec S.2).choose_spec
  haveI : Fintype BB := Fintype.ofInjective (fun S : BB => S.1) (by tidy)
  let GG := (Finset.univ : Finset BB).image FF
  obtain ⟨j0, hj0⟩ := exists_le_finset GG
  use j0 ⊓ i, inf_le_right
  intro k hk
  have : ∃ (e : α) (he : e ≤ i) (heFF : e ∈ GG), f k hk = f e he :=
    by
    let T : BB := ⟨f k hk, k, hk, rfl⟩
    use FF T, hFF _
    constructor
    · erw [Finset.mem_image]
      use T
      simp
    · rw [← hFF']; rfl
  obtain ⟨e, he, heFF, hhe⟩ := this
  rw [hhe]
  exact hf _ _ _ _ (le_trans inf_le_left (hj0 _ heFF))

theorem eventually_constant {α β : Type _} [Inhabited α] [Fintype β] [SemilatticeInf α] (i : α)
    (f : ∀ (a : α) (ha : a ≤ i), Set β)
    (hf : ∀ (a b : α) (ha : a ≤ i) (hb : b ≤ i) (h : a ≤ b), f a ha ≤ f b hb) :
    ∃ (j : α) (hj : j ≤ i), ∀ (k : α) (hk : k ≤ j), f k (le_trans hk hj) = f j hj :=
  by
  let S := ⋂ (k : α) (hk : k ≤ i), f k hk
  obtain ⟨j0, hj0, h⟩ := iInter_eq i f hf
  use j0, hj0
  intro e he
  refine' le_antisymm (hf _ _ _ _ he) _
  rw [← h]
  rintro x hx
  refine' hx _ ⟨e, _⟩
  tidy

