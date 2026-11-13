import LiquidTensorExperiment.FreePfpng.Setup

#align_import free_pfpng.mono

noncomputable section

open scoped Classical

open CategoryTheory

open Opposite

universe u

theorem Profinite.mono_free'_toCondensedFreePfpng_aux (S B : Profinite.{u}) (b : B)
    (T : DiscreteQuotient S) (t : S.toCondensed.val.obj (op B) →₀ ℤ) :
    let e : S.toCondensed.val.obj (op B) → S.condensedFreePfpng.val.obj (op B) := fun f =>
      S.toCondensedFreePfpng.val.app (op B) f
    let ι : S.toCondensed.val.obj (op B) → S := fun f => (ULift.down f).1 b
    ((Limits.limit.π (S.fintypeDiagram ⋙ forget FintypeCat ⋙ AddCommGroupCat.free' ⋙ Ab.ulift) T)
          (S.condensedFreePfpngSpecialize B b (free'Lift e t))).down =
      t.mapDomain (T.proj ∘ ι) :=
  by
  dsimp
  revert t
  rw [← Function.funext_iff]
  dsimp
  change ULift.down ∘ _ = _
  apply Finsupp.fun_ext
  · intros; simp only [Function.comp_apply, map_add, ULift.add_down, eq_self_iff_true, forall_const]
  · intros; simp only [Function.comp_apply, map_zero, ULift.zero_down, Finsupp.mapDomain_add]
  · intros
    simp only [Function.comp_apply, Finsupp.mapDomain_single, free'Lift_eq_finsupp_lift]
    dsimp [Profinite.condensedFreePfpngSpecialize]
    simp only [← comp_apply]
    erw [Limits.limit.lift_π]
    simp only [Finsupp.sum_single_index, zero_smul, one_zsmul]
    ext i
    dsimp [Profinite.condensedFreePfpngSpecializeCone, Finsupp.single, Profinite.freePfpngπ,
      Profinite.toFreePfpng]
    erw [ProFiltPseuNormGrp₁.limit_π_coe_eq]
    simp only [← comp_apply, Category.assoc]
    dsimp [Profinite.freePfpngLevelIso, Limits.IsLimit.conePointUniqueUpToIso]
    simp only [← comp_apply, Category.assoc]
    erw [(Limits.isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj 1)
          (Limits.limit.isLimit (S.fintype_diagram ⋙ freePfpngFunctor))).fac]
    erw [Limits.limit.lift_π]
    rfl

theorem Profinite.specialization_eq_zero_of_eq_zero (S B : Profinite.{u}) (b : B)
    (t : S.toCondensed.val.obj (op B) →₀ ℤ)
    (ht : free'Lift (S.toCondensedFreePfpng.val.app (op B)) t = 0) :
    (t.mapDomain fun f => (ULift.down f).1 b) = 0 :=
  by
  apply FreePfpng.discreteQuotient_separates_points' S
  intro T
  apply_fun fun e => S.condensed_free_pfpng_specialize B b e at ht 
  rw [AddMonoidHom.map_zero] at ht 
  apply_fun fun e =>
    Limits.limit.π (S.fintype_diagram ⋙ forget FintypeCat ⋙ AddCommGroupCat.free' ⋙ Ab.ulift) T e at
    ht 
  rw [AddMonoidHom.map_zero] at ht 
  apply_fun ULift.down at ht 
  dsimp [AddCommGroupCat.free']
  rw [← Finsupp.mapDomain_comp]
  have := S.mono_free'_to_condensed_free_pfpng_aux B b T t
  dsimp at this ; erw [← this]; exact ht

theorem Profinite.adj'_homEquiv_symm_eq_free'Lift (S B : Profinite.{u}) :
    (((AddCommGroupCat.adj'.whiskerRight Profinite.{u}ᵒᵖ).homEquiv S.toCondensed.val
                S.condensedFreePfpng.val).symm
            S.toCondensedFreePfpng.val).app
        (op B) =
      free'Lift (S.toCondensedFreePfpng.val.app (op B)) :=
  by
  ext u v; dsimp [free'Lift]
  simp only [Adjunction.homEquiv_counit, CategoryTheory.whiskeringRight_obj_map, NatTrans.comp_app,
    CategoryTheory.whiskerRight_app, Adjunction.whiskerRight_counit_app_app]

open scoped BigOperators

theorem Finsupp.mapDomain_ne_zero_of_ne_zero_of_injOn {α β γ : Type _} [AddCommGroup β] (t : α →₀ β)
    (ht : t ≠ 0) (f : α → γ) (hinj : Set.InjOn f t.support) : t.mapDomain f ≠ 0 :=
  by
  contrapose! ht
  have : ∀ (e : γ) (he : e ∈ (t.mapDomain f).support), ∃ (q : α) (hq : q ∈ t.support), f q = e :=
    by
    intro e he; by_contra c; push_neg at c 
    simp only [Finsupp.mem_support_iff, Ne.def] at he 
    apply he
    erw [Finset.sum_apply']
    apply Finset.sum_eq_zero
    intro a ha
    dsimp [Finsupp.single]; rw [if_neg]; apply c; exact ha
  choose q hq hh using this
  let ι : (t.mapDomain f).support → t.support := fun e => ⟨q e.1 e.2, hq e.1 e.2⟩
  have hι : Function.Surjective ι := by
    rintro ⟨e, he⟩; use f e
    · simp only [Finsupp.mem_support_iff, Ne.def]
      rw [Finsupp.mapDomain_apply' _ _ (Set.Subset.refl _) hinj he]
      simpa using he
    · ext; dsimp
      apply hinj; apply hq; apply he; apply hh
  have : (t.mapDomain f).support = ∅ := by simpa using ht
  suffices t.support = ∅ by simpa using this
  by_contra c; change _ ≠ _ at c 
  erw [← Finset.nonempty_iff_ne_empty] at c 
  obtain ⟨c, hc⟩ := c; obtain ⟨⟨c, hc⟩, ee⟩ := hι ⟨c, hc⟩
  rw [this] at hc ; simpa using hc

theorem Finsupp.lift_mapDomain {γ α β : Type _} [AddCommGroup β] (f : α → β) (ι : γ → α) :
    Finsupp.lift _ ℤ _ f ∘ Finsupp.mapDomain ι = Finsupp.lift _ ℤ _ (f ∘ ι) :=
  by
  apply Finsupp.fun_ext
  · intro x y
    dsimp only [Function.comp_apply]
    simp only [Finsupp.mapDomain_add]
    erw [((Finsupp.lift β ℤ α) f).toAddMonoidHom.map_add]; rfl
  · intro x y
    erw [((Finsupp.lift β ℤ γ) (f ∘ ι)).toAddMonoidHom.map_add]; rfl
  · intro x; simp

theorem Finsupp.lift_mapDomain_apply {γ α β : Type _} [AddCommGroup β] (f : α → β) (ι : γ → α)
    (e : γ →₀ ℤ) :
    (Finsupp.lift _ ℤ _ f).toAddMonoidHom (e.mapDomain ι) = Finsupp.lift _ ℤ _ (f ∘ ι) e := by
  rw [← Finsupp.lift_mapDomain]; rfl

theorem Finsupp.card_supp_mapDomain_lt {α β γ : Type _} [AddCommGroup γ] (f : α → β) (t : α →₀ γ)
    (u v : α) (huv : u ≠ v) (hu : u ∈ t.support) (hv : v ∈ t.support) (hf : f u = f v) :
    (t.mapDomain f).support.card < t.support.card := by
  classical
  have key : (Finsupp.mapDomain f t).support ⊆ _ := Finsupp.mapDomain_support
  have : (Finsupp.mapDomain f t).support.card ≤ (t.support.image f).card :=
    Finset.card_le_of_subset key
  refine' lt_of_le_of_lt this _
  have key' : (t.support.image f).card ≤ t.support.card := Finset.card_image_le
  apply lt_of_le_of_ne key'
  change ¬_
  rw [Finset.card_image_iff]
  dsimp [Set.InjOn]
  push_neg
  use u, hu, v, hv, hf

theorem Profinite.mono_free'_toCondensedFreePfpng_induction_aux (n : ℕ) :
    ∀ (S B : Profinite.{u}) (t : S.toCondensed.val.obj (op B) →₀ ℤ),
      t.support.card ≤ n →
        (free'Lift (S.toCondensedFreePfpng.val.app (op B))) t = 0 →
          (∀ b : ↥B,
              Finsupp.mapDomain (fun f : S.toCondensed.val.obj (op B) => (ULift.down f).1 b) t =
                0) →
            ∃ (α : Type u) (_inst_1 : Fintype α) (X : α → Profinite) (π : ∀ a : α, X a ⟶ B) (surj :
              ∀ b : ↥B, ∃ (a : α) (x : ↥(X a)), (π a) x = b),
              ∀ a : α, Finsupp.mapDomain (S.toCondensed.val.map (π a).op) t = 0 :=
  by
  /-
    TODO: This proof is very slow. It would be better to pull out a few
    of the `have` statements into separate lemmas to (hopefully)
    speed this up.
    -/
  induction n
  case zero =>
    intro S B t ht; simp at ht ; rw [ht]; intro h1 h2
    use PUnit, inferInstance, fun _ => B, fun _ => 𝟙 _
    constructor; · intro b; use PUnit.unit, b; rfl
    · intro _; rw [Finsupp.mapDomain_zero]
  case succ n hn =>
    intro S B t ht1 ht2 H
    by_cases ht1' : t.support.card = n + 1; swap
    · apply hn; exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne ht1 ht1')
      assumption'
    clear ht1
    let F := t.support
    let e : F → (B ⟶ S) := fun f => f.1.1
    obtain ⟨Q, h1, h2, ee, -⟩ :
      ∃ (α : Type u) (hα1 : Fintype α) (hα2 : LinearOrder α) (ee : α ≃ F), True := by
      refine'
        ⟨ULift (Fin (Fintype.card F)), inferInstance, IsWellOrder.linearOrder WellOrderingRel,
          equiv.ulift.trans (Fintype.equivFin _).symm, trivial⟩
    skip
    let E₀ := {a : Q × Q | a.1 < a.2}
    let X₀ : E₀ → Profinite.{u} := fun i => Profinite.equalizer (e (ee i.1.1)) (e (ee i.1.2))
    let π₀ : ∀ i : E₀, X₀ i ⟶ B := fun i => Profinite.equalizer.ι _ _
    have surj₀ : ∀ b : B, ∃ (e₀ : E₀) (x : X₀ e₀), π₀ _ x = b :=
      by
      intro b; specialize H b
      contrapose! H
      have key : ∀ (i j : Q) (h : i < j), e (ee i) b ≠ e (ee j) b :=
        by
        intro i j h; specialize H ⟨⟨i, j⟩, h⟩; intro c
        specialize H; dsimp [X₀] at H ; specialize H ⟨b, c⟩
        apply H; rfl
      apply Finsupp.mapDomain_ne_zero_of_ne_zero_of_injOn
      · intro c; rw [c] at ht1' ; simpa using ht1'
      · intro x hx y hy hxy; dsimp at hxy 
        let i : Q := ee.symm ⟨x, hx⟩
        let j : Q := ee.symm ⟨y, hy⟩
        rcases lt_trichotomy i j with (hhh | hhh | hhh)
        · specialize key i j hhh; contrapose hxy; convert key
          · dsimp [i]; rw [ee.apply_symm_apply]; rfl
          · dsimp [j]; rw [ee.apply_symm_apply]; rfl
        · apply_fun fun q => (ee q).1 at hhh ; dsimp [i, j] at hhh 
          simp_rw [ee.apply_symm_apply] at hhh ; exact hhh
        · specialize key j i hhh; contrapose hxy; convert key.symm
          · dsimp [j]; rw [ee.apply_symm_apply]; rfl
          · dsimp [i]; rw [ee.apply_symm_apply]; rfl
    let f₀ : ∀ i : E₀, S.to_Condensed.val.obj (op B) → S.to_Condensed.val.obj (op (X₀ i)) :=
      fun i => S.to_Condensed.val.map (π₀ i).op
    let t₀ : ∀ i : E₀, S.to_Condensed.val.obj (op (X₀ i)) →₀ ℤ := fun i => t.mapDomain (f₀ i)
    have card₀ : ∀ i : E₀, (t₀ i).support.card ≤ n :=
      by
      intro i; suffices (t₀ i).support.card < n + 1 by exact nat.lt_succ_iff.mp this
      rw [← ht1']
      fapply Finsupp.card_supp_mapDomain_lt
      refine' (ee i.1.1).1
      refine' (ee i.1.2).1
      · change ¬_
        erw [← Subtype.ext_iff]
        apply ee.injective.ne
        apply ne_of_lt
        exact i.2
      refine' (ee i.1.1).2
      refine' (ee i.1.2).2
      · dsimp [f₀, π₀, Profinite.toCondensed]; ext1; dsimp
        -- missing Profinite.equalizer.condition
        ext t;
        exact t.2
    have lift₀ : ∀ i : E₀, free'Lift (S.to_condensed_free_pfpng.val.app (op (X₀ i))) (t₀ i) = 0 :=
      by
      intro i; rw [free'Lift_eq_finsupp_lift]; dsimp only [t₀, f₀]
      apply_fun fun q => S.condensed_free_pfpng.val.map (π₀ i).op q at ht2 
      rw [AddMonoidHom.map_zero, free'Lift_eq_finsupp_lift] at ht2 
      convert ht2
      rw [Finsupp.lift_mapDomain_apply]
      dsimp [Finsupp.lift]
      rw [(S.condensed_free_pfpng.val.map (π₀ i).op).map_finsupp_sum]
      rfl
    have map₀ :
      ∀ (i : E₀) (b : ↥(X₀ i)),
        Finsupp.mapDomain (fun f : S.to_Condensed.val.obj (op (X₀ i)) => f.down.toFun b) (t₀ i) =
          0 :=
      by
      intro i b; dsimp [t₀]; rw [← Finsupp.mapDomain_comp]
      exact H (π₀ i b)
    have key := fun i => hn S (X₀ i) (t₀ i) (card₀ i) (lift₀ i) (map₀ i)
    choose A hA X₁ π₁ surj₁ key using key; skip
    let E := Σ e : E₀, A e
    let X : E → Profinite.{u} := fun i => X₁ i.1 i.2
    let π : ∀ e : E, X e ⟶ B := fun e => π₁ e.1 e.2 ≫ π₀ e.1
    use E, inferInstance, X, π; constructor
    · intro b
      obtain ⟨e₀, x, hx⟩ := surj₀ b
      obtain ⟨i, q, hq⟩ := surj₁ e₀ x
      use⟨e₀, i⟩, q; dsimp [π]; rw [hq, hx]
    · intro a
      dsimp [π]; rw [Functor.map_comp]
      erw [Finsupp.mapDomain_comp]
      apply key

instance Profinite.mono_free'ToCondensedFreePfpng (S : Profinite.{u}) :
    Mono S.free'ToCondensedFreePfpng :=
  by
  apply presheaf_to_condensed_ab_map_mono_of_exists; intro B t ht
  let e : S.to_Condensed.val.obj (op B) → S.condensed_free_pfpng.val.obj (op B) := fun f =>
    S.to_condensed_free_pfpng.val.app (op B) f
  dsimp at t ht 
  replace ht : free'Lift e t = 0; · rwa [← S.adj'_hom_equiv_symm_eq_free'_lift]
  let ι : ∀ b : B, S.to_Condensed.val.obj (op B) → S := fun b f => (ULift.down f).1 b
  have aux : ∀ b : B, t.mapDomain (ι b) = 0 := fun b =>
    S.specialization_eq_zero_of_eq_zero B b t ht
  dsimp
  apply Profinite.mono_free'_toCondensedFreePfpng_induction_aux
  rfl
  assumption'

