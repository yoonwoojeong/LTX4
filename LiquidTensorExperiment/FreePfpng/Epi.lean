import LiquidTensorExperiment.FreePfpng.Setup

#align_import free_pfpng.epi

noncomputable section

open scoped Classical BigOperators

open CategoryTheory

open Opposite

universe u

instance condensedAbToCondensedSet_faithful : Faithful condensedAbToCondensedSet
    where map_injective' := by
    intro X Y f g h; ext W t : 4
    apply_fun fun e => e.val.app W t at h ; dsimp at h 
    exact h

theorem CategoryTheory.epi_to_colimit_of_exists {J : Type u} [SmallCategory J] {C : Type _}
    [Category.{u} C] {F : J ⥤ C} (T : C) (E : Limits.Cocone F) (hE : Limits.IsColimit E)
    (f : T ⟶ E.pt)
    (h : ∀ j : J, ∃ (Z : C) (p : Z ⟶ T) (q : Z ⟶ F.obj j) (hq : Epi q), q ≫ E.ι.app j = p ≫ f) :
    Epi f := by
  constructor; intro W a b hh
  apply hE.hom_ext; intro j; specialize h j
  obtain ⟨Z, p, q, hq, w⟩ := h; skip
  rw [← cancel_epi q]; simp_rw [← category.assoc, w, category.assoc, hh]

theorem epi_profiniteToCondensed_map_of_epi {X Y : Profinite.{u}} (f : X ⟶ Y) [hf : Epi f] :
    Epi (profiniteToCondensed.map f) := by
  constructor; intro Z a b h; ext W q : 34; induction W using Opposite.rec'
  have hZ := Z.2
  rw [is_sheaf_iff_is_sheaf_of_type] at hZ 
  rw [Z.val.is_proetale_sheaf_of_types_tfae.out 0 1] at hZ 
  let q' := q.down
  dsimp at q q' 
  dsimp [functor.is_proetale_sheaf_of_types] at hZ 
  specialize hZ PUnit W (fun _ => Profinite.pullback f q') (fun _ => Profinite.pullback.snd _ _) _ _
  · intro w
    rw [Profinite.epi_iff_surjective] at hf 
    obtain ⟨x, hx⟩ := hf (q' w)
    refine' ⟨PUnit.unit, ⟨(x, w), hx⟩, rfl⟩
  · intro i; dsimp; refine' Z.val.map _ (b.val.app (op W) q)
    refine' Quiver.Hom.op _; exact Profinite.pullback.snd _ _
  specialize hZ _
  · clear hZ
    rintro ⟨⟩ ⟨⟩ S g₁ g₂ H; dsimp only at H 
    apply_fun fun φ => Z.val.map φ.op (b.val.app (op W) q) at H 
    simp only [op_comp, Z.val.map_comp] at H ; exact H
  obtain ⟨t, ht1, ht2⟩ := hZ
  have : b.val.app (op W) q = t := by
    apply ht2
    intro i; rfl
  rw [this]; apply ht2
  intro i; dsimp
  change (a.val.app (op W) ≫ Z.val.map _) q = (b.val.app (op W) ≫ Z.val.map _) q
  simp only [← nat_trans.naturality]
  dsimp
  apply_fun fun e => Profinite_to_Condensed.map (Profinite.pullback.fst f q') ≫ e at h 
  apply_fun fun e => e.val.app (op (Profinite.pullback f q')) at h 
  dsimp at h 
  let i : (Profinite.pullback f q').toCondensed.val.obj (op (Profinite.pullback f q')) :=
    ULift.up (𝟙 _)
  apply_fun fun e => e i at h 
  dsimp [ulift_functor] at h 
  convert h
  all_goals
    ext1
    dsimp [Profinite.toCondensed]
    simp only [category.id_comp, Profinite.pullback.condition]

/-
inductive pmz : set ℤ
| neg_one : pmz (-1)
| zero : pmz 0
| one : pmz 1

def pmz_eq : pmz = {0,1,-1} :=
begin
  ext, split,
  { intros h, cases h, right, right, simpa, left, simp, right, left, simp },
  { intros h, simp at h, rcases h with (rfl|rfl|rfl),
    apply pmz.zero,
    apply pmz.one,
    apply pmz.neg_one }
end

lemma pmz_finite : set.finite pmz :=
by simp [pmz_eq]

instance fintype_pmz : fintype pmz := pmz_finite.fintype
-/
--abbreviation Profinite.pow (S : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
--Profinite.product (λ i : fin n, S)
/-- `S.pmz n` is `(S × {-1,0,1})^n`. -/
def Profinite.pmz (S : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
  Profinite.sigma fun x : ULift.{u} (Fin n → SignType) => S.pow n

/-- the canonical map of condensed sets `(S × {-1,0,1})^n ⟶ ℤ[S]` -/
def Profinite.pmzToFree' (S : Profinite.{u}) (n : ℕ) :
    (S.pmz n).toCondensed ⟶ condensedAbToCondensedSet.obj S.free' :=
  (Profinite.toCondensedEquiv (S.pmz n) (condensedAbToCondensedSet.obj S.free')).symm <|
    (CondensedSet.valObjSigmaEquiv (fun f : ULift.{u} (Fin n → SignType) => S.pow n)
          (condensedAbToCondensedSet.obj S.free')).symm
      fun f : ULift.{u} (Fin n → SignType) =>
      let e := proetaleTopology.toSheafify (S.toCondensed.val ⋙ AddCommGroupCat.free')
      e.app (op <| S.pow n) <|
        ∑ i : Fin n, Finsupp.single (ULift.up <| Profinite.product.π _ i) (f.down i : ℤ)

def Profinite.pmzFunctor (n : ℕ) : Profinite.{u} ⥤ Profinite.{u}
    where
  obj S := S.pmz n
  map S T f :=
    Profinite.sigma.desc _ fun e =>
      (Profinite.product.lift (fun i : Fin n => T) fun i => Profinite.product.π _ i ≫ f) ≫
        Profinite.sigma.ι _ e
  map_id' := by
    intro X
    apply Profinite.sigma.hom_ext; intro e
    erw [category.comp_id]; rfl
  map_comp' := by
    intro X Y Z f g
    apply Profinite.sigma.hom_ext; intro e; dsimp; simp
    erw [Profinite.sigma.ι_desc]
    rfl

def Profinite.pmzDiagram (S : Profinite.{u}) (n : ℕ) : DiscreteQuotient S ⥤ Profinite.{u} :=
  S.diagram ⋙ Profinite.pmzFunctor n

def Profinite.pmzCone (S : Profinite.{u}) (n : ℕ) : Limits.Cone (S.pmzDiagram n) :=
  (Profinite.pmzFunctor n).mapCone S.asLimitCone

def Profinite.sigmaFunctor {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u}) (α : Type u)
    [Fintype α] : J ⥤ Profinite.{u}
    where
  obj j := Profinite.sigma fun a : α => F.obj j
  map i j e := Profinite.sigma.desc _ fun a => F.map e ≫ Profinite.sigma.ι _ a
  map_id' := by
    intro j; apply Profinite.sigma.hom_ext; intro a
    simp
  map_comp' := by
    intro i j k e f
    apply Profinite.sigma.hom_ext; intro a
    simp

def Profinite.sigmaCone {J : Type u} [SmallCategory J] {F : J ⥤ Profinite.{u}} (α : Type u)
    [Fintype α] (E : Limits.Cone F) : Limits.Cone (Profinite.sigmaFunctor F α)
    where
  pt := Profinite.sigma fun a : α => E.pt
  π :=
    { app := fun j => Profinite.sigma.desc _ fun a => E.π.app j ≫ Profinite.sigma.ι _ a
      naturality' := by
        intro i j e; dsimp
        apply Profinite.sigma.hom_ext; intro a
        simp; dsimp [Profinite.sigmaFunctor]; simp }

def Profinite.sigmaToLimit {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u}) (α : Type u)
    [Fintype α] (E : Limits.Cone F) :
    (Profinite.sigmaCone α E).pt ⟶ (Profinite.limitCone (Profinite.sigmaFunctor F α)).pt :=
  Profinite.sigma.desc _ fun a =>
    (Profinite.limitConeIsLimit (Profinite.sigmaFunctor F α)).lift
      ⟨E.pt,
        { app := fun j => E.π.app j ≫ Profinite.sigma.ι _ a
          naturality' := by
            intro i j e; dsimp [Profinite.sigmaFunctor]
            simp }⟩

theorem Profinite.exists_of_sigma_limit {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u})
    (α : Type u) [Fintype α] [IsCofiltered J]
    (t : (Profinite.limitCone (Profinite.sigmaFunctor F α)).pt) :
    ∃ (a₀ : α) (t₀ : (Profinite.limitCone F).pt),
      ∀ j : J,
        Profinite.sigma.ι _ a₀ ((Profinite.limitCone F).π.app j t₀) =
          (Profinite.limitCone (Profinite.sigmaFunctor F α)).π.app j t :=
  by
  rcases t with ⟨t, ht⟩; dsimp at ht 
  obtain ⟨j₀⟩ : Nonempty J := is_cofiltered.nonempty
  let a₀ := (t j₀).1; use a₀
  have h1 : ∀ ⦃i j : J⦄ (f : i ⟶ j), (t i).1 = (t j).1 :=
    by
    intro i j e; specialize ht e
    apply_fun fun q => q.1 at ht 
    cases t i; exact ht
  have h2 : ∀ j : J, (t j).1 = a₀ := by
    intro j
    let j₁ := is_cofiltered.min j j₀
    rw [← h1 (is_cofiltered.min_to_left j j₀)]; dsimp [a₀]
    rw [← h1 (is_cofiltered.min_to_right j j₀)]
  let t₀ : (Profinite.limitCone F).pt := ⟨_, _⟩
  rotate_left
  · intro j; exact (t j).2
  · intro i j e
    specialize ht e
    cases t i
    dsimp [Profinite.sigmaFunctor, Profinite.sigma.desc, Profinite.sigma.ι] at ht 
    cases t j
    erw [Sigma.mk.inj_iff] at ht 
    exact eq_of_hEq ht.2
  use t₀
  intro j
  dsimp [Profinite.limitCone, Profinite.sigmaFunctor, Profinite.sigma.ι, Profinite.sigma.desc,
    CompHaus.limitCone, TopCat.limitCone]
  ext
  exact (h2 _).symm; rfl

theorem Profinite.bijective_sigmaToLimit {J : Type u} [SmallCategory J] (F : J ⥤ Profinite.{u})
    (α : Type u) [Fintype α] (E : Limits.Cone F) (hE : Limits.IsLimit E) [IsCofiltered J] :
    Function.Bijective (Profinite.sigmaToLimit F α E) :=
  by
  constructor
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    dsimp [Profinite.sigmaToLimit, Profinite.sigma.desc, Profinite.limitConeIsLimit,
      CompHaus.limitConeIsLimit, TopCat.limitConeIsLimit] at h 
    apply_fun fun e => e.1 at h 
    have hh := h
    obtain ⟨j₀⟩ : Nonempty J := is_cofiltered.nonempty
    apply_fun fun e => (e j₀).1 at h ; dsimp [Profinite.sigma.ι] at h 
    subst h; ext; rfl
    apply hEq_of_eq
    apply limits.concrete.is_limit_ext _ hE
    intro jj; apply_fun fun e => e jj at hh 
    erw [Sigma.mk.inj_iff] at hh 
    exact eq_of_hEq hh.2
  · rintro t
    obtain ⟨a, s, ht⟩ := Profinite.exists_of_sigma_limit F α t
    use a;
    let EE : E.X ≅ (Profinite.limitCone F).pt :=
      hE.cone_point_unique_up_to_iso (Profinite.limitConeIsLimit _)
    use EE.inv s; dsimp; ext j : 2
    convert ht j; ext; rfl
    apply hEq_of_eq
    change (hE.lift (Profinite.limitCone F) ≫ E.π.app j) s = _
    rw [hE.fac]; rfl

theorem Profinite.isIso_lift_sigmaCone {J : Type u} [SmallCategory J] {F : J ⥤ Profinite.{u}}
    (α : Type u) [Fintype α] [IsCofiltered J] (E : Limits.Cone F) (hE : Limits.IsLimit E) :
    IsIso ((Profinite.limitConeIsLimit _).lift (Profinite.sigmaCone α E)) :=
  by
  apply Profinite.isIso_of_bijective
  convert Profinite.bijective_sigmaToLimit F α E hE
  symm
  apply (Profinite.limitConeIsLimit (Profinite.sigmaFunctor F α)).uniq
  intro j
  apply Profinite.sigma.hom_ext
  intro a; rfl

def Profinite.sigmaConeIsLimit {J : Type u} [SmallCategory J] {F : J ⥤ Profinite.{u}} (α : Type u)
    [Fintype α] [IsCofiltered J] (E : Limits.Cone F) (hE : Limits.IsLimit E) :
    Limits.IsLimit (Profinite.sigmaCone α E) :=
  by
  haveI : is_iso ((Profinite.limitConeIsLimit _).lift (Profinite.sigmaCone α E)) :=
    Profinite.isIso_lift_sigmaCone α E hE
  apply limits.is_limit.of_point_iso (Profinite.limitConeIsLimit _)
  assumption

def Profinite.pmzToLimit (S : Profinite.{u}) (n : ℕ) :
    S.pmz n ⟶ (Profinite.limitCone (S.pmzDiagram n)).pt :=
  Profinite.sigma.desc _ fun f =>
    (Profinite.limitConeIsLimit (S.pmzDiagram n)).lift
      ⟨S.pow n,
        { app := fun T => Profinite.mapPow (S.asLimitCone.π.app T) n ≫ Profinite.sigma.ι _ f
          naturality' := by
            intro A B e
            dsimp [Profinite.pmzDiagram, Profinite.pmzFunctor]
            simpa }⟩

def Profinite.powFunctor (n : ℕ) : Profinite.{u} ⥤ Profinite.{u}
    where
  obj S := S.pow n
  map S T f := Profinite.mapPow f n
  map_id' := by intro X; apply Profinite.product.hom_ext; intro i; dsimp [Profinite.mapPow]; simp
  map_comp' := by
    intro X Y Z f g
    apply Profinite.product.hom_ext; intro i; dsimp [Profinite.mapPow]; simp

def Profinite.powCone {J : Type u} [SmallCategory J] {F : J ⥤ Profinite.{u}} (E : Limits.Cone F)
    (n : ℕ) : Limits.Cone (F ⋙ Profinite.powFunctor n) :=
  (Profinite.powFunctor n).mapCone E

def Profinite.powConeIsLimit {J : Type u} [SmallCategory J] {F : J ⥤ Profinite.{u}}
    (E : Limits.Cone F) (hE : Limits.IsLimit E) (n : ℕ) : Limits.IsLimit (Profinite.powCone E n)
    where
  lift Q :=
    Profinite.product.lift _ fun a =>
      hE.lift
        ⟨Q.pt,
          { app := fun j => Q.π.app j ≫ Profinite.product.π _ a
            naturality' := by
              intro i j e; dsimp
              simp only [category.id_comp, category.assoc]
              rw [← Q.w e]
              dsimp [Profinite.powFunctor, Profinite.mapPow]
              simp }⟩
  fac := by
    intro Q j; apply Profinite.product.hom_ext; intro i
    dsimp [Profinite.powCone, Profinite.powFunctor, Profinite.mapPow]
    simp only [category.assoc, Profinite.product.lift_π, Profinite.product.lift_π_assoc,
      limits.is_limit.fac]
  uniq := by
    intro Q m hm
    apply Profinite.product.hom_ext; intro a
    dsimp [Profinite.powCone, Profinite.powFunctor, Profinite.mapPow]
    simp only [Profinite.product.lift_π]
    apply hE.hom_ext
    intro j
    simp only [category.assoc, limits.is_limit.fac]; rw [← hm]
    dsimp [Profinite.powCone, Profinite.powFunctor, Profinite.mapPow]
    simp only [category.assoc, Profinite.product.lift_π]

theorem Profinite.isIso_pmzToLimit (S : Profinite.{u}) (n : ℕ) : IsIso (S.pmzToLimit n) :=
  by
  let E := Profinite.sigmaCone (ULift.{u} (Fin n → SignType)) (Profinite.powCone S.as_limit_cone n)
  let hE : limits.is_limit E :=
    Profinite.sigmaConeIsLimit _ _ (Profinite.powConeIsLimit _ S.as_limit n)
  let q : E.X ≅ (Profinite.limitCone (S.pmz_diagram n)).pt :=
    hE.cone_point_unique_up_to_iso (Profinite.limitConeIsLimit _)
  have : is_iso q.hom := inferInstance
  convert this
  apply Profinite.sigma.hom_ext; intro e
  apply (Profinite.limitConeIsLimit _).hom_ext
  intro T
  rfl

def Profinite.pmzConeIsLimit (S : Profinite.{u}) (n : ℕ) : Limits.IsLimit (S.pmzCone n) :=
  by
  apply limits.is_limit.of_point_iso (Profinite.limitConeIsLimit _)
  convert Profinite.isIso_pmzToLimit S n
  apply Profinite.sigma.hom_ext; intro a
  apply (Profinite.limitConeIsLimit _).hom_ext; intro j
  rfl

-- A finite product of finite discrete sets is discrete.
instance Profinite.discreteTopology_pow (S : Profinite.{u}) [DiscreteTopology S] (n : ℕ) :
    DiscreteTopology (S.pow n) :=
  Pi.discreteTopology

-- A finite union of finite products of finite discrete sets is discrete.
instance Profinite.discreteTopology_pmz (S : Profinite.{u}) [DiscreteTopology S] (n : ℕ) :
    DiscreteTopology (S.pmz n) :=
  Sigma.discreteTopology

-- move this
theorem SignType.nnnorm_coe_int_le_one : ∀ i : SignType, ‖i : ℤ‖₊ ≤ 1
  | SignType.zero => by erw [nnnorm_zero]; exact zero_le'
  | SignType.neg => by simp
  | SignType.pos => by erw [nnnorm_one]

def Profinite.pmzToLevelComponent (S : Profinite.{u}) (j : NNReal) (T : DiscreteQuotient S)
    (e : Fin ⌊j⌋₊ → SignType) :
    (Profinite.of ↥T).pow ⌊j⌋₊ ⟶
      (ProFiltPseuNormGrp₁.level.obj j).obj (freePfpngFunctor.obj (FintypeCat.of ↥T))
    where
  toFun t :=
    { val := ∑ i : Fin ⌊j⌋₊, fun s => if t i = s then (e i : ℤ) else 0
      property :=
        by
        have : (∑ i : Fin ⌊j⌋₊, ∑ s : T, if t i = s then (1 : NNReal) else 0) ≤ j :=
          by
          calc
            _ ≤ ∑ i : Fin ⌊j⌋₊, (1 : NNReal) := _
            _ ≤ j := _
          · apply Finset.sum_le_sum; rintro i -; apply le_of_eq
            erw [Finset.sum_eq_single_of_mem (t i : T) (@Finset.mem_univ T _ _), if_pos rfl]
            rintro s - hs; rw [if_neg hs.symm]
          · simp only [Finset.sum_const, Finset.card_fin, Nat.smul_one_eq_coe]
            exact Nat.floor_le zero_le'
        apply PseudoNormedGroup.filtration_mono this
        apply PseudoNormedGroup.sum_mem_filtration
        rintro i -
        apply Finset.sum_le_sum
        rintro s -
        dsimp
        split_ifs
        · apply SignType.nnnorm_coe_int_le_one
        · rw [nnnorm_zero] }
  continuous_toFun := continuous_of_discreteTopology

def Profinite.pmzToLevel (S : Profinite.{u}) (j : NNReal) (T : DiscreteQuotient S) :
    (Profinite.of T).pmz ⌊j⌋₊ ⟶
      (ProFiltPseuNormGrp₁.level.obj j).obj (freePfpngFunctor.obj <| FintypeCat.of T) :=
  Profinite.sigma.desc _ fun e => S.pmzToLevelComponent j T (ULift.down e)

theorem Profinite.pmz_to_level_nat_trans_aux (S : Profinite.{u}) (j : NNReal)
    (T₁ T₂ : DiscreteQuotient S) (f : T₁ ⟶ T₂) (e : Fin ⌊j⌋₊ → SignType)
    (t : (Profinite.of T₁).pow ⌊j⌋₊) (s : T₂) :
    (∑ i : Fin ⌊j⌋₊, fun s : T₂ => ite (S.fintypeDiagram.map f (t i) = s) (e i : ℤ) 0) s =
      (@Finset.filter (@Bundled.α Fintype (S.fintypeDiagram.obj T₁))
            (fun w : T₁ => S.fintypeDiagram.map f w = s)
            (fun a : @Bundled.α Fintype (S.fintypeDiagram.obj T₁) => Classical.propDecidable _)
            (@Finset.univ (@Bundled.α Fintype (S.fintypeDiagram.obj T₁))
              (@FintypeCat.fintype (S.fintypeDiagram.obj T₁)))).Sum
        (∑ i : Fin ⌊j⌋₊, fun s : T₁ => @ite ℤ (t i = s) _ (↑(e i)) 0) :=
  by
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine' Finset.sum_congr rfl _
  rintro i -
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff]

def Profinite.pmzToLevelNatTrans (S : Profinite.{u}) (j : NNReal) :
    S.pmzDiagram ⌊j⌋₊ ⟶ (S.fintypeDiagram ⋙ freePfpngFunctor) ⋙ ProFiltPseuNormGrp₁.level.obj j
    where
  app T := S.pmzToLevel j T
  naturality' := by
    intro T₁ T₂ f
    dsimp [Profinite.pmzDiagram, Profinite.pmzToLevel, Profinite.pmzFunctor]
    apply Profinite.sigma.hom_ext
    rintro ⟨e⟩
    simp only [Profinite.sigma.ι_desc_assoc, category.assoc, Profinite.sigma.ι_desc]
    ext t s
    exact Profinite.pmz_to_level_nat_trans_aux S j T₁ T₂ f e t s

def Profinite.pmzToFreePfpng (S : Profinite.{u}) (j : NNReal) :
    S.pmz ⌊j⌋₊ ⟶ (ProFiltPseuNormGrp₁.level.obj j).obj S.FreePfpng :=
  let E :=
    Limits.isLimitOfPreserves (ProFiltPseuNormGrp₁.level.obj j)
      (Limits.limit.isLimit (S.fintypeDiagram ⋙ freePfpngFunctor))
  E.map (S.pmzCone _) (S.pmzToLevelNatTrans j)

theorem Profinite.IsLimit.surjective_of_surjective {J : Type u} [SmallCategory J]
    (F G : J ⥤ Profinite.{u}) (α : F ⟶ G) (cF : Limits.Cone F) (cG : Limits.Cone G)
    (hcF : Limits.IsLimit cF) (hcG : Limits.IsLimit cG) [IsCofiltered J]
    (surj : ∀ j : J, Function.Surjective ⇑(α.app j)) :
    Function.Surjective ⇑(Limits.IsLimit.map cF hcG α) :=
  by
  have :=
    CompHaus.IsLimit.surjective_of_surjective (F ⋙ profiniteToCompHaus) (G ⋙ profiniteToCompHaus)
      (whisker_right α _) (Profinite_to_CompHaus.map_cone cF) (Profinite_to_CompHaus.map_cone cG)
      (limits.is_limit_of_preserves _ hcF) (limits.is_limit_of_preserves _ hcG) surj
  change Function.Surjective (Profinite_to_CompHaus.map (limits.is_limit.map cF hcG α))
  convert this
  apply hcG.hom_ext; intro j
  simp only [limits.is_limit.map_π, iso.trans_hom, iso.symm_hom, functor.map_iso_hom,
    limits.is_limit.unique_up_to_iso_hom, limits.cone.category_comp_hom,
    limits.is_limit.lift_cone_morphism_hom, limits.limit.is_limit_lift,
    limits.cones.functoriality_map_hom, profiniteToCompHaus_map]
  erw [category.assoc, category.assoc]
  erw [hcG.fac]
  have := (lifted_limit_maps_to_original (limits.limit.is_limit (G ⋙ profiniteToCompHaus))).inv.w j
  erw [this]
  dsimp;
  simp only [limits.limit.lift_π, limits.cones.postcompose_obj_π, nat_trans.comp_app,
    functor.map_cone_π_app, profiniteToCompHaus_map, whisker_right_app]
  rfl

section

variable {α : Type _} [DecidableEq α] [Nonempty α]

open Finset

-- TODO: Inlining this yields an app-builder exception
theorem exists_signed_sum_aux {n : ℕ} (sgn : ℕ → SignType) (b : α) [DecidableEq α] {f : α → ℤ}
    ⦃a : α⦄ (g : ℕ → α) (i : ℕ) :
    ite ((range (n - (f a).natAbs)).piecewise g (fun _ => a) i = b)
        ((range (n - (f a).natAbs)).piecewise sgn (fun _ => SignType.sign (f a)) i : ℤ) 0 =
      (range (n - (f a).natAbs)).piecewise (fun j => ite (g j = b) (↑(sgn j)) 0)
        (fun j => ite (a = b) (↑(SignType.sign (f a))) 0) i :=
  by unfold piecewise; split_ifs <;> rfl

-- switch to the version in mathlib
theorem Refactor.exists_signed_sum (s : Finset α) (n : ℕ) (f : α → ℤ)
    (hn : ∑ i in s, (f i).natAbs ≤ n) :
    ∃ (sgn : ℕ → SignType) (g : ℕ → α),
      (∀ i, g i ∉ s → sgn i = 0) ∧
        ∀ a ∈ s, (∑ i in range n, if g i = a then (sgn i : ℤ) else 0) = f a :=
  by
  induction' s using Finset.cons_induction with a s ha ih generalizing n
  · exact ⟨0, Classical.arbitrary _, fun _ _ => rfl, fun _ => False.elim⟩
  rw [sum_cons] at hn 
  obtain ⟨sgn, g, hg, hf⟩ := ih _ (le_tsub_of_add_le_left hn)
  refine'
    ⟨(range <| n - (f a).natAbs).piecewise sgn fun _ => SignType.sign (f a),
      (range <| n - (f a).natAbs).piecewise g fun _ => a, fun i hi => _, fun b hb => _⟩
  · by_cases i ∈ range (n - (f a).natAbs)
    · rw [piecewise_eq_of_mem _ _ _ h] at hi ⊢
      exact hg _ fun h => hi <| subset_cons _ h
    · rw [piecewise_eq_of_not_mem _ _ _ h] at hi 
      exact (hi <| mem_cons_self _ _).elim
  trans
    ∑ i in range n,
      (range <| n - (f a).natAbs).piecewise (fun j => ite (g j = b) (sgn j : ℤ) 0)
        (fun j => ite (a = b) (SignType.sign <| f a) 0) i
  · exact sum_congr rfl fun i _ => exists_signed_sum_aux _ _ _ _
  rw [sum_piecewise, (inter_eq_right_iff_subset _ _).2 (range_mono tsub_le_self)]
  rw [mem_cons] at hb 
  obtain rfl | hb := hb
  · rw [sum_eq_zero, zero_add, sum_const, if_pos rfl, card_sdiff (range_mono tsub_le_self),
      card_range, card_range, tsub_tsub_cancel_of_le (le_of_add_le_left hn), nsmul_eq_mul, mul_comm,
      ← Int.sign_eq_sign, (f b).sign_mul_natAbs]
    refine' fun i hi => ite_eq_right_iff.2 _
    rintro rfl
    rw [hg _ ha, SignType.coe_zero]
  · simp_rw [if_neg (ne_of_mem_of_not_mem hb ha).symm, hf _ hb, sum_const_zero, add_zero]

theorem Profinite.pmz_to_free_pfpng_epi_aux' [Fintype α] (r : NNReal) (f : α → ℤ)
    (hf : ∑ i : α, ‖f i‖₊ ≤ r) :
    ∃ (sgn : ℕ → SignType) (g : ℕ → α),
      ∀ t, (∑ i in range ⌊r⌋₊, if g i = t then (sgn i : ℤ) else 0) = f t :=
  by
  refine' Exists₂.imp (fun _ _ h t => _) (Refactor.exists_signed_sum univ ⌊r⌋₊ f _)
  · exact h.2 t (mem_univ _)
  refine' Nat.le_floor _
  simp_rw [Nat.cast_sum, NNReal.coe_natAbs]
  exact hf

theorem Profinite.pmz_to_free_pfpng_epi_aux [Fintype α] (r : NNReal) (f : α → ℤ)
    (hf : ∑ i : α, ‖f i‖₊ ≤ r) :
    ∃ (sgn : Fin ⌊r⌋₊ → SignType) (g : Fin ⌊r⌋₊ → α),
      (∑ i : Fin ⌊r⌋₊, fun t : α => if g i = t then (sgn i : ℤ) else 0) = f :=
  by
  obtain ⟨e, g, h⟩ := Profinite.pmz_to_free_pfpng_epi_aux' r f hf
  let e' : Fin ⌊r⌋₊ → SignType := fun i => e i.1
  let g' : Fin ⌊r⌋₊ → α := fun i => g i.1
  use e', g'
  ext t; rw [← h]
  simp only [Finset.sum_apply]
  rw [Finset.sum_range]; rfl

end

-- Move this
instance DiscreteQuotient.nonempty (X : Type _) [TopologicalSpace X] [h : Nonempty X]
    (T : DiscreteQuotient X) : Nonempty T :=
  ⟨T.proj (Nonempty.some h)⟩

instance Profinite.pmzToFreePfpng_epi (S : Profinite.{u}) [Nonempty S] (j : NNReal) :
    Epi (S.pmzToFreePfpng j) := by
  rw [Profinite.epi_iff_surjective]
  dsimp only [Profinite.pmzToFreePfpng]
  have :=
    Profinite.IsLimit.surjective_of_surjective _ _ (S.pmz_to_level_nat_trans j) (S.pmz_cone _)
      ((ProFiltPseuNormGrp₁.level.obj j).mapCone (limits.limit.cone _)) (S.pmz_cone_is_limit _)
      (limits.is_limit_of_preserves _ (limits.limit.is_limit _))
  apply this
  intro T
  rintro ⟨f : T → ℤ, hf : ∑ i : T, _ ≤ _⟩
  obtain ⟨e, t, ht⟩ := Profinite.pmz_to_free_pfpng_epi_aux j f hf
  change ∃ a : Σ i, Fin ⌊j⌋₊ → T, _
  use ULift.up e; use t; apply Subtype.ext
  dsimp [Profinite.pmzToLevelNatTrans, Profinite.pmzToLevel, Profinite.sigma.desc,
    Profinite.pmzToLevelComponent]
  exact ht

namespace Profinite.EpiFree'ToCondensedSetup

variable (S : Profinite.{u}) (j : NNReal)

theorem free'Lift_app_eq (A : Condensed.{u} Ab.{u + 1})
    (η : S.toCondensed ⟶ condensedAbToCondensedSet.obj A) (T : Profinite.{u}) :
    (proetaleTopology.toSheafify _).app _ ≫ (S.free'Lift η).val.app (op T) =
      free'Lift (η.val.app _) :=
  by
  dsimp [Profinite.free'Lift]
  rw [← nat_trans.comp_app, proetale_topology.to_sheafify_sheafify_lift]
  dsimp [adjunction.whisker_right, free'Lift]; simp

theorem free'Lift_app_eq' (A : Condensed.{u} Ab.{u + 1})
    (η : S.toCondensed ⟶ condensedAbToCondensedSet.obj A) (T : Profinite.{u}) :
    (proetaleTopology.toSheafify _).app _ ≫ (S.free'Lift η).val.app (op T) =
      ((Finsupp.lift (↥(A.val.obj (op T))) ℤ
            (((sheafToPresheaf proetaleTopology (Type (u + 1))).obj S.toCondensed).obj (op T)))
          (η.val.app (op T))).toAddMonoidHom :=
  by rw [free'_lift_app_eq]; rw [free'Lift_eq_finsupp_lift]

instance (A : Condensed.{u} Ab.{u + 1}) (T) :
    AddCommGroup ((condensedAbToCondensedSet.obj A).val.obj T) :=
  show AddCommGroup (A.val.obj T) by infer_instance

theorem freePfpng_ext (u v : S.FreePfpng)
    (huv : ∀ T : DiscreteQuotient S, S.freePfpngπ T u = S.freePfpngπ T v) : u = v :=
  by
  let E : limits.cone (S.fintype_diagram ⋙ freePfpngFunctor) :=
    ProFiltPseuNormGrp₁.boundedCone ⟨Ab.explicitLimitCone.{u, u} _, Ab.explicitLimitConeIsLimit _⟩
  let hE : limits.is_limit E := ProFiltPseuNormGrp₁.boundedConeIsLimit _
  let ee : S.free_pfpng ≅ E.X := (limits.limit.is_limit _).conePointUniqueUpToIso hE
  apply_fun ee.hom; swap
  · intro x y hh; apply_fun ee.inv at hh ; simpa using hh
  ext T : 3; exact huv T

variable (x : S.pmz ⌊j⌋₊) (T : DiscreteQuotient S)

theorem lhs_helper :
    (S.freePfpngπ T) ((S.pmzToFreePfpng j) x).1 =
      ∑ i : Fin ⌊j⌋₊, Pi.single (T.proj (x.2 i)) (x.1.down i : ℤ) :=
  by
  change
    ((S.pmz_to_free_pfpng _ ≫ (ProFiltPseuNormGrp₁.level.obj j).map (S.free_pfpng_π T)) _).val = _
  dsimp [Profinite.pmzToFreePfpng, Profinite.freePfpngπ]
  erw [← comp_apply]
  erw [limits.is_limit.fac]
  dsimp [Profinite.pmzToLevelNatTrans, Profinite.pmzToLevel]
  rcases x with ⟨x1, x2⟩
  dsimp [Profinite.pmzCone, Profinite.sigma.desc, Profinite.pmzToLevelComponent,
    Profinite.pmzFunctor, Profinite.product.lift, Profinite.sigma.ι]
  congr 1; ext i t; erw [Pi.single_apply]
  split_ifs with h1 h2 h3 h4
  · rfl
  · exact False.elim (h2 h1.symm)
  · exact False.elim (h1 h3.symm)
  · rfl

theorem rhs_helper₁ :
    (fun f : ULift (Fin ⌊j⌋₊ → SignType) =>
        ∑ x : Fin ⌊j⌋₊,
          ((proetaleTopology.toSheafify (S.toCondensed.val ⋙ AddCommGroupCat.free')).app
              (op (S.pow ⌊j⌋₊)))
            (Finsupp.single { down := Profinite.product.π (fun i : Fin ⌊j⌋₊ => S) x }
              ↑(f.down x))) =
      ∑ x : Fin ⌊j⌋₊, fun f =>
        (proetaleTopology.toSheafify (S.toCondensed.val ⋙ AddCommGroupCat.free')).app
            (op (S.pow ⌊j⌋₊)) <|
          Finsupp.single ⟨Profinite.product.π _ x⟩ (f.down x) :=
  by ext; simp

def CompHausFiltPseuNormGrp.coeAddMonoidHom (A : CompHausFiltPseuNormGrp.{u}) (T : Profinite.{u}) :
    (CompHausFiltPseuNormGrp.toCondensed.obj A).val.obj (op T) →+ T → A
    where
  toFun f := f.down.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem CompHausFiltPseuNormGrp.toCondensed_app_sum_apply (n : ℕ) (A : CompHausFiltPseuNormGrp.{u})
    (T : Profinite.{u}) (g : Fin n → (CompHausFiltPseuNormGrp.toCondensed.obj A).val.obj (op T))
    (t : T) : (ULift.down (∑ i : Fin n, g i)).1 t = ∑ i : Fin n, (ULift.down (g i)).1 t :=
  by
  let e := A.coe_add_monoid_hom T
  change _ = ∑ i : Fin n, (e (g i)) t
  rw [← Finset.sum_apply t Finset.univ fun i : Fin n => e (g i), ← e.map_sum]
  rfl

theorem Profinite.free'Lift_val_obj_sigma_equiv_symm {α : Type u} [Fintype α]
    (A : Condensed.{u} Ab.{u + 1}) (η : S.toCondensed ⟶ condensedAbToCondensedSet.obj A)
    (X : α → Profinite.{u}) (t) :
    (S.free'Lift η).val.app (op <| Profinite.sigma X) ((Condensed.valObjSigmaAddEquiv _ _).symm t) =
      (Condensed.valObjSigmaAddEquiv _ _).symm fun a => (S.free'Lift η).val.app _ (t a) :=
  by
  apply_fun Condensed.valObjSigmaAddEquiv (fun a : α => X a) A
  simp only [AddEquiv.apply_symm_apply]
  funext a
  dsimp
  simp only [← comp_apply, ← nat_trans.naturality]
  simp only [comp_apply]
  congr 1
  rw [← Condensed.valObjSigmaAddEquiv_apply_apply]
  simp only [AddEquiv.apply_symm_apply]

-- move and rename
def rhsHelperEquiv (A : ProFiltPseuNormGrp₁.{u}) :
    A ≃
      (CompHausFiltPseuNormGrp.toCondensed.obj
              (cHFPNG₁ToCHFPNGₑₗ.obj (pFPNG₁ToCHFPNG₁ₑₗ.obj A))).val.obj
        (op Profinite.punit)
    where
  toFun a :=
    ULift.up <|
      ⟨fun _ => a, by
        obtain ⟨c, hc⟩ := ProFiltPseuNormGrp₁.exhaustive _ a
        refine' ⟨c, fun _ => ⟨a, hc⟩, _, rfl⟩
        apply continuous_of_discreteTopology⟩
  invFun f := f.down.val PUnit.unit
  left_inv t := rfl
  right_inv t := by ext ⟨⟩; rfl

-- move and rename
def rhsHelperEquiv' : S ≃ S.toCondensed.val.obj (op Profinite.punit)
    where
  toFun s := ULift.up <| Profinite.pt s
  invFun s := (ULift.down s).1 PUnit.unit
  left_inv t := rfl
  right_inv t := by ext ⟨⟩; rfl

theorem rhs_helper₄ {α : Type u} [Fintype α] (A : ProFiltPseuNormGrp₁.{u}) (X : α → Profinite.{u})
    (e :
      ∀ a : α,
        (CompHausFiltPseuNormGrp.toCondensed.obj
                (cHFPNG₁ToCHFPNGₑₗ.obj (pFPNG₁ToCHFPNG₁ₑₗ.obj A))).val.obj
          (op <| X a))
    (a₀ : α) (x₀ : X a₀) :
    ((Condensed.valObjSigmaAddEquiv X _).symm e).down.val ⟨a₀, x₀⟩ = (e a₀).down.val x₀ :=
  by
  let B :=
    Condensed_Ab_to_CondensedSet.obj
      (CompHausFiltPseuNormGrp.to_Condensed.obj
        (CHFPNG₁_to_CHFPNGₑₗ.obj (PFPNG₁_to_CHFPNG₁ₑₗ.obj A)))
  let e₀ : (X a₀).toCondensed ⟶ B := (Profinite.toCondensedEquiv _ B).symm (e a₀)
  let ee : (Profinite.sigma X).toCondensed ⟶ B :=
    (Profinite.toCondensedEquiv _ B).symm ((Condensed.valObjSigmaAddEquiv X _).symm e)
  apply_fun rhs_helper_equiv A
  let s₀ : (X a₀).toCondensed.val.obj (op Profinite.punit) := rhs_helper_equiv' _ x₀
  have : (rhs_helper_equiv A) ((e a₀).down.val x₀) = e₀.val.app _ s₀
  rfl
  rw [this]
  have : e₀ = Profinite_to_Condensed.map (Profinite.sigma.ι X a₀) ≫ ee :=
    by
    dsimp only [e₀, ee]; symm
    apply _root_.Condensed.val_obj_sigma_add_equiv_symm_apply
  rw [this]; rfl

theorem rhs_helper₃ (i : Fin ⌊j⌋₊) :
    (((S.free'Lift S.toCondensedFreePfpng).val.app (op (S.pmz ⌊j⌋₊)))
              ((Condensed.valObjSigmaAddEquiv (fun f : ULift (Fin ⌊j⌋₊ → SignType) => S.pow ⌊j⌋₊)
                    S.free').symm
                fun f : ULift (Fin ⌊j⌋₊ → SignType) =>
                ((proetaleTopology.toSheafify (S.toCondensed.val ⋙ AddCommGroupCat.free')).app
                    (op (S.pow ⌊j⌋₊)))
                  (Finsupp.single { down := Profinite.product.π (fun i : Fin ⌊j⌋₊ => S) i }
                    ↑(f.down i)))).down.1
        x =
      (x.1.down i : ℤ) • (S.toFreePfpng (x.2 i)).1 :=
  by
  erw [Profinite.free'_lift_val_obj_sigma_equiv_symm]
  simp only [← comp_apply]
  erw [free'_lift_app_eq']
  simp only [ContinuousMap.toFun_eq_coe, LinearMap.toAddMonoidHom_coe, Finsupp.lift_apply,
    Profinite.toCondensedFreePfpng_app, Finsupp.sum_single_index, zero_smul, Subtype.val_eq_coe]
  -- This is now very close...
  let Q :=
    Condensed.valObjSigmaAddEquiv (fun a : ULift (Fin ⌊j⌋₊ → SignType) => S.pow ⌊j⌋₊)
      S.condensed_free_pfpng
  change (Q.symm _).down.1 _ = _
  cases' x with x1 x2
  erw [rhs_helper₄]
  rfl

theorem rhs_helper₂ (i : Fin ⌊j⌋₊) :
    (S.freePfpngπ T)
        ((((S.free'Lift S.toCondensedFreePfpng).val.app (op (S.pmz ⌊j⌋₊)))
                ((Condensed.valObjSigmaAddEquiv (fun f : ULift (Fin ⌊j⌋₊ → SignType) => S.pow ⌊j⌋₊)
                      S.free').symm
                  fun f : ULift (Fin ⌊j⌋₊ → SignType) =>
                  ((proetaleTopology.toSheafify (S.toCondensed.val ⋙ AddCommGroupCat.free')).app
                      (op (S.pow ⌊j⌋₊)))
                    (Finsupp.single { down := Profinite.product.π (fun i : Fin ⌊j⌋₊ => S) i }
                      ↑(f.down i)))).down.1
          x) =
      Pi.single (T.proj (x.snd i)) ↑(x.fst.down i) :=
  by
  rw [rhs_helper₃]
  erw [(S.free_pfpng_π T).toAddMonoidHom.map_zsmul]
  change
    _ • ((S.to_free_pfpng ≫ (ProFiltPseuNormGrp₁.level.obj 1).map (S.free_pfpng_π T)) _).val = _
  dsimp [Profinite.toFreePfpng, Profinite.freePfpngπ, Profinite.freePfpngLevelIso]
  dsimp [limits.is_limit.cone_point_unique_up_to_iso]
  erw [← comp_apply]
  erw [← comp_apply]
  erw [limits.is_limit.fac]
  erw [limits.is_limit.fac]
  dsimp [FintypeCat.freePfpngUnit, Profinite.asLimitCone]
  ext t; erw [Pi.single_apply]; split_ifs <;> simp
  · intro hh; exact False.elim (hh h.symm)
  · intro hh; exact False.elim (h hh.symm)

theorem rhs_helper :
    (S.freePfpngπ T)
        ((((S.free'Lift S.toCondensedFreePfpng).val.app (op (S.pmz ⌊j⌋₊)))
                ((S.pmzToFree' ⌊j⌋₊).val.app (op (S.pmz ⌊j⌋₊)) { down := 𝟙 (S.pmz ⌊j⌋₊) })).1.1
          x) =
      ∑ i : Fin ⌊j⌋₊, Pi.single (T.proj (x.2 i)) (x.1.down i : ℤ) :=
  by
  dsimp [Profinite.pmzToFree']
  rw [CategoryTheory.Functor.map_id, id_apply]
  simp only [AddMonoidHom.map_sum]
  rw [rhs_helper₁]
  rw [AddEquiv.map_sum, AddMonoidHom.map_sum]
  have := _root_.CompHausFiltPseuNormGrp.to_Condensed_app_sum_apply ⌊j⌋₊ _ _ _ x
  dsimp at this ; erw [this]; clear this
  erw [(S.free_pfpng_π T).toAddMonoidHom.map_sum]
  congr 1; funext i; dsimp
  erw [rhs_helper₂]

theorem key (j : ULift.{u + 1} NNReal) :
    profiniteToCondensed.map (S.pmzToFreePfpng j.down) ≫
        (cHFPNG₁ToCHFPNGₑₗ.obj
                  (pFPNG₁ToCHFPNG₁ₑₗ.obj S.FreePfpng)).levelCondensedDiagramCocone.ι.app
          j =
      S.pmzToFree' ⌊j.down⌋₊ ≫ condensedAbToCondensedSet.map S.free'ToCondensedFreePfpng :=
  by
  apply_fun Profinite.toCondensedEquiv _ _
  ext x : 3; dsimp at x 
  dsimp [CompHausFiltPseuNormGrp.levelCondensedDiagramCocone, Profinite.free'ToCondensedFreePfpng]
  apply free_pfpng_ext; intro T
  erw [lhs_helper]; erw [rhs_helper]

end Profinite.EpiFree'ToCondensedSetup

instance Profinite.epi_free'ToCondensedFreePfpng_of_nonempty (S : Profinite.{u}) [Nonempty S] :
    Epi S.free'ToCondensedFreePfpng :=
  by
  apply functor.epi_of_epi_map condensedAbToCondensedSet
  let E :=
    CompHausFiltPseuNormGrp.levelCondensedDiagramCocone
      (CHFPNG₁_to_CHFPNGₑₗ.obj (PFPNG₁_to_CHFPNG₁ₑₗ.obj S.free_pfpng))
  have hh : is_iso (limits.colimit.desc _ E) :=
    by
    change is_iso (CompHausFiltPseuNormGrp.colimitToCondensedObj _)
    infer_instance
  let hE : limits.is_colimit E := @limits.is_colimit.of_point_iso _ _ _ _ _ _ _ _ hh
  -- <-- move this
  apply CategoryTheory.epi_to_colimit_of_exists _ E hE
  intro j
  let j' : NNReal := ULift.down j
  use(S.pmz ⌊j'⌋₊).toCondensed, S.pmz_to_free' ⌊j'⌋₊,
    Profinite_to_Condensed.map (S.pmz_to_free_pfpng j')
  constructor
  · apply epi_profiniteToCondensed_map_of_epi
  · apply Profinite.EpiFree'ToCondensedSetup.key

