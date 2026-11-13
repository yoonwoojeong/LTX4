import LiquidTensorExperiment.BreenDeligne.Main
import LiquidTensorExperiment.BreenDeligne.Eg
import LiquidTensorExperiment.Condensed.TensorShortExact
import LiquidTensorExperiment.Condensed.EvaluationHomology
import LiquidTensorExperiment.Condensed.SheafificationHomology
import LiquidTensorExperiment.PseudoNormedGroup.QprimeFP
import LiquidTensorExperiment.ForMathlib.AddCommGroup
import LiquidTensorExperiment.ForMathlib.MapToSheafIsIso
import LiquidTensorExperiment.Condensed.IsIsoIffExtrdisc
import LiquidTensorExperiment.Lbar.TorsionFreeCondensed
import LiquidTensorExperiment.Condensed.Ab5
import LiquidTensorExperiment.Condensed.Ab4
import LiquidTensorExperiment.ForMathlib.Endomorphisms.Ab4
import LiquidTensorExperiment.ForMathlib.HomologyExact
import LiquidTensorExperiment.Condensed.QprimeIsoms2
import LiquidTensorExperiment.ForMathlib.FreeAbelianExact
import LiquidTensorExperiment.ForMathlib.Unflip
import LiquidTensorExperiment.BreenDeligne.EvalPowFunctorNatTransCompatibility

#align_import condensed.bd_lemma

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits BreenDeligne Opposite

open scoped BigOperators

section

open CategoryTheory.Preadditive

attribute [simps map] AddCommGroupCat.free

theorem oof (A B : AddCommGroupCat.{u}) : (A →+ B) = (A ⟶ B) :=
  rfl

theorem reorder {M : Type _} [AddCommMonoid M] (a b c d : M) : a + b + (c + d) = a + c + (b + d) :=
  by simp only [add_assoc, add_left_comm b c d]

def evalFreeπ (A : AddCommGroupCat.{u}) (i : Fin 2) :
    (Preadditive.pow 2).obj A ⟶ (Preadditive.pow 1).obj A :=
  biproduct.π _ i ≫ biproduct.ι (fun _ => A) 0

theorem evalFreeπ_eq (A : AddCommGroupCat.{u}) (k : Fin 2) :
    evalFreeπ A k =
      biproduct.matrix fun (i : Fin 2) (j : Fin 1) => BasicUniversalMap.proj 1 k j i • 𝟙 A :=
  by
  apply biproduct.hom_ext; rintro j; fin_cases j
  rw [biproduct.matrix_π, evalFreeπ, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id]
  apply biproduct.hom_ext'; rintro i; rw [biproduct.ι_desc]
  suffices basic_universal_map.proj 1 k 0 i = if i = k then 1 else 0
    by
    rw [this, biproduct.ι_π]; dsimp; obtain rfl | hik := eq_or_ne i k
    · rw [if_pos rfl, if_pos rfl, one_smul]
    · rw [if_neg, if_neg hik, zero_smul]
      intro H; apply hik; exact H
  · dsimp [basic_universal_map.proj, basic_universal_map.proj_aux]; decide!

def evalFreeσ (A : AddCommGroupCat.{u}) : (Preadditive.pow 2).obj A ⟶ (Preadditive.pow 1).obj A :=
  evalFreeπ A 0 + evalFreeπ A 1

theorem eval_free_d10 (A : AddCommGroupCat.{u}) :
    (((Data.evalFunctor (forget _ ⋙ AddCommGroupCat.free)).obj BreenDeligne.eg.data).obj A).d 1 0 =
      ((forget _ ⋙ AddCommGroupCat.free).map <| evalFreeπ A 0) +
          ((forget _ ⋙ AddCommGroupCat.free).map <| evalFreeπ A 1) -
        ((forget _ ⋙ AddCommGroupCat.free).map <| evalFreeσ A) :=
  by
  dsimp only [eg, eg.BD, data.eval_functor_obj_obj_d]; rw [dif_pos rfl]
  dsimp only [universal_map.eval_Pow]; rw [lift_app]
  dsimp only [whisker_right_app, eg.map, eg.σπ, universal_map.proj, universal_map.sum]
  simp only [AddMonoidHom.map_sub, FreeAbelianGroup.lift.of, basic_universal_map.eval_Pow_app,
    functor.comp_map, forget_map_eq_coe, sub_comp, add_comp, preadditive.Pow_obj, forget_obj_eq_coe,
    Fin.sum_univ_two, AddMonoidHom.map_add]
  refine' congr_arg₂ _ (congr_arg₂ _ _ _) _ <;> congr 2
  · rw [evalFreeπ_eq]; rfl
  · rw [evalFreeπ_eq]; rfl
  · rw [evalFreeσ, evalFreeπ_eq, evalFreeπ_eq]
    apply biproduct.hom_ext; rintro j; fin_cases j; simp only [add_comp, biproduct.matrix_π]
    erw [biproduct.matrix_π, biproduct.matrix_π]
    apply biproduct.hom_ext'; rintro i; simp only [comp_add, biproduct.ι_desc, ← add_smul]
    rfl

def pow1Iso (A : AddCommGroupCat.{u}) : (Preadditive.pow 1).obj A ≅ A
    where
  hom := biproduct.π (fun _ => A) 0
  inv := biproduct.ι (fun _ => A) 0
  hom_inv_id' := by erw [← biproduct.total, Fin.sum_univ_one]
  inv_hom_id' := by simp only [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl]

def pow2Iso (A : AddCommGroupCat.{u}) : (Preadditive.pow 2).obj A ≅ AddCommGroupCat.of (A × A)
    where
  hom := AddMonoidHom.prod (biproduct.π (fun _ => A) 0) (biproduct.π (fun _ => A) 1)
  inv := AddMonoidHom.coprod (biproduct.ι (fun _ => A) 0) (biproduct.ι (fun _ => A) 1)
  hom_inv_id' := by
    ext x; erw [← biproduct.total, comp_apply]
    --swap, apply_instance,
    dsimp only [AddMonoidHom.coprod_apply, AddMonoidHom.prod_apply]
    simp only [← comp_apply, Fin.sum_univ_two]; rfl
  inv_hom_id' := by
    ext1 x; rw [comp_apply, id_apply]
    dsimp only [AddMonoidHom.coprod_apply, AddMonoidHom.prod_apply]
    simp only [AddMonoidHom.map_add, ← comp_apply, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
      id_apply]
    rw [dif_neg]; swap; decide
    rw [dif_neg]; swap; decide
    erw [add_zero, zero_add]; cases x; rfl

theorem evalFreeπ_eq_fst (A : AddCommGroupCat.{u}) :
    (pow2Iso A).inv ≫ evalFreeπ A 0 ≫ (pow1Iso A).hom =
      AddCommGroupCat.ofHom (AddMonoidHom.fst A A) :=
  by
  ext x; simp only [comp_apply]
  dsimp only [pow2Iso, pow1Iso, evalFreeπ, AddMonoidHom.coprod_apply]
  simp only [← comp_apply, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id, AddMonoidHom.map_add, id_apply]
  erw [dif_neg, add_zero]; rfl; decide

theorem evalFreeπ_eq_snd (A : AddCommGroupCat.{u}) :
    (pow2Iso A).inv ≫ evalFreeπ A 1 ≫ (pow1Iso A).hom =
      AddCommGroupCat.ofHom (AddMonoidHom.snd A A) :=
  by
  ext x; simp only [comp_apply]
  dsimp only [pow2Iso, pow1Iso, evalFreeπ, AddMonoidHom.coprod_apply]
  simp only [← comp_apply, category.assoc, biproduct.ι_π, dif_pos rfl, eq_to_hom_refl,
    category.comp_id, AddMonoidHom.map_add, id_apply]
  erw [dif_neg, zero_add]; rfl; decide

theorem evalFreeσ_eq_add (A : AddCommGroupCat.{u}) :
    (pow2Iso A).inv ≫ evalFreeσ A ≫ (pow1Iso A).hom =
      AddCommGroupCat.ofHom (AddMonoidHom.coprod (AddMonoidHom.id _) (AddMonoidHom.id _)) :=
  by simp only [evalFreeσ, add_comp, comp_add, evalFreeπ_eq_fst, evalFreeπ_eq_snd]; rfl

theorem eval_free_homology_zero_exact (A : AddCommGroupCat.{u}) :
    Exact
      ((((Data.evalFunctor (forget _ ⋙ AddCommGroupCat.free)).obj BreenDeligne.eg.data).obj A).d 1
        0)
      ((forget _ ⋙ AddCommGroupCat.free).map (pow1Iso A).hom ≫
        AddCommGroupCat.ofHom (FreeAbelianGroup.lift id)) :=
  by
  let F := forget _ ⋙ AddCommGroupCat.free
  refine'
    exact_of_iso_of_exact' _ _ _ _ (F.map_iso (pow2Iso A).symm) (F.map_iso (pow1Iso A).symm)
      (iso.refl _) _ _ (FreeAbelianGroup.exact_σπ A)
  swap
  · dsimp only [functor.map_iso_hom, iso.symm_hom, iso.refl_hom, F]
    rw [category.comp_id, ← functor.map_iso_inv, ← functor.map_iso_hom, iso.inv_hom_id_assoc]
  rw [← iso.comp_inv_eq, category.assoc, eval_free_d10]
  simp only [comp_add, add_comp, comp_sub, sub_comp]
  refine' congr_arg₂ _ (congr_arg₂ _ _ _) _
  · simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv, ←
      functor.map_comp, evalFreeπ_eq_fst]
    rfl
  · simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv, ←
      functor.map_comp, evalFreeπ_eq_snd]
    rfl
  · simp only [functor.map_iso_hom, functor.map_iso_inv, iso.symm_hom, iso.symm_inv, ←
      functor.map_comp, evalFreeσ_eq_add]
    rfl

instance eval_free_homology_zero_epi (A : AddCommGroupCat.{u}) :
    Epi
      ((forget _ ⋙ AddCommGroupCat.free).map (pow1Iso A).hom ≫
        AddCommGroupCat.ofHom (FreeAbelianGroup.lift id)) :=
  by
  apply (config := { instances := false }) epi_comp; infer_instance
  rw [AddCommGroupCat.epi_iff_surjective]; intro a
  exact ⟨FreeAbelianGroup.of a, FreeAbelianGroup.lift.of _ _⟩

open scoped ZeroObject

section

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {A B C X : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (γ : B ⟶ X)

def ofEpiG (hfg : Exact f g) (hg : Epi g) (hγ : γ = 0) : HomologyIsoDatum f γ C
    where
  w := by rw [hγ, comp_zero]
  k := B
  ι := 𝟙 B
  f' := f
  fac := Category.comp_id _
  zero₁' := by rw [hγ, comp_zero]
  π := g
  zero₂' := hfg.w
  forkIsLimit :=
    isLimitAux _ (fun s => s.ι) (fun s => by apply category.comp_id) fun s m hm => by rw [← hm];
      symm; apply category.comp_id
  coforkIsColimit := @Abelian.isColimitOfExactOfEpi _ _ _ _ _ _ _ _ hg hfg

@[simp]
theorem ofEpiG.toHomologyIsoPredatum_π (hfg : Exact f g) (hg : Epi g) (hγ : γ = 0) :
    (ofEpiG f g γ hfg hg hγ).toHomologyIsoPredatum.π = g :=
  rfl

end

def natTransEvalFree :
    (Data.evalFunctor (forget _ ⋙ AddCommGroupCat.free.{u})).obj BreenDeligne.eg.data ⋙
        HomologicalComplex.eval _ _ 0 ⟶
      𝟭 AddCommGroupCat
    where
  app A :=
    (forget _ ⋙ AddCommGroupCat.free).map (pow1Iso A).hom ≫
      AddCommGroupCat.ofHom (FreeAbelianGroup.lift id)
  naturality' A₁ A₂ f :=
    by
    simp only [functor.comp_map, HomologicalComplex.eval_map, data.eval_functor_obj_map_f,
      forget_map_eq_coe, AddCommGroupCat.free_map, functor.id_map, category.assoc]
    ext x
    dsimp [eg, eg.BD, eg.rank] at x 
    have h : ∃ y, x = (pow1Iso A₁).inv y :=
      by
      use(pow1Iso A₁).hom x
      rw [← comp_apply, iso.hom_inv_id, id_apply]
    cases' h with y hy
    subst hy
    simp only [comp_apply, FreeAbelianGroup.map_of_apply, AddCommGroupCat.ofHom_apply,
      FreeAbelianGroup.lift.of, id.def, iso.inv_hom_id_apply, biproduct.map_eq]
    let z : Fin (eg.data.X 0) :=
      ⟨0, by
        dsimp [eg, eg.BD, eg.rank]
        linarith⟩
    rw [Finset.sum_eq_single z]; rotate_left
    · intro b hb₁ hb₂
      exfalso
      apply hb₂
      --cases b,
      --simp only [ulift.up_inj],
      rw [Fin.eq_mk_iff_val_eq]
      have hb₃ := b.is_lt
      dsimp [eg, eg.BD, eg.rank] at hb₃ 
      linarith
    · intro h
      exfalso
      apply h
      simp only [Finset.mem_univ]
    simp only [← comp_apply, category.assoc]
    congr 1
    dsimp
    change _ ≫ (pow1Iso A₁).hom ≫ _ ≫ (pow1Iso A₂).inv ≫ _ = _
    rw [iso.inv_hom_id, iso.inv_hom_id_assoc, category.comp_id]

def shortComplexNatTransEvalFree :
    (Data.evalFunctor (forget _ ⋙ AddCommGroupCat.free)).obj BreenDeligne.eg.data ⋙
        ShortComplex.functorHomologicalComplex _ _ 0 ⟶
      ShortComplex.ιMiddle :=
  by
  refine'
    ShortComplex.natTransHomMk 0 natTransEvalFree 0 _
      (by apply is_zero.eq_of_tgt; apply ShortComplex.ιMiddle_π₃_isZero)
  ext1; ext1 A
  simp only [zero_comp, nat_trans.app_zero, nat_trans.hcomp_app, nat_trans.comp_app,
    nat_trans.id_app, short_complex.π₂.map_id, category.comp_id]
  dsimp only [ShortComplex.φ₁₂, ShortComplex.functorHomologicalComplex, functor.comp_obj,
    ShortComplex.mk]
  simp only [@HomologicalComplex.dTo_eq _ _ _ _ (ComplexShape.down ℕ) _ 1 0 (zero_add 1),
    category.assoc]
  erw [(eval_free_homology_zero_exact A).w, comp_zero]

theorem shortComplexNatTransEvalFree_app_τ₂ (A : AddCommGroupCat) :
    (shortComplexNatTransEvalFree.app A).τ₂ = natTransEvalFree.app A :=
  rfl

def evalFreeHomologyZeroNatTrans :=
  shortComplexNatTransEvalFree ◫ 𝟙 ShortComplex.homologyFunctor

theorem ShortComplex.homology_map_isIso_of_exact_and_epi {A : Type _} [Category A] [Abelian A]
    {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂) (hg₁ : S₁.1.g = 0) (hf₂ : S₂.1.f = 0) (hg₂ : S₂.1.g = 0)
    (ex : Exact S₁.1.f φ.τ₂) (epi_τ₂ : Epi φ.τ₂) : IsIso (ShortComplex.homologyFunctor.map φ) :=
  by
  let h₁ := HomologyIsoDatum.ofGIsZero S₁.1.f S₁.1.g hg₁
  let h₂ := HomologyIsoDatum.ofBothZeros S₂.1.f S₂.1.g hf₂ hg₂
  let ψ := cokernel.desc _ φ.τ₂ ex.w
  let μ : HomologyMapDatum φ h₁ h₂ ψ :=
    { κ := φ.τ₂
      fac₁' := by erw [φ.comm₁₂]; simp only [hf₂]; rfl
      fac₂' := by erw [category.id_comp, category.comp_id]
      fac₃' := by erw [category.comp_id]; apply cokernel.π_desc }
  rw [μ.homology_map_eq]
  suffices is_iso ψ by haveI := this; infer_instance
  exact abelian.category_theory.limits.cokernel.desc.category_theory.is_iso _ _ ex

instance : IsIso evalFreeHomologyZeroNatTrans.{u} :=
  by
  suffices ∀ A, is_iso ((shortComplexNatTransEvalFree ◫ 𝟙 ShortComplex.homologyFunctor).app A) by
    apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app; exact this
  intro A
  simp only [nat_trans.hcomp_id_app]
  refine' ShortComplex.homology_map_isIso_of_exact_and_epi _ _ rfl rfl _ _
  · apply HomologicalComplex.shape
    simp only [ChainComplex.next_nat_zero, ComplexShape.down_Rel, Nat.one_ne_zero, not_false_iff]
  · refine' exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ (eval_free_homology_zero_exact A)
    · symm
      exact HomologicalComplex.xPrevIso _ (zero_add 1)
    · rfl
    · apply eq_to_iso; cases A; rfl
    · dsimp only [ShortComplex.functorHomologicalComplex, functor.comp_obj, ShortComplex.mk]
      rw [HomologicalComplex.dTo_eq]; pick_goal 3; exact 1; swap; dsimp; rfl
      simp only [iso.symm_hom, iso.refl_hom, category.comp_id]
      apply iso.inv_hom_id_assoc
    · apply category.id_comp
  · rw [shortComplexNatTransEvalFree_app_τ₂]
    dsimp [natTransEvalFree]
    convert eval_free_homology_zero_epi.{u} A
    cases A
    rfl

def evalFreeHomologyZero :
    (Data.evalFunctor (forget _ ⋙ AddCommGroupCat.free)).obj BreenDeligne.eg.data ⋙
        homology'Functor _ _ 0 ≅
      𝟭 _ :=
  isoWhiskerLeft _ (ShortComplex.homologyFunctorIso _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      asIso evalFreeHomologyZeroNatTrans ≪≫ ShortComplex.ιMiddleHomologyNatIso.symm

end

open BoundedHomotopyCategory

namespace Condensed

def hQ'Z (n : ℤ) : Ab :=
  ((eg.eval <| CategoryTheory.forget AddCommGroupCat ⋙ AddCommGroupCat.free).obj
            (AddCommGroupCat.free.obj PUnit)).val.as.homology'
    n

variable (BD : Package)

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : Abelian (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Endomorphisms.CategoryTheory.abelian

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : HasFiniteBiproducts (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Abelian.hasFiniteBiproducts

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : EnoughProjectives (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Endomorphisms.CategoryTheory.enoughProjectives

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : HasCoproductsOfShape (ULift.{u + 1} ℕ) (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Endomorphisms.hasColimitsOfShape

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : HasProductsOfShape (ULift.{u + 1} ℕ) (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Endomorphisms.hasLimitsOfShape

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : HasCoproducts (Endomorphisms <| Condensed.{u} Ab.{u + 1}) := fun J : Type (u + 1) =>
  Endomorphisms.hasColimitsOfShape

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : AB4 (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Endomorphisms.CategoryTheory.aB4 _

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : HasFiniteLimits (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Abelian.hasFiniteLimits

-- `by apply_instance` takes for ever, so we provide this shortcut
instance : HasFiniteColimits (Endomorphisms <| Condensed.{u} Ab.{u + 1}) :=
  Abelian.hasFiniteColimits

-- move this
attribute [reassoc] homology_bd_eval_natural

def existsTensorIso (A : Endomorphisms (Condensed.{u} Ab.{u + 1}))
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (A.pt.val.obj (op S.val))] (n : ℕ) :
    ((Package.endoT tensorFunctor).obj A).obj (hQ'Z (-n)) ≅
      ((eg.eval freeCond'.mapEndomorphisms).obj A).val.as.homology' (-n) :=
  by
  refine' endomorphisms.mk_iso _ _
  · refine' _ ≪≫ ((package.hH_endo₁ eg freeCond' n).app A).symm
    refine' (homology_bd_eval eg A.X (-n)).symm ≪≫ _
    exact (package.eval'_homology eg freeCond' n).app A.X
  · dsimp only [iso.trans_hom, iso.symm_hom, package.endo_T_obj_obj_e, tensor_functor, HQ'Z]
    simp only [category.assoc, ← homology_bd_eval_natural_assoc]
    refine' congr_arg₂ _ rfl _
    dsimp only [iso.app_hom, iso.app_inv]
    rw [← functor.comp_map, nat_trans.naturality_assoc]
    refine' congr_arg₂ _ rfl _
    dsimp only [← iso.app_inv]
    rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp]
    exact (eg.hH_endo₁_natural freeCond' A n).symm

-- move this
theorem isTensorUnit_of_iso (A B : Ab) (e : A ≅ B) (ha : AddCommGroupCat.IsTensorUnit A) :
    AddCommGroupCat.IsTensorUnit B := by
  obtain ⟨a, ha⟩ := ha
  refine' ⟨e.hom a, _⟩
  intro C; specialize ha C
  let φ := iso.AddCommGroup_iso_to_add_equiv ((preadditive_yoneda.obj C).mapIso e.op)
  exact ha.comp φ.bijective

theorem bd_lemma (A : Condensed.{u} Ab.{u + 1}) (B : Condensed.{u} Ab.{u + 1})
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (A.val.obj (op S.val))] (f : A ⟶ A) (g : B ⟶ B) :
    (∀ i, IsIso <| ((ext' i).map f.op).app B - ((ext' i).obj (op A)).map g) ↔
      ∀ i,
        IsIso <|
          ((ext i).map ((BreenDeligne.eg.eval freeCond').map f).op).app ((single _ 0).obj B) -
            ((ext i).obj (op <| (BreenDeligne.eg.eval freeCond').obj A)).map ((single _ 0).map g) :=
  by
  apply eg.main_lemma_general' _ A B f g tensor_functor tensor_punit fun n => HQ'Z (-n)
  · apply tensor_tunit
    apply is_tensor_unit_of_iso (AddCommGroup.free.obj PUnit) (HQ'Z 0)
    · let e := (eval_free_homology_zero.app (AddCommGroup.free.obj PUnit)).symm
      refine' e ≪≫ _; clear e
      let e := (package.eval'_homology eg (forget AddCommGroupCat ⋙ AddCommGroupCat.free) 0).symm
      exact e.app (AddCommGroup.free.obj PUnit)
    · refine' ⟨FreeAbelianGroup.of PUnit.unit, _⟩
      intro B; constructor
      · intro f g h; ext ⟨⟩; exact h
      · intro b; refine' ⟨FreeAbelianGroup.lift fun _ => b, _⟩
        apply FreeAbelianGroup.lift.of
  · apply exists_tensor_iso

end Condensed

