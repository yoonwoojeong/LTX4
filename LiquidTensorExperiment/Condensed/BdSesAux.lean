import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.Condensed.ShortExact
import LiquidTensorExperiment.ForMathlib.AddCommGroup.DirectSumColimit
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitProducts

#align_import condensed.bd_ses_aux

open scoped Classical BigOperators

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace Condensed

universe u

variable (F : AsSmall.{u + 1} ℕ ⥤ Condensed.{u} Ab.{u + 1})

noncomputable section

def coproductToColimit : ∐ F.obj ⟶ colimit F :=
  Sigma.desc fun i => colimit.ι _ i

def coproductToCoproduct : ∐ F.obj ⟶ ∐ F.obj :=
  Sigma.desc fun i =>
    F.map (AsSmall.up.map <| homOfLE <| Nat.le_succ _) ≫
      Sigma.ι _ (AsSmall.up.obj (AsSmall.down.obj i + 1))

def sigmaEvalIso {α : Type (u + 1)} (X : α → Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) :
    (∐ X).val.obj (op S.val) ≅ ∐ fun a => (X a).val.obj (op S.val) :=
  preservesColimitIso (Condensed.evaluation _ S.val) _ ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun i => Iso.refl _)

@[reassoc]
theorem ι_sigmaEvalIso {α : Type (u + 1)} (X : α → Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u})
    (i : α) : (Sigma.ι X i : X i ⟶ _).val.app (op S.val) ≫ (sigmaEvalIso X S).hom = Sigma.ι _ i :=
  by
  dsimp only [Condensed.sigmaEvalIso]
  erw [(CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation _ S.val) _).fac_assoc]
  erw [colimit.ι_desc]; dsimp; simp

def sigmaEvalIsoDirectSum {α : Type (u + 1)} (X : α → Condensed.{u} Ab.{u + 1}) (S : ExtrDisc.{u}) :
    (∐ X).val.obj (op S.val) ≅ AddCommGroupCat.of (DirectSum α fun i => (X i).val.obj (op S.val)) :=
  let φ : α → AddCommGroupCat.{u + 1} := fun i => (X i).val.obj (op S.val)
  sigmaEvalIso _ _ ≪≫
    (colimit.isColimit (Discrete.functor φ)).coconePointUniqueUpToIso
      (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} φ)

def shiftCofan (S : ExtrDisc.{u}) (T : Cofan fun i => (F.obj i).val.obj (op S.val)) :
    Cofan fun i => (F.obj i).val.obj (op S.val) :=
  Cofan.mk T.pt fun i : AsSmall.{u + 1} ℕ =>
    by
    refine' _ ≫ T.ι.app ⟨as_small.up.obj <| as_small.down.obj i + 1⟩
    refine' (F.map _).val.app _
    refine' as_small.up.map _
    refine' hom_of_le _
    exact Nat.le_succ _

def directSumToDirectSum (S : ExtrDisc.{u}) :
    AddCommGroupCat.of (DirectSum (AsSmall.{u + 1} ℕ) fun i => (F.obj i).val.obj (op S.val)) ⟶
      AddCommGroupCat.of (DirectSum (AsSmall.{u + 1} ℕ) fun i => (F.obj i).val.obj (op S.val)) :=
  let φ : AsSmall.{u + 1} ℕ → AddCommGroupCat := fun i => (F.obj i).val.obj (op S.val)
  (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} φ).desc
    (shiftCofan F S <| AddCommGroupCat.directSumCofan.{u + 1, u + 1} φ)

def directSumToExplicitColimit (S : ExtrDisc.{u}) :
    AddCommGroupCat.of (DirectSum (AsSmall.{u + 1} ℕ) fun i => (F.obj i).val.obj (op S.val)) ⟶
      (AddCommGroupCat.explicitCocone (F ⋙ Condensed.evaluation _ S.val)).pt :=
  (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
        (F.obj i).val.obj (op S.val)).desc
    (Cofan.mk (AddCommGroupCat.explicitCocone (F ⋙ Condensed.evaluation _ S.val)).pt fun i =>
      (AddCommGroupCat.explicitCocone.{u + 1} (F ⋙ Condensed.evaluation _ S.val)).ι.app i)

theorem key_lemma_aux (S : ExtrDisc.{u}) :
    directSumToExplicitColimit F S = QuotientAddGroup.mk' _ :=
  by
  apply
    (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
        (F.obj i).val.obj (op S.val)).hom_ext
  intro j
  erw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
        (F.obj i).val.obj (op S.val)).fac]
  ext t
  rfl

theorem key_lemma (S : ExtrDisc.{u}) :
    Exact (directSumToDirectSum F S - 𝟙 _) (directSumToExplicitColimit F S) :=
  by
  rw [AddCommGroupCat.exact_iff']; constructor
  · apply
      (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
          (F.obj i).val.obj (op S.val)).hom_ext
    intro j
    simp only [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, comp_zero]
    rw [sub_eq_zero]
    dsimp [Condensed.directSumToDirectSum, Condensed.directSumToExplicitColimit]
    rw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
          (F.obj i).val.obj (op S.val)).fac_assoc]
    rw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
          (F.obj i).val.obj (op S.val)).fac]
    dsimp [Condensed.shiftCofan]; simp only [Category.assoc]
    rw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
          (F.obj i).val.obj (op S.val)).fac]
    dsimp
    apply (AddCommGroupCat.explicitCocone (F ⋙ evaluation Ab S.val)).w
  · rintro x hx; rw [AddMonoidHom.mem_ker] at hx ; rw [key_lemma_aux] at hx 
    dsimp at hx 
    rw [QuotientAddGroup.eq_zero_iff] at hx 
    rw [AddCommGroupCat.explicitCoconePointKernel_eq_of_asSmall_nat] at hx 
    apply AddSubgroup.closure_induction hx
    · rintro x ⟨i, t, rfl⟩;
      let tt :=
        (AddCommGroupCat.directSumCofan.{u + 1, u + 1} fun j => (F.obj j).val.obj (op S.val)).ι.app
          ⟨i⟩ t
      use tt
      change _ - _ = _ - _; congr 1
      swap
      · dsimp only [tt]; rw [id_apply]
        dsimp [AddCommGroupCat.directSumCofan, AddCommGroupCat.directSumι]
        congr
      · dsimp [tt]; rw [← comp_apply]
        erw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun j =>
              (F.obj j).val.obj (op S.val)).fac]
        dsimp [Condensed.shiftCofan, AddCommGroupCat.directSumCofan, AddCommGroupCat.directSumι,
          AddCommGroupCat.toAsSmallSucc]
        rw [comp_apply]
        dsimp [AddCommGroupCat.asSmallSucc]
        congr
    · use 0; simp only [map_zero]
    · rintro x y ⟨x, rfl⟩ ⟨y, rfl⟩; use x + y; simp only [map_add]
    · rintro x ⟨x, rfl⟩; use-x; simp only [map_neg]

theorem sigmaEvalIsoDirectSum_directSumToDirectSum (S : ExtrDisc.{u}) :
    (sigmaEvalIsoDirectSum F.obj S).hom ≫ directSumToDirectSum F S =
      (coproductToCoproduct _).val.app _ ≫ (sigmaEvalIsoDirectSum F.obj S).hom :=
  by
  apply
    (CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab.{u + 1} S.val)
        (colimit.isColimit (Discrete.functor F.obj))).hom_ext
  intro j
  dsimp [Condensed.coproductToCoproduct]
  slice_rhs 1 2 => rw [← NatTrans.comp_app, ← Sheaf.Hom.comp_val, colimit.ι_desc]
  dsimp [Condensed.sigmaEvalIsoDirectSum, Condensed.sigmaEvalIso]; simp only [Category.assoc]
  slice_lhs 1 2 =>
    erw [(CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab.{u + 1} S.val)
          (colimit.isColimit (Discrete.functor F.obj))).fac]
  slice_rhs 2 3 =>
    erw [(CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab.{u + 1} S.val)
          (colimit.isColimit (Discrete.functor F.obj))).fac]
  dsimp
  simp only [HasColimit.isoOfNatIso_ι_hom, Discrete.natIso_hom_app, Category.assoc,
    colimit.comp_coconePointUniqueUpToIso_hom]
  dsimp
  simp only [Category.id_comp]
  erw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i =>
        (F.obj i).val.obj (op S.val)).fac]
  rfl

def colimitValAppIsoExplicitColimit (S : ExtrDisc.{u}) :
    (colimit F).val.obj (op S.val) ≅
      (AddCommGroupCat.explicitCocone (F ⋙ Condensed.evaluation _ S.val)).pt :=
  (isColimitOfPreserves (Condensed.evaluation _ S.val)
        (colimit.isColimit F)).coconePointUniqueUpToIso
    (AddCommGroupCat.isColimitExplicitCocone _)

theorem sigmaEvalIsoDirectSum_to_explicit_colimit (S : ExtrDisc.{u}) :
    (sigmaEvalIsoDirectSum F.obj S).hom ≫ directSumToExplicitColimit F S =
      (coproductToColimit _).val.app _ ≫ (colimitValAppIsoExplicitColimit _ _).hom :=
  by
  apply
    (CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab.{u + 1} S.val)
        (colimit.isColimit (Discrete.functor F.obj))).hom_ext
  intro j
  dsimp [Condensed.sigmaEvalIsoDirectSum, Condensed.sigmaEvalIso, Condensed.coproductToColimit,
    Condensed.colimitValAppIsoExplicitColimit]
  simp only [Category.assoc]
  erw [(CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab.{u + 1} S.val)
        (colimit.isColimit (Discrete.functor F.obj))).fac_assoc]
  slice_rhs 1 2 => rw [← NatTrans.comp_app, ← Sheaf.Hom.comp_val, colimit.ι_desc]
  erw [colimit.ι_desc_assoc]
  dsimp
  simp only [Category.id_comp, colimit.comp_coconePointUniqueUpToIso_hom_assoc]
  dsimp [Condensed.directSumToExplicitColimit]
  erw [(AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun i : as_small ℕ =>
        (F.obj i).val.obj (op S.val)).fac]
  erw [(CategoryTheory.Limits.isColimitOfPreserves (evaluation Ab S.val) (colimit.isColimit F)).fac]
  rfl

theorem ι_sigmaEvalIsoDirectSum {α : Type (u + 1)} (X : α → Condensed.{u} Ab.{u + 1})
    (S : ExtrDisc.{u}) (i : α) :
    (Sigma.ι X i : X i ⟶ _).val.app (op S.val) ≫ (sigmaEvalIsoDirectSum X S).hom =
      DirectSum.of _ i :=
  by
  dsimp only [Condensed.sigmaEvalIsoDirectSum]
  erw [ι_sigma_eval_iso_assoc]; erw [colimit.ι_desc]; rfl

instance epi_coproductToColimit : Epi (coproductToColimit F) :=
  by
  constructor
  intro Z a b h
  apply colimit.hom_ext
  intro j
  apply_fun fun e => sigma.ι F.obj j ≫ e at h 
  dsimp [Condensed.coproductToColimit] at h 
  simpa using h

instance mono_coproductToCoproduct : Mono (coproductToCoproduct F - 𝟙 _) :=
  by
  rw [mono_iff_ExtrDisc]; intro S
  let φ : AsSmall.{u + 1} ℕ → AddCommGroupCat := fun i => (F.obj i).val.obj (op S.val)
  let e :
    (∐ F.obj).val.obj (ExtrDisc_to_Profinite.op.obj (op S)) ≅
      AddCommGroupCat.of (DirectSum (AsSmall.{u + 1} ℕ) fun i => φ i) :=
    Condensed.sigmaEvalIsoDirectSum _ _
  change mono (_ - _); dsimp
  let D := AddCommGroupCat.directSumCofan.{u + 1, u + 1} φ
  let hD : is_colimit D := AddCommGroupCat.isColimitDirectSumCofan _
  let D' : cofan φ := Cofan.mk D.X fun i => _ ≫ D.ι.app ⟨as_small.up.obj (as_small.down.obj i + 1)⟩
  swap
  · refine' (F.map _).val.app _
    refine' as_small.up.map _
    refine' hom_of_le _
    exact Nat.le_succ _
  let t : D.X ⟶ D'.X := (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} φ).desc D'
  have ht : (Condensed.coproductToCoproduct F).val.app (op S.val) = e.hom ≫ t ≫ e.inv :=
    by
    rw [← Category.assoc, Iso.eq_comp_inv]
    apply
      (CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab.{u + 1} S.val)
          (colimit.isColimit _)).hom_ext
    rintro ⟨j⟩; swap; infer_instance
    dsimp [Condensed.coproductToCoproduct]
    rw [← Category.assoc, ← NatTrans.comp_app, ← Sheaf.Hom.comp_val, colimit.ι_desc]
    dsimp; rw [Category.assoc]
    erw [ι_sigma_eval_iso_direct_sum]
    rw [← Category.assoc]
    erw [ι_sigma_eval_iso_direct_sum]
    exact (hD.fac D' ⟨j⟩).symm
  rw [ht]
  have : 𝟙 ((∐ F.obj).val.obj (op S.val)) = e.hom ≫ 𝟙 _ ≫ e.inv := by simp
  rw [this]
  simp only [← Preadditive.comp_sub, ← Preadditive.sub_comp]
  suffices mono (t - 𝟙 (AddCommGroupCat.of (DirectSum (as_small ℕ) fun i : as_small ℕ => ↥(φ i))))
    by
    apply (config := { instances := false }) mono_comp; infer_instance
    apply (config := { instances := false }) mono_comp; exact this; infer_instance
  rw [AddCommGroupCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  erw [sub_eq_zero, id_apply] at hx 
  ext ⟨i⟩
  induction' i with i IH
  · rw [← hx]
    dsimp [t, AddCommGroupCat.isColimitDirectSumCofan, AddCommGroupCat.directSumDesc,
      Discrete.natTrans, DirectSum.toAddMonoid]
    rw [DFinsupp.sumAddHom_apply, DFinsupp.sum_apply]
    apply Finset.sum_eq_zero
    rintro ⟨j⟩ -; convert dif_neg _
    intro H; rw [ULift.ext_iff] at H ; revert H; apply Nat.noConfusion
  · rw [← hx]
    dsimp [t, AddCommGroupCat.isColimitDirectSumCofan, AddCommGroupCat.directSumDesc,
      Discrete.natTrans, DirectSum.toAddMonoid]
    rw [DFinsupp.sumAddHom_apply, DFinsupp.sum_apply]
    rw [DFinsupp.zero_apply] at IH 
    convert Finset.sum_eq_single (ULift.up <| i) _ _
    · rw [IH, AddMonoidHom.map_zero, DFinsupp.zero_apply]
    · rintro ⟨j⟩ - hj; convert dif_neg _
      intro H; apply hj; rw [ULift.ext_iff] at H ⊢; change i + 1 = j + 1 at H 
      change j = i; linarith only [H]
    · intro; rw [IH, AddMonoidHom.map_zero, DFinsupp.zero_apply]
  recover all_goals infer_instance

theorem exactness_in_the_middle_part_one :
    (coproductToCoproduct F - 𝟙 _) ≫ coproductToColimit F = 0 :=
  by
  apply colimit.hom_ext; intro j
  dsimp [Condensed.coproductToCoproduct, Condensed.coproductToColimit]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, colimit.ι_desc_assoc, Category.id_comp,
    Category.comp_id, colimit.ι_desc]
  dsimp; simp

theorem exactness_in_the_middle : Exact (coproductToCoproduct F - 𝟙 _) (coproductToColimit F) :=
  by
  rw [exact_iff_ExtrDisc]; intro S
  let e₁ : (∐ F.obj).val.obj (ExtrDisc_to_Profinite.op.obj (op S)) ≅ _ :=
    Condensed.sigmaEvalIsoDirectSum F.obj S
  let e₂ : (colimit F).val.obj (op S.val) ≅ _ := Condensed.colimitValAppIsoExplicitColimit F S
  let a := _; let b := _; change exact a b
  have ha : a = e₁.hom ≫ (Condensed.directSumToDirectSum _ _ - 𝟙 _) ≫ e₁.inv :=
    by
    simp only [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Iso.hom_inv_id]
    rw [← Category.assoc]
    erw [Condensed.sigmaEvalIsoDirectSum_directSumToDirectSum]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hb : b = e₁.hom ≫ Condensed.directSumToExplicitColimit _ _ ≫ e₂.inv :=
    by
    dsimp [e₁, e₂]
    rw [← Category.assoc, Condensed.sigmaEvalIsoDirectSum_to_explicit_colimit]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [ha, hb]; clear ha hb a b
  suffices exact (Condensed.directSumToDirectSum F S - 𝟙 _) (Condensed.directSumToExplicitColimit _ _)
    by
    rw [← Category.assoc]; apply exact_comp_inv_hom_comp
    rw [exact_iso_comp]; rw [exact_comp_iso]; exact this
  apply key_lemma

theorem shortExact_sequence_aux :
    ShortExact (coproductToCoproduct F - 𝟙 _) (coproductToColimit F) :=
  by
  constructor
  apply exactness_in_the_middle

end Condensed

