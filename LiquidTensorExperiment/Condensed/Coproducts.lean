import LiquidTensorExperiment.Condensed.IsProetaleSheaf
import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.Condensed.Adjunctions

#align_import condensed.coproducts

/-!
We show that passing from a profinite set to a condensed set
preserves (finite) coproducts.
-/


open scoped BigOperators Classical

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe u

namespace Profinite

@[simps]
def toCondensedEquiv (X : Profinite.{u}) (Y : CondensedSet.{u}) :
    (X.toCondensed ⟶ Y) ≃ Y.val.obj (op X)
    where
  toFun f := f.val.app _ <| ULift.up <| 𝟙 _
  invFun f :=
    Sheaf.Hom.mk <|
      { app := fun T g => Y.val.map (Quiver.Hom.op (ULift.down g)) f
        naturality := by
          intro A B ff; ext t
          obtain ⟨t⟩ := t
          dsimp [Profinite.toCondensed, CategoryTheory.uliftFunctor, yoneda] at t ⊢
          simp only [Functor.map_comp]; rfl }
  left_inv f := by
    ext T ⟨t⟩
    dsimp [yoneda] at t ⊢
    change (f.val.app _ ≫ Y.val.map _) _ = _
    rw [← NatTrans.naturality]
    change f.val.app _ _ = _
    congr 1; ext; rfl
  right_inv f := by dsimp; simp

end Profinite

namespace CondensedSet

variable {α : Type u} [Fintype α] (X : α → Profinite.{u})

@[simps]
def sigmaCone : Cocone (Discrete.functor X ⋙ profiniteToCondensed)
    where
  pt := (Profinite.sigma X).toCondensed
  ι :=
    { app := fun i => profiniteToCondensed.map <| Profinite.sigma.ι X i.1
      naturality := by rintro ⟨i⟩ ⟨j⟩ ⟨⟨⟨⟩⟩⟩; dsimp; simp; dsimp; simp; dsimp; simp }

noncomputable def valObjSigmaEquiv (Y : CondensedSet.{u}) :
    Y.val.obj (op <| Profinite.sigma X) ≃ ∀ a : α, Y.val.obj (op <| X a) :=
  Equiv.ofBijective (fun f a => Y.val.map (Profinite.sigma.ι X a).op f)
    (by
      have := Y.2
      rw [CategoryTheory.isSheaf_iff_isSheaf_of_type] at this 
      rw [Y.val.isProetaleSheafOfTypes_tFAE.out 0 4] at this 
      have key := this.1
      exact key ⟨α⟩ X)

noncomputable def Condensed.valObjSigmaAddEquiv (Y : Condensed.{u} Ab.{u + 1}) :
    Y.val.obj (op <| Profinite.sigma X) ≃+ ∀ a : α, Y.val.obj (op <| X a) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun f a => Y.val.map (Profinite.sigma.ι X a).op f) (by intros; ext1; simp))
    ((condensedAbToCondensedSet.obj Y).valObjSigmaEquiv X).bijective

@[simp]
theorem coe_valObjSigmaEquiv (Y : Condensed.{u} Ab.{u + 1}) :
    ⇑((condensedAbToCondensedSet.obj Y).valObjSigmaEquiv X) = Y.valObjSigmaAddEquiv X :=
  rfl

@[simp]
theorem coe_valObjSigmaEquiv_symm (Y : Condensed.{u} Ab.{u + 1}) :
    ⇑((condensedAbToCondensedSet.obj Y).valObjSigmaEquiv X).symm = (Y.valObjSigmaAddEquiv X).symm :=
  rfl

@[simp]
theorem Condensed.valObjSigmaAddEquiv_apply_apply (Y : Condensed.{u} Ab.{u + 1}) (t) (a) :
    Y.valObjSigmaAddEquiv X t a = Y.val.map (Profinite.sigma.ι X a).op t :=
  rfl

theorem valObjSigmaEquiv_symm_apply' (Y : CondensedSet.{u}) (e : ∀ a : α, Y.val.obj (op <| X a))
    (a₀ : α) : (Y.val.map (Profinite.sigma.ι X a₀).op) ((valObjSigmaEquiv X Y).symm e) = e a₀ :=
  by
  let e' := _; change (Y.val.map (Profinite.sigma.ι X a₀).op) e' = _
  have : e a₀ = (CondensedSet.valObjSigmaEquiv X Y) e' a₀ := by revert a₀; rw [← Function.funext_iff];
    dsimp only [e']; simp
  rw [this]; rfl

-- TODO reuse the nonadditive variant for this.
theorem Condensed.valObjSigmaAddEquiv_symm_apply' (Y : Condensed.{u} Ab.{u + 1})
    (e : ∀ a : α, Y.val.obj (op <| X a)) (a₀ : α) :
    (Y.val.map (Profinite.sigma.ι X a₀).op) ((Condensed.valObjSigmaAddEquiv X Y).symm e) = e a₀ :=
  by
  let e' := _; change (Y.val.map (Profinite.sigma.ι X a₀).op) e' = _
  have : e a₀ = (_root_.Condensed.val_obj_sigma_add_equiv X Y) e' a₀ := by revert a₀;
    rw [← Function.funext_iff]; dsimp only [e']; simp
  rw [this]; rfl

theorem valObjSigmaEquiv_symm_apply (Y : CondensedSet.{u}) (e : ∀ a : α, Y.val.obj (op <| X a))
    (a₀ : α) :
    profiniteToCondensed.map (Profinite.sigma.ι X a₀) ≫
        (Profinite.toCondensedEquiv (Profinite.sigma X) Y).symm ((Y.valObjSigmaEquiv X).symm e) =
      (Profinite.toCondensedEquiv (X a₀) Y).symm (e a₀) :=
  by
  apply_fun (X a₀).toCondensedEquiv Y
  simp only [Equiv.apply_symm_apply]
  dsimp [Profinite.toCondensedEquiv]
  simp only [Category.comp_id]
  apply CondensedSet.valObjSigmaEquiv_symm_apply'

-- TODO reuse the nonadditive variant for this.
theorem Condensed.valObjSigmaAddEquiv_symm_apply (Y : Condensed.{u} Ab.{u + 1})
    (e : ∀ a : α, Y.val.obj (op <| X a)) (a₀ : α) :
    profiniteToCondensed.map (Profinite.sigma.ι X a₀) ≫
        (Profinite.toCondensedEquiv (Profinite.sigma X) (condensedAbToCondensedSet.obj Y)).symm
          ((Y.valObjSigmaAddEquiv X).symm e) =
      (Profinite.toCondensedEquiv (X a₀) (condensedAbToCondensedSet.obj Y)).symm (e a₀) :=
  by
  apply_fun (X a₀).toCondensedEquiv (Condensed_Ab_to_CondensedSet.obj Y)
  simp only [Equiv.apply_symm_apply]
  dsimp [Profinite.toCondensedEquiv]
  simp only [Category.comp_id]
  apply _root_.Condensed.val_obj_sigma_add_equiv_symm_apply'

noncomputable def isColimitSigmaCone : IsColimit (sigmaCone X)
    where
  desc S :=
    (Profinite.toCondensedEquiv _ _).symm <|
      (S.pt.valObjSigmaEquiv X).symm fun a => Profinite.toCondensedEquiv _ _ <| S.ι.app ⟨_⟩
  fac := by
    rintro Q ⟨T⟩
    dsimp
    rw [CondensedSet.valObjSigmaEquiv_symm_apply]
    ext W ⟨t : _ ⟶ _⟩
    dsimp [Profinite.toCondensedEquiv]
    change ((Q.ι.app ⟨T⟩).val.app (op (X T)) ≫ Q.X.val.map t.op) _ = _
    erw [← (Q.ι.app ⟨T⟩).val.naturality]
    change (Q.ι.app ⟨T⟩).val.app (op (unop W)) _ = _
    congr 1
    dsimp [Profinite.toCondensed]; ext; rfl
  uniq := by
    intro S m hm
    apply_fun (Profinite.sigma X).toCondensedEquiv S.X
    apply_fun val_obj_sigma_equiv X S.X
    simp only [Equiv.apply_symm_apply]
    ext a
    specialize hm ⟨a⟩
    dsimp [CondensedSet.valObjSigmaEquiv]
    change (m.val.app (op (Profinite.sigma X)) ≫ S.X.val.map _) _ = _
    rw [← m.val.naturality]
    apply_fun fun e => e.val.app (op (X a)) ⟨𝟙 _⟩ at hm 
    exact hm

end CondensedSet

