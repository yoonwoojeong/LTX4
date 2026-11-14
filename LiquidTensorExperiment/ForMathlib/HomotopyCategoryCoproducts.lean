import Mathlib.CategoryTheory.Limits.Preserves.Limits
import LiquidTensorExperiment.ForMathlib.Derived.KProjective
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitLimits

#align_import for_mathlib.homotopy_category_coproducts

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{v} A]

open scoped ZeroObject

namespace CategoryTheory

instance isIso_coproduct {α : Type v} (X Y : α → A) (f : ∀ a, X a ⟶ Y a) [∀ a, IsIso (f a)] :
    IsIso (Sigma.desc fun a => f a ≫ Sigma.ι _ a) :=
  by
  use sigma.desc fun a => inv (f a) ≫ sigma.ι _ a
  constructor
  · ext; dsimp; cases j; simp
  · ext; dsimp; cases j; simp

noncomputable theorem isInitialColimit {J : Type v} [SmallCategory J] (K : J ⥤ A)
    (hK : ∀ j, IsInitial (K.obj j)) [HasColimit K] : IsInitial (colimit K) :=
  { desc := fun T =>
      colimit.desc _
        ⟨_, {
            app := fun j => (hK j).to _
            naturality := fun i j f => (hK _).hom_ext _ _ }⟩
    fac := by rintro S ⟨⟨⟩⟩
    uniq := by
      intro S m hm; apply colimit.hom_ext; intro j
      apply (hK _).hom_ext }

theorem isZero_colimit {J : Type v} [SmallCategory J] (K : J ⥤ A) (hK : ∀ j, IsZero (K.obj j))
    [HasColimit K] : IsZero (colimit K) :=
  by
  suffices is_initial (colimit K)
    by
    let e : colimit K ≅ ⊥_ _ := (CategoryTheory.Limits.initialIsoIsInitial this).symm
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ e.symm
    apply CategoryTheory.Limits.isZero_initial
  apply CategoryTheory.isInitialColimit
  intro j
  apply IsZero.isInitial
  apply hK

noncomputable def preadditiveYonedaCoproductToProduct {A : Type u} [Category.{v} A] [Preadditive A]
    {α : Type v} (X : α → A) [HasCoproduct X] (Y : A) :
    (preadditiveYoneda.obj Y).obj (Opposite.op <| sigmaObj X) ⟶
      piObj fun a => (preadditiveYoneda.obj Y).obj (Opposite.op <| X a) :=
  Pi.lift fun b => Functor.map _ <| Quiver.Hom.op <| Sigma.ι _ _

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

instance isIso_preadditiveYonedaCoproductToProduct {A : Type u} [Category.{v} A] [Preadditive A]
    {α : Type v} (X : α → A) [HasCoproduct X] (Y : A) :
    IsIso (preadditiveYonedaCoproductToProduct X Y) :=
  by
  apply CategoryTheory.isIso_of_reflects_iso _ (forget AddCommGroupCat)
  rw [CategoryTheory.isIso_iff_bijective]
  constructor
  · intro f g h; dsimp [CategoryTheory.preadditiveYonedaCoproductToProduct] at f g h ⊢
    apply colimit.hom_ext
    intro a
    let q : (∏ fun a : α => AddCommGroupCat.of (X a ⟶ Y)) ⟶ AddCommGroupCat.of (X a.1 ⟶ Y) :=
      pi.π _ a.1
    apply_fun fun e => q e at h 
    simp only [← comp_apply, limit.lift_π] at h ; cases a; exact h
  · intro f; dsimp at f 
    let P : ∀ a, (∏ fun a : α => AddCommGroupCat.of (X a ⟶ Y)) ⟶ AddCommGroupCat.of (X a ⟶ Y) :=
      fun a => pi.π _ a
    let q : CategoryTheory.Limits.sigmaObj X ⟶ Y := sigma.desc fun a => P a f
    use q
    apply Concrete.limit_ext (Discrete.functor fun a => AddCommGroupCat.of (X a ⟶ Y))
    intro i; dsimp [CategoryTheory.preadditiveYonedaCoproductToProduct]
    simp only [← comp_apply, limit.lift_π]
    dsimp; rw [colimit.ι_desc]; cases i; rfl

noncomputable def preadditiveYonedaCoproductIso {A : Type u} [Category.{v} A] [Preadditive A]
    {α : Type v} (X : α → A) [HasCoproduct X] (Y : A) :
    (preadditiveYoneda.obj Y).obj (Opposite.op <| sigmaObj X) ≅
      piObj fun a => (preadditiveYoneda.obj Y).obj (Opposite.op <| X a) :=
  asIso (preadditiveYonedaCoproductToProduct _ _)

noncomputable def piIso {A : Type u} [Category.{v} A] {α : Type v} (X Y : α → A)
    (I : ∀ a, X a ≅ Y a) [HasProduct X] [HasProduct Y] : piObj X ≅ piObj Y
    where
  hom := Pi.lift fun b => Pi.π _ _ ≫ (I b).hom
  inv := Pi.lift fun b => Pi.π _ _ ≫ (I b).inv
  hom_inv_id := by
    apply limit.hom_ext; rintro ⟨i⟩
    simp
  inv_hom_id := by
    apply limit.hom_ext; rintro ⟨i⟩
    simp

end CategoryTheory

namespace HomotopyCategory

noncomputable def coproductIso {α : Type v} (X : α → CochainComplex A ℤ) (i) :
    (sigmaObj X).pt i ≅ sigmaObj fun a : α => (X a).pt i :=
  CategoryTheory.preservesColimitIso (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
      (Discrete.functor X) ≪≫
    HasColimit.isoOfNatIso
      (NatIso.ofComponents (fun _ => Iso.refl _)
        (by
          rintro ⟨⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩
          simp))

@[reassoc (attr := simp)]
theorem coproduct_ι_coproductIso_inv {α : Type v} (X : α → CochainComplex A ℤ) (i) (a) :
    Sigma.ι _ a ≫ (coproductIso X i).inv = (Sigma.ι X a : _ ⟶ _).f i :=
  by
  dsimp [coproduct_iso, HasColimit.isoOfNatIso, IsColimit.map, CategoryTheory.preservesColimitIso,
    IsColimit.coconePointUniqueUpToIso]
  simp; dsimp; simp

@[reassoc (attr := simp)]
theorem coproduct_ι_coproductIso_hom {α : Type v} (X : α → CochainComplex A ℤ) (i) (a : α) :
    (Sigma.ι X a : _ ⟶ _).f i ≫ (coproductIso X i).hom = Sigma.ι _ a :=
  by
  dsimp [coproduct_iso, HasColimit.isoOfNatIso, IsColimit.map, CategoryTheory.preservesColimitIso,
    IsColimit.coconePointUniqueUpToIso]
  slice_lhs 0 1 =>
    erw [(CategoryTheory.Limits.isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
          (colimit.isColimit (Discrete.functor X))).fac]
  simp; dsimp; simp

noncomputable def homotopyCoprod {α : Type v} (X : α → CochainComplex A ℤ) (Y)
    (f g : sigmaObj X ⟶ Y) (h : ∀ a, Homotopy (Sigma.ι _ a ≫ f) (Sigma.ι _ a ≫ g)) : Homotopy f g
    where
  Hom i j := (coproductIso X i).hom ≫ Sigma.desc fun a => (h a).hom _ _
  zero' := by
    intro i j hh
    simp only [Preadditive.IsIso.comp_left_eq_zero]
    apply colimit.hom_ext; intro a
    simp only [colimit.ι_desc, Cofan.mk_ι_app, comp_zero, (h a.1).zero' i j hh]
  comm := by
    intro i
    rw [← cancel_epi (coproduct_iso X i).inv]
    apply colimit.hom_ext; rintro ⟨a⟩
    simp only [coproduct_ι_coproduct_iso_inv_assoc, HomologicalComplex.cochainComplex_dNext,
      HomologicalComplex.cochainComplex_prevD, Category.assoc, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc, coproduct_ι_coproduct_iso_hom_assoc, colimit.ι_desc,
      Cofan.mk_ι_app, colimit.ι_desc_assoc]
    have := (h a).comm i
    refine' this.trans _
    simp only [HomologicalComplex.cochainComplex_dNext, HomologicalComplex.cochainComplex_prevD]
    rfl

theorem homotopic_coprod {α : Type v} (X : α → CochainComplex A ℤ) (Y) (f g : sigmaObj X ⟶ Y)
    (h : ∀ a : α, homotopic _ _ (Sigma.ι _ a ≫ f) (Sigma.ι _ a ≫ g)) : homotopic _ _ f g :=
  by
  constructor
  apply HomotopyCategory.homotopyCoprod
  intro a
  exact (h a).some

-- Move this
theorem homotopic_of_quotient_map_eq {X Y : CochainComplex A ℤ} (f g : X ⟶ Y)
    (h : (quotient _ _).map f = (quotient _ _).map g) : homotopic _ _ f g := by
  erw [Quotient.functor_map_eq_iff] at h ; assumption

noncomputable def colimitCofan {α : Type v} (X : α → HomotopyCategory A (ComplexShape.up ℤ)) :
    Cofan X :=
  Cofan.mk ((quotient _ _).obj <| sigmaObj fun a => (X a).as) fun a =>
    (quotient _ _).map <| Sigma.ι _ a

noncomputable def isColimitCofan {α : Type v} (X : α → HomotopyCategory A (ComplexShape.up ℤ)) :
    IsColimit (colimitCofan X)
    where
  desc S := (quotient _ _).map <| Sigma.desc fun a => (S.ι.app ⟨a⟩).out
  fac := by
    rintro S ⟨j⟩
    dsimp
    erw [← (Quotient A (ComplexShape.up ℤ)).map_comp, colimit.ι_desc]
    dsimp [Quotient]
    simp
  uniq := by
    intro S m hm
    let mm := m.out
    have : (Quotient _ _).map mm = m := by simp
    rw [← this]
    apply Quot.sound
    apply Quotient.CompClosure.of
    apply homotopic_coprod
    intro a
    specialize hm ⟨a⟩; rw [← this] at hm ; dsimp at hm 
    erw [← (Quotient A (ComplexShape.up ℤ)).map_comp] at hm 
    erw [colimit.ι_desc]
    dsimp
    have : S.ι.app ⟨a⟩ = (Quotient _ _).map (S.ι.app ⟨a⟩).out := by simp
    rw [this] at hm 
    apply homotopic_of_quotient_map_eq
    exact hm

instance {α : Type v} (X : α → HomotopyCategory A (ComplexShape.up ℤ)) : HasCoproduct X
    where exists_colimit := Nonempty.intro <| ⟨colimitCofan _, isColimitCofan _⟩

instance {α : Type v} : HasColimitsOfShape (Discrete α) (HomotopyCategory A (ComplexShape.up ℤ)) :=
  by
  constructor; intro K
  let E : K ≅ Discrete.functor fun n => K.obj ⟨n⟩ := Discrete.natIso fun ⟨i⟩ => iso.refl _
  apply CategoryTheory.Limits.hasColimitOfIso E

noncomputable instance {α : Type v} :
    PreservesColimitsOfShape (Discrete α) (quotient A (ComplexShape.up ℤ)) :=
  by
  constructor; intro K
  apply CategoryTheory.Limits.preservesColimitOfPreservesColimitCocone (colimit.isColimit K)
  let T :
    K ⋙ Quotient A _ ≅ Discrete.functor fun a : α => (Quotient _ _).obj ((fun n => K.obj ⟨n⟩) a) :=
    NatIso.ofComponents (fun ⟨i⟩ => iso.refl _) _
  swap
  · rintro ⟨i⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩
    dsimp
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    dsimp
    simp only [Category.comp_id]
  apply
    (IsColimit.precomposeInvEquiv T
        ((Quotient A (ComplexShape.up ℤ)).mapCocone (colimit.cocone K))).toFun
  let ee :
    (colimit_cofan fun a : α => (Quotient _ _).obj (K.obj ⟨a⟩)) ≅
      (Cocones.precompose T.inv).obj
        ((Quotient A (ComplexShape.up ℤ)).mapCocone (colimit.cocone K)) :=
    _
  swap
  · refine' Cocones.ext _ _
    · apply Functor.mapIso
      refine' HasColimit.isoOfNatIso _
      refine' NatIso.ofComponents (fun ⟨i⟩ => iso.refl _) _
      rintro ⟨i⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩
      dsimp
      simp only [Discrete.functor_map_id, Category.comp_id]
      dsimp
      simp only [Category.id_comp]
    rintro ⟨i⟩
    dsimp [colimit_cofan, T, NatIso.ofComponents, HasColimit.isoOfNatIso, IsColimit.map]
    simp only [← Functor.map_comp, Category.id_comp, colimit.ι_desc]
    dsimp [Cocones.precompose]
    simpa only [Functor.map_comp]
  apply IsColimit.ofIsoColimit _ ee
  apply is_colimit_cofan

instance isKProjectiveSigma {α : Type v} (X : α → HomotopyCategory A (ComplexShape.up ℤ))
    [∀ a, IsKProjective (X a)] : IsKProjective (sigmaObj X) :=
  by
  constructor
  intro Y hY f
  apply colimit.hom_ext
  rintro ⟨a⟩
  rw [comp_zero]
  apply IsKProjective.cond Y
  dsimp; infer_instance

instance isKProjectiveColimitCofan {α : Type v} (X : α → HomotopyCategory A (ComplexShape.up ℤ))
    [∀ a, IsKProjective (X a)] : IsKProjective (colimitCofan X).pt :=
  by
  let e : (colimit_cofan X).pt ≅ CategoryTheory.Limits.sigmaObj X :=
    (is_colimit_cofan X).coconePointUniqueUpToIso (colimit.isColimit _)
  apply is_K_projective_of_iso _ _ e.symm

end HomotopyCategory

