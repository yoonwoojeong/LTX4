import Mathlib.Algebra.Homology.HomologicalComplex

#align_import for_mathlib.homological_complex_equiv_functor_category

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe w' w v v' u u'

variable {V : Type u} [Category.{v} V] {J : Type w} [Category.{w'} J]

variable {ι : Type u'} {c : ComplexShape ι}

-- move this
section

variable {C : Type u} [Category.{v} C] {Z : C → Prop}

@[simps]
def liftIso {X Y : FullSubcategory Z} (h : X.obj ≅ Y.obj) : X ≅ Y
    where
  hom := h.Hom
  inv := h.inv
  hom_inv_id' := h.hom_inv_id
  inv_hom_id' := h.inv_hom_id

end

section WalkingComplex

@[nolint unused_arguments]
def WalkingComplex (c : ComplexShape ι) :=
  ι

inductive WalkingComplexHom : WalkingComplex c → WalkingComplex c → Type u'
  | id : ∀ i, walking_complex_hom i i
  | d : ∀ {i j}, c.Rel i j → walking_complex_hom i j
  | zero : ∀ i j, walking_complex_hom i j

section

open WalkingComplexHom

def walkingComplexHomComp (i j k : WalkingComplex c) :
    WalkingComplexHom i j → WalkingComplexHom j k → WalkingComplexHom i k :=
  by
  intro f g
  cases' f with _ _ _ r
  · exact g
  · cases g;
    exacts [walking_complex_hom.d r, walking_complex_hom.zero _ _, walking_complex_hom.zero _ _]
  · exact walking_complex_hom.zero _ _

instance : CategoryStruct (WalkingComplex c)
    where
  Hom := WalkingComplexHom
  id := WalkingComplexHom.id
  comp := by
    intro i j k f g
    cases' f with _ _ _ r
    · exact g
    · cases g;
      exacts [walking_complex_hom.d r, walking_complex_hom.zero _ _, walking_complex_hom.zero _ _]
    · exact walking_complex_hom.zero _ _

end

attribute [local tidy] tactic.case_bash

instance : Category (WalkingComplex c) where

instance walkingComplexHomHasZero (i j : WalkingComplex c) : Zero (i ⟶ j) :=
  ⟨WalkingComplexHom.zero i j⟩

instance : HasZeroMorphisms (WalkingComplex c) where

@[simp]
theorem walkingComplexHom_id (i : WalkingComplex c) : WalkingComplexHom.id i = 𝟙 i :=
  rfl

@[simp]
theorem walkingComplexHom_zero (i : WalkingComplex c) : WalkingComplexHom.zero i = 0 :=
  rfl

def walkingComplexD {i j : WalkingComplex c} (r : c.Rel i j) : i ⟶ j :=
  WalkingComplexHom.d r

@[simp]
theorem walkingComplexD_eq {i j : WalkingComplex c} (r : c.Rel i j) :
    WalkingComplexHom.d r = walkingComplexD r :=
  rfl

@[simp]
theorem walkingComplex_hom_d_comp_d {i j k : WalkingComplex c} (r : c.Rel i j) (r' : c.Rel j k) :
    walkingComplexD r ≫ walkingComplexD r' = 0 :=
  rfl

variable [HasZeroMorphisms V]

def complexToFunctorMap (h : HomologicalComplex V c) {i j : WalkingComplex c} (f : i ⟶ j) :
    h.X i ⟶ h.X j := by cases f; exacts [𝟙 _, h.d _ _, 0]

@[simp]
theorem complexToFunctorMap_id (h : HomologicalComplex V c) (i : WalkingComplex c) :
    complexToFunctorMap h (𝟙 i) = 𝟙 _ :=
  rfl

@[simp]
theorem complexToFunctorMap_zero (h : HomologicalComplex V c) (i j : WalkingComplex c) :
    complexToFunctorMap h (0 : i ⟶ j) = 0 :=
  rfl

@[simp]
theorem complexToFunctorMap_d (h : HomologicalComplex V c) {i j : WalkingComplex c}
    (r : c.Rel i j) : complexToFunctorMap h (walkingComplexD r) = h.d _ _ :=
  rfl

@[simps]
def complexToFunctor (h : HomologicalComplex V c) : WalkingComplex c ⥤ V
    where
  obj := h.X
  map i j f := complexToFunctorMap h f

variable [DecidableRel c.Rel]

@[simps]
def functorToComplex (F : WalkingComplex c ⥤ V) (hF : ∀ i j, F.map (0 : i ⟶ j) = 0) :
    HomologicalComplex V c where
  X := F.obj
  d i j := if r : c.Rel i j then F.map (walkingComplexD r) else 0
  d_comp_d' := by
    introv r r'
    rw [dif_pos r, dif_pos r', ← F.map_comp, walking_complex_hom_d_comp_d, hF]

variable (c V)

@[simps]
def complexToFunctorFunctor :
    HomologicalComplex V c ⥤
      FullSubcategory fun F : WalkingComplex c ⥤ V => ∀ i j, F.map (0 : i ⟶ j) = 0
    where
  obj X := ⟨complexToFunctor X, fun _ _ => rfl⟩
  map X Y f := { app := f.f }

@[simps]
def functorToComplexFunctor :
    (FullSubcategory fun F : WalkingComplex c ⥤ V => ∀ i j, F.map (0 : i ⟶ j) = 0) ⥤
      HomologicalComplex V c
    where
  obj F := functorToComplex F.1 F.2
  map F G f :=
    { f := f.app
      comm' := by intro i j r; simp [dif_pos r] }

@[simps]
def complexEquivFunctorUnit : 𝟭 _ ≅ complexToFunctorFunctor V c ⋙ functorToComplexFunctor V c :=
  NatIso.ofComponents
    (fun X => Hom.isoOfComponents (fun i => Iso.refl _) (by introv r; dsimp; simp [if_pos r]))
    (by intros; ext; dsimp; simp)

@[simps]
def complexEquivFunctorCounit : functorToComplexFunctor V c ⋙ complexToFunctorFunctor V c ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun F =>
      liftIso <|
        NatIso.ofComponents (fun i => Iso.refl _)
          (by introv ; cases' F with F hF; cases f <;> dsimp <;> simp [*, hF]))
    (by introv ; ext; dsimp; erw [nat_trans.comp_app, nat_trans.comp_app]; dsimp; simp)

@[simps]
def complexEquivFunctor :
    HomologicalComplex V c ≌
      FullSubcategory fun F : WalkingComplex c ⥤ V => ∀ i j, F.map (0 : i ⟶ j) = 0
    where
  functor := complexToFunctorFunctor V c
  inverse := functorToComplexFunctor V c
  unitIso := complexEquivFunctorUnit V c
  counitIso := complexEquivFunctorCounit V c
  functor_unitIso_comp' := by intro x; ext; erw [nat_trans.comp_app, nat_trans.id_app]; dsimp; simp

instance : IsEquivalence (complexToFunctorFunctor V c) :=
  IsEquivalence.ofEquivalence (complexEquivFunctor V c)

instance : IsEquivalence (functorToComplexFunctor V c) :=
  IsEquivalence.ofEquivalenceInverse (complexEquivFunctor V c)

@[simps]
def complexToFunctorCategoryFunctor : HomologicalComplex V c ⥤ WalkingComplex c ⥤ V :=
  complexToFunctorFunctor V c ⋙ inducedFunctor _
deriving Full, Faithful

end WalkingComplex

section WalkingPreadditiveComplex

/-
TODO : If `V` is preadditive, then the cateogory of homological complexes is equivalent to the
category of additive functors from a preadditive category `walking_preadditive_complex` to `V`.
-/
end WalkingPreadditiveComplex

end HomologicalComplex

