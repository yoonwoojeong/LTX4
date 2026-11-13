import Mathlib.CategoryTheory.Abelian.Projective
import LiquidTensorExperiment.ForMathlib.HomotopyCategoryPretriangulated
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.Derived.Homological
import LiquidTensorExperiment.ForMathlib.Derived.Lemmas
import LiquidTensorExperiment.ForMathlib.SnakeLemma3
import LiquidTensorExperiment.ForMathlib.LesHomology
import LiquidTensorExperiment.ForMathlib.ExactSeq3
import LiquidTensorExperiment.ForMathlib.TriangleShift
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.ProjectiveReplacement
import LiquidTensorExperiment.ForMathlib.AdditiveFunctor

#align_import for_mathlib.derived.bounded_homotopy_category

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

open HomologicalComplex

universe v v' u u'

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace BoundedHomotopyCategory

instance : Category (BoundedHomotopyCategory A)
    where
  Hom X Y := X.val ⟶ Y.val
  id X := 𝟙 X.val
  comp X Y Z f g := f ≫ g
  id_comp' _ _ _ := Category.id_comp _
  comp_id' _ _ _ := Category.comp_id _
  assoc' _ _ _ _ _ _ _ := Category.assoc _ _ _

attribute [local instance] has_zero_object.has_zero

instance (X : BoundedHomotopyCategory A) : HomotopyCategory.IsBoundedAbove X.val :=
  X.bdd

def of (X : HomotopyCategory A (ComplexShape.up ℤ)) [HomotopyCategory.IsBoundedAbove X] :
    BoundedHomotopyCategory A :=
  ⟨X⟩

abbrev homVal {X Y : BoundedHomotopyCategory A} (f : X ⟶ Y) : X.val ⟶ Y.val :=
  f

theorem hom_ext {X Y : BoundedHomotopyCategory A} (f g : X ⟶ Y) (h : homVal f = homVal g) : f = g :=
  h

@[simps]
def mkIso {X Y : BoundedHomotopyCategory A} (i : X.val ≅ Y.val) : X ≅ Y
    where
  Hom := i.Hom
  inv := i.inv
  hom_inv_id' := i.hom_inv_id
  inv_hom_id' := i.inv_hom_id

instance : Preadditive (BoundedHomotopyCategory A)
    where
  homGroup A B := show AddCommGroup (A.val ⟶ B.val) by infer_instance
  add_comp P Q R f g h := Preadditive.add_comp _ _ _ _ _ _
  comp_add P Q R f g h := Preadditive.comp_add _ _ _ _ _ _

protected def zero : BoundedHomotopyCategory A
    where
  val := HomotopyCategory.zero
  bdd := ⟨⟨0, fun i _ => by apply limits.is_zero_zero⟩⟩

protected theorem isZero_zero : IsZero (BoundedHomotopyCategory.zero : BoundedHomotopyCategory A) :=
  by
  rw [is_zero_iff_id_eq_zero]
  apply homotopy_category.is_zero_zero.eq_of_src

theorem zero_val {X : BoundedHomotopyCategory A} (hX : IsZero X) : IsZero X.val := by
  rwa [is_zero_iff_id_eq_zero] at hX ⊢

instance : HasZeroObject (BoundedHomotopyCategory A) :=
  ⟨⟨BoundedHomotopyCategory.zero, BoundedHomotopyCategory.isZero_zero⟩⟩

/-
lemma is_bounded_shift (X : bounded_homotopy_category A) (i : ℤ) :
  ∃ (a : ℤ), ∀ j, a ≤ j → is_zero (X.val⟦i⟧.as.X j) :=
begin
  obtain ⟨a,ha⟩ := X.2,
  use a - i,
  intros j hj,
  apply ha,
  linarith
end
-/
attribute [local instance] endofunctor_monoidal_category

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal

instance : HasShift (BoundedHomotopyCategory A) ℤ :=
  hasShiftMk _ _
    { f := fun i =>
        { obj := fun X => ⟨X.val⟦(i : ℤ)⟧⟩
          map := fun X Y f => f⟦i⟧'
          map_id' := fun X => (CategoryTheory.shiftFunctor _ _).map_id _
          map_comp' := fun X Y Z f g => (CategoryTheory.shiftFunctor _ _).map_comp _ _ }
      ε :=
        { Hom :=
            { app := fun X => (HomotopyCategory.shiftε _).Hom.app X.val
              naturality' := fun _ _ _ => (HomotopyCategory.shiftε _).Hom.naturality _ }
          inv :=
            { app := fun X => (HomotopyCategory.shiftε _).inv.app X.val
              naturality' := fun _ _ _ => (HomotopyCategory.shiftε _).inv.naturality _ }
          hom_inv_id' := by
            ext
            dsimp
            erw [← nat_trans.comp_app, iso.hom_inv_id]
            rfl
          inv_hom_id' := by
            ext
            dsimp
            erw [← nat_trans.comp_app, iso.inv_hom_id]
            rfl }
      μ := fun m n =>
        { Hom :=
            { app := fun X => (HomotopyCategory.shiftFunctorAdd _ _ _).Hom.app X.val
              naturality' := fun _ _ _ =>
                (HomotopyCategory.shiftFunctorAdd _ _ _).Hom.naturality _ }
          inv :=
            { app := fun X => (HomotopyCategory.shiftFunctorAdd _ _ _).inv.app X.val
              naturality' := fun _ _ _ =>
                (HomotopyCategory.shiftFunctorAdd _ _ _).inv.naturality _ }
          hom_inv_id' := by
            ext
            dsimp
            erw [← nat_trans.comp_app, iso.hom_inv_id]
            rfl
          inv_hom_id' := by
            ext
            dsimp
            erw [← nat_trans.comp_app, iso.inv_hom_id]
            rfl }
      associativity := fun m₁ m₂ m₃ X =>
        HomotopyCategory.has_shift_associativity_aux _ m₁ m₂ m₃ X.val
      left_unitality := fun n X => HomotopyCategory.has_shift_left_unitality_aux _ n X.val
      right_unitality := fun n X => HomotopyCategory.has_shift_right_unitality_aux _ n X.val }

@[simp]
theorem shiftFunctor_obj_val (X : BoundedHomotopyCategory A) (i : ℤ) :
    ((CategoryTheory.shiftFunctor _ i).obj X).val = X.val⟦i⟧ :=
  rfl

instance shiftFunctor_additive (i : ℤ) :
    (CategoryTheory.shiftFunctor (BoundedHomotopyCategory A) i).Additive := by constructor

instance : triangulated.pretriangulated (BoundedHomotopyCategory A)
    where
  distinguishedTriangles :=-- This could be expresed using `.map_triangle`?
    {T |
      triangle.mk (HomotopyCategory _ _) T.mor₁ T.mor₂ T.mor₃ ∈
        (dist_triang HomotopyCategory A (ComplexShape.up ℤ))}
  isomorphic_distinguished := by
    async
      intro T₁ hT₁ T₂ e
      let S₁ : triangle (HomotopyCategory _ _) := triangle.mk _ T₁.mor₁ T₁.mor₂ T₁.mor₃
      let S₂ : triangle (HomotopyCategory _ _) := triangle.mk _ T₂.mor₁ T₂.mor₂ T₂.mor₃
      let E : S₂ ≅ S₁ :=
        triangle.iso.of_components ⟨e.hom.hom₁, e.inv.hom₁, _, _⟩ ⟨e.hom.hom₂, e.inv.hom₂, _, _⟩
          ⟨e.hom.hom₃, e.inv.hom₃, _, _⟩ _ _ _
      apply pretriangulated.isomorphic_distinguished _ _ _ E
      apply hT₁
      · show (e.hom ≫ e.inv).hom₁ = _; rw [iso.hom_inv_id]; rfl
      · show (e.inv ≫ e.hom).hom₁ = _; rw [iso.inv_hom_id]; rfl
      · show (e.hom ≫ e.inv).hom₂ = _; rw [iso.hom_inv_id]; rfl
      · show (e.inv ≫ e.hom).hom₂ = _; rw [iso.inv_hom_id]; rfl
      · show (e.hom ≫ e.inv).hom₃ = _; rw [iso.hom_inv_id]; rfl
      · show (e.inv ≫ e.hom).hom₃ = _; rw [iso.inv_hom_id]; rfl
      · exact e.hom.comm₁
      · exact e.hom.comm₂
      · exact e.hom.comm₃
  contractible_distinguished := by
    intro X
    apply
      pretriangulated.isomorphic_distinguished _ (pretriangulated.contractible_distinguished X.val)
    delta contractible_triangle
    dsimp
    refine' mk_triangle_iso (iso.refl _) (iso.refl _) _ _ _ _
    · dsimp; refine' is_zero.iso_zero _; apply zero_val; exact limits.is_zero_zero _
    all_goals dsimp; simp only [category.comp_id, category.id_comp, zero_comp, comp_zero] <;> rfl
  distinguished_cocone_triangle := by
    intro X Y f
    let T := (neg₃_functor (HomotopyCategory A (ComplexShape.up ℤ))).obj (cone.triangleₕ f.out)
    let E := T.obj₃
    have : HomotopyCategory.IsBoundedAbove E :=
      by
      obtain ⟨a, ha⟩ := X.2
      obtain ⟨b, hb⟩ := Y.2
      use max (a - 1) b
      intro i hi
      apply is_zero_biprod
      · apply ha; suffices a - 1 ≤ i by linarith; apply le_trans _ hi; apply le_max_left
      · apply hb; apply le_trans _ hi; apply le_max_right
    refine' ⟨⟨E⟩, T.mor₂, T.mor₃, _⟩
    · erw [HomotopyCategory.mem_distinguished_iff_exists_iso_cone]
      use X.val.as, Y.val.as, f.out
      rcases X with ⟨⟨X⟩, hX⟩
      rcases Y with ⟨⟨Y⟩, hY⟩
      constructor
      refine' triangle.iso.of_components (iso.refl _) (iso.refl _) (iso.refl _) _ _ _
      · dsimp; simp only [category.comp_id, HomotopyCategory.quotient_map_out, category.id_comp]
      · dsimp [T]; simp only [category.comp_id, category.id_comp]
      · dsimp [T]; simp only [CategoryTheory.Functor.map_id, category.comp_id, category.id_comp]
  rotate_distinguished_triangle := by
    async
      intro T
      constructor
      · intro hT
        apply HomotopyCategory.rotate_mem_distinguishedTriangles _ hT
      · intro hT
        erw [pretriangulated.rotate_distinguished_triangle]
        exact hT
  complete_distinguished_triangle_morphism := by
    async
      intro T₁ T₂ hT₁ hT₂ f g h
      apply pretriangulated.complete_distinguished_triangle_morphism _ _ hT₁ hT₂ f g h

variable (A)

-- Move this
@[simps]
def HomotopyCategory.single (i : ℤ) : A ⥤ HomotopyCategory A (ComplexShape.up ℤ) :=
  HomologicalComplex.single _ _ i ⋙ HomotopyCategory.quotient _ _

def single (i : ℤ) : A ⥤ BoundedHomotopyCategory A
    where
  obj X :=
    { val := (HomotopyCategory.single A i).obj X
      bdd := by
        use i + 1
        intro j hj
        dsimp
        erw [if_neg]
        · apply limits.is_zero_zero
        · exact ((i.lt_iff_add_one_le j).mpr hj).ne' }
  map X Y f := (HomotopyCategory.single A i).map f
  map_id' X := (HomotopyCategory.single A i).map_id _
  map_comp' X Y Z f g := (HomotopyCategory.single A i).map_comp f g

def forget : BoundedHomotopyCategory A ⥤ HomotopyCategory A (ComplexShape.up ℤ)
    where
  obj := BoundedHomotopyCategory.val
  map _ _ := id

instance : Full (forget A) where preimage _ _ := id

instance : Faithful (forget A) where

def forgetShift (i : ℤ) :
    forget A ⋙ shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) i ≅
      shiftFunctor _ i ⋙ forget A :=
  Iso.refl _

noncomputable def singleForget (i : ℤ) : single A i ⋙ forget A ≅ HomotopyCategory.single A i :=
  Iso.refl _

variable {A}

section

@[simps]
def HomologicalComplex.shiftSingleObj (i j : ℤ) (X : A) :
    (HomologicalComplex.single A (ComplexShape.up ℤ) i).obj X⟦j⟧ ≅
      (HomologicalComplex.single A (ComplexShape.up ℤ) (i - j)).obj X
    where
  Hom := { f := fun k => eqToHom (by dsimp; congr 1; simpa using eq_sub_iff_add_eq.symm) }
  inv := { f := fun k => eqToHom (by dsimp; congr 1; simpa using eq_sub_iff_add_eq) }

@[simps]
def HomologicalComplex.singleShift (i j : ℤ) :
    HomologicalComplex.single A (ComplexShape.up ℤ) i ⋙ CategoryTheory.shiftFunctor _ j ≅
      HomologicalComplex.single A (ComplexShape.up ℤ) (i - j) :=
  NatIso.ofComponents (fun X => HomologicalComplex.shiftSingleObj i j X)
    (by
      intros
      ext k
      dsimp
      split_ifs
      · rw [dif_pos (eq_sub_iff_add_eq.mpr h)]; simp
      · rw [dif_neg (eq_sub_iff_add_eq.not.mpr h)]; simp)

noncomputable def shiftSingleIso (i j : ℤ) : single A i ⋙ shiftFunctor _ j ≅ single A (i - j) :=
  fullyFaithfulCancelRight (BoundedHomotopyCategory.forget A)
    (isoWhiskerRight (HomologicalComplex.singleShift i j)
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)) :
      _)

end

end BoundedHomotopyCategory

namespace CategoryTheory.Functor

variable {B : Type u'} [Category.{v'} B] [Abelian B]

variable (F : A ⥤ B) [Functor.Additive F]

instance isBoundedAboveMapHomotopyCategoryObj (X : BoundedHomotopyCategory A) :
    ((Functor.mapHomotopyCategory (ComplexShape.up ℤ) F).obj X.val).IsBoundedAbove :=
  by
  obtain ⟨a, ha⟩ := HomotopyCategory.IsBoundedAbove.cond X.val
  refine' ⟨⟨a, _⟩⟩
  intro i hi
  apply functor.map_is_zero
  apply ha
  apply hi

@[simps]
def mapBoundedHomotopyCategory : BoundedHomotopyCategory A ⥤ BoundedHomotopyCategory B
    where
  obj X := BoundedHomotopyCategory.of <| (F.mapHomotopyCategory _).obj X.val
  map X Y f := (F.mapHomotopyCategory _).map f
  map_id' X := (F.mapHomotopyCategory _).map_id _
  map_comp' X Y Z f g := (F.mapHomotopyCategory _).map_comp _ _

end CategoryTheory.Functor

