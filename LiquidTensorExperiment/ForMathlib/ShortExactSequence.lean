import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Generator
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.InjectiveResolution
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Preadditive.OfBiproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Data.Matrix.Notation
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.FinFunctor
import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import for_mathlib.short_exact_sequence

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Preadditive

universe v u

namespace CategoryTheory

variable (𝒞 : Type u) [Category.{v} 𝒞]

@[ext]
structure ShortExactSequence [HasImages 𝒞] [HasZeroMorphisms 𝒞] [HasKernels 𝒞] where
  (fst snd trd : 𝒞)
  f : fst ⟶ snd
  g : snd ⟶ trd
  [mono' : Mono f]
  [epi' : Epi g]
  exact' : Exact f g

namespace ShortExactSequence

attribute [instance] mono' epi'

variable {𝒞} [HasImages 𝒞] [HasZeroMorphisms 𝒞] [HasKernels 𝒞]

@[simp, reassoc]
theorem f_comp_g (A : ShortExactSequence 𝒞) : A.f ≫ A.g = 0 :=
  A.exact'.w

@[ext]
structure Hom (A B : ShortExactSequence 𝒞) where
  fst : A.1 ⟶ B.1
  snd : A.2 ⟶ B.2
  trd : A.3 ⟶ B.3
  sq1' : fst ≫ B.f = A.f ≫ snd := by obviously
  sq2' : snd ≫ B.g = A.g ≫ trd := by obviously

namespace Hom

attribute [reassoc] sq1 sq2

end Hom

instance : Quiver (ShortExactSequence 𝒞) :=
  ⟨Hom⟩

def id (A : ShortExactSequence 𝒞) : A ⟶ A
    where
  fst := 𝟙 _
  snd := 𝟙 _
  trd := 𝟙 _
  sq1' := by simp only [category.id_comp, category.comp_id]
  sq2' := by simp only [category.id_comp, category.comp_id]

def comp {A B C : ShortExactSequence 𝒞} (f : A ⟶ B) (g : B ⟶ C) : A ⟶ C
    where
  fst := f.1 ≫ g.1
  snd := f.2 ≫ g.2
  trd := f.3 ≫ g.3
  sq1' := by rw [category.assoc, hom.sq1, hom.sq1_assoc]
  sq2' := by rw [category.assoc, hom.sq2, hom.sq2_assoc]

instance : Category (ShortExactSequence 𝒞) :=
  {
    (inferInstance : Quiver (ShortExactSequence
          𝒞)) with
    id := id
    comp := fun A B C f g => comp f g
    id_comp' := by intros; ext <;> dsimp <;> apply category.id_comp
    comp_id' := by intros; ext <;> dsimp <;> apply category.comp_id
    assoc' := by intros; ext <;> dsimp <;> apply category.assoc }

@[simp]
theorem id_fst (A : ShortExactSequence 𝒞) : Hom.fst (𝟙 A) = 𝟙 A.1 :=
  rfl

@[simp]
theorem id_snd (A : ShortExactSequence 𝒞) : Hom.snd (𝟙 A) = 𝟙 A.2 :=
  rfl

@[simp]
theorem id_trd (A : ShortExactSequence 𝒞) : Hom.trd (𝟙 A) = 𝟙 A.3 :=
  rfl

variable {A B C : ShortExactSequence 𝒞} (f : A ⟶ B) (g : B ⟶ C)

@[simp, reassoc]
theorem comp_fst : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

@[simp, reassoc]
theorem comp_snd : (f ≫ g).2 = f.2 ≫ g.2 :=
  rfl

@[simp, reassoc]
theorem comp_trd : (f ≫ g).3 = f.3 ≫ g.3 :=
  rfl

variable (𝒞)

/- warning: category_theory.short_exact_sequence.Fst clashes with category_theory.short_exact_sequence.fst -> CategoryTheory.ShortExactSequence.fst
Case conversion may be inaccurate. Consider using '#align category_theory.short_exact_sequence.Fst CategoryTheory.ShortExactSequence.fstₓ'. -/
#print CategoryTheory.ShortExactSequence.fst /-
@[simps]
def fst : ShortExactSequence 𝒞 ⥤ 𝒞 where
  obj := fst
  map A B f := f.1
-/

/- warning: category_theory.short_exact_sequence.Snd clashes with category_theory.short_exact_sequence.snd -> CategoryTheory.ShortExactSequence.snd
Case conversion may be inaccurate. Consider using '#align category_theory.short_exact_sequence.Snd CategoryTheory.ShortExactSequence.sndₓ'. -/
#print CategoryTheory.ShortExactSequence.snd /-
@[simps]
def snd : ShortExactSequence 𝒞 ⥤ 𝒞 where
  obj := snd
  map A B f := f.2
-/

/- warning: category_theory.short_exact_sequence.Trd clashes with category_theory.short_exact_sequence.trd -> CategoryTheory.ShortExactSequence.trd
Case conversion may be inaccurate. Consider using '#align category_theory.short_exact_sequence.Trd CategoryTheory.ShortExactSequence.trdₓ'. -/
#print CategoryTheory.ShortExactSequence.trd /-
@[simps]
def trd : ShortExactSequence 𝒞 ⥤ 𝒞 where
  obj := trd
  map A B f := f.3
-/

@[simps]
def fNat : fst 𝒞 ⟶ snd 𝒞 where
  app A := A.f
  naturality' A B f := f.sq1

@[simps]
def gNat : snd 𝒞 ⟶ trd 𝒞 where
  app A := A.g
  naturality' A B f := f.sq2

instance : HasZeroMorphisms (ShortExactSequence 𝒞)
    where
  Zero A B :=
    ⟨{  fst := 0
        snd := 0
        trd := 0 }⟩
  comp_zero := by intros; ext <;> apply comp_zero
  zero_comp := by intros; ext <;> apply zero_comp

@[simp]
theorem hom_zero_fst : (0 : A ⟶ B).1 = 0 :=
  rfl

@[simp]
theorem hom_zero_snd : (0 : A ⟶ B).2 = 0 :=
  rfl

@[simp]
theorem hom_zero_trd : (0 : A ⟶ B).3 = 0 :=
  rfl

variable {𝒞}

protected def functor (A : ShortExactSequence 𝒞) : Fin 3 ⥤ 𝒞 :=
  fin3FunctorMk ![A.1, A.2, A.3] A.f A.g

def functorMap {A B : ShortExactSequence 𝒞} (f : A ⟶ B) : ∀ i, A.Functor.obj i ⟶ B.Functor.obj i
  | ⟨0, h⟩ => f.1
  | ⟨1, h⟩ => f.2
  | ⟨2, h⟩ => f.3
  | ⟨i + 3, hi⟩ => by exfalso; revert hi; decide

/- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
unsafe def aux_tac : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.short_exact_sequence.aux_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.short_exact_sequence.aux_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic category_theory.short_exact_sequence.aux_tac -/
theorem functorMap_naturality {A B : ShortExactSequence 𝒞} (f : A ⟶ B) :
    ∀ (i j : Fin 3) (hij : i ≤ j),
      functorMap f i ≫ B.Functor.map hij.hom = A.Functor.map hij.hom ≫ functorMap f j
  | ⟨0, hi⟩, ⟨0, hj⟩, hij => by
    run_tac
      aux_tac
  | ⟨1, hi⟩, ⟨1, hj⟩, hij => by
    run_tac
      aux_tac
  | ⟨2, hi⟩, ⟨2, hj⟩, hij => by
    run_tac
      aux_tac
  | ⟨0, hi⟩, ⟨1, hj⟩, hij => f.sq1
  | ⟨1, hi⟩, ⟨2, hj⟩, hij => f.sq2
  | ⟨i + 3, hi⟩, _, _ => by exfalso; revert hi; decide
  | _, ⟨j + 3, hj⟩, _ => by exfalso; revert hj; decide
  | ⟨i + 1, hi⟩, ⟨0, hj⟩, H => by exfalso; revert H; decide
  | ⟨i + 2, hi⟩, ⟨1, hj⟩, H => by exfalso; revert H; decide
  | ⟨0, hi⟩, ⟨2, hj⟩, hij =>
    by
    have h01 : (0 : Fin 3) ⟶ 1 := hom_of_le (by decide)
    have h12 : (1 : Fin 3) ⟶ 2 := hom_of_le (by decide)
    calc
      functor_map f ⟨0, hi⟩ ≫ B.functor.map hij.hom =
          functor_map f ⟨0, hi⟩ ≫ B.functor.map h01 ≫ B.functor.map h12 :=
        _
      _ = (functor_map f ⟨0, hi⟩ ≫ B.functor.map h01) ≫ B.functor.map h12 := by rw [category.assoc]
      _ = (A.functor.map h01 ≫ functor_map f _) ≫ B.functor.map h12 := _
      _ = A.functor.map h01 ≫ functor_map f _ ≫ B.functor.map h12 := (category.assoc _ _ _)
      _ = A.functor.map h01 ≫ A.functor.map h12 ≫ functor_map f _ := _
      _ = A.functor.map hij.hom ≫ functor_map f ⟨2, hj⟩ := _
    · rw [← functor.map_comp]; congr
    · congr 1; exact f.sq1
    · congr 1; exact f.sq2
    · rw [← functor.map_comp_assoc]; congr

/- warning: category_theory.short_exact_sequence.Functor clashes with category_theory.short_exact_sequence.functor -> CategoryTheory.ShortExactSequence.functor
Case conversion may be inaccurate. Consider using '#align category_theory.short_exact_sequence.Functor CategoryTheory.ShortExactSequence.functorₓ'. -/
#print CategoryTheory.ShortExactSequence.functor /-
@[simps]
def functor : ShortExactSequence 𝒞 ⥤ Fin 3 ⥤ 𝒞
    where
  obj := ShortExactSequence.functor
  map A B f :=
    { app := functorMap f
      naturality' := fun i j hij => (functorMap_naturality f i j hij.le).symm }
  map_id' A := by ext i; fin_cases i <;> rfl
  map_comp' A B C f g := by ext i; fin_cases i <;> rfl
-/

end ShortExactSequence

namespace ShortExactSequence

variable {𝒞} [Abelian 𝒞]

variable {A B C : ShortExactSequence 𝒞} (f : A ⟶ B) (g : B ⟶ C)

section Iso

variable {A B C} (f g)

open scoped ZeroObject

/-- One form of the five lemma: if a morphism of short exact sequences has isomorphisms
as first and third component, then the second component is also an isomorphism. -/
theorem snd_isIso (h1 : IsIso f.1) (h3 : IsIso f.3) : IsIso f.2 :=
  @Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono 𝒞 _ _ 0 A.1 A.2 A.3 0 B.1 B.2 B.3 0 A.f A.g 0 B.f
    B.g 0 f.1 f.2 f.3 (by rw [zero_comp, zero_comp]) f.sq1 f.sq2 0 0 0 0 0
    (by rw [comp_zero, comp_zero]) (exact_zero_left_of_mono _) A.exact'
    ((epi_iff_exact_zero_right _).mp inferInstance) (exact_zero_left_of_mono _) B.exact'
    ((epi_iff_exact_zero_right _).mp inferInstance) _ _ _ _

/-- One form of the five lemma: if a morphism `f` of short exact sequences has isomorphisms
as first and third component, then `f` itself is an isomorphism. -/
theorem isIso_of_fst_of_trd (h1 : IsIso f.1) (h3 : IsIso f.3) : IsIso f :=
  {
    out := by
      haveI : is_iso f.2 := snd_is_iso f h1 h3
      refine' ⟨⟨inv f.1, inv f.2, inv f.3, _, _⟩, _, _⟩
      · dsimp; simp only [is_iso.inv_comp_eq, f.sq1_assoc, category.comp_id, is_iso.hom_inv_id]
      · dsimp; simp only [is_iso.inv_comp_eq, f.sq2_assoc, category.comp_id, is_iso.hom_inv_id]
      · ext <;> dsimp <;> simp only [is_iso.hom_inv_id]
      · ext <;> dsimp <;> simp only [is_iso.inv_hom_id] }

@[simps]
def isoOfComponents (f₁ : A.1 ≅ B.1) (f₂ : A.2 ≅ B.2) (f₃ : A.3 ≅ B.3)
    (sq1 : f₁.hom ≫ B.f = A.f ≫ f₂.hom) (sq2 : f₂.hom ≫ B.g = A.g ≫ f₃.hom) : A ≅ B
    where
  hom := ⟨f₁.hom, f₂.hom, f₃.hom, sq1, sq2⟩
  inv := by
    refine' ⟨f₁.inv, f₂.inv, f₃.inv, _, _⟩ <;> dsimp
    rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, sq1]
    rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, sq2]
  hom_inv_id' := by ext <;> apply iso.hom_inv_id
  inv_hom_id' := by ext <;> apply iso.inv_hom_id

@[simps]
def isoOfComponents' (f₁ : A.1 ≅ B.1) (f₂ : A.2 ⟶ B.2) (f₃ : A.3 ≅ B.3)
    (sq1 : f₁.hom ≫ B.f = A.f ≫ f₂) (sq2 : f₂ ≫ B.g = A.g ≫ f₃.hom) : A ≅ B :=
  let F : A ⟶ B := ⟨f₁.hom, f₂, f₃.hom, sq1, sq2⟩
  { hom := F
    inv := by
      haveI : is_iso F.2 := snd_is_iso _ inferInstance inferInstance
      refine' ⟨f₁.inv, inv F.2, f₃.inv, _, _⟩ <;> dsimp
      rw [iso.inv_comp_eq, ← category.assoc, is_iso.eq_comp_inv, sq1]
      rw [is_iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, sq2]
    hom_inv_id' := by ext <;> try apply iso.hom_inv_id; apply is_iso.hom_inv_id
    inv_hom_id' := by ext <;> try apply iso.inv_hom_id; apply is_iso.inv_hom_id }

end Iso

section Split

/-- A short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is *left split*
if there exists a morphism `φ : A₂ ⟶ A₁` such that `f ≫ φ = 𝟙 A₁`. -/
def LeftSplit (A : ShortExactSequence 𝒞) : Prop :=
  ∃ φ : A.2 ⟶ A.1, A.f ≫ φ = 𝟙 A.1

/-- A short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is *right split*
if there exists a morphism `φ : A₂ ⟶ A₁` such that `f ≫ φ = 𝟙 A₁`. -/
def RightSplit (A : ShortExactSequence 𝒞) : Prop :=
  ∃ χ : A.3 ⟶ A.2, χ ≫ A.g = 𝟙 A.3

variable {𝒜 : Type _} [Category 𝒜] [Abelian 𝒜]

theorem exact_of_split {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (χ : C ⟶ B) (φ : B ⟶ A) (hfg : f ≫ g = 0)
    (H : φ ≫ f + g ≫ χ = 𝟙 B) : Exact f g :=
  { w := hfg
    Epi :=
      by
      let ψ : (kernel_subobject g : 𝒜) ⟶ image_subobject f :=
        subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f
      suffices ψ ≫ imageToKernel f g hfg = 𝟙 _ by convert epi_of_epi ψ _; rw [this]; infer_instance
      rw [← cancel_mono (subobject.arrow _)]; swap; · infer_instance
      simp only [imageToKernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc]
      calc
        (kernel_subobject g).arrow ≫ φ ≫ f = (kernel_subobject g).arrow ≫ 𝟙 B := _
        _ = (kernel_subobject g).arrow := category.comp_id _
      rw [← H, preadditive.comp_add]
      simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc] }

-- move this
theorem exact_inl_snd (A B : 𝒜) : Exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
  exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

def mkOfSplit {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (φ : B ⟶ A) (χ : C ⟶ B) (hfg : f ≫ g = 0)
    (hφ : f ≫ φ = 𝟙 A) (hχ : χ ≫ g = 𝟙 C) (H : φ ≫ f + g ≫ χ = 𝟙 B) : ShortExactSequence 𝒜 :=
  { fst := A
    snd := B
    trd := C
    f
    g
    mono' :=
      haveI : mono (f ≫ φ) := by rw [hφ]; infer_instance
      mono_of_mono f φ
    epi' :=
      haveI : epi (χ ≫ g) := by rw [hχ]; infer_instance
      epi_of_epi χ g
    exact' := exact_of_split f g χ φ hfg H }

def mkOfSplit' {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C)
    (H : ∃ (φ : B ⟶ A) (χ : C ⟶ B), f ≫ g = 0 ∧ f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ φ ≫ f + g ≫ χ = 𝟙 B) :
    ShortExactSequence 𝒜 :=
  mkOfSplit f g H.some H.choose_spec.some H.choose_spec.choose_spec.1 H.choose_spec.choose_spec.2.1
    H.choose_spec.choose_spec.2.2.1 H.choose_spec.choose_spec.2.2.2

@[simp]
def mkSplit (A B : 𝒜) : ShortExactSequence 𝒜
    where
  fst := A
  snd := A ⊞ B
  trd := B
  f := biprod.inl
  g := biprod.snd
  exact' := exact_inl_snd _ _

/-- A *splitting* of a short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is
an isomorphism to the short exact sequence `0 ⟶ A₁ ⟶ A₁ ⊕ A₃ ⟶ A₃ ⟶ 0`,
where the left and right components of the isomorphism are identity maps. -/
structure Splitting (A : ShortExactSequence 𝒜) extends A ≅ mkSplit A.1 A.3 where
  fst_eq_id : hom.1 = 𝟙 A.1
  trd_eq_id : hom.3 = 𝟙 A.3

/-- A short exact sequence `0 ⟶ A₁ -f⟶ A₂ -g⟶ A₃ ⟶ 0` is *split* if there exist
`φ : A₂ ⟶ A₁` and `χ : A₃ ⟶ A₂` such that:
* `f ≫ φ = 𝟙 A₁`
* `χ ≫ g = 𝟙 A₃`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 A₂`
-/
def Split (A : ShortExactSequence 𝒜) : Prop :=
  ∃ (φ : A.2 ⟶ A.1) (χ : A.3 ⟶ A.2),
    A.f ≫ φ = 𝟙 A.1 ∧ χ ≫ A.g = 𝟙 A.3 ∧ χ ≫ φ = 0 ∧ φ ≫ A.f + A.g ≫ χ = 𝟙 A.2

theorem mkSplit_split (A B : 𝒜) : (mkSplit A B).split :=
  ⟨biprod.fst, biprod.inr, biprod.inl_fst, biprod.inr_snd, biprod.inr_fst, biprod.total⟩

theorem Splitting.split {A : ShortExactSequence 𝒜} (i : Splitting A) : A.split :=
  by
  refine' ⟨i.hom.2 ≫ biprod.fst ≫ i.inv.1, i.hom.3 ≫ biprod.inr ≫ i.inv.2, _⟩
  simp only [category.assoc, ← hom.sq1_assoc, hom.sq2]; dsimp
  simp only [biprod.inl_fst_assoc, biprod.inr_snd_assoc, category.comp_id, category.assoc, ←
    comp_fst, ← comp_snd_assoc, ← comp_trd, i.to_iso.hom_inv_id, i.to_iso.inv_hom_id]
  dsimp
  simp only [true_and_iff, biprod.inr_fst_assoc, zero_comp, eq_self_iff_true, comp_zero,
    category.id_comp]
  simp only [hom.sq1, ← hom.sq2_assoc, ← comp_add]
  simp only [← category.assoc, ← add_comp, biprod.total, category.comp_id, ← comp_snd,
    i.to_iso.hom_inv_id]
  rfl

def LeftSplit.splitting {A : ShortExactSequence 𝒜} (h : A.LeftSplit) : A.Splitting
    where
  toIso :=
    isoOfComponents' (Iso.refl _) (biprod.lift h.some A.g) (Iso.refl _)
      (by
        dsimp; simp only [category.id_comp]; ext
        · simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.some_spec.symm
        · simp only [exact.w, f_comp_g, biprod.lift_snd, category.assoc, exact_inl_snd])
      (by dsimp; simp only [category.comp_id, biprod.lift_snd])
  fst_eq_id := rfl
  trd_eq_id := rfl

def RightSplit.splitting {A : ShortExactSequence 𝒜} (h : A.RightSplit) : A.Splitting
    where
  toIso :=
    Iso.symm <|
      isoOfComponents' (Iso.refl _) (biprod.desc A.f h.some) (Iso.refl _)
        (by dsimp; simp only [biprod.inl_desc, category.id_comp])
        (by
          dsimp; simp only [category.comp_id]; ext
          · simp only [exact.w, f_comp_g, biprod.inl_desc_assoc, exact_inl_snd]
          · simpa only [biprod.inr_snd, biprod.inr_desc_assoc] using h.some_spec)
  fst_eq_id := rfl
  trd_eq_id := rfl

theorem tFAE_split (A : ShortExactSequence 𝒜) :
    TFAE [A.LeftSplit, A.RightSplit, A.split, Nonempty A.Splitting] :=
  by
  tfae_have 3 → 1; · rintro ⟨φ, χ, hφ, hχ, hχφ, H⟩; exact ⟨φ, hφ⟩
  tfae_have 3 → 2; · rintro ⟨φ, χ, hφ, hχ, hχφ, H⟩; exact ⟨χ, hχ⟩
  tfae_have 4 → 3; · rintro ⟨i⟩; exact i.split
  tfae_have 1 → 4; · intro h; exact ⟨h.splitting⟩
  tfae_have 2 → 4; · intro h; exact ⟨h.splitting⟩
  tfae_finish

end Split

end ShortExactSequence

namespace ShortExactSequence

open CategoryTheory.Preadditive

variable {𝒞} [Preadditive 𝒞] [HasImages 𝒞] [HasKernels 𝒞]

variable (A B : ShortExactSequence 𝒞)

local notation "π₁" => congr_arg Prod.fst

local notation "π₂" => congr_arg Prod.snd

protected def homInj (f : A ⟶ B) : (A.1 ⟶ B.1) × (A.2 ⟶ B.2) × (A.3 ⟶ B.3) :=
  ⟨f.1, f.2, f.3⟩

protected theorem homInj_injective : Function.Injective (ShortExactSequence.homInj A B) :=
  fun f g h => by
  let aux := π₂ h
  ext <;> [have := π₁ h; have := π₁ aux; have := π₂ aux] <;> exact this

instance : Add (A ⟶ B)
    where add f g :=
    { fst := f.1 + g.1
      snd := f.2 + g.2
      trd := f.3 + g.3
      sq1' := by rw [add_comp, comp_add, f.sq1, g.sq1]
      sq2' := by rw [add_comp, comp_add, f.sq2, g.sq2] }

instance : Neg (A ⟶ B)
    where neg f :=
    { fst := -f.1
      snd := -f.2
      trd := -f.3
      sq1' := by rw [neg_comp, comp_neg, f.sq1]
      sq2' := by rw [neg_comp, comp_neg, f.sq2] }

instance : Sub (A ⟶ B)
    where sub f g :=
    { fst := f.1 - g.1
      snd := f.2 - g.2
      trd := f.3 - g.3
      sq1' := by rw [sub_comp, comp_sub, f.sq1, g.sq1]
      sq2' := by rw [sub_comp, comp_sub, f.sq2, g.sq2] }

instance hasNsmul : SMul ℕ (A ⟶ B)
    where smul n f :=
    { fst := n • f.1
      snd := n • f.2
      trd := n • f.3
      sq1' := by rw [nsmul_comp, comp_nsmul, f.sq1]
      sq2' := by rw [nsmul_comp, comp_nsmul, f.sq2] }

instance hasZsmul : SMul ℤ (A ⟶ B)
    where smul n f :=
    { fst := n • f.1
      snd := n • f.2
      trd := n • f.3
      sq1' := by rw [zsmul_comp, comp_zsmul, f.sq1]
      sq2' := by rw [zsmul_comp, comp_zsmul, f.sq2] }

variable (𝒞)

instance : Preadditive (ShortExactSequence 𝒞)
    where
  homGroup A B :=
    (ShortExactSequence.homInj_injective A B).AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
  add_comp := by intros; ext <;> apply add_comp
  comp_add := by intros; ext <;> apply comp_add

instance fst_additive : (fst 𝒞).Additive where

instance snd_additive : (snd 𝒞).Additive where

instance trd_additive : (trd 𝒞).Additive where

end ShortExactSequence

end CategoryTheory

