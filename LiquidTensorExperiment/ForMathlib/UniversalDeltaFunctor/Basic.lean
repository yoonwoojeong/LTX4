import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import LiquidTensorExperiment.ForMathlib.ShortExactSequence
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.ExactLiftDesc

#align_import for_mathlib.universal_delta_functor.basic

/-!

Refs:
1. Grothendieck's Tôhoku paper
2. Stacks tag 010T

-/


noncomputable section

namespace CategoryTheory

universe v v' u u'

variable (A : Type u) (B : Type u') [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]

/-- Cohomological covariant delta functor. -/
@[nolint has_inhabited_instance]
structure DeltaFunctor where
  f : ℕ → A ⥤ B
  [Additive : ∀ n, Functor.Additive (F n)]
  δ : ∀ n : ℕ, ShortExactSequence.trd A ⋙ F n ⟶ ShortExactSequence.fst A ⋙ F (n + 1)
  Mono : ∀ S : ShortExactSequence _, Mono ((F 0).map S.f)
  exact' : ∀ (n : ℕ) (S : ShortExactSequence _), Exact ((F n).map S.f) ((F n).map S.g)
  exact_δ : ∀ (n : ℕ) (S : ShortExactSequence _), Exact ((F n).map S.g) ((δ n).app S)
  δ_exact : ∀ (n : ℕ) (S : ShortExactSequence _), Exact ((δ n).app S) ((F (n + 1)).map S.f)

namespace DeltaFunctor

infixr:26 " ⥤δ " => DeltaFunctor

instance : CoeFun (A ⥤δ B) fun F => ℕ → A ⥤ B :=
  ⟨f⟩

instance additive_apply (F : A ⥤δ B) (n : ℕ) : Functor.Additive (F n) :=
  F.Additive n

variable {A B}

/-- Morphisms of cohomological covariant delta functors. -/
@[nolint has_inhabited_instance]
structure Hom (F G : A ⥤δ B) where
  η : ∀ n, F n ⟶ G n
  comm' : ∀ n, F.δ n ≫ whiskerLeft _ (η _) = whiskerLeft _ (η _) ≫ G.δ _

instance : Quiver (A ⥤δ B) where Hom := Hom

namespace Hom

instance {F G : A ⥤δ B} : CoeFun (F ⟶ G) fun η => ∀ n, F n ⟶ G n :=
  ⟨η⟩

@[ext]
theorem ext {F G : A ⥤δ B} (η γ : F ⟶ G) (h : ∀ n, η n = γ n) : η = γ := by cases η; cases γ; congr;
  ext1; apply h

@[simp]
theorem η_eq_coe {F G : A ⥤δ B} (η : F ⟶ G) (n : ℕ) : η.η n = η n :=
  rfl

@[reassoc (attr := simp)]
theorem comm {F G : A ⥤δ B} (η : F ⟶ G) (n : ℕ) (S : ShortExactSequence A) :
    (F.δ n).app S ≫ (η (n + 1)).app S.fst = (η n).app S.trd ≫ (G.δ n).app S :=
  by
  have := η.comm' n
  apply_fun fun e => e.app S at this 
  exact this

/-- Identity morphisms of delta functors. -/
def id (F : A ⥤δ B) : F ⟶ F :=
  ⟨fun n => 𝟙 _, by
    intro n
    ext; dsimp
    erw [NatTrans.id_app]
    erw [NatTrans.id_app]
    simp⟩

@[simp]
theorem id_apply (F : A ⥤δ B) (n : ℕ) : id F n = 𝟙 _ :=
  rfl

/-- Compositions of morphisms of delta functors. -/
def comp {F G H : A ⥤δ B} (η : F ⟶ G) (γ : G ⟶ H) : Hom F H
    where
  η n := η n ≫ γ n
  comm' := by
    intro n; ext
    dsimp
    simp

@[simp]
theorem comp_apply {F G H : A ⥤δ B} (η : F ⟶ G) (γ : G ⟶ H) (n : ℕ) :
    (Hom.comp η γ) n = η n ≫ γ n :=
  rfl

end Hom

/-- delta functors form a category. -/
instance category : Category (A ⥤δ B) :=
  {
    (inferInstance : Quiver (A ⥤δ B)) with
    id := fun F => Hom.id _
    comp := fun X Y Z F G => Hom.comp F G
    id_comp := by intro F G f; ext; dsimp; simp
    comp_id := by intro F G f; ext; dsimp; simp
    assoc := by intro F G H W a b c; ext; dsimp; simp }

/-- Universal delta functors. -/
class Universal (F : A ⥤δ B) : Prop where
  cond : ∀ (G : A ⥤δ B) (e0 : F 0 ⟶ G 0), ∃! e : F ⟶ G, (e : ∀ n, F n ⟶ G n) 0 = e0

namespace Tohoku

/-- An effacement relative to a δ functor. -/
@[nolint has_inhabited_instance]
structure Effacement (F : A ⥤δ B) (X : A) (n : ℕ) where
  i : A
  ι : X ⟶ I
  [Mono : CategoryTheory.Mono ι]
  w : (F (n + 1)).map ι = 0

/-- Morphisms between effacements. -/
@[ext, nolint has_inhabited_instance]
structure Effacement.Hom (F : A ⥤δ B) (X : A) (n : ℕ) (e₁ e₂ : Effacement F X n) where
  t : e₁.i ⟶ e₂.i
  w : e₁.ι ≫ t = e₂.ι

instance Effacement.category (F : A ⥤δ B) (X : A) (n : ℕ) : Category (Effacement F X n)
    where
  Hom e₁ e₂ := e₁.hom _ _ _ e₂
  id e := ⟨𝟙 _, Category.comp_id _⟩
  comp a b c f g := ⟨f.t ≫ g.t, by simp [reassoc_of f.w, g.w]⟩
  id_comp a b f := Effacement.Hom.ext _ _ <| Category.id_comp _
  comp_id a b f := Effacement.Hom.ext _ _ <| Category.comp_id _
  assoc a b c d f g h := Effacement.Hom.ext _ _ <| Category.assoc _ _ _

instance effacement_mono (F : A ⥤δ B) (X : A) (n : ℕ) (e : Effacement F X n) :
    CategoryTheory.Mono e.ι :=
  e.Mono

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-- Effacable δ functors. -/
class Effaceable (F : A ⥤δ B) : Prop where
  cond : ∀ (X : A) (n : ℕ), Nonempty (Effacement F X n)

/-- A choice of effacement. -/
def chooseEffacement (F : A ⥤δ B) [Effaceable F] (X : A) (n : ℕ) : Effacement F X n :=
  (Effaceable.cond F X n).some

/-- A short exact sequence associated to an effacement -/
def Effacement.ses {F : A ⥤δ B} {X n} (e : Effacement F X n) : ShortExactSequence A
    where
  fst := X
  snd := e.i
  trd := Limits.cokernel e.ι
  f := e.ι
  g := Limits.cokernel.π _
  exact' := Abelian.exact_cokernel e.ι

/-- An auxiliary definition used to obtain the isomorphism below -/
def Effacement.cokernelComparison {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    Limits.cokernel ((F n).map (Limits.cokernel.π e.ι)) ⟶ (F (n + 1)).obj X :=
  Limits.cokernel.desc _ ((F.δ n).app e.ses) (F.exact_δ n e.ses).w

open scoped ZeroObject

instance Effacement.epi_cokernelComparison {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    Epi e.cokernelComparison :=
  by
  dsimp [Effacement.cokernelComparison]
  let t := _; change epi t
  suffices epi (Limits.cokernel.π _ ≫ t) by
    skip
    apply epi_of_epi (Limits.cokernel.π _) t
  simp only [Limits.cokernel.π_desc]
  have : exact ((F.δ n).app e.ses) ((F (n + 1)).map e.ι) := F.δ_exact n e.ses
  rw [e.w] at this 
  apply Abelian.Pseudoelement.epi_of_pseudo_surjective
  intro q
  exact (Abelian.Pseudoelement.pseudo_exact_of_exact this).2 q (by simp)

-- This is true with fewer assumptions...
instance Effacement.mono_cokernelComparison {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    CategoryTheory.Mono e.cokernelComparison :=
  by
  dsimp [Effacement.cokernelComparison]
  let t := _; change CategoryTheory.Mono t
  suffices : exact ((F n).map (Limits.cokernel.π e.ι)) ((F.δ n).app e.ses)
  exact
    abelian.category_theory.limits.cokernel.desc.category_theory.mono
      ((F n).map (Limits.cokernel.π e.ι)) ((F.δ n).app (Effacement.ses e)) this
  exact F.exact_δ n e.ses

instance Effacement.isIso_cokernelComparison {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    IsIso e.cokernelComparison :=
  isIso_of_mono_of_epi _

/-- The cokernel isomorphism associated to an effacement. -/
def Effacement.cokernelIso {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    Limits.cokernel ((F n).map (Limits.cokernel.π e.ι)) ≅ (F (n + 1)).obj X :=
  asIso e.cokernelComparison

@[reassoc (attr := simp)]
theorem Effacement.cokernelIso_spec {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    Limits.cokernel.π _ ≫ e.cokernelIso.hom = (F.δ n).app e.ses :=
  Limits.cokernel.π_desc _ _ _

/-- An auxiliary definition used in `lift` below. -/
def Effacement.liftAppAux {F G : A ⥤δ B} {X n} (η : F n ⟶ G n) (e : Effacement F X n) :
    (F (n + 1)).obj X ⟶ (G (n + 1)).obj X :=
  e.cokernelIso.inv ≫
    Limits.cokernel.desc _ (η.app _ ≫ (G.δ n).app e.ses)
      (by
        rw [← Category.assoc, η.naturality, Category.assoc]
        erw [(G.exact_δ n e.ses).w]
        rw [Limits.comp_zero])

/-- An auxiliary definition used in `lift` below. -/
def Effacement.mapSes {F : A ⥤δ B} {X n} (e₁ e₂ : Effacement F X n) (q : e₁ ⟶ e₂) : e₁.ses ⟶ e₂.ses
    where
  fst := 𝟙 _
  snd := q.t
  trd := by
    refine' Limits.cokernel.desc _ _ _
    refine' _ ≫ Limits.cokernel.π _
    exact q.t
    rw [← Category.assoc, q.w, Limits.cokernel.condition]
  sq1' := by simp only [Category.id_comp]; exact q.w.symm
  sq2' := by
    erw [Limits.cokernel.π_desc]
    rfl

theorem Effacement.liftAppAux_eq_of_hom {F G : A ⥤δ B} {X n} (η : F n ⟶ G n)
    (e₁ e₂ : Effacement F X n) (q : e₁ ⟶ e₂) : e₁.liftAppAux η = e₂.liftAppAux η :=
  by
  dsimp only [Effacement.liftAppAux]
  rw [Iso.inv_comp_eq]
  apply Limits.coequalizer.hom_ext
  simp only [Limits.cokernel.π_desc, Effacement.cokernelIso_spec_assoc]
  rw [← Category.assoc]; let t := _; change _ = t ≫ _
  have ht : t = (F n).map (e₁.mapSes e₂ q).trd ≫ Limits.cokernel.π _ :=
    by
    dsimp [t]; rw [Iso.comp_inv_eq]
    simp only [Category.assoc, Effacement.cokernelIso_spec]
    erw [(F.δ n).naturality (e₁.mapSes e₂ q)]
    dsimp [Effacement.mapSes]
    simp
  rw [ht]; clear ht t
  simp only [Category.assoc, Limits.cokernel.π_desc]
  erw [NatTrans.naturality_assoc]
  congr 1
  erw [(G.δ n).naturality (e₁.mapSes e₂ q)]
  symm
  convert Category.comp_id _
  exact Functor.map_id _ _

theorem Effacement.liftAppAux_well_defined {F G : A ⥤δ B} {X n} (η : F n ⟶ G n)
    (e₁ e₂ : Effacement F X n) : e₁.liftAppAux η = e₂.liftAppAux η :=
  by
  let II := Limits.biprod e₁.I e₂.I
  let ι : X ⟶ II := Limits.biprod.lift e₁.ι e₂.ι
  let e : effacement F X n := ⟨II, ι, _⟩
  -- use additivity of `F n`.
  swap
  · haveI : Limits.PreservesBinaryBiproducts (F (n + 1)) :=
      Limits.preservesBinaryBiproductsOfPreservesBiproducts (F (n + 1))
    let E : (F (n + 1)).obj (e₁.I ⊞ e₂.I) ≅ (F (n + 1)).obj e₁.I ⊞ (F (n + 1)).obj e₂.I :=
      Functor.mapBiprod (F (n + 1)) _ _
    rw [← cancel_mono E.hom, Limits.zero_comp]
    rw [Functor.mapBiprod_hom]
    apply Limits.biprod.hom_ext
    · simp only [Category.assoc, Limits.biprod.lift_fst, Limits.zero_comp]
      simp only [← Functor.map_comp, Limits.biprod.lift_fst, e₁.w]
    · simp only [Category.assoc, Limits.biprod.lift_snd, Limits.zero_comp]
      simp only [← Functor.map_comp, Limits.biprod.lift_snd, e₂.w]
  let π₁ : e ⟶ e₁ := ⟨Limits.biprod.fst, _⟩
  swap; · dsimp [e]; simp
  let π₂ : e ⟶ e₂ := ⟨Limits.biprod.snd, _⟩
  swap; · dsimp [e]; simp
  rw [← Effacement.liftAppAux_eq_of_hom η _ _ π₁]
  rw [← Effacement.liftAppAux_eq_of_hom η _ _ π₂]

theorem Effacement.lift_naturality {F G : A ⥤δ B} {X Y n} (η : F n ⟶ G n) (e₁ : Effacement F X n)
    (e₂ : Effacement F Y n) (f : X ⟶ Y) :
    e₁.liftAppAux η ≫ (G (n + 1)).map f = (F (n + 1)).map f ≫ e₂.liftAppAux η :=
  by
  let e₁' : effacement F X n := ⟨Limits.biprod e₁.I e₂.I, Limits.biprod.lift e₁.ι (f ≫ e₂.ι), _⟩
  -- again, additivity
  swap
  · haveI : Limits.PreservesBinaryBiproducts (F (n + 1)) :=
      Limits.preservesBinaryBiproductsOfPreservesBiproducts (F (n + 1))
    let E : (F (n + 1)).obj (e₁.I ⊞ e₂.I) ≅ (F (n + 1)).obj e₁.I ⊞ (F (n + 1)).obj e₂.I :=
      Functor.mapBiprod (F (n + 1)) _ _
    rw [← cancel_mono E.hom, Limits.zero_comp]
    rw [Functor.mapBiprod_hom]
    apply Limits.biprod.hom_ext
    simp only [Category.assoc, Limits.biprod.lift_fst, Limits.zero_comp]
    simp only [← Functor.map_comp, Limits.biprod.lift_fst]
    exact e₁.w
    simp only [Category.assoc, Limits.biprod.lift_snd, Limits.zero_comp]
    simp only [← Functor.map_comp, Limits.biprod.lift_snd]
    simp only [Functor.map_comp, e₂.w, Limits.comp_zero]
  rw [e₁.liftAppAux_well_defined η e₁']
  dsimp [Effacement.liftAppAux]
  simp only [Category.assoc, Iso.inv_comp_eq]
  apply Limits.coequalizer.hom_ext
  simp only [Limits.coequalizer_as_cokernel, Limits.cokernel.π_desc_assoc, Category.assoc]
  erw [Limits.cokernel.π_desc_assoc]
  let q : e₁'.ses ⟶ e₂.ses :=
    ⟨f, Limits.biprod.snd, Limits.cokernel.desc _ (Limits.biprod.snd ≫ Limits.cokernel.π _) _, _, _⟩
  erw [← (F.δ n).naturality_assoc q]
  erw [← (G.δ n).naturality q]
  dsimp
  have : (F.δ n).app e₂.ses ≫ e₂.cokernelIso.inv = Limits.cokernel.π _ := by rw [Iso.comp_inv_eq];
    simp
  rw [reassoc_of this]; clear this
  simp only [Category.assoc, Limits.cokernel.π_desc]
  erw [← NatTrans.naturality_assoc]
  rfl
  · dsimp [e₁']
    simp
  · dsimp [e₁', Effacement.ses]
    simp
  · dsimp [e₁', Effacement.ses]; simp

theorem Effacement.lift_δ_naturality {F G : A ⥤δ B} {n} (η : F n ⟶ G n) (S : ShortExactSequence A)
    (e₁ : Effacement F S.fst n) (e₂ : Effacement F S.snd n) :
    (F.δ n).app S ≫ e₁.liftAppAux η = η.app _ ≫ (G.δ _).app S :=
  by
  let e₁' : effacement F S.fst n := ⟨e₂.I, S.f ≫ e₂.ι, by simp [e₂.w]⟩
  rw [e₁.liftAppAux_well_defined η e₁']
  let q : S ⟶ e₁'.ses := ⟨𝟙 _, e₂.ι, S.exact'.epiDesc (e₂.ι ≫ Limits.cokernel.π _) _, _, _⟩
  dsimp only [Effacement.liftAppAux]
  have : (F.δ n).app S ≫ e₁'.cokernelIso.inv = (F n).map q.trd ≫ Limits.cokernel.π _ :=
    by
    rw [Iso.comp_inv_eq]
    simp
    erw [(F.δ n).naturality q]
    dsimp
    simp only [Functor.map_id, Category.comp_id]
  slice_lhs 1 2 => erw [this]
  simp only [Category.assoc, Limits.cokernel.π_desc]
  erw [η.naturality_assoc]
  congr 1
  erw [(G.δ n).naturality q]; convert Category.comp_id _
  · dsimp; simpa only [Functor.map_id]
  rw [← Category.assoc]; exact Limits.cokernel.condition _
  · dsimp; simpa
  · dsimp; simpa only [Exact.comp_epiDesc]

/-- An auxiliary definition used in `lift` below. -/
def Effaceable.liftComponent (F G : A ⥤δ B) [Effaceable F] (n) (η : F n ⟶ G n) :
    F (n + 1) ⟶ G (n + 1)
    where
  app X := (chooseEffacement F X n).liftAppAux η
  naturality := by
    intro X Y f
    symm
    apply Effacement.lift_naturality

/-- The lift of η0. -/
noncomputable def Effaceable.lift (F G : A ⥤δ B) [Effaceable F] (η0 : F 0 ⟶ G 0) : ∀ n, F n ⟶ G n
  | 0 => η0
  | n + 1 => Effaceable.liftComponent _ _ _ (Effaceable.lift n)

/-- The lift of η0, as an actual delta functor. -/
def Effaceable.liftWithδ (F G : A ⥤δ B) [Effaceable F] (η0 : F 0 ⟶ G 0) : F ⟶ G
    where
  η := Effaceable.lift _ _ η0
  comm' := by
    intro n; ext S : 2
    dsimp
    rcases n with (_ | n)
    · dsimp [Effaceable.lift]
      apply Effacement.lift_δ_naturality
      apply CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement
    · dsimp [Effaceable.lift]
      apply Effacement.lift_δ_naturality
      apply CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement

theorem Effaceable.liftWithδ_unique (F G : A ⥤δ B) [Effaceable F] (η0 : F 0 ⟶ G 0) (η : F ⟶ G)
    (hη : η 0 = η0) : η = Effaceable.liftWithδ F G η0 :=
  by
  ext1 n; induction' n with n hn
  · rw [hη]; rfl
  · ext T; dsimp [Effaceable.liftWithδ] at hn ⊢
    change _ = ((Effaceable.lift F G η0) _).app _
    dsimp [Effaceable.lift]
    change _ = Effaceable.lift F G η0 n at hn 
    erw [← hn]
    dsimp [Effaceable.liftComponent]
    dsimp [Effacement.liftAppAux]
    rw [Iso.eq_inv_comp]
    apply Limits.coequalizer.hom_ext
    dsimp
    simp only [Effacement.cokernelIso_spec_assoc, Limits.cokernel.π_desc]
    have :=
      Effacement.lift_δ_naturality (η n) (CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement F T n).ses (CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement _ _ _)
        (CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement _ _ _)
    erw [← this]; congr 1
    dsimp only [Effacement.liftAppAux]
    rw [Iso.eq_inv_comp]
    apply Limits.coequalizer.hom_ext
    simp only [Effacement.cokernelIso_spec_assoc, Limits.cokernel.π_desc]
    clear this
    have := η.comm' n
    apply_fun fun e => e.app (CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement F (CategoryTheory.DeltaFunctor.Tohoku.chooseEffacement F T n).ses.fst n).ses at this 
    exact this

end Tohoku

open Tohoku

theorem universalOfEffaceable (F : A ⥤δ B) [Effaceable F] : Universal F :=
  by
  constructor; intro G η0
  use Effaceable.liftWithδ F G η0
  constructor
  · ext; rfl
  · intro η hη; apply Effaceable.liftWithδ_unique; exact hη

-- Sketch:
-- TODO: Prove stacks tag 010T. -- DONE!
-- TODO: Construct `Ext^*(-,X)` a delta functor (on objects!).
-- These should be functors `Aᵒᵖ ⥤ Ab` (assuming `A` has enough projectives).
-- Use `010T` to see that `Ext^*(-,X)` is universal.
end DeltaFunctor

end CategoryTheory

