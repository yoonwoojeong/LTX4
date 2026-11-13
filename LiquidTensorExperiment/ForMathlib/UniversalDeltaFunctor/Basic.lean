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

@[simp, reassoc]
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
    erw [nat_trans.id_app]
    erw [nat_trans.id_app]
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
    id_comp' := by intro F G f; ext; dsimp; simp
    comp_id' := by intro F G f; ext; dsimp; simp
    assoc' := by intro F G H W a b c; ext; dsimp; simp }

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
  Hom e₁ e₂ := e₁.Hom _ _ _ e₂
  id e := ⟨𝟙 _, Category.comp_id _⟩
  comp a b c f g := ⟨f.t ≫ g.t, by simp [reassoc_of f.w, g.w]⟩
  id_comp' a b f := Effacement.Hom.ext _ _ <| Category.id_comp _
  comp_id' a b f := Effacement.Hom.ext _ _ <| Category.comp_id _
  assoc' a b c d f g h := Effacement.Hom.ext _ _ <| Category.assoc _ _ _

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
  dsimp [effacement.cokernel_comparison]
  let t := _; change epi t
  suffices epi (limits.cokernel.π _ ≫ t) by
    skip
    apply epi_of_epi (limits.cokernel.π _) t
  simp only [limits.cokernel.π_desc]
  have : exact ((F.δ n).app e.ses) ((F (n + 1)).map e.ι) := F.δ_exact n e.ses
  rw [e.w] at this 
  apply abelian.pseudoelement.epi_of_pseudo_surjective
  intro q
  exact (abelian.pseudoelement.pseudo_exact_of_exact this).2 q (by simp)

-- This is true with fewer assumptions...
instance Effacement.mono_cokernelComparison {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    CategoryTheory.Mono e.cokernelComparison :=
  by
  dsimp [effacement.cokernel_comparison]
  let t := _; change CategoryTheory.Mono t
  suffices : exact ((F n).map (limits.cokernel.π e.ι)) ((F.δ n).app e.ses)
  exact
    abelian.category_theory.limits.cokernel.desc.category_theory.mono
      ((F n).map (limits.cokernel.π e.ι)) ((F.δ n).app (effacement.ses e)) this
  exact F.exact_δ n e.ses

instance Effacement.isIso_cokernelComparison {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    IsIso e.cokernelComparison :=
  isIso_of_mono_of_epi _

/-- The cokernel isomorphism associated to an effacement. -/
def Effacement.cokernelIso {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    Limits.cokernel ((F n).map (Limits.cokernel.π e.ι)) ≅ (F (n + 1)).obj X :=
  asIso e.cokernelComparison

@[simp, reassoc]
theorem Effacement.cokernelIso_spec {F : A ⥤δ B} {X n} (e : Effacement F X n) :
    Limits.cokernel.π _ ≫ e.cokernelIso.Hom = (F.δ n).app e.ses :=
  Limits.cokernel.π_desc _ _ _

/-- An auxiliary definition used in `lift` below. -/
def Effacement.liftAppAux {F G : A ⥤δ B} {X n} (η : F n ⟶ G n) (e : Effacement F X n) :
    (F (n + 1)).obj X ⟶ (G (n + 1)).obj X :=
  e.cokernelIso.inv ≫
    Limits.cokernel.desc _ (η.app _ ≫ (G.δ n).app e.ses)
      (by
        rw [← category.assoc, η.naturality, category.assoc]
        erw [(G.exact_δ n e.ses).w]
        rw [limits.comp_zero])

/-- An auxiliary definition used in `lift` below. -/
def Effacement.mapSes {F : A ⥤δ B} {X n} (e₁ e₂ : Effacement F X n) (q : e₁ ⟶ e₂) : e₁.ses ⟶ e₂.ses
    where
  fst := 𝟙 _
  snd := q.t
  trd := by
    refine' limits.cokernel.desc _ _ _
    refine' _ ≫ limits.cokernel.π _
    exact q.t
    rw [← category.assoc, q.w, limits.cokernel.condition]
  sq1' := by simp only [category.id_comp]; exact q.w.symm
  sq2' := by
    erw [limits.cokernel.π_desc]
    rfl

theorem Effacement.liftAppAux_eq_of_hom {F G : A ⥤δ B} {X n} (η : F n ⟶ G n)
    (e₁ e₂ : Effacement F X n) (q : e₁ ⟶ e₂) : e₁.liftAppAux η = e₂.liftAppAux η :=
  by
  dsimp only [effacement.lift_app_aux]
  rw [iso.inv_comp_eq]
  apply limits.coequalizer.hom_ext
  simp only [limits.cokernel.π_desc, effacement.cokernel_iso_spec_assoc]
  rw [← category.assoc]; let t := _; change _ = t ≫ _
  have ht : t = (F n).map (e₁.map_ses e₂ q).trd ≫ limits.cokernel.π _ :=
    by
    dsimp [t]; rw [iso.comp_inv_eq]
    simp only [category.assoc, effacement.cokernel_iso_spec]
    erw [(F.δ n).naturality (e₁.map_ses e₂ q)]
    dsimp [effacement.map_ses]
    simp
  rw [ht]; clear ht t
  simp only [category.assoc, limits.cokernel.π_desc]
  erw [nat_trans.naturality_assoc]
  congr 1
  erw [(G.δ n).naturality (e₁.map_ses e₂ q)]
  symm
  convert category.comp_id _
  exact Functor.map_id _ _

theorem Effacement.liftAppAux_well_defined {F G : A ⥤δ B} {X n} (η : F n ⟶ G n)
    (e₁ e₂ : Effacement F X n) : e₁.liftAppAux η = e₂.liftAppAux η :=
  by
  let II := limits.biprod e₁.I e₂.I
  let ι : X ⟶ II := limits.biprod.lift e₁.ι e₂.ι
  let e : effacement F X n := ⟨II, ι, _⟩
  -- use additivity of `F n`.
  swap
  · haveI : limits.preserves_binary_biproducts (F (n + 1)) :=
      limits.preserves_binary_biproducts_of_preserves_biproducts (F (n + 1))
    let E : (F (n + 1)).obj (e₁.I ⊞ e₂.I) ≅ (F (n + 1)).obj e₁.I ⊞ (F (n + 1)).obj e₂.I :=
      functor.map_biprod (F (n + 1)) _ _
    rw [← cancel_mono E.hom, limits.zero_comp]
    rw [functor.map_biprod_hom]
    apply limits.biprod.hom_ext
    · simp only [category.assoc, limits.biprod.lift_fst, limits.zero_comp]
      simp only [← functor.map_comp, limits.biprod.lift_fst, e₁.w]
    · simp only [category.assoc, limits.biprod.lift_snd, limits.zero_comp]
      simp only [← functor.map_comp, limits.biprod.lift_snd, e₂.w]
  let π₁ : e ⟶ e₁ := ⟨limits.biprod.fst, _⟩
  swap; · dsimp [e]; simp
  let π₂ : e ⟶ e₂ := ⟨limits.biprod.snd, _⟩
  swap; · dsimp [e]; simp
  rw [← effacement.lift_app_aux_eq_of_hom η _ _ π₁]
  rw [← effacement.lift_app_aux_eq_of_hom η _ _ π₂]

theorem Effacement.lift_naturality {F G : A ⥤δ B} {X Y n} (η : F n ⟶ G n) (e₁ : Effacement F X n)
    (e₂ : Effacement F Y n) (f : X ⟶ Y) :
    e₁.liftAppAux η ≫ (G (n + 1)).map f = (F (n + 1)).map f ≫ e₂.liftAppAux η :=
  by
  let e₁' : effacement F X n := ⟨limits.biprod e₁.I e₂.I, limits.biprod.lift e₁.ι (f ≫ e₂.ι), _⟩
  -- again, additivity
  swap
  · haveI : limits.preserves_binary_biproducts (F (n + 1)) :=
      limits.preserves_binary_biproducts_of_preserves_biproducts (F (n + 1))
    let E : (F (n + 1)).obj (e₁.I ⊞ e₂.I) ≅ (F (n + 1)).obj e₁.I ⊞ (F (n + 1)).obj e₂.I :=
      functor.map_biprod (F (n + 1)) _ _
    rw [← cancel_mono E.hom, limits.zero_comp]
    rw [functor.map_biprod_hom]
    apply limits.biprod.hom_ext
    simp only [category.assoc, limits.biprod.lift_fst, limits.zero_comp]
    simp only [← functor.map_comp, limits.biprod.lift_fst]
    exact e₁.w
    simp only [category.assoc, limits.biprod.lift_snd, limits.zero_comp]
    simp only [← functor.map_comp, limits.biprod.lift_snd]
    simp only [functor.map_comp, e₂.w, limits.comp_zero]
  rw [e₁.lift_app_aux_well_defined η e₁']
  dsimp [effacement.lift_app_aux]
  simp only [category.assoc, iso.inv_comp_eq]
  apply limits.coequalizer.hom_ext
  simp only [limits.coequalizer_as_cokernel, limits.cokernel.π_desc_assoc, category.assoc]
  erw [limits.cokernel.π_desc_assoc]
  let q : e₁'.ses ⟶ e₂.ses :=
    ⟨f, limits.biprod.snd, limits.cokernel.desc _ (limits.biprod.snd ≫ limits.cokernel.π _) _, _, _⟩
  erw [← (F.δ n).naturality_assoc q]
  erw [← (G.δ n).naturality q]
  dsimp
  have : (F.δ n).app e₂.ses ≫ e₂.cokernel_iso.inv = limits.cokernel.π _ := by rw [iso.comp_inv_eq];
    simp
  rw [reassoc_of this]; clear this
  simp only [category.assoc, limits.cokernel.π_desc]
  erw [← nat_trans.naturality_assoc]
  rfl
  · dsimp [e₁']
    simp
  · dsimp [e₁', effacement.ses]
    simp
  · dsimp [e₁', effacement.ses]; simp

theorem Effacement.lift_δ_naturality {F G : A ⥤δ B} {n} (η : F n ⟶ G n) (S : ShortExactSequence A)
    (e₁ : Effacement F S.fst n) (e₂ : Effacement F S.snd n) :
    (F.δ n).app S ≫ e₁.liftAppAux η = η.app _ ≫ (G.δ _).app S :=
  by
  let e₁' : effacement F S.fst n := ⟨e₂.I, S.f ≫ e₂.ι, by simp [e₂.w]⟩
  rw [e₁.lift_app_aux_well_defined η e₁']
  let q : S ⟶ e₁'.ses := ⟨𝟙 _, e₂.ι, S.exact'.epi_desc (e₂.ι ≫ limits.cokernel.π _) _, _, _⟩
  dsimp only [effacement.lift_app_aux]
  have : (F.δ n).app S ≫ e₁'.cokernel_iso.inv = (F n).map q.trd ≫ limits.cokernel.π _ :=
    by
    rw [iso.comp_inv_eq]
    simp
    erw [(F.δ n).naturality q]
    dsimp
    simp only [Functor.map_id, category.comp_id]
  slice_lhs 1 2 => erw [this]
  simp only [category.assoc, limits.cokernel.π_desc]
  erw [η.naturality_assoc]
  congr 1
  erw [(G.δ n).naturality q]; convert category.comp_id _
  · dsimp; simpa only [Functor.map_id]
  rw [← category.assoc]; exact limits.cokernel.condition _
  · dsimp; simpa
  · dsimp; simpa only [exact.comp_epi_desc]

/-- An auxiliary definition used in `lift` below. -/
def Effaceable.liftComponent (F G : A ⥤δ B) [Effaceable F] (n) (η : F n ⟶ G n) :
    F (n + 1) ⟶ G (n + 1)
    where
  app X := (chooseEffacement F X n).liftAppAux η
  naturality' := by
    intro X Y f
    symm
    apply effacement.lift_naturality

/-- The lift of η0. -/
noncomputable def Effaceable.lift (F G : A ⥤δ B) [Effaceable F] (η0 : F 0 ⟶ G 0) : ∀ n, F n ⟶ G n
  | 0 => η0
  | n + 1 => Effaceable.liftComponent _ _ _ (effaceable.lift n)

/-- The lift of η0, as an actual delta functor. -/
def Effaceable.liftWithδ (F G : A ⥤δ B) [Effaceable F] (η0 : F 0 ⟶ G 0) : F ⟶ G
    where
  η := Effaceable.lift _ _ η0
  comm' := by
    intro n; ext S : 2
    dsimp
    rcases n with (_ | n)
    · dsimp [effaceable.lift]
      apply effacement.lift_δ_naturality
      apply choose_effacement
    · dsimp [effaceable.lift]
      apply effacement.lift_δ_naturality
      apply choose_effacement

theorem Effaceable.liftWithδ_unique (F G : A ⥤δ B) [Effaceable F] (η0 : F 0 ⟶ G 0) (η : F ⟶ G)
    (hη : η 0 = η0) : η = Effaceable.liftWithδ F G η0 :=
  by
  ext1 n; induction' n with n hn
  · rw [hη]; rfl
  · ext T; dsimp [effaceable.lift_with_δ] at hn ⊢
    change _ = ((effaceable.lift F G η0) _).app _
    dsimp [effaceable.lift]
    change _ = effaceable.lift F G η0 n at hn 
    erw [← hn]
    dsimp [effaceable.lift_component]
    dsimp [effacement.lift_app_aux]
    rw [iso.eq_inv_comp]
    apply limits.coequalizer.hom_ext
    dsimp
    simp only [effacement.cokernel_iso_spec_assoc, limits.cokernel.π_desc]
    have :=
      effacement.lift_δ_naturality (η n) (choose_effacement F T n).ses (choose_effacement _ _ _)
        (choose_effacement _ _ _)
    erw [← this]; congr 1
    dsimp only [effacement.lift_app_aux]
    rw [iso.eq_inv_comp]
    apply limits.coequalizer.hom_ext
    simp only [effacement.cokernel_iso_spec_assoc, limits.cokernel.π_desc]
    clear this
    have := η.comm' n
    apply_fun fun e => e.app (choose_effacement F (choose_effacement F T n).ses.fst n).ses at this 
    exact this

end Tohoku

open Tohoku

theorem universalOfEffaceable (F : A ⥤δ B) [Effaceable F] : Universal F :=
  by
  constructor; intro G η0
  use effaceable.lift_with_δ F G η0
  constructor
  · ext; rfl
  · intro η hη; apply effaceable.lift_with_δ_unique; exact hη

-- Sketch:
-- TODO: Prove stacks tag 010T. -- DONE!
-- TODO: Construct `Ext^*(-,X)` a delta functor (on objects!).
-- These should be functors `Aᵒᵖ ⥤ Ab` (assuming `A` has enough projectives).
-- Use `010T` to see that `Ext^*(-,X)` is universal.
end DeltaFunctor

end CategoryTheory

