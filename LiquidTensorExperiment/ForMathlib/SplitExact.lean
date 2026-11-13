/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

#align_import for_mathlib.split_exact

/-!
# Short exact sequences, and splittings.

`short_exact f g` is the proposition that `0 ⟶ A -f⟶ B -g⟶ C ⟶ 0` is an exact sequence.

We define when a short exact sequence is left-split, right-split, and split.

In an abelian category, a left-split short exact sequence admits a splitting.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {𝒜 : Type _} [Category 𝒜]

namespace CategoryTheory

variable {A B C A' B' C' : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasKernels 𝒜] [HasImages 𝒜]

/-- If `f : A ⟶ B` and `g : B ⟶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is an exact sequence. -/
structure ShortExact : Prop where
  [mono : Mono f]
  [epi : Epi g]
  exact : Exact f g

open scoped ZeroObject

-- TODO move
instance zero_to_zero_isIso {C : Type _} [Category C] [HasZeroObject C] (f : (0 : C) ⟶ 0) :
    IsIso f := by
  convert show IsIso (𝟙 (0 : C)) by infer_instance
  -- Porting note: Lean 3's `convert` closed this by subsingleton elimination
  exact HasZeroObject.from_zero_ext _ _

/-- An exact sequence `A -f⟶ B -g⟶ C` is *left split*
if there exists a morphism `φ : B ⟶ A` such that `f ≫ φ = 𝟙 A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure LeftSplit : Prop where
  leftSplit : ∃ φ : B ⟶ A, f ≫ φ = 𝟙 A
  [epi : Epi g]
  exact : Exact f g

theorem LeftSplit.shortExact {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : ShortExact f g :=
  { mono := by
      obtain ⟨φ, hφ⟩ := h.leftSplit
      haveI : Mono (f ≫ φ) := by rw [hφ]; infer_instance
      exact mono_of_mono f φ
    epi := h.epi
    exact := h.exact }

/-- An exact sequence `A -f⟶ B -g⟶ C` is *right split*
if there exists a morphism `φ : C ⟶ B` such that `f ≫ φ = 𝟙 A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure RightSplit : Prop where
  rightSplit : ∃ χ : C ⟶ B, χ ≫ g = 𝟙 C
  [mono : Mono f]
  exact : Exact f g

theorem RightSplit.shortExact {f : A ⟶ B} {g : B ⟶ C} (h : RightSplit f g) : ShortExact f g :=
  { epi := by
      obtain ⟨χ, hχ⟩ := h.rightSplit
      haveI : Epi (χ ≫ g) := by rw [hχ]; infer_instance
      exact epi_of_epi χ g
    mono := h.mono
    exact := h.exact }

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜]

/-- An exact sequence `A -f⟶ B -g⟶ C` is *split* if there exist
`φ : B ⟶ A` and `χ : C ⟶ B` such that:
* `f ≫ φ = 𝟙 A`
* `χ ≫ g = 𝟙 C`
* `f ≫ g = 0`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure Split : Prop where
  split :
    ∃ (φ : B ⟶ A) (χ : C ⟶ B),
      f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ f ≫ g = 0 ∧ χ ≫ φ = 0 ∧ φ ≫ f + g ≫ χ = 𝟙 B

variable [HasKernels 𝒜] [HasImages 𝒜]

theorem exact_of_split {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (χ : C ⟶ B) (φ : B ⟶ A) (hfg : f ≫ g = 0)
    (H : φ ≫ f + g ≫ χ = 𝟙 B) : Exact f g :=
  { w := hfg
    epi :=
      by
      let ψ : (kernelSubobject g : 𝒜) ⟶ CategoryTheory.Limits.imageSubobject f :=
        Subobject.arrow _ ≫ φ ≫ CategoryTheory.Limits.factorThruImageSubobject f
      suffices ψ ≫ imageToKernel f g hfg = 𝟙 _ by convert epi_of_epi ψ _; rw [this]; infer_instance
      rw [← cancel_mono (Subobject.arrow _)]
      simp only [imageToKernel_arrow, CategoryTheory.Limits.imageSubobject_arrow_comp, Category.id_comp, Category.assoc]
      -- Porting note: Lean 4 `calc` does not defer `_` steps, so the proof is given inline
      calc
        (kernelSubobject g).arrow ≫ φ ≫ f = (kernelSubobject g).arrow ≫ 𝟙 B := by
          rw [← H, Preadditive.comp_add]
          simp only [add_zero, zero_comp, CategoryTheory.Limits.kernelSubobject_arrow_comp_assoc]
        _ = (kernelSubobject g).arrow := Category.comp_id _ }

section

variable {f g}

theorem Split.exact (h : Split f g) : Exact f g := by
  obtain ⟨φ, χ, -, -, h1, -, h2⟩ := h
  exact exact_of_split f g χ φ h1 h2

theorem Split.leftSplit (h : Split f g) : LeftSplit f g :=
  { leftSplit := by obtain ⟨φ, χ, h1, -⟩ := h; exact ⟨φ, h1⟩
    epi := by
      obtain ⟨φ, χ, -, h2, -⟩ := h
      have : Epi (χ ≫ g) := by rw [h2]; infer_instance
      exact epi_of_epi χ g
    exact := h.exact }

theorem Split.rightSplit (h : Split f g) : RightSplit f g :=
  { rightSplit := by obtain ⟨φ, χ, -, h1, -⟩ := h; exact ⟨χ, h1⟩
    mono := by
      obtain ⟨φ, χ, h1, -⟩ := h
      have : Mono (f ≫ φ) := by rw [h1]; infer_instance
      exact mono_of_mono f φ
    exact := h.exact }

theorem Split.shortExact (h : Split f g) : ShortExact f g :=
  h.leftSplit.shortExact

end

theorem Split.map {𝒜 ℬ : Type _} [Category 𝒜] [Abelian 𝒜] [Category ℬ] [Abelian ℬ] (F : 𝒜 ⥤ ℬ)
    [Functor.Additive F] {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (h : Split f g) :
    Split (F.map f) (F.map g) :=
  by
  obtain ⟨φ, χ, h1, h2, h3, h4, h5⟩ := h
  refine' ⟨⟨F.map φ, F.map χ, _⟩⟩
  simp only [← F.map_comp, ← F.map_id]
  -- Porting note: `simp only` does not use `← F.map_add` here (as in mathlib4's port)
  rw [← F.map_add]
  simp only [F.map_zero, *, true_and]

/-- The sequence `A ⟶ A ⊞ B ⟶ B` is exact. -/
theorem exact_inl_snd [HasBinaryBiproducts 𝒜] (A B : 𝒜) :
    Exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
  exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

/-- The sequence `B ⟶ A ⊞ B ⟶ A` is exact. -/
theorem exact_inr_fst [HasBinaryBiproducts 𝒜] (A B : 𝒜) :
    Exact (biprod.inr : B ⟶ A ⊞ B) biprod.fst :=
  exact_of_split _ _ biprod.inl biprod.snd biprod.inr_fst ((add_comm _ _).trans biprod.total)

end Preadditive

section Abelian

variable [Abelian 𝒜]

open scoped ZeroObject

theorem isIso_of_shortExact_of_isIso_of_isIso (h : ShortExact f g) (h' : ShortExact f' g')
    (i₁ : A ⟶ A') (i₂ : B ⟶ B') (i₃ : C ⟶ C') (comm₁ : i₁ ≫ f' = f ≫ i₂) (comm₂ : i₂ ≫ g' = g ≫ i₃)
    [IsIso i₁] [IsIso i₃] : IsIso i₂ :=
  by
  -- Porting note: proof adapted from mathlib4's port of the identical mathlib3 lemma
  haveI := h.mono; haveI := h.epi; haveI := h'.mono; haveI := h'.epi
  have := h.exact; have := h'.exact
  refine @Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono 𝒜 _ _ 0 _ _ _ 0 _ _ _ 0 f g 0 f' g'
      0 i₁ i₂ i₃ ?_ comm₁ comm₂ 0 0 0 0 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ _ _
  all_goals try simp
  all_goals try assumption
  all_goals try apply exact_zero_left_of_mono
  all_goals rwa [← epi_iff_exact_zero_right ]

end Abelian

/-- A *splitting* of a sequence `A -f⟶ B -g⟶ C` is an isomorphism
to the short exact sequence `0 ⟶ A ⟶ A ⊞ C ⟶ C ⟶ 0` such that
the vertical maps on the left and the right are the identity. -/
structure Splitting [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜] where
  iso : B ≅ A ⊞ C
  comp_iso_eq_inl : f ≫ iso.hom = biprod.inl
  iso_comp_snd_eq : iso.hom ≫ biprod.snd = g

variable {f g}

namespace Splitting

section HasZeroMorphisms

variable [HasZeroMorphisms 𝒜] [HasBinaryBiproducts 𝒜]

attribute [reassoc (attr := simp)] comp_iso_eq_inl iso_comp_snd_eq

variable (h : Splitting f g)

@[reassoc (attr := simp)]
theorem inl_comp_iso_eq : biprod.inl ≫ h.iso.inv = f := by rw [Iso.comp_inv_eq, h.comp_iso_eq_inl]

@[reassoc (attr := simp)]
theorem iso_comp_eq_snd : h.iso.inv ≫ g = biprod.snd := by rw [Iso.inv_comp_eq, h.iso_comp_snd_eq]

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.section : C ⟶ B` is the morphism satisfying `h.section ≫ g = 𝟙 C`. -/
def «section» : C ⟶ B :=
  biprod.inr ≫ h.iso.inv

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.retraction : B ⟶ A` is the morphism satisfying `f ≫ h.retraction = 𝟙 A`. -/
def retraction : B ⟶ A :=
  h.iso.hom ≫ biprod.fst

@[reassoc (attr := simp)]
theorem section_π : h.section ≫ g = 𝟙 C := by delta Splitting.«section»; simp

@[reassoc (attr := simp)]
theorem ι_retraction : f ≫ h.retraction = 𝟙 A := by delta retraction; simp

@[reassoc (attr := simp)]
theorem section_retraction : h.section ≫ h.retraction = 0 := by
  delta Splitting.«section» retraction
  simp

/-- The retraction in a splitting is a split mono. -/
protected def splitMono : SplitMono f :=
  ⟨h.retraction, by simp⟩

/-- The section in a splitting is a split epi. -/
protected def splitEpi : SplitEpi g :=
  ⟨h.section, by simp⟩

@[reassoc (attr := simp)]
theorem inr_iso_inv : biprod.inr ≫ h.iso.inv = h.section :=
  rfl

@[reassoc (attr := simp)]
theorem iso_hom_fst : h.iso.hom ≫ biprod.fst = h.retraction :=
  rfl

-- move this, add `iso_zero_biprod`
/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps]
def isoBiprodZero {C : Type _} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C] {X Y : C}
    (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  inv_hom_id :=
    by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

/-- A short exact sequence of the form `X -f⟶ Y -0⟶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splittingOfIsIsoZero {X Y Z : 𝒜} (f : X ⟶ Y) [IsIso f] (hZ : IsZero Z) :
    Splitting f (0 : Y ⟶ Z) :=
  ⟨(asIso f).symm ≪≫ isoBiprodZero hZ, by simp [hZ.eq_of_tgt _ 0], by simp⟩

protected theorem mono : Mono f :=
  -- Porting note: as in mathlib4's port of the identical lemma
  mono_of_mono_fac h.ι_retraction

protected theorem epi : Epi g :=
  by
  -- Porting note: `apply_with` has no direct Lean 4 equivalent; mathlib4's proof
  exact epi_of_epi_fac h.section_π

instance : Mono h.section := by delta Splitting.«section»; infer_instance

instance : Epi h.retraction := by delta retraction; apply epi_comp

end HasZeroMorphisms

section Preadditive

variable [Preadditive 𝒜] [HasBinaryBiproducts 𝒜]

variable (h : Splitting f g)

theorem split_add : h.retraction ≫ f + g ≫ h.section = 𝟙 _ :=
  by
  delta Splitting.«section» retraction
  rw [← cancel_mono h.iso.hom, ← cancel_epi h.iso.inv]
  simp only [Category.comp_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Limits.biprod.total, Preadditive.comp_add, Preadditive.add_comp,
    Splitting.comp_iso_eq_inl, Splitting.iso_comp_eq_snd_assoc]

@[reassoc]
theorem retraction_ι_eq_id_sub : h.retraction ≫ f = 𝟙 _ - g ≫ h.section :=
  eq_sub_iff_add_eq.mpr h.split_add

@[reassoc]
theorem π_section_eq_id_sub : g ≫ h.section = 𝟙 _ - h.retraction ≫ f :=
  eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.split_add)

theorem splittings_comm (h h' : Splitting f g) :
    h'.section ≫ h.retraction = -h.section ≫ h'.retraction :=
  by
  haveI := h.mono
  rw [← cancel_mono f]
  simp [retraction_ι_eq_id_sub]

theorem split : Split f g := by
  let φ := h.iso.hom ≫ biprod.fst
  let χ := biprod.inr ≫ h.iso.inv
  refine'
    ⟨⟨h.retraction, h.section, h.ι_retraction, h.section_π, _, h.section_retraction, h.split_add⟩⟩
  rw [← h.inl_comp_iso_eq, Category.assoc, h.iso_comp_eq_snd, biprod.inl_snd]

@[reassoc]
theorem comp_eq_zero : f ≫ g = 0 :=
  h.split.1.choose_spec.choose_spec.2.2.1

variable [HasKernels 𝒜] [HasImages 𝒜] [HasZeroObject 𝒜] [HasCokernels 𝒜]

protected theorem exact : Exact f g :=
  by
  rw [exact_iff_exact_of_iso f g (biprod.inl : A ⟶ A ⊞ C) (biprod.snd : A ⊞ C ⟶ C) _ _ _]
  · exact exact_inl_snd _ _
  -- Porting note: the remaining goals as in mathlib4's port of the identical lemma
  · refine Arrow.isoMk (Iso.refl _) h.iso ?_
    simp only [Iso.refl_hom, Arrow.mk_hom, Category.id_comp, comp_iso_eq_inl]
    rfl
  · refine Arrow.isoMk h.iso (Iso.refl _) ?_
    dsimp
    simp
  · rfl

protected theorem shortExact : ShortExact f g :=
  { mono := h.mono
    epi := h.epi
    exact := h.exact }

end Preadditive

section Abelian

variable [Abelian 𝒜]

-- TODO: this should be generalized to isoms of short sequences,
-- because now it forces one direction, and we want both.
/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `biprod.inl : A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is than automatically an isomorphism. -/
def mk' (h : ShortExact f g) (i : B ⟶ A ⊞ C) (h1 : f ≫ i = biprod.inl) (h2 : i ≫ biprod.snd = g) :
    Splitting f g
    where
  iso := by
    refine' @CategoryTheory.asIso _ _ _ _ i (id _)
    refine'
      CategoryTheory.isIso_of_shortExact_of_isIso_of_isIso f g _ _ h _ _ _ _
        (h1.trans (Category.id_comp _).symm).symm (h2.trans (Category.comp_id _).symm)
    constructor
    apply exact_inl_snd
  comp_iso_eq_inl := by rwa [CategoryTheory.asIso_hom]
  iso_comp_snd_eq := by exact h2

end Abelian

end Splitting

section

variable [Abelian 𝒜]

/-- A short exact sequence that is left split admits a splitting. -/
def LeftSplit.splitting {f : A ⟶ B} {g : B ⟶ C} (h : LeftSplit f g) : Splitting f g :=
  Splitting.mk' h.shortExact (biprod.lift h.leftSplit.choose g)
    (by
      ext
      · simpa only [biprod.inl_fst, biprod.lift_fst, Category.assoc] using h.leftSplit.choose_spec
      · simp only [biprod.inl_snd, biprod.lift_snd, Category.assoc, h.exact.w])
    (by simp only [biprod.lift_snd])

end

end CategoryTheory

