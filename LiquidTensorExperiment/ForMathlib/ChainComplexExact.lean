import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import LiquidTensorExperiment.ForMathlib.ComplexExtend
import LiquidTensorExperiment.ForMathlib.HomologyExact

#align_import for_mathlib.chain_complex_exact

open CategoryTheory

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace ChainComplex

variable (C : ChainComplex A ℤ)

theorem CategoryTheory.isZero_homology'_iff_exact {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : f ≫ g = 0) : IsZero (homology' f g w) ↔ Exact f g :=
  by
  rw [Preadditive.exact_iff_homology'_zero]
  constructor
  · intro h
    use w, h.isoZero
  · rintro ⟨w, ⟨h⟩⟩
    apply IsZero.of_iso _ h
    exact is_zero_zero _

theorem exact_of_isZero_homology' (h : ∀ i : ℤ, IsZero (C.homology' i)) :
    ∀ i j k : ℤ,
      (ComplexShape.down ℤ).Rel i j → (ComplexShape.down ℤ).Rel j k → Exact (C.d i j) (C.d j k) :=
  by
  rintro i j k ⟨rfl⟩ ⟨rfl⟩
  dsimp
  specialize h (k + 1)
  erw [_root_.category_theory.isZero_homology'_iff_exact] at h 
  let e : C.X_prev (k + 1) ≅ C.X (k + 1 + 1) := C.X_prev_iso rfl
  let q : C.X_next (k + 1) ≅ C.X k := C.X_next_iso rfl
  suffices exact (e.hom ≫ C.d (k + 1 + 1) (k + 1)) (C.d (k + 1) k ≫ q.inv) by simpa using this
  dsimp [e, q]; rwa [← C.d_to_eq, ← C.d_from_eq]

-- change of variables ideas
theorem isZero_homology'_of_exact
    (h :
      ∀ i j k : ℤ,
        (ComplexShape.down ℤ).Rel i j → (ComplexShape.down ℤ).Rel j k → Exact (C.d i j) (C.d j k)) :
    ∀ i : ℤ, IsZero (C.homology' i) := by
  intro i
  specialize h (i + 1) i (i - 1) rfl (sub_add_cancel i 1)
  rw [_root_.category_theory.isZero_homology'_iff_exact]
  rw [← HomologicalComplex.xPrevIso_comp_dTo] at h ; swap; simp
  rw [← HomologicalComplex.dFrom_comp_xNextIso] at h ; swap; simp
  simpa only [exact_comp_iso, exact_iso_comp] using h

/-

kmb experiments  -- happy to delete

-- change of variables ideas
lemma is_zero_homology_of_exact
  (h : ∀ i j k : ℤ, (complex_shape.down ℤ).rel i j → (complex_shape.down ℤ).rel j k →
  exact (C.d i j) (C.d j k)) :
  ∀ i : ℤ, is_zero (C.homology i) :=
begin
  -- For stupid defeq reasons coming up later on we want to change
  -- variables

  -- this has a name (it's `f 1` for some `f`) but I can't find it.
  let eij : ℤ ≃ ℤ := ⟨λ i, i - 1, λ j, j + 1,
  λ i, sub_add_cancel i 1, λ j, add_tsub_cancel_right _ _⟩,
  -- Make the abstract change of variables claim
  suffices : ∀ (j : ℤ), is_zero (homological_complex.homology C (eij.symm j)),
  --
  { intro i,
    -- use the equiv the other way
    specialize this (eij i),
    -- the simplifier can take it from here (avoiding motive not type correct errors)
    simpa, },
  -- now unravel the equiv
  dsimp [eij],
  -- and forget it
  clear eij,
  /-
  alternative approach involves changing goal to ∀ i, P((i - 1) + 1)
  and then generalizing (i - 1) to j, but then you're rewriting under binders,
  TODO: try other way
  -/
  /-
  Third approach (working code below) : instead of defining eij just do the
  rewrite more brutally. I didn't like how you couldn't get rid of i afterwards
  until you introduced j.

  -- convenient to have i of the form k+1 for stupid
  -- definitional reasons so let's start by changing variables.
  have k := i - 1,
  have hk : k = i - 1 := by refl,
  have hi : i = k + 1 := by {rw hk, ring },
  -- That's our bijections between the `i` and `k` world.
  rw hi, -- change all the i's to k's
  -- Define a new variable j to be "k, but forget about whole "defined
  -- in terms of i" part".
  generalize : k = j,
  -- We'll do the entire rest of the problem with the abstract
  -- variable j. We tidy up, for no particular reason.
  clear hi hk k i,
  -/
  intro k,
  rw _root_.category_theory.is_zero_homology_iff_exact,
  specialize h (k+1+1) (k+1) k rfl rfl,
  /-
  h: exact (C.d (i + 1) i) (C.d i (i - 1))
  ⊢ exact (homological_complex.d_to C i) (homological_complex.d_from C i)
  -/
  convert h,
  -- gives me `heq`s
  repeat {admit },
end

-/
theorem exact_iff_isZero_homology' :
    (∀ i : ℤ, IsZero (C.homology' i)) ↔
      ∀ i j k : ℤ,
        (ComplexShape.down ℤ).Rel i j → (ComplexShape.down ℤ).Rel j k → Exact (C.d i j) (C.d j k) :=
  ⟨exact_of_isZero_homology' _, isZero_homology'_of_exact _⟩

variable (D : ChainComplex A ℕ)

theorem epi_and_exact_of_isZero_homology'
    (h :
      ∀ i : ℤ,
        IsZero
          (((HomologicalComplex.embed <| ComplexShape.Embedding.natDownIntDown).obj D).homology'
            i)) :
    Epi (D.d 1 0) ∧ ∀ i : ℕ, Exact (D.d (i + 2) (i + 1)) (D.d (i + 1) i) :=
  by
  constructor
  · specialize h 0
    rw [CategoryTheory.isZero_homology'_iff_exact,
      HomologicalComplex.dFrom_eq _ (show (ComplexShape.down ℤ).Rel 0 (-1) by simp), exact_comp_iso,
      HomologicalComplex.dTo_eq _ (show (ComplexShape.down ℤ).Rel 1 0 by simp), exact_iso_comp] at h 
    rw [IsZero.eq_zero_of_tgt (is_zero_zero _)
        (((HomologicalComplex.embed ComplexShape.Embedding.natDownIntDown).obj D).d 0 (-1))] at
      h 
    rw [epi_iff_exact_zero_right]
    exact h
  -- defeq abuse probably
  · intro i
    specialize h (i + 1 : ℕ)
    rw [CategoryTheory.isZero_homology'_iff_exact,
      HomologicalComplex.dFrom_eq _ (show (ComplexShape.down ℤ).Rel (i + 1 : ℕ) (i : ℕ) by simp),
      exact_comp_iso,
      HomologicalComplex.dTo_eq _
        (show (ComplexShape.down ℤ).Rel (i + 2 : ℕ) (i + 1 : ℕ) by simp [add_assoc] <;> rfl),
      exact_iso_comp] at h 
    exact h

-- more defeq abuse
theorem exact_of_epi {𝒞 : Type _} [Category 𝒞] [Abelian 𝒞] {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C}
    (hfg : f ≫ g = 0) [Epi f] : Exact f g :=
  by
  rw [Abelian.exact_iff]
  refine' ⟨hfg, _⟩
  rw [(Abelian.epi_iff_cokernel_π_eq_zero _).1 (show epi f from inferInstance), comp_zero]

theorem exact_zero_snd_iff_epi {𝒞 : Type _} [Category 𝒞] [Abelian 𝒞] {A B C : 𝒞} {f : A ⟶ B} :
    Exact f (0 : B ⟶ C) ↔ Epi f := by
  constructor
  · intro h
    apply Preadditive.epi_of_cokernel_zero
    rcases(Abelian.exact_iff _ _).1 h with ⟨-, h2⟩
    simpa using h2
  · intro
    exact exact_of_epi comp_zero

theorem exact_of_mono {𝒞 : Type _} [Category 𝒞] [Abelian 𝒞] {A B C : 𝒞} {f : A ⟶ B} {g : B ⟶ C}
    (hfg : f ≫ g = 0) [Mono g] : Exact f g :=
  by
  rw [Abelian.exact_iff]
  refine' ⟨hfg, _⟩
  rw [(Abelian.mono_iff_kernel_ι_eq_zero g).1 inferInstance, zero_comp]

theorem exact_zero_fst_iff_mono {𝒞 : Type _} [Category 𝒞] [Abelian 𝒞] {A B C : 𝒞} {g : B ⟶ C} :
    Exact (0 : A ⟶ B) g ↔ Mono g := by
  constructor
  · intro h
    apply Preadditive.mono_of_kernel_zero
    rcases(Abelian.exact_iff _ _).1 h with ⟨-, h2⟩
    simpa using h2
  · intro
    exact exact_of_mono zero_comp

theorem nat_epi_iff_exact :
    Epi (D.d 1 0) ↔ Exact (HomologicalComplex.dTo D 0) (HomologicalComplex.dFrom D 0) :=
  by
  rw [HomologicalComplex.dTo_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp), exact_iso_comp]
  constructor
  · intro h
    apply exact_of_epi
    apply HomologicalComplex.d_comp_d
  · intro h
    refine' h.epi_of_eq_zero (D.shape _ _ _)
    simp only [next_nat_zero, ComplexShape.down_Rel, Nat.one_ne_zero, not_false_iff]

theorem nat_exact_iff_to_from_exact (i : ℕ) :
    Exact (D.d (i + 2) (i + 1)) (D.d (i + 1) i) ↔
      Exact (HomologicalComplex.dTo D (i + 1)) (HomologicalComplex.dFrom D (i + 1)) :=
  by
  rw [HomologicalComplex.dFrom_eq _ (show (ComplexShape.down ℕ).Rel i.succ i by simp),
    exact_comp_iso,
    HomologicalComplex.dTo_eq _ (show (ComplexShape.down ℕ).Rel i.succ.succ i.succ by simp),
    exact_iso_comp]

theorem isZero_homology'_of_epi_and_exact (h1 : Epi (D.d 1 0))
    (h2 : ∀ i : ℕ, Exact (D.d (i + 2) (i + 1)) (D.d (i + 1) i)) :
    ∀ i : ℤ,
      IsZero
        (((HomologicalComplex.embed <| ComplexShape.Embedding.natDownIntDown).obj D).homology' i) :=
  by
  intro i
  rw [CategoryTheory.isZero_homology'_iff_exact]
  rcases lt_trichotomy i 0 with (hi | rfl | hi)
  · have :
      is_zero (((HomologicalComplex.embed ComplexShape.Embedding.natDownIntDown).obj D).pt i) :=
      by
      delta HomologicalComplex.embed HomologicalComplex.Embed.obj
        ComplexShape.Embedding.natDownIntDown ComplexShape.Embedding.posIntToOnat
      obtain ⟨j, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
      simp only [is_zero_zero A, HomologicalComplex.Embed.x_none]
    exact CategoryTheory.Limits.IsZero.exact this _ _
  · rw [HomologicalComplex.dFrom_eq _ (show (ComplexShape.down ℤ).Rel 0 (-1) by simp),
      exact_comp_iso, HomologicalComplex.dTo_eq _ (show (ComplexShape.down ℤ).Rel 1 0 by simp),
      exact_iso_comp]
    apply exact_of_epi (HomologicalComplex.d_comp_d _ (1 : ℤ) 0 (-1))
    exact h1
  -- maybe defeq abuse?
  · obtain ⟨j, rfl⟩ := Int.eq_succ_of_zero_lt hi; clear hi
    specialize h2 j
    rw [HomologicalComplex.dFrom_eq _ (show (ComplexShape.down ℤ).Rel (j.succ : ℕ) j by simp),
      exact_comp_iso,
      HomologicalComplex.dTo_eq _ (show (ComplexShape.down ℤ).Rel (j.succ.succ : ℕ) j.succ by simp),
      exact_iso_comp]
    exact h2

-- maybe defeq abuse
theorem epi_and_exact_iff_isZero_homology' :
    (Epi (D.d 1 0) ∧ ∀ i : ℕ, Exact (D.d (i + 2) (i + 1)) (D.d (i + 1) i)) ↔
      ∀ i : ℤ,
        IsZero
          (((HomologicalComplex.embed <| ComplexShape.Embedding.natDownIntDown).obj D).homology'
            i) :=
  ⟨fun h => isZero_homology'_of_epi_and_exact D h.1 h.2, epi_and_exact_of_isZero_homology' _⟩

theorem homology'_zero_iff_homology'_zero :
    (∀ i : ℤ,
        IsZero
          (((HomologicalComplex.embed <| ComplexShape.Embedding.natDownIntDown).obj D).homology'
            i)) ↔
      ∀ i : ℕ, IsZero (D.homology' i) :=
  by
  rw [← ChainComplex.epi_and_exact_iff_isZero_homology']
  simp_rw [CategoryTheory.isZero_homology'_iff_exact, nat_epi_iff_exact,
    nat_exact_iff_to_from_exact]
  constructor
  · rintro ⟨h0, hS⟩ (_ | i)
    · exact h0
    · exact hS i
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩

theorem epi_and_exact_iff_zero_homology' :
    (Epi (D.d 1 0) ∧ ∀ i : ℕ, Exact (D.d (i + 2) (i + 1)) (D.d (i + 1) i)) ↔
      ∀ i : ℕ, IsZero (D.homology' i) :=
  by
  rw [← ChainComplex.homology'_zero_iff_homology'_zero]
  apply ChainComplex.epi_and_exact_iff_isZero_homology'

universe v' u'

-- `kernel_comparison_comp_ι` in mathlib master (as I write) is not
-- maximally universe-polymorphic; the morphisms of both categories live in the
-- same universe. So we write `[category.{v} B]` instead of `[category.{v'} B]` here.
-- TODO : fix kernel_comparison_comp_ι (if this is indeed an oversight)
theorem exact_iff_map_exact {α : Type _} {c : ComplexShape α} (D : HomologicalComplex A c)
    {B : Type u'} [Category.{v} B] [Abelian B] (E : A ≌ B) [E.Functor.Additive] (i j k : α)
    (f : D.pt i ⟶ D.pt j) (g : D.pt j ⟶ D.pt k) :
    Exact f g ↔ Exact (E.Functor.map f) (E.Functor.map g) :=
  by
  rw [Abelian.exact_iff]
  rw [Abelian.exact_iff]
  apply and_congr
  · rw [← Functor.map_comp]
    exact (Functor.map_eq_zero_iff _).symm
  · rw [← Functor.map_eq_zero_iff E.functor, Functor.map_comp]
    rw [← kernel_comparison_comp_ι]
    rw [← π_comp_cokernel_comparison]
    rw [← PreservesKernel.iso_hom]
    rw [← PreservesCokernel.iso_inv]
    rw [Category.assoc]
    rw [Preadditive.IsIso.comp_left_eq_zero]
    rw [← Category.assoc]
    rw [Preadditive.IsIso.comp_right_eq_zero]

-- morphisms of B in same universe as morphisms of A because of `exact_iff_map_exact`
theorem homology'_zero_iff_map_homology'_zero {α : Type _} {c : ComplexShape α}
    (D : HomologicalComplex A c) {B : Type u'} [Category.{v} B] [Abelian B] (E : A ≌ B)
    [E.Functor.Additive] :
    (∀ i : α, IsZero (D.homology' i)) ↔
      ∀ i : α, IsZero (((E.Functor.mapHomologicalComplex _).obj D).homology' i) :=
  by
  apply forall_congr'
  intro i
  rw [CategoryTheory.isZero_homology'_iff_exact]
  rw [CategoryTheory.isZero_homology'_iff_exact]
  rw [Functor.mapHomologicalComplex]
  apply exact_iff_map_exact

end ChainComplex

