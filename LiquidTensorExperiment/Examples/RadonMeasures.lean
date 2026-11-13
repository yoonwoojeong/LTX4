import LiquidTensorExperiment.ChallengeNotations

#align_import examples.radon_measures

/-!
In this file we explain how the condensed abelian group `ℳ_{p} S`, for a profinite set `S`,
is related to the space of signed `p`-Radon measures on `S`.
-/


noncomputable section

open scoped LiquidTensorExperiment NNReal ZeroObject BigOperators Classical

open LiquidTensorExperiment CategoryTheory CategoryTheory.Limits Opposite PseudoNormedGroup
  TopologicalSpace

variable (p : ℝ≥0) [Fact (0 < p)] [Fact (p ≤ 1)]

/-!
The functor which associates a condensed abelian group to a
CompHaus-ly filtered pseudo normed group is denoted by
`CompHausFiltPseuNormGrp.to_Condensed`.
-/


example : CompHausFiltPseuNormGrp.{0} ⥤ Condensed.{0} Ab.{1} :=
  CompHausFiltPseuNormGrp.toCondensed

/-!
On objects, the functor `CompHausFiltPseuNormGrp.to_Condensed` behaves as expected.
For technical reasons related to size issues in topos theory,
we need to bump to a higher universe using `ulift`.
-/


example (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0}) :
    (Γ_ S (CompHausFiltPseuNormGrp.toCondensed X) : Type 1) =
      ULift.{1}-- universe bump
        {f :
          S → X |-- the set of all functions `S → X` such that...
          ∃ (c : ℝ≥0) -- there exists a non-negative real `c`,
          (g :
            S → filtration X c),-- a map `g` from `S` to the `c`-th term of the filtration of `X`
                Continuous
                g ∧-- such that `g` is continuous and
                f =
                coe ∘ g} :=
  rfl

/-!
The group structure on the `S`-sections of the condensed abelian group associated to
`X : CompHausFiltPseuNormGrp` is the obvious one.
-/


-- `f` is the composition of `g` with the inclusion.
example (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0})
    (f g : Γ_ S (CompHausFiltPseuNormGrp.toCondensed X)) (s : S) : (f + g) s = f s + g s :=
  rfl

/-!
The category `CompHausFiltPseuNormGrp₁` is similar to that of
CompHaus-ly filtered pseudo-normed groups, except that the filtration is assumed to be exhaustive
and the morphisms are strict.
`CHFPNG₁_to_CHFPNGₑₗ` is the obvious forgetful functor between these two categories.
-/


example : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp :=
  cHFPNG₁ToCHFPNGₑₗ

example (X : CompHausFiltPseuNormGrp₁) : (cHFPNG₁ToCHFPNGₑₗ X : Type) = X :=
  rfl

/-!
The condensed abelian group `ℳ_p(S)` is isomorphic to the condensed abelian group associated
to the CompHaus-ly filtered pseudo normed group `S.Radon_png p`.
In the examples below, we explain how `S.Radon_png p` is related to Radon measures.
-/


example (S : Profinite.{0}) :
    (ℳ_{p}S) ≅ CompHausFiltPseuNormGrp.toCondensed (cHFPNG₁ToCHFPNGₑₗ (S.radonPng p)) :=
  CompHausFiltPseuNormGrp.toCondensed.mapIso <| cHFPNG₁ToCHFPNGₑₗ.mapIso <| (S.radonPngIso p).symm

/-!
Any element of `S.Radon_png p` induces a continuous linear map from `C(S,ℝ)` to `ℝ`.
In particular, this allows us to consider `μ : S.Radon_png p` as a function on `C(S,ℝ)` with
values in `ℝ`.
-/


example (S : Profinite.{0}) (μ : S.radonPng p) : C(S, ℝ) →L[ℝ] ℝ :=
  μ.1

example (S : Profinite.{0}) (μ : S.radonPng p) (f : C(S, ℝ)) : μ f = μ.1 f :=
  rfl

/-!
If `μ : S.Radon_png p`, then there exists a nonnegative real `c` such that for all partitions of
`S` into clopens `S = V_1 ∪ ⋯ ∪ V_n`, letting `I_i` denote the indicator function of `V_i`, one has
`∑ i, ∥ μ (I_i) ∥^p ≤ c`.
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
example (S : Profinite.{0})
    (μ : S.radonPng p) :-- there exists some `c : ℝ≥0` such that...
    ∃ c :
      ℝ≥0,-- for any finite indexing set `ι`,
      ∀ (ι : FintypeCat.{0})
        -- family of subsets of `S`,
        (V : ι → Set S)
        -- which forms a partition of `S`,
        (I : IndexedPartition V)
        -- by clopens,
        (hV : ∀ i, IsClopen (V i)),-- the sum mentioned above is bounded by `c`.
          ∑ i : ι, «expr∥ ∥₊» (μ (Clopens.indicator ⟨V i, hV i⟩)) ^ (p : ℝ) ≤
          c :=
  by
  obtain ⟨c, hc⟩ := μ.2
  use c
  rwa [WeakDual.bdd_iff_indexed_parition] at hc 

/-!
The indicator function on a clopen set, which was used in the example above, behaves as expected.
-/


example (S : Profinite.{0}) (V : Set S) (hV : IsClopen V) (s : S) :
    Clopens.indicator ⟨V, hV⟩ s = if s ∈ V then 1 else 0 :=
  rfl

/-! Conversely, if we are given a continuous linear map `C(S,ℝ) → ℝ` and a nonnegative real `c`
satisfying the inequality appearing in the example above, then we may construct an element of
the `c`-th term of the filtration of `S.Radon_png p`.
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
example (S : Profinite.{0}) (μ : C(S, ℝ) →L[ℝ] ℝ) (c : ℝ≥0)
    (h :
      ∀ (ι : FintypeCat.{0}) (V : ι → Set S) (I : IndexedPartition V) (hV : ∀ i, IsClopen (V i)),
        ∑ i : ι, «expr∥ ∥₊» (μ (Clopens.indicator ⟨V i, hV i⟩)) ^ (p : ℝ) ≤ c) :
    filtration (S.radonPng p) c :=
  { val := ⟨μ, c, by rw [WeakDual.bdd_iff_indexed_parition]; assumption⟩
    property := by erw [← WeakDual.bdd_iff_indexed_parition] at h ; assumption }

/-- This is the canonical embedding of `S.Radon_png p` into the weak dual of `C(S,ℝ)`. -/
def embeddingIntoTheWeakDual (S : Profinite.{0}) : S.radonPng p ↪ WeakDual ℝ C(S, ℝ) :=
  ⟨fun μ => μ.1, fun x y h => Subtype.ext h⟩

/-!
This embedding is precisely what allows us to view `μ : S.Radon_png p` as `ℝ`-valued functions
on `C(S,ℝ)`.
-/


example (S : Profinite.{0}) (μ : S.radonPng p) (f : C(S, ℝ)) :
    embeddingIntoTheWeakDual p S μ f = μ f :=
  rfl

/-- The canonical embedding from the `c`-th term of the filtration of `S.Radon_png p` into
the `S.Radon_png p` itself. -/
def filtrationEmbedding (S : Profinite.{0}) (c : ℝ≥0) :
    filtration (S.radonPng p) c ↪ S.radonPng p :=
  ⟨fun μ => μ.1, fun x y h => Subtype.ext h⟩

/-! The topology of the `c`-th term of the filtration of `S.Radon_png p` is induced
by the weak topology on the set of continuous linear map `C(S,ℝ) → ℝ`. -/


example (S : Profinite.{0}) (c : ℝ≥0) :
    Inducing (embeddingIntoTheWeakDual p S ∘ filtrationEmbedding p S c) :=
  Inducing.mk rfl

/-! The group structure on `S.Radon_png p` is also induced by the weak dual. -/


example (S : Profinite.{0}) (F G : S.radonPng p) :
    embeddingIntoTheWeakDual p S (F + G) =
      embeddingIntoTheWeakDual p S F + embeddingIntoTheWeakDual p S G :=
  rfl

