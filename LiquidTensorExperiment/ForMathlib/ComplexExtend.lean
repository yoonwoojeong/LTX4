import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Abelian.Basic
import LiquidTensorExperiment.ForMathlib.ShortComplexFunctorCategory
import LiquidTensorExperiment.ForMathlib.ShortComplexHomologicalComplex

#align_import for_mathlib.complex_extend

universe v u

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {ι ι' ι₁ ι₂ : Type _}

namespace ComplexShape

/-- An embedding `embedding c₁ c₂` between two complex shapes `ι₁` and `ι₂` is
an injection `ι₁ → ι₂` sending related vertices to related vertices. Recall that two
vertices are related in a complex shape iff the differential between them is allowed to
be nonzero. -/
@[nolint has_inhabited_instance]
structure Embedding (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂) where
  f : ι₁ → ι₂
  R : ι₂ → Option ι₁
  eq_some : ∀ i₂ i₁, r i₂ = some i₁ ↔ f i₁ = i₂
  c : ∀ ⦃i j⦄, c₁.Rel i j → c₂.Rel (f i) (f j)

namespace Embedding

/-- extra condition which shall be useful to compare homology -/
def CIff {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} (e : c₁.Embedding c₂) : Prop :=
  ∀ i j, c₁.Rel i j ↔ c₂.Rel (e.f i) (e.f j)

theorem r_f {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} (e : c₁.Embedding c₂) (i : ι₁) :
    e.R (e.f i) = some i := by rw [e.eq_some]

theorem r_none {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} (e : c₁.Embedding c₂) (i : ι₂)
    (hi : ¬∃ i₁ : ι₁, i = e.f i₁) : e.R i = none := by
  classical
  by_contra hi2
  apply hi
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.1 hi2
  use j
  rw [e.eq_some] at hj 
  rw [hj]

/-- The map from `ℤ` to `option ℕ` which is `some n` on `n : ℕ : ℤ` and `none otherwise. -/
def posIntToOnat : ℤ → Option ℕ
  | (n : ℕ) => n
  | -[n+1] => none

/-- The map from `ℤ` to `option ℕ` which is `some n` on `-(n : ℕ : ℤ)` and `none otherwise. -/
def negIntToOnat : ℤ → Option ℕ
  | 0 => (0 : ℕ)
  | (n + 1 : ℕ) => none
  | -[n+1] => (n + 1 : ℕ)

/-- The obvious embedding from the ℕ-indexed "cohomological" complex `* → * → * → ...`
  to the corresponding ℤ-indexed complex. -/
def natUpIntUp : Embedding (ComplexShape.up ℕ) (ComplexShape.up ℤ)
    where
  f := coe
  R := posIntToOnat
  eq_some := by
    rintro (i | i) i'
    · constructor <;> · rintro ⟨rfl⟩; rfl
    · constructor <;> · rintro ⟨⟩
  c := by rintro i j (rfl : _ = _); dsimp; rfl

/-- The obvious embedding from the ℕ-indexed "homological" complex `* ← * ← * ← ...`
  to the corresponding ℤ-indexed homological complex. -/
def natDownIntDown : Embedding (ComplexShape.down ℕ) (ComplexShape.down ℤ)
    where
  f := coe
  R := posIntToOnat
  eq_some := by
    rintro (i | i) i'
    · constructor <;> · rintro ⟨rfl⟩; rfl
    · constructor <;> · rintro ⟨⟩
  c := by rintro i j (rfl : _ = _); dsimp; rfl

/-- Obvious embedding from the `ℕ`-indexed homological complex `* ← * ← * ...`
  to `ℤ`-indexed cohomological complex ` ... → * → * → ...` sending $n$ to $-n$
  on the corresponding map `ℕ → ℤ`. -/
def natDownIntUp : Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ)
    where
  f := -coe
  R := negIntToOnat
  eq_some := by
    rintro ((_ | i) | i) (_ | i')
    any_goals constructor <;> · rintro ⟨⟩
    any_goals constructor <;> · rintro ⟨rfl⟩; rfl
  c := by
    rintro i j (rfl : _ = _)
    simp only [Pi.neg_apply, Int.ofNat_succ, neg_add_rev, up_rel, neg_add_cancel_comm]

theorem natDownIntUp_cIff : natDownIntUp.CIff :=
  by
  intro i j
  constructor
  · apply nat_down_int_up.c
  · intro hij
    change j + 1 = i
    dsimp [nat_down_int_up] at hij 
    rw [← Int.ofNat_inj]
    simp only [Int.ofNat_succ]
    linarith

/-- Obvious embedding from the `ℕ`-indexed cohomological complex `* → * → * ...`
  to `ℤ`-indexed homological complex ` ... ← * ← * ← ...` sending $n$ to $-n$
  on the corresponding map `ℕ → ℤ`. -/
def natUpIntDown : Embedding (ComplexShape.up ℕ) (ComplexShape.down ℤ)
    where
  f := -coe
  R := negIntToOnat
  eq_some := by
    rintro ((_ | i) | i) (_ | i')
    any_goals constructor <;> · rintro ⟨⟩
    any_goals constructor <;> · rintro ⟨rfl⟩; rfl
  c := by
    rintro i j (rfl : _ = _)
    simp only [Pi.neg_apply, Int.ofNat_succ, neg_add_rev, down_rel, neg_add_cancel_comm]

end Embedding

end ComplexShape

variable {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {cι : ComplexShape ι} {cι' : ComplexShape ι'}

variable {𝒞 : Type _} [Category 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞]

-- reclaim category notation!
namespace HomologicalComplex

open scoped ZeroObject

section EmbedXAndDBasics

/-

`embed`, not to be confused with `embedding` later on, is simply
the extension of constructions involving the index type `ι` of our complex,
to the larger type `option ι`, with `none` being sent to `zero`.

-/
variable (X : HomologicalComplex 𝒞 cι)

/-- If `𝒞` is an abelian category,  and `(Xᵢ)ᵢ` is a `𝒞`-valued homological
complex on a complex-shape with index `ι`, then `embed.X X oi` for `oi : option ι`
is the value `Xᵢ` of `h` at `some i` (an object of `𝒞`), or `0` for `none`. -/
def Embed.x : Option ι → 𝒞
  | some i => X.pt i
  | none => 0

def Embed.xIsoOfNone {e : Option ι} (he : e = none) : Embed.x X e ≅ 0 := by rw [he]; rfl

def Embed.x_isZero_of_none {e : Option ι} (he : e = none) : IsZero (Embed.x X e) :=
  IsZero.of_iso (CategoryTheory.Limits.isZero_zero 𝒞) (Embed.xIsoOfNone X he)

def Embed.xIsoOfSome {e : Option ι} {i} (he : e = some i) : Embed.x X e ≅ X.pt i := by rw [he]; rfl

@[simp]
theorem Embed.x_none : Embed.x X none = 0 :=
  rfl

@[simp]
theorem Embed.x_some (i : ι) : Embed.x X (some i) = X.pt i :=
  rfl

/-- The morphism `Xᵢ → Xⱼ` with `i j : option ι` coming from the complex `X`.
Equal to zero if either `i` or `j` is `none`.  -/
def Embed.d : ∀ i j, Embed.x X i ⟶ Embed.x X j
  | some i, some j => X.d i j
  | some i, none => 0
  | none, j => 0

def Embed.d_of_none_src {e₁ e₂ : Option ι} (he : e₁ = none) : Embed.d X e₁ e₂ = 0 := by rw [he]; rfl

def Embed.d_of_none_tgt {e₁ e₂ : Option ι} (he : e₂ = none) : Embed.d X e₁ e₂ = 0 := by rw [he];
  cases e₁ <;> rfl

def Embed.d_of_some_of_some {e₁ e₂ : Option ι} {i j} (h₁ : e₁ = some i) (h₂ : e₂ = some j) :
    Embed.d X e₁ e₂ = (Embed.xIsoOfSome X h₁).Hom ≫ X.d i j ≫ (Embed.xIsoOfSome X h₂).inv := by
  subst h₁; subst h₂; change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; simpa

@[simp]
theorem Embed.d_some_some (i j : ι) : Embed.d X (some i) (some j) = X.d i j :=
  rfl

theorem Embed.d_ne_zero (e₁ e₂ : Option ι) (h : Embed.d X e₁ e₂ ≠ 0) :
    ∃ (i j : ι) (h₁ : e₁ = some i) (h₂ : e₂ = some j), X.d i j ≠ 0 :=
  by
  rcases h₁ : e₁ with (_ | ⟨i⟩)
  · exfalso
    apply h
    exact embed.d_of_none_src X h₁
  · rcases h₂ : e₂ with (_ | ⟨j⟩)
    · exfalso
      apply h
      exact embed.d_of_none_tgt X h₂
    · substs h₁ h₂
      refine' ⟨i, j, rfl, rfl, h⟩

/-- Prop-valued so probably won't break anything. To deal with zerology. -/
instance HomologicalComplex.Embed.subsingleton_to_none (c : _) :
    Subsingleton (c ⟶ Embed.x X none) :=
  @Unique.subsingleton _ (HasZeroObject.uniqueFrom c)

instance HomologicalComplex.Embed.subsingleton_of_none (c) : Subsingleton (Embed.x X none ⟶ c) :=
  @Unique.subsingleton _ (HasZeroObject.uniqueTo c)

@[simp]
theorem Embed.d_to_none (i : Option ι) : Embed.d X i none = 0 := by cases i <;> rfl

@[simp]
theorem Embed.d_of_none (i : Option ι) : Embed.d X none i = 0 :=
  rfl

theorem Embed.shape :
    ∀ (i j : Option ι) (h : ∀ i' j' : ι, i = some i' → j = some j' → ¬cι.Rel i' j'),
      Embed.d X i j = 0
  | some i, some j, h => X.shape _ _ <| h i j rfl rfl
  | some i, none, h => rfl
  | none, j, h => rfl

theorem Embed.d_comp_d : ∀ i j k, Embed.d X i j ≫ Embed.d X j k = 0
  | some i, some j, some k => X.d_comp_d _ _ _
  | some i, some j, none => comp_zero
  | some i, none, k => comp_zero
  | none, j, k => zero_comp

end EmbedXAndDBasics

section EmbeddingChangeOfComplex

variable (e : cι.Embedding cι')

/-- Object-valued pushforward of `𝒞`-valued homological complexes along an embedding
  `ι₁ ↪ ι₂` of complex-shapes (with all indexes not in the image going to `0`). -/
def Embed.obj (X : HomologicalComplex 𝒞 cι) : HomologicalComplex 𝒞 cι'
    where
  pt i := Embed.x X (e.R i)
  d i j := Embed.d X (e.R i) (e.R j)
  shape' i j hij :=
    Embed.shape X _ _
      (by
        simp only [e.eq_some]
        rintro i' j' rfl rfl h'
        exact hij (e.c h'))
  d_comp_d' i j k hij hjk := Embed.d_comp_d X _ _ _

variable {X Y Z : HomologicalComplex 𝒞 cι} (f : X ⟶ Y) (g : Y ⟶ Z)

/--
Morphism-valued pushforward of `𝒞`-valued homological complexes along an embedding of complex-shapes
( with all morphisms not in the image being defined to be 0) -/
def Embed.f : ∀ i, Embed.x X i ⟶ Embed.x Y i
  | some i => f.f i
  | none => 0

@[simp]
theorem Embed.f_none : Embed.f f none = 0 :=
  rfl

@[simp]
theorem Embed.f_some (i : ι) : Embed.f f (some i) = f.f i :=
  rfl

theorem Embed.f_add {f g : X ⟶ Y} : ∀ i, Embed.f (f + g) i = Embed.f f i + Embed.f g i
  | some i => by simp
  | none => by simp

theorem Embed.comm : ∀ i j, Embed.f f i ≫ Embed.d Y i j = Embed.d X i j ≫ Embed.f f j
  | some i, some j => f.comm _ _
  | some i, none => show _ ≫ 0 = 0 ≫ 0 by simp only [comp_zero]
  | none, j => show 0 ≫ 0 = 0 ≫ _ by simp only [zero_comp]

/-- Pushforward of a morphism `(Xᵢ)ᵢ ⟶ (Yᵢ)ᵢ` of homological complexes with
  the same complex-shape `ι`, along an embedding of complex shapes c.embedding `ι → ι'` -/
def Embed.map : Embed.obj e X ⟶ Embed.obj e Y
    where
  f i := Embed.f f _
  comm' i j hij := Embed.comm f _ _

theorem Embed.f_id : ∀ i, Embed.f (𝟙 X) i = 𝟙 (Embed.x X i)
  | some i => rfl
  | none => HasZeroObject.from_zero_ext _ _

theorem Embed.f_comp : ∀ i, Embed.f (f ≫ g) i = Embed.f f i ≫ Embed.f g i
  | some i => rfl
  | none => HasZeroObject.from_zero_ext _ _

theorem Embed.f_of_some {e : Option ι} {i} (he : e = some i) :
    Embed.f f e = (Embed.xIsoOfSome _ he).Hom ≫ f.f i ≫ (Embed.xIsoOfSome _ he).inv := by subst he;
  change _ = 𝟙 _ ≫ _ ≫ 𝟙 _; simp

/-- Functor pushing forward, for a fixed abelian category `𝒞`, the category
of `𝒞`-valued homological complexes of shape `ι₁` along an embedding `ι₁ ↪ ι₂`
(not Lean notation -- fix somehow?) of complexes. -/
def embed : HomologicalComplex 𝒞 cι ⥤ HomologicalComplex 𝒞 cι'
    where
  obj := Embed.obj e
  map X Y f := Embed.map e f
  map_id' X := by ext i; exact embed.f_id _
  map_comp' := by intros; ext i; exact embed.f_comp f g _

instance embed_additive : (embed e : HomologicalComplex 𝒞 cι ⥤ HomologicalComplex 𝒞 cι').Additive
    where map_add' X Y f g := by ext; exact embed.f_add _

def embedIso (i : ι) : ((embed e).obj X).pt (e.f i) ≅ X.pt i :=
  eqToIso
    (by
      delta embed embed.obj
      dsimp
      rw [e.r_f]
      rfl)

theorem embed_eval_isZero_of_none (i' : ι') (hi' : e.R i' = none) :
    IsZero (embed e ⋙ HomologicalComplex.eval 𝒞 _ i') :=
  by
  rw [functor.is_zero_iff]
  intro X
  exact is_zero.of_iso (limits.is_zero_zero _) (embed.X_iso_of_none X hi')

@[simps]
def embedEvalIsoOfSome (i' : ι') (i : ι) (hi' : e.R i' = some i) :
    embed e ⋙ HomologicalComplex.eval 𝒞 cι' i' ≅ HomologicalComplex.eval 𝒞 cι i :=
  NatIso.ofComponents (fun X => Embed.xIsoOfSome X hi') fun X₁ X₂ f =>
    by
    dsimp [embed, embed.map]
    rw [embed.f_of_some f hi']
    simp only [category.assoc, iso.inv_hom_id, category.comp_id]

@[simp]
theorem embed_nat_obj_down_up_succ (C : ChainComplex 𝒞 ℕ) (i : ℕ) :
    ((embed ComplexShape.Embedding.natDownIntUp).obj C).pt -[i+1] = C.pt (i + 1) :=
  rfl

@[simp]
theorem embed_nat_obj_down_up_zero (C : ChainComplex 𝒞 ℕ) :
    ((embed ComplexShape.Embedding.natDownIntUp).obj C).pt 0 = C.pt 0 :=
  rfl

@[simp]
theorem embed_nat_obj_down_up_pos (C : ChainComplex 𝒞 ℕ) (i : ℕ) :
    ((embed ComplexShape.Embedding.natDownIntUp).obj C).pt (i + 1) = 0 :=
  rfl

@[simp]
theorem embed_nat_obj_down_up_succ_f (C₁ C₂ : ChainComplex 𝒞 ℕ) (f : C₁ ⟶ C₂) (i : ℕ) :
    ((embed ComplexShape.Embedding.natDownIntUp).map f).f -[i+1] = f.f (i + 1) :=
  rfl

@[simp]
theorem embed_nat_obj_down_up_zero_f (C₁ C₂ : ChainComplex 𝒞 ℕ) (f : C₁ ⟶ C₂) :
    ((embed ComplexShape.Embedding.natDownIntUp).map f).f 0 = f.f 0 :=
  rfl

@[simp]
theorem embed_nat_obj_down_up_zero_pos (C₁ C₂ : ChainComplex 𝒞 ℕ) (f : C₁ ⟶ C₂) (i : ℕ) :
    ((embed ComplexShape.Embedding.natDownIntUp).map f).f (i + 1) = 0 :=
  rfl

end EmbeddingChangeOfComplex

section Homotopy

variable {X Y : HomologicalComplex 𝒞 cι}

variable (f f' : X ⟶ Y) (h : Homotopy f f')

/-- The morphism `hᵢⱼ: Xᵢ ⟶ Yⱼ` coming from a homotopy between two morphisms of type `X ⟶ Y`.
  Here `X` and `Y` are complexes of shape `ι` and the indices `i j` run over `option ι`. -/
def embedHomotopyHom : ∀ i j : Option ι, Embed.x X i ⟶ Embed.x Y j
  | some i, some j => h.Hom i j
  | some i, none => 0
  | none, j => 0

@[simp]
theorem embedHomotopyHom_some (i j : ι) : embedHomotopyHom f f' h (some i) (some j) = h.Hom i j :=
  rfl

@[simp]
theorem embedHomotopyHom_eq_zero_of_to_none (oi : Option ι) : embedHomotopyHom f f' h oi none = 0 :=
  by cases oi <;> rfl

@[simp]
theorem embedHomotopyHom_eq_zero_of_of_none (oi : Option ι) : embedHomotopyHom f f' h none oi = 0 :=
  rfl

theorem embed_homotopy_zero :
    ∀ (oi oj : Option ι) (H : ∀ i j : ι, oi = some i → oj = some j → ¬cι.Rel j i),
      embedHomotopyHom f f' h oi oj = 0
  | some i, some j, H => h.zero i j <| H _ _ rfl rfl
  | some i, none, H => rfl
  | none, j, H => rfl

def embedHomotopy (e : cι.Embedding cι') : Homotopy ((embed e).map f) ((embed e).map f')
    where
  Hom i j := embedHomotopyHom f f' h (e.R i) (e.R j)
  zero' i j hij :=
    embed_homotopy_zero f f' h _ _
      (by
        simp only [e.eq_some]
        rintro i' j' rfl rfl h'
        exact hij (e.c h'))
  comm i' := by
    by_cases hi : ∃ i : ι, i' = e.f i
    · rcases hi with ⟨i, rfl⟩
      delta embed embed.map embed.obj embed.X embed.d embed.f embed_homotopy_hom dNext prevD id
      dsimp only [AddMonoidHom.mk'_apply]
      rw [e.r_f i]
      dsimp only
      rw [h.comm i]
      delta dNext prevD id
      dsimp only [AddMonoidHom.mk'_apply]
      rw [add_left_inj]
      congr 1
      · by_cases aux : ∃ j, cι.rel i j
        · rcases aux with ⟨j, hj⟩
          rw [cι.next_eq' hj, cι'.next_eq' (e.c hj), e.r_f]
        · push_neg at aux 
          induction' x : e.r (cι'.next (e.f i)) with <;> simp only [X.shape _ _ (aux _), zero_comp]
      · by_cases aux : ∃ j, cι.rel j i
        · rcases aux with ⟨j, hj⟩
          rw [cι.prev_eq' hj, cι'.prev_eq' (e.c hj), e.r_f]
        · push_neg at aux 
          induction' x : e.r (cι'.prev (e.f i)) with <;> simp only [Y.shape _ _ (aux _), comp_zero]
    · -- i' not in image
      have foo := e.r_none _ hi
      suffices Subsingleton (embed.X X (e.r i') ⟶ embed.X Y (e.r i')) by
        refine' @Subsingleton.elim _ this _ _
      convert homological_complex.embed.subsingleton_of_none X _

end Homotopy

section HomologyComparison

def congrEval (𝓐 : Type _) [Category 𝓐] [Preadditive 𝓐] (c₁ : ComplexShape ι₁) (i j : ι₁)
    (h : i = j) : eval 𝓐 c₁ i ≅ eval 𝓐 c₁ j :=
  eqToIso (by rw [h])

def congrPrevFunctor (𝓐 : Type _) [Category 𝓐] [Abelian 𝓐] (c₁ : ComplexShape ι₁) (i j : ι₁)
    (h : i = j) : prevFunctor 𝓐 c₁ i ≅ prevFunctor 𝓐 c₁ j :=
  eqToIso (by rw [h])

def congrNextFunctor (𝓐 : Type _) [Category 𝓐] [Abelian 𝓐] (c₁ : ComplexShape ι₁) (i j : ι₁)
    (h : i = j) : nextFunctor 𝓐 c₁ i ≅ nextFunctor 𝓐 c₁ j :=
  eqToIso (by rw [h])

def embedCompEval (𝓐 : Type _) [Category 𝓐] [Preadditive 𝓐] [HasZeroObject 𝓐] {c₁ : ComplexShape ι₁}
    {c₂ : ComplexShape ι₂} (e : c₁.Embedding c₂) (i₁ : ι₁) :
    embed e ⋙ eval 𝓐 c₂ (e.f i₁) ≅ eval 𝓐 c₁ i₁ :=
  NatIso.ofComponents (fun X => Embed.xIsoOfSome X (e.r_f i₁)) fun X Y f =>
    by
    dsimp [embed, embed.map]
    rw [embed.f_of_some f (e.r_f i₁)]
    simp only [category.assoc, iso.inv_hom_id, category.comp_id]

/-
def embed_comp_prev_functor (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff) (i₁ : ι₁) :
  embed e ⋙ prev_functor 𝓐 c₂ (e.f i₁) ≅ prev_functor 𝓐 c₁ i₁ :=
begin
  rcases h₁ : c₁.prev i₁ with _ | ⟨j, hj⟩,
  { apply is_zero.iso,
    { rcases h₂ : c₂.prev (e.f i₁) with _ | ⟨k, hk⟩,
      { apply functor.is_zero_of_comp,
        exact prev_functor_is_zero _ _ _ h₂, },
      { rw is_zero.iff_id_eq_zero,
        ext X,
        apply is_zero.eq_of_src,
        dsimp,
        refine is_zero.of_iso _ (((embed e).obj X).X_prev_iso hk),
        dsimp [embed, embed.obj],
        apply embed.X_is_zero_of_none X,
        apply e.r_none,
        rintro ⟨i, hi⟩,
        rw [hi, ← he] at hk,
        rw c₁.prev_eq_some hk at h₁,
        simpa only using h₁, }, },
    { exact prev_functor_is_zero _ _ _ h₁, }, },
  { exact iso_whisker_left (embed e) (prev_functor_iso_eval 𝓐 c₂ (e.f i₁) (e.f j) (e.c hj)) ≪≫
       embed_comp_eval 𝓐 e j ≪≫
       (prev_functor_iso_eval 𝓐 c₁ i₁ j hj).symm, }
end

def embed_comp_next_functor (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff) (i₁ : ι₁) :
  embed e ⋙ next_functor 𝓐 c₂ (e.f i₁) ≅ next_functor 𝓐 c₁ i₁ :=
begin
  rcases h₁ : c₁.next i₁ with _ | ⟨j, hj⟩,
  { apply is_zero.iso,
    { rcases h₂ : c₂.next (e.f i₁) with _ | ⟨k, hk⟩,
      { apply functor.is_zero_of_comp,
        exact next_functor_is_zero _ _ _ h₂, },
      { rw is_zero.iff_id_eq_zero,
        ext X,
        apply is_zero.eq_of_src,
        dsimp,
        refine is_zero.of_iso _ (((embed e).obj X).X_next_iso hk),
        dsimp [embed, embed.obj],
        apply embed.X_is_zero_of_none X,
        apply e.r_none,
        rintro ⟨i, hi⟩,
        rw [hi, ← he] at hk,
        rw c₁.next_eq_some hk at h₁,
        simpa only using h₁,}, },
    { exact next_functor_is_zero _ _ _ h₁, }, },
  { exact iso_whisker_left (embed e) (next_functor_iso_eval 𝓐 c₂ (e.f i₁) (e.f j) (e.c hj)) ≪≫
       embed_comp_eval 𝓐 e j ≪≫
       (next_functor_iso_eval 𝓐 c₁ i₁ j hj).symm }
end

def embed_short_complex_functor_homological_complex_π₁ (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙ short_complex.π₁ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙ short_complex.π₁ :=
functor.associator _ _ _ ≪≫
  iso_whisker_left (embed e)
    (short_complex.functor_homological_complex_π₁_iso_prev_functor 𝓐 c₂ i₂) ≪≫
  (iso_whisker_left (embed e) (congr_prev_functor 𝓐 c₂ i₂ (e.f i₁) h₁₂.symm)) ≪≫
  embed_comp_prev_functor 𝓐 e he i₁ ≪≫
  (short_complex.functor_homological_complex_π₁_iso_prev_functor 𝓐 c₁ i₁).symm

def embed_short_complex_functor_homological_complex_π₂ (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (i₁ : ι₁) (i₂ : ι₂)
  (h₁₂ : e.f i₁ = i₂) :
  (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙ short_complex.π₂ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙ short_complex.π₂ :=
functor.associator _ _ _ ≪≫
  iso_whisker_left (embed e)
    (short_complex.functor_homological_complex_π₂_iso_eval 𝓐 c₂ i₂) ≪≫
  (iso_whisker_left (embed e) (congr_eval 𝓐 c₂ i₂ (e.f i₁) h₁₂.symm)) ≪≫
  embed_comp_eval 𝓐 e i₁ ≪≫
  (short_complex.functor_homological_complex_π₂_iso_eval 𝓐 c₁ i₁).symm

def embed_short_complex_functor_homological_complex_π₃ (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  (embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂) ⋙ short_complex.π₃ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ ⋙ short_complex.π₃ :=
functor.associator _ _ _ ≪≫
  iso_whisker_left (embed e)
    (short_complex.functor_homological_complex_π₃_iso_next_functor 𝓐 c₂ i₂) ≪≫
  (iso_whisker_left (embed e) (congr_next_functor 𝓐 c₂ i₂ (e.f i₁) h₁₂.symm)) ≪≫
  embed_comp_next_functor 𝓐 e he i₁ ≪≫
  (short_complex.functor_homological_complex_π₃_iso_next_functor 𝓐 c₁ i₁).symm

lemma embed_d_to (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (X : homological_complex 𝓐 c₁) :
  ((embed e).obj X).d_to (e.f i₁) ≫ (embed.X_iso_of_some X (e.r_f i₁)).hom =
  (embed_comp_prev_functor 𝓐 e he i₁).hom.app X ≫ X.d_to i₁ :=
begin
  dsimp [embed_comp_prev_functor],
  rcases h₁ : c₁.prev i₁ with _ | ⟨j, hj⟩,
  { simp only [h₁, d_to_eq_zero, comp_zero, preadditive.is_iso.comp_right_eq_zero],
    rcases h₂ : c₂.prev (e.f i₁) with _ | ⟨k, hk⟩,
    { apply is_zero.eq_of_src,
      exact is_zero.of_iso (limits.is_zero_zero _) (((embed e).obj X).X_prev_iso_zero h₂), },
    { simp only [homological_complex.d_to_eq _ hk, preadditive.is_iso.comp_left_eq_zero],
      dsimp [embed, embed.obj, embed.d],
      rcases h₃ : e.r k with _ | l,
      { refl, },
      { rw e.r_f i₁,
        dsimp [embed.d],
        by_cases h₄ : c₁.rel l i₁,
        { exfalso,
          simpa only [c₁.prev_eq_some h₄] using h₁, },
        { exact X.shape _ _ h₄, }, }, }, },
  { simp only [h₁, homological_complex.d_to_eq _ hj,
      homological_complex.d_to_eq _ (e.c hj)],
    conv_lhs { congr, congr, skip, dsimp [embed, embed.obj, embed.d], },
    rw embed.d_of_some_of_some X (e.r_f j) (e.r_f i₁),
    dsimp [iso_whisker_left, prev_functor_iso_eval, embed_comp_eval, nat_iso.of_components],
    simp only [category.assoc, iso.inv_hom_id, category.comp_id, iso.inv_hom_id_assoc], },
end

lemma embed_d_from (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (X : homological_complex 𝓐 c₁) :
  ((embed e).obj X).d_from (e.f i₁) ≫ (embed_comp_next_functor 𝓐 e he i₁).hom.app X =
  (embed.X_iso_of_some X (e.r_f i₁)).hom ≫ X.d_from i₁ :=
begin
  dsimp [embed_comp_next_functor],
  rcases h₁ : c₁.next i₁ with _ | ⟨j, hj⟩,
  { simp only [h₁, d_from_eq_zero, comp_zero, preadditive.is_iso.comp_right_eq_zero],
    rcases h₂ : c₂.next (e.f i₁) with _ | ⟨k, hk⟩,
    { apply is_zero.eq_of_tgt,
      exact is_zero.of_iso (limits.is_zero_zero _) (((embed e).obj X).X_next_iso_zero h₂), },
    { simp only [homological_complex.d_from_eq _ hk, preadditive.is_iso.comp_right_eq_zero],
      dsimp [embed, embed.obj, embed.d],
      rcases h₃ : e.r k with _ | l,
      { exact embed.d_of_none_tgt X rfl, },
      { rw e.r_f i₁,
        dsimp [embed.d],
        by_cases h₄ : c₁.rel i₁ l,
        { exfalso,
          simpa only [c₁.next_eq_some h₄] using h₁, },
        { exact X.shape _ _ h₄, }, }, }, },
  { simp only [h₁, homological_complex.d_from_eq _ hj,
      homological_complex.d_from_eq _ (e.c hj)],
    conv_lhs { congr, congr, dsimp [embed, embed.obj, embed.d], },
    rw embed.d_of_some_of_some X (e.r_f i₁) (e.r_f j),
    dsimp [iso_whisker_left, next_functor_iso_eval, embed_comp_eval, nat_iso.of_components],
    simp only [category.assoc, eq_to_hom_trans, eq_to_hom_refl, category.comp_id,
      iso.inv_hom_id_assoc], },
end

def embed_short_complex_functor_homological_complex (𝓐 : Type*) [category 𝓐] [abelian 𝓐]
  {c₁ : complex_shape ι₁} {c₂ : complex_shape ι₂} (e : c₁.embedding c₂) (he : e.c_iff)
  (i₁ : ι₁) (i₂ : ι₂) (h₁₂ : e.f i₁ = i₂) :
  embed e ⋙ short_complex.functor_homological_complex 𝓐 c₂ i₂ ≅
  short_complex.functor_homological_complex 𝓐 c₁ i₁ :=
begin
  refine short_complex.functor_nat_iso_mk
    (embed_short_complex_functor_homological_complex_π₁ 𝓐 e he i₁ i₂ h₁₂)
    (embed_short_complex_functor_homological_complex_π₂ 𝓐 e i₁ i₂ h₁₂)
    (embed_short_complex_functor_homological_complex_π₃ 𝓐 e he i₁ i₂ h₁₂) _ _,
  { subst h₁₂,
    ext X,
    dsimp [nat_trans.hcomp, embed_short_complex_functor_homological_complex_π₂,
      short_complex.functor_homological_complex_π₂_iso_eval,
      embed_short_complex_functor_homological_complex_π₁, congr_eval,
      congr_prev_functor, embed_comp_eval, iso.refl,
      short_complex.functor_homological_complex_π₁_iso_prev_functor],
    simp only [category.assoc],
    erw [nat_trans.id_app, nat_trans.id_app],
    repeat { erw category.id_comp, },
    repeat { erw category.comp_id, },
    apply embed_d_to, },
  { subst h₁₂,
    ext X,
    dsimp [nat_trans.hcomp, embed_short_complex_functor_homological_complex_π₂,
      short_complex.functor_homological_complex_π₂_iso_eval,
      embed_short_complex_functor_homological_complex_π₃, congr_eval,
      congr_prev_functor, embed_comp_eval, iso.refl,
      short_complex.functor_homological_complex_π₃_iso_next_functor],
    simp only [category.assoc],
    erw [nat_trans.id_app, nat_trans.id_app],
    repeat { erw category.id_comp, },
    repeat { erw category.comp_id, },
    apply embed_d_from, },
end
-/
variable (𝓐 : Type _) [Category 𝓐] [Abelian 𝓐] (e : c₁.Embedding c₂) (i₁ : ι₁) (i₂ : ι₂)

@[simp]
def embedShortComplexπ₁ι :
    embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ ⋙ ShortComplex.π₁ ⟶
      ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ ⋙ ShortComplex.π₁ :=
  by
  by_cases e.r (c₂.prev i₂) = some (c₁.prev i₁)
  · exact (embed_eval_iso_of_some e _ _ h).Hom
  · exact 0

@[simp]
def embedShortComplexπ₂Iso (h₁₂ : e.f i₁ = i₂) :
    embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ ⋙ ShortComplex.π₂ ≅
      ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ ⋙ ShortComplex.π₂ :=
  embedEvalIsoOfSome e i₂ i₁ (by rw [← h₁₂, e.r_f])

@[simp]
def embedShortComplexπ₃ι :
    embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ ⋙ ShortComplex.π₃ ⟶
      ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ ⋙ ShortComplex.π₃ :=
  by
  by_cases e.r (c₂.next i₂) = some (c₁.next i₁)
  · exact (embed_eval_iso_of_some e _ _ h).Hom
  · exact 0

-- @[simps]
def embedShortComplexι (h₁₂ : e.f i₁ = i₂) :
    embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ ⟶
      ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ :=
  ShortComplex.natTransHomMk (embedShortComplexπ₁ι 𝓐 e _ _) (embedShortComplexπ₂Iso 𝓐 e _ _ h₁₂).Hom
    (embedShortComplexπ₃ι 𝓐 e _ _)
    (by
      ext X
      subst h₁₂
      show
        (((embed e).obj X).dTo (e.f i₁) ≫ 𝟙 (((embed e).obj X).pt (e.f i₁))) ≫
            (embed.X_iso_of_some X _).Hom =
          (embed_short_complex_π₁_ι 𝓐 e i₁ (e.f i₁)).app X ≫ X.d_to i₁ ≫ 𝟙 (X.X i₁)
      simp only [embed_short_complex_π₁_ι, category.comp_id]
      split_ifs with h
      · show
          embed.d X (e.r (c₂.prev (e.f i₁))) (e.r (e.f i₁)) ≫ (embed.X_iso_of_some X _).Hom =
            (embed.X_iso_of_some X h).Hom ≫ X.d (c₁.prev i₁) i₁
        simp only [embed.d_of_some_of_some X h (e.r_f i₁), category.assoc, iso.inv_hom_id,
          category.comp_id]
      · suffices ((embed e).obj X).dTo (e.f i₁) = 0 by
          simp only [this, nat_trans.app_zero, zero_comp]
        rcases h₂ : e.r (c₂.prev (e.f i₁)) with (_ | j)
        · apply is_zero.eq_of_src
          apply embed.X_is_zero_of_none
          exact h₂
        · show embed.d X (e.r (c₂.prev (e.f i₁))) (e.r (e.f i₁)) = 0
          by_contra h'
          rcases embed.d_ne_zero _ _ _ h' with ⟨i, k, h₃, h₄, h₅⟩
          rw [e.r_f] at h₄ 
          rw [h₂] at h₃ 
          simp only at h₄ h₃ 
          substs h₃ h₄
          have h₅' : c₁.rel j i₁ := by
            by_contra h₅''
            exact h₅ (X.shape _ _ h₅'')
          rw [c₁.prev_eq' h₅'] at h 
          exact h h₂)
    (by
      ext X
      show
        (((embed e).obj X).dFrom i₂ ≫ 𝟙 (((embed e).obj X).xNext i₂)) ≫ _ =
          (embed.X_iso_of_some X _).Hom ≫ X.d_from i₁ ≫ 𝟙 (X.X_next i₁)
      dsimp only [embed_short_complex_π₃_ι]
      subst h₁₂
      split_ifs with h
      · simp only [category.comp_id]
        show
          embed.d X (e.r (e.f i₁)) (e.r (c₂.next (e.f i₁))) ≫ (embed.X_iso_of_some X h).Hom =
            (embed.X_iso_of_some X _).Hom ≫ X.d_from i₁
        simp only [embed.d_of_some_of_some X (e.r_f i₁) h, category.assoc, iso.inv_hom_id,
          category.comp_id]
      · suffices X.d i₁ (c₁.next i₁) = 0 by delta d_from;
          simp only [this, zero_comp, comp_zero, nat_trans.app_zero]
        apply X.shape
        rw [e.eq_some] at h 
        contrapose! h
        rw [c₂.next_eq' (e.c h)])

@[simp]
def embedShortComplexπ₁π :
    ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ ⋙ ShortComplex.π₁ ⟶
      embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ ⋙ ShortComplex.π₁ :=
  by
  by_cases e.r (c₂.prev i₂) = some (c₁.prev i₁)
  · exact (embed_eval_iso_of_some e _ _ h).inv
  · exact 0

@[simp]
def embedShortComplexπ₃π :
    ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ ⋙ ShortComplex.π₃ ⟶
      embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ ⋙ ShortComplex.π₃ :=
  by
  by_cases e.r (c₂.next i₂) = some (c₁.next i₁)
  · exact (embed_eval_iso_of_some e _ _ h).inv
  · exact 0

@[simps]
def embedShortComplexπ (h₁₂ : e.f i₁ = i₂) :
    ShortComplex.functorHomologicalComplex 𝓐 c₁ i₁ ⟶
      embed e ⋙ ShortComplex.functorHomologicalComplex 𝓐 c₂ i₂ :=
  ShortComplex.natTransHomMk (embedShortComplexπ₁π 𝓐 e _ _) (embedShortComplexπ₂Iso 𝓐 e _ _ h₁₂).inv
    (embedShortComplexπ₃π 𝓐 e _ _)
    (by
      ext X
      show
        (X.d_to i₁ ≫ 𝟙 (X.X i₁)) ≫ (embed.X_iso_of_some X _).inv =
          _ ≫ ((embed e).obj X).dTo i₂ ≫ 𝟙 (((embed e).obj X).pt i₂)
      dsimp only [embed_short_complex_π₁_π]
      subst h₁₂
      split_ifs with h
      · simp only [category.comp_id]
        show
          X.d (c₁.prev i₁) i₁ ≫ (embed.X_iso_of_some X _).inv =
            (embed.X_iso_of_some X h).inv ≫ embed.d X (e.r (c₂.prev (e.f i₁))) (e.r (e.f i₁))
        simp only [embed.d_of_some_of_some X h (e.r_f i₁), category.assoc, iso.inv_hom_id_assoc]
      · suffices X.d (c₁.prev i₁) i₁ = 0 by delta d_to;
          simp only [this, zero_comp, nat_trans.app_zero]
        apply X.shape
        rw [e.eq_some] at h 
        contrapose! h
        rw [c₂.prev_eq' (e.c h)])
    (by
      ext X
      show
        (X.d_from i₁ ≫ 𝟙 (X.X_next i₁)) ≫ _ =
          (embed.X_iso_of_some X _).inv ≫
            ((embed e).obj X).dFrom i₂ ≫ 𝟙 (((embed e).obj X).xNext i₂)
      dsimp only [embed_short_complex_π₃_π]
      subst h₁₂
      split_ifs with h
      · simp only [category.comp_id]
        show
          X.d i₁ (c₁.next i₁) ≫ (embed.X_iso_of_some X h).inv =
            (embed.X_iso_of_some X _).inv ≫ embed.d X (e.r (e.f i₁)) (e.r (c₂.next (e.f i₁)))
        simp only [embed.d_of_some_of_some X (e.r_f i₁) h, category.assoc, iso.inv_hom_id_assoc]
      · suffices ((embed e).obj X).dFrom (e.f i₁) = 0 by
          simp only [this, nat_trans.app_zero, zero_comp, comp_zero]
        rcases h₂ : e.r (c₂.next (e.f i₁)) with (_ | j)
        · apply is_zero.eq_of_tgt
          apply embed.X_is_zero_of_none
          exact h₂
        · show embed.d X (e.r (e.f i₁)) (e.r (c₂.next (e.f i₁))) = 0
          by_contra h'
          rcases embed.d_ne_zero _ _ _ h' with ⟨i, k, h₃, h₄, h₅⟩
          rw [e.r_f] at h₃ 
          rw [h₂] at h₄ 
          simp only at h₄ h₃ 
          substs h₃ h₄
          have h₅' : c₁.rel i₁ j := by
            by_contra h₅''
            exact h₅ (X.shape _ _ h₅'')
          rw [c₁.next_eq' h₅'] at h 
          exact h h₂)

def homologyEmbedNatIso (h₁₂ : e.f i₁ = i₂) :
    embed e ⋙ homology'Functor 𝓐 c₂ i₂ ≅ homology'Functor 𝓐 c₁ i₁
    where
  Hom := embedShortComplexι 𝓐 e i₁ i₂ h₁₂ ◫ 𝟙 ShortComplex.homologyFunctor
  inv := embedShortComplexπ 𝓐 e i₁ i₂ h₁₂ ◫ 𝟙 ShortComplex.homologyFunctor
  hom_inv_id' := by
    ext K : 2
    simp only [nat_trans.comp_app, nat_trans.hcomp_id_app, nat_trans.id_app, ← functor.map_comp]
    apply ShortComplex.homologyFunctor_map_eq_id
    simp only [ShortComplex.comp_τ₂]
    dsimp only [embed_short_complex_ι, embed_short_complex_π]
    simpa only [ShortComplex.natTransHomMk_app_τ₂_eq, iso.hom_inv_id_app]
  inv_hom_id' := by
    ext K : 2
    simp only [nat_trans.comp_app, nat_trans.hcomp_id_app, nat_trans.id_app, ← functor.map_comp]
    apply ShortComplex.homologyFunctor_map_eq_id
    simp only [ShortComplex.comp_τ₂]
    dsimp only [embed_short_complex_ι, embed_short_complex_π]
    simpa only [ShortComplex.natTransHomMk_app_τ₂_eq, iso.inv_hom_id_app]

end HomologyComparison

end HomologicalComplex

namespace ChainComplex

def single₀CompEmbedIsoSingleComponent (X : 𝒞) :
    ∀ i : ℤ,
      ((single₀ 𝒞 ⋙ HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj X).pt i ≅
        ((HomologicalComplex.single 𝒞 (ComplexShape.up ℤ) 0).obj X).pt i
  | 0 => Iso.refl _
  | (n + 1 : ℕ) => Iso.refl _
  | -[n+1] => Iso.refl _

def single₀CompEmbedIsoSingle :
    single₀ 𝒞 ⋙ HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ≅
      HomologicalComplex.single 𝒞 (ComplexShape.up ℤ) 0 :=
  NatIso.ofComponents
    (fun X =>
      HomologicalComplex.Hom.isoOfComponents (single₀CompEmbedIsoSingleComponent X)
        (by rintro ((_ | i) | i) ((_ | j) | j) hij <;> exact comp_zero.trans zero_comp.symm))
    (by
      intro X Y f
      ext ((_ | i) | i) <;>
          refine' (category.comp_id _).trans (Eq.trans _ (category.id_comp _).symm) <;>
        dsimp [HomologicalComplex.single]
      · simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, Nat.cast_zero];
        rfl
      · rw [dif_neg]; swap; decide; rfl
      · rw [dif_neg]; swap; decide)

end ChainComplex

