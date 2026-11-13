import LiquidTensorExperiment.HacksAndTricks.ByExactIHack
import LiquidTensorExperiment.SystemOfComplexes.Basic
import LiquidTensorExperiment.Facts.Default

#align_import system_of_complexes.double

universe v u

noncomputable section

open Opposite CategoryTheory

open scoped NNReal

/-!

# Systems of double complexes of seminormed groups

In this file we define systems of double complexes of seminormed groups,
as needed for Definition 9.6 of [Analytic].

## Main declarations

* `system_of_double_complexes`: a system of complexes of seminormed groups.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing.

-/


/-- A system of double complexes of seminormed groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic]. -/
def SystemOfDoubleComplexes : Type (u + 1) :=
  ℝ≥0ᵒᵖ ⥤ CochainComplex (CochainComplex SemiNormedGroupCat.{u} ℕ) ℕ
deriving CategoryTheory.Category

namespace SystemOfDoubleComplexes

variable (C : SystemOfDoubleComplexes)

/-- `C.X c p q` is the object $C_c^{p,q}$ in a system of double complexes `C`. -/
def x (c : ℝ≥0) (p q : ℕ) : SemiNormedGroupCat :=
  ((C.obj <| op c).pt p).pt q

/-- `C.res` is the restriction map `C.X c' p q ⟶ C.X c p q` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {c' c : ℝ≥0} {p q : ℕ} [h : Fact (c ≤ c')] : C.pt c' p q ⟶ C.pt c p q :=
  ((C.map (homOfLE h.out).op).f p).f q

variable (c : ℝ≥0) {c₁ c₂ c₃ : ℝ≥0} (p p' q q' : ℕ)

@[simp]
theorem res_refl : @res C c c p q _ = 𝟙 _ :=
  by
  have := CategoryTheory.Functor.map_id C (op <| c)
  delta res; erw [this]; rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
@[simp]
theorem norm_res_of_eq (h : c₂ = c₁) (x : C.pt c₁ p q) :
    «expr∥ ∥» (@res C _ _ p q ⟨h.le⟩ x) = «expr∥ ∥» x := by cases h; rw [res_refl]; rfl

@[simp]
theorem res_comp_res (h₁ : Fact (c₂ ≤ c₁)) (h₂ : Fact (c₃ ≤ c₂)) :
    @res C _ _ p q h₁ ≫ @res C _ _ p q h₂ = @res C _ _ p q ⟨h₂.out.trans h₁.out⟩ :=
  by
  have := CategoryTheory.Functor.map_comp C (hom_of_le h₁.out).op (hom_of_le h₂.out).op
  rw [← op_comp] at this 
  delta res; erw [this]; rfl

@[simp]
theorem res_res (h₁ : Fact (c₂ ≤ c₁)) (h₂ : Fact (c₃ ≤ c₂)) (x : C.pt c₁ p q) :
    @res C _ _ p q h₂ (@res C _ _ p q h₁ x) = @res C _ _ p q ⟨h₂.out.trans h₁.out⟩ x := by
  rw [← C.res_comp_res p q h₁ h₂]; rfl

/-- `C.d` is the differential `C.X c p q ⟶ C.X c (p+1) q` for a system of double complexes `C`. -/
def d {c : ℝ≥0} (p p' : ℕ) {q : ℕ} : C.pt c p q ⟶ C.pt c p' q :=
  ((C.obj <| op c).d p p').f q

theorem d_eq_zero (c : ℝ≥0) (h : p + 1 ≠ p') : (C.d p p' : C.pt c p q ⟶ _) = 0 := by
  have : (C.obj (op c)).d p p' = 0 := (C.obj <| op c).shape _ _ h; rw [d, this]; rfl

theorem d_eq_zero_apply (c : ℝ≥0) (h : p + 1 ≠ p') (x : C.pt c p q) : C.d p p' x = 0 := by
  rw [d_eq_zero C p p' q c h]; rfl

@[simp]
theorem d_self_apply (c : ℝ≥0) (x : C.pt c p q) : C.d p p x = 0 :=
  d_eq_zero_apply _ _ _ _ _ p.succ_ne_self _

theorem d_comp_res (h : Fact (c₂ ≤ c₁)) :
    C.d p p' ≫ @res C _ _ _ q h = @res C _ _ p q _ ≫ C.d p p' :=
  congr_fun (congr_arg HomologicalComplex.Hom.f ((C.map (homOfLE h.out).op).comm p p')).symm q

theorem d_res (h : Fact (c₂ ≤ c₁)) (x) :
    @d C c₂ p p' q (@res C _ _ p q _ x) = @res C _ _ _ _ h (@d C c₁ p p' q x) :=
  show (@res C _ _ p q _ ≫ C.d p p') x = (C.d p p' ≫ @res C _ _ _ _ h) x by rw [d_comp_res]

@[simp]
theorem d_comp_d {c : ℝ≥0} {p p' p'' q : ℕ} : @d C c p p' q ≫ C.d p' p'' = 0 :=
  congr_fun (congr_arg HomologicalComplex.Hom.f ((C.obj <| op c).d_comp_d p p' p'')) q

@[simp]
theorem d_d {c : ℝ≥0} {p p' p'' q : ℕ} (x : C.pt c p q) : C.d p' p'' (C.d p p' x) = 0 :=
  show (C.d _ _ ≫ C.d _ _) x = 0 by rw [d_comp_d]; rfl

/-- `C.d'` is the differential `C.X c p q ⟶ C.X c p (q+1)` for a system of double complexes `C`. -/
def d' {c : ℝ≥0} {p : ℕ} (q q' : ℕ) : C.pt c p q ⟶ C.pt c p q' :=
  ((C.obj <| op c).pt p).d q q'

theorem d'_eq_zero (c : ℝ≥0) (h : q + 1 ≠ q') : (C.d' q q' : C.pt c p q ⟶ _) = 0 :=
  ((C.obj <| op c).pt p).shape _ _ h

theorem d'_eq_zero_apply (c : ℝ≥0) (h : q + 1 ≠ q') (x : C.pt c p q) : C.d' q q' x = 0 := by
  rw [d'_eq_zero C p q q' c h]; rfl

@[simp]
theorem d'_self_apply (c : ℝ≥0) (x : C.pt c p q) : C.d' q q x = 0 :=
  d'_eq_zero_apply _ _ _ _ _ q.succ_ne_self _

theorem d'_comp_res (h : Fact (c₂ ≤ c₁)) :
    @d' C c₁ p q q' ≫ @res C _ _ _ _ h = @res C _ _ p q _ ≫ @d' C c₂ p q q' :=
  (((C.map (homOfLE h.out).op).f p).comm q q').symm

theorem d'_res (h : Fact (c₂ ≤ c₁)) (x) :
    C.d' q q' (@res C _ _ p q _ x) = @res C _ _ _ _ h (C.d' q q' x) :=
  show (@res C _ _ p q _ ≫ C.d' q q') x = (C.d' q q' ≫ @res C _ _ _ _ h) x by rw [d'_comp_res]

@[simp]
theorem d'_comp_d' {c : ℝ≥0} {p q q' q'' : ℕ} : @d' C c p q q' ≫ C.d' q' q'' = 0 :=
  ((C.obj <| op c).pt p).d_comp_d q q' q''

@[simp]
theorem d'_d' {c : ℝ≥0} {p q q' q'' : ℕ} (x : C.pt c p q) : C.d' q' q'' (C.d' q q' x) = 0 :=
  show (C.d' _ _ ≫ C.d' _ _) x = 0 by rw [d'_comp_d']; rfl

theorem d'_comp_d (c : ℝ≥0) (p p' q q' : ℕ) :
    C.d' q q' ≫ C.d p p' = C.d p p' ≫ (C.d' q q' : C.pt c p' q ⟶ _) :=
  (((C.obj <| op c).d p p').comm q q').symm

theorem d'_d (c : ℝ≥0) (p p' q q' : ℕ) (x : C.pt c p q) :
    C.d' q q' (C.d p p' x) = C.d p p' (C.d' q q' x) :=
  show (C.d p p' ≫ C.d' q q') x = (C.d' q q' ≫ C.d p p') x by rw [d'_comp_d]

/-- Convenience definition:
The identity morphism of an object in the system of double complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {p p' q q' : ℕ} (hc : c = c') (hp : p = p') (hq : q = q') :
    C.pt c p q ⟶ C.pt c' p' q' :=
  eqToHom <| by subst hc; subst hp; subst hq

/-- The `p`-th row in a system of double complexes, as system of complexes.
  It has object `(C.obj c).X p`over `c`. -/
def row (C : SystemOfDoubleComplexes.{u}) (p : ℕ) : SystemOfComplexes.{u} :=
  C ⋙ HomologicalComplex.forget _ _ ⋙ Pi.eval _ p

@[simp]
theorem row_x (C : SystemOfDoubleComplexes) (p q : ℕ) (c : ℝ≥0) : C.row p c q = C.pt c p q :=
  rfl

@[simp]
theorem row_res (C : SystemOfDoubleComplexes) (p q : ℕ) {c' c : ℝ≥0} [h : Fact (c ≤ c')] :
    @SystemOfComplexes.res (C.row p) _ _ q h = @res C _ _ p q h :=
  rfl

@[simp]
theorem row_d (C : SystemOfDoubleComplexes) (c : ℝ≥0) (p : ℕ) : (C.row p).d = @d' C c p :=
  rfl

/-- The differential between rows in a system of double complexes,
as map of system of complexes. -/
@[simps app_f]
def rowMap (C : SystemOfDoubleComplexes.{u}) (p p' : ℕ) : C.row p ⟶ C.row p'
    where
  app c :=
    { f := fun q => (C.d p p' : C.pt c.unop p q ⟶ C.pt c.unop p' q)
      comm' := fun q q' _ => (C.d'_comp_d _ p p' q q').symm }
  naturality' c₁ c₂ h := (C.map h).comm p p'

@[simp]
theorem rowMap_apply (C : SystemOfDoubleComplexes.{u}) (c : ℝ≥0) (p p' q : ℕ) (x : C.pt c p q) :
    C.rowMap p p' x = C.d p p' x :=
  rfl

-- -- this should be found by TC, but we first need to make `pi.eval` and `graded_object` additive
-- instance aux : (homological_complex.forget SemiNormedGroup (complex_shape.up ℕ) ⋙
--   pi.eval (λ (_ : ℕ), SemiNormedGroup) q).additive :=
-- { map_zero' := λ C₁ C₂, by { dsimp, refl },
--   map_add' := by { intros, dsimp, refl } }
/-- The `q`-th column in a system of double complexes, as system of complexes. -/
@[simps]
def col (C : SystemOfDoubleComplexes.{u}) (q : ℕ) : SystemOfComplexes.{u} :=
  C ⋙ Functor.mapHomologicalComplex (HomologicalComplex.eval _ _ q) _

@[simp]
theorem col_x (C : SystemOfDoubleComplexes) (p q : ℕ) (c : ℝ≥0) : C.col q c p = C.pt c p q :=
  rfl

@[simp]
theorem col_res (C : SystemOfDoubleComplexes) (p q : ℕ) {c' c : ℝ≥0} [h : Fact (c ≤ c')] :
    (@SystemOfComplexes.res (C.col q) _ _ p h :
        C.col q c' p ⟶ C.col q c p) =-- (@res C _ _ p q h : C.X c' p q ⟶ C.X c p q) :=
    by dsimp_result => dsimp; exact (@res C _ _ p q h : C.X c' p q ⟶ C.X c p q) :=
  rfl

@[simp]
theorem col_d (C : SystemOfDoubleComplexes) (c : ℝ≥0) (p p' q : ℕ) :
    @SystemOfComplexes.d (C.col q) c p p' = by dsimp_result => dsimp; exact @d C c p p' q :=
  rfl

/-- The differential between columns in a system of double complexes,
as map of system of complexes. -/
def colMap (C : SystemOfDoubleComplexes.{u}) (q q' : ℕ) : C.col q ⟶ C.col q'
    where
  app c :=
    { f := fun p => (C.d' q q' : C.pt c.unop p q ⟶ C.pt c.unop p q')
      comm' := fun p p' _ => C.d'_comp_d _ p p' q q' }
  naturality' c₁ c₂ h := by ext p : 2; exact ((C.map h).f p).comm q q'

/-- A system of double complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure Admissible (C : SystemOfDoubleComplexes) : Prop where
  d_norm_noninc' : ∀ (c p p' q) (h : p + 1 = p'), (@d C c p p' q).NormNoninc
  d'_norm_noninc' : ∀ (c p q q') (h : q + 1 = q'), (@d' C c p q q').NormNoninc
  res_normNoninc : ∀ c' c p q h, (@res C c' c p q h).NormNoninc

namespace Admissible

variable {C}

theorem d_normNoninc (hC : C.Admissible) (c : ℝ≥0) (p p' q : ℕ) :
    (C.d p p' : C.pt c p q ⟶ _).NormNoninc :=
  by
  by_cases h : p + 1 = p'
  · exact hC.d_norm_noninc' c p p' q h
  · rw [C.d_eq_zero p p' q c h]; intro v; simp

theorem d'_normNoninc (hC : C.Admissible) (c : ℝ≥0) (p q q' : ℕ) :
    (C.d' q q' : C.pt c p q ⟶ _).NormNoninc :=
  by
  by_cases h : q + 1 = q'
  · exact hC.d'_norm_noninc' c p q q' h
  · rw [C.d'_eq_zero p q q' c h]; intro v; simp

theorem col (hC : C.Admissible) (q : ℕ) : (C.col q).Admissible :=
  { d_norm_noninc' := fun c i j h => hC.d_normNoninc _ _ _ _
    res_normNoninc := fun c i j h => hC.res_normNoninc _ _ _ _ _ }

theorem row (hC : C.Admissible) (p : ℕ) : (C.row p).Admissible :=
  { d_norm_noninc' := fun c i j h => hC.d'_normNoninc _ _ _ _
    res_normNoninc := fun c i j h => hC.res_normNoninc _ _ _ _ _ }

theorem mk' (h : ∀ p, (C.row p).Admissible)
    (hd : ∀ (c p p' q) (h : p + 1 = p'), (@d C c p p' q).NormNoninc) : C.Admissible :=
  { d_norm_noninc' := fun c p p' q h' => hd c p p' q h'
    d'_norm_noninc' := fun c p q q' h' => (h p).d_norm_noninc' _ _ _ h'
    res_normNoninc := fun c₁ c₂ p q h' => by skip; apply (h p).res_normNoninc }

end Admissible

end SystemOfDoubleComplexes

