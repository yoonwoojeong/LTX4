import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Completion
import LiquidTensorExperiment.Facts.Default

#align_import system_of_complexes.basic

universe v u

noncomputable section

open Opposite CategoryTheory

open scoped NNReal

/-!

# Systems of complexes of seminormed groups

In this file we define systems of complexes of seminormed groups,
as in of Definition 9.3 of [Analytic].

## Main declarations

* `system_of_complexes`: a system of complexes of seminormed groups. See Definition 4.1
  of the blueprint.
* `admissible`: such a system is *admissible* if all maps that occur in the system
    are norm-nonincreasing. See Definition 4.2 of the blueprint.
* `is_bounded_exact`: an exactness criterion for such systems, See Definition 4.3 of the
  blueprint. It asks for a suitable interplay between the norms and the algebraic properties
  of the system.
* `is_weak_bounded_exact` : another exactness criterion for such systems. See Definition 4.4
   of the blueprint.

## TODO

It seems a bit ridiculous that this file has to import `locally_constant.Vhat`.

-/


-- TODO: at some point we can abstract the following definition over `SemiNormedGroup` and `ℝ≥0`.
-- But I don't think that is relevant for this project.
/-- A system of complexes of seminormed groups, indexed by `ℝ≥0`.
See also Definition 9.3 of [Analytic]. -/
def SystemOfComplexes : Type _ :=
  ℝ≥0ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ
deriving CategoryTheory.Category

-- Porting note: `deriving Preadditive` is not supported; provide the instance by hand
instance : CategoryTheory.Preadditive SystemOfComplexes :=
  inferInstanceAs (CategoryTheory.Preadditive (ℝ≥0ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ))

-- instance : has_shift system_of_complexes := has_shift.mk $ (shift _).congr_right
variable {M M' N : SystemOfComplexes.{u}} (f : M ⟶ M') (g : M' ⟶ N)

instance : CoeFun SystemOfComplexes fun C => ℝ≥0 → ℕ → SemiNormedGroupCat :=
  ⟨fun C c i => (C.obj <| op c).X i⟩

/-- `f.apply c i` is application of the natural transformation `f`: $f_c^i : M_c^i ⟶ N_c^i$. -/
def Quiver.Hom.apply (f : M ⟶ N) {c : ℝ≥0} {i : ℕ} : M c i ⟶ N c i :=
  -- Porting note: `op` would resolve to `Quiver.Hom.op` inside this namespace
  (f.app (Opposite.op c)).f i

instance homToFun : CoeFun (M ⟶ N) fun f => ∀ {c : ℝ≥0} {i : ℕ}, M c i → N c i :=
  ⟨fun f {c} {i} x => f.apply x⟩

theorem SystemOfComplexes.hom_apply (f : M ⟶ N) {c : ℝ≥0} {i : ℕ} (x : M c i) : f x = f.apply x :=
  rfl

theorem SystemOfComplexes.map_sub (f : M ⟶ N) {c i} (m m' : M c i) : f (m - m') = f m - f m' :=
  _root_.map_sub ((f.app (op c)).f i) m m'

/-- `f.apply c i` is application of the natural isomorphism `f`: $f_c^i : M_c^i ≅ N_c^i$. -/
def CategoryTheory.Iso.apply (f : M ≅ N) {c : ℝ≥0} {i : ℕ} : M c i ≅ N c i :=
  HomologicalComplex.Hom.isoApp (f.app (op c)) i

namespace SystemOfComplexes

variable (C C₁ C₂ : SystemOfComplexes.{u})

/-- `res` is the restriction map `C c' i ⟶ C c i` for a system of complexes `C`,
and nonnegative reals `c ≤ c'`. -/
def res {C : SystemOfComplexes} {c' c : ℝ≥0} {i : ℕ} [h : Fact (c ≤ c')] : C c' i ⟶ C c i :=
  (C.map (homOfLE h.out).op).f i

variable {c₁ c₂ c₃ : ℝ≥0} (i j : ℕ)

@[simp]
theorem res_comp_res (h₁ : Fact (c₂ ≤ c₁)) (h₂ : Fact (c₃ ≤ c₂)) :
    @res C _ _ i h₁ ≫ @res C _ _ i h₂ = @res C _ _ i ⟨h₂.out.trans h₁.out⟩ :=
  by
  have := CategoryTheory.Functor.map_comp C (homOfLE h₁.out).op (homOfLE h₂.out).op
  rw [← op_comp] at this 
  delta res
  erw [this]
  rfl

@[simp]
theorem res_res (h₁ : Fact (c₂ ≤ c₁)) (h₂ : Fact (c₃ ≤ c₂)) (x : C c₁ i) :
    @res C _ _ i h₂ (@res C _ _ i h₁ x) = @res C _ _ i ⟨h₂.out.trans h₁.out⟩ x := by
  rw [← C.res_comp_res i h₁ h₂]; rfl

/-- `C.d` is the differential `C c i ⟶ C c (i+1)` for a system of complexes `C`. -/
def d (C : SystemOfComplexes) {c : ℝ≥0} (i j : ℕ) : C c i ⟶ C c j :=
  (C.obj <| op c).d i j

theorem d_eq_zero (c : ℝ≥0) (h : i + 1 ≠ j) : (C.d i j : C c i ⟶ C c j) = 0 :=
  (C.obj <| op c).shape _ _ h

theorem d_eq_zero_apply (c : ℝ≥0) (h : i + 1 ≠ j) (x : C c i) : C.d i j x = 0 := by
  rw [d_eq_zero C i j c h]; rfl

@[simp]
theorem d_self_apply (c : ℝ≥0) (x : C c i) : C.d i i x = 0 :=
  d_eq_zero_apply _ _ _ _ i.succ_ne_self _

theorem d_comp_d (c : ℝ≥0) (i j k : ℕ) : C.d i j ≫ (C.d j k : C c j ⟶ _) = 0 :=
  (C.obj <| op c).d_comp_d _ _ _

@[simp]
theorem d_d (c : ℝ≥0) (i j k : ℕ) (x : C c i) : C.d j k (C.d i j x) = 0 :=
  show (C.d i j ≫ C.d j k) x = 0 by rw [d_comp_d]; rfl

theorem d_comp_res (h : Fact (c₂ ≤ c₁)) : C.d i j ≫ @res C _ _ _ h = @res C _ _ _ _ ≫ C.d i j :=
  ((C.map (homOfLE h.out).op).comm _ _).symm

theorem d_res (h : Fact (c₂ ≤ c₁)) (x) : C.d i j (@res C _ _ _ _ x) = @res C _ _ _ h (C.d i j x) :=
  show (@res C _ _ _ _ ≫ C.d i j) x = (C.d i j ≫ @res C _ _ _ h) x by rw [d_comp_res]

section Iso

variable (ϕ : M ≅ N) (c : ℝ≥0)

theorem apply_hom_eq_hom_apply : (ϕ.apply.hom : M c i ⟶ N c i) = ϕ.hom.apply :=
  rfl

theorem apply_inv_eq_inv_apply : (ϕ.apply.inv : N c i ⟶ M c i) = ϕ.inv.apply :=
  rfl

@[simp]
theorem hom_apply_comp_inv_apply : (ϕ.hom.apply : M c i ⟶ N c i) ≫ ϕ.inv.apply = 𝟙 _ := by
  rw [← SystemOfComplexes.apply_hom_eq_hom_apply, ← apply_inv_eq_inv_apply, CategoryTheory.Iso.hom_inv_id]

@[simp]
theorem inv_apply_comp_hom_apply : (ϕ.inv.apply : N c i ⟶ M c i) ≫ ϕ.hom.apply = 𝟙 _ := by
  rw [← SystemOfComplexes.apply_hom_eq_hom_apply, ← apply_inv_eq_inv_apply, CategoryTheory.Iso.inv_hom_id]

@[simp]
theorem inv_apply_hom_apply (x : M c i) : ϕ.inv.apply (ϕ.hom.apply x) = x :=
  show ((ϕ.hom.apply : M c i ⟶ N c i) ≫ ϕ.inv.apply) x = x by
    rw [SystemOfComplexes.hom_apply_comp_inv_apply]
    rfl

@[simp]
theorem hom_apply_inv_apply (x : N c i) : ϕ.hom (ϕ.inv x) = x :=
  show ((ϕ.inv.apply : N c i ⟶ M c i) ≫ ϕ.hom.apply) x = x by
    rw [SystemOfComplexes.inv_apply_comp_hom_apply]
    rfl

end Iso

/-- Convenience definition:
The identity morphism of an object in the system of complexes
when it is given by different indices that are not
definitionally equal. -/
def congr {c c' : ℝ≥0} {i i' : ℕ} (hc : c = c') (hi : i = i') : C c i ⟶ C c' i' :=
  eqToHom <| by subst hc; subst hi; rfl

variable (M M' N)

theorem d_apply (f : M ⟶ N) {c : ℝ≥0} {i j : ℕ} (m : M c i) : N.d i j (f m) = f (M.d i j m) :=
  by
  show (_ ≫ N.d i j) m = (M.d i j ≫ _) m
  congr 1
  exact (f.app (op c)).comm i j

theorem res_comp_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : Fact (c ≤ c')] (i : ℕ) :
    @res M c' c i _ ≫ f.apply = f.apply ≫ res :=
  congr_fun (congr_arg HomologicalComplex.Hom.f (f.naturality (homOfLE h.out).op)) i

theorem res_apply (f : M ⟶ N) (c c' : ℝ≥0) [h : Fact (c ≤ c')] {i : ℕ} (m : M c' i) :
    @res N c' c _ _ (f m) = f (res m) :=
  show (f.apply ≫ @res N c' c _ _) m = (@res M c' c _ _ ≫ f.apply) m by rw [res_comp_apply]

/-- A system of complexes is *admissible*
if all the differentials and restriction maps are norm-nonincreasing.

See Definition 9.3 of [Analytic]. -/
structure Admissible (C : SystemOfComplexes) : Prop where
  d_norm_noninc' : ∀ (c i j) (h : i + 1 = j), (C.d i j : C c i ⟶ C c j).NormNoninc
  res_normNoninc : ∀ c' c i h, (@res C c' c i h).NormNoninc

theorem Admissible.d_normNoninc (hC : C.Admissible) (c : ℝ≥0) (i j : ℕ) :
    (C.d i j : C c i ⟶ _).NormNoninc :=
  by
  by_cases h : i + 1 = j
  · exact hC.d_norm_noninc' c i j h
  · rw [C.d_eq_zero i j c h]; intro v; simp

variable {M M'}

theorem admissibleOfIsometry {f : M ⟶ M'} (hadm : M'.Admissible)
    (hiso : ∀ c i, @Isometry (M c i) (M' c i) _ _ f.apply) : M.Admissible :=
  by
  refine' ⟨fun c i j h x => _, fun c' c i h x => _⟩
  · rw [← (AddMonoidHomClass.isometry_iff_norm _).1 (hiso c i) _, ←
      (AddMonoidHomClass.isometry_iff_norm _).1 (hiso c j) _, ← SystemOfComplexes.hom_apply f, ←
      d_apply]
    exact hadm.d_normNoninc _ _ _ _ _
  · rw [← (AddMonoidHomClass.isometry_iff_norm _).1 (hiso c i) _, ←
      (AddMonoidHomClass.isometry_iff_norm _).1 (hiso c' i) _, ← SystemOfComplexes.hom_apply f, ←
      SystemOfComplexes.hom_apply f, ← res_apply]
    exact hadm.res_normNoninc _ _ _ _ _

variable (M M')

/-- `is_bounded_exact k K m c₀` is a predicate on systems of complexes.

A system of complexes `C` is `(k,K)`-exact in degrees `≤ m` for `c ≥ c₀`*
if the following condition is satisfied:
For all `c ≥ c₀` and all `x : C (k * c) i` with `i ≤ m` there is some `y : C c (i-1)`
(which is defined to be `0` when `i = 0`) such that `∥(C.res x) - (C.d y)∥ ≤ K * ∥C.d x∥`.

See Definition 9.3 of [Analytic] (which coalesces the roles of `k` and `K`).

Implementation details:
* Because we have a differential `d i j : C c i ⟶ C c j` for all `i` and `j`,
  and because `d 0 0 = 0` and `0 - 1 = 0` in Lean's natural numbers,
  we automatically take care of the parenthetical condition about `i = 0`.
* We phrase the condition in a somewhat roundabout way, as
  ```
  ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j)
    (y : C c i₀), ∥res x - C.d _ _ y∥ ≤ K * ∥C.d i j x∥
  ```
  This is a hack around an inconvenience known as dependent type theory hell. -/
def IsBoundedExact (k K : ℝ≥0) (m : ℕ) [hk : Fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
  ∀ (c) (hc : Fact (c₀ ≤ c)) (i) (hi : i ≤ m) (x : C (k * c) i),
    ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : C c i₀),
      ‖res x - C.d _ _ y‖ ≤ K * ‖C.d i j x‖

/-- Weak version of `is_bounded_exact`. -/
def IsWeakBoundedExact (k K : ℝ≥0) (m : ℕ) [hk : Fact (1 ≤ k)] (c₀ : ℝ≥0) : Prop :=
  ∀ (c) (hc : Fact (c₀ ≤ c)) (i) (hi : i ≤ m) (x : C (k * c) i) (ε : ℝ) (hε : 0 < ε),
    ∃ (i₀ j : ℕ) (hi₀ : i₀ = i - 1) (hj : i + 1 = j) (y : C c i₀),
      ‖res x - C.d _ _ y‖ ≤ K * ‖C.d i j x‖ + ε

namespace IsWeakBoundedExact

variable {C C₁ C₂}

variable {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0} [Fact (1 ≤ k)] [Fact (1 ≤ k')]

theorem ofLe (hC : C.IsWeakBoundedExact k K m c₀) (hC_adm : C.Admissible) (hk : Fact (k ≤ k'))
    (hK : Fact (K ≤ K')) (hm : m' ≤ m) (hc₀ : Fact (c₀ ≤ c₀')) :
    C.IsWeakBoundedExact k' K' m' c₀' :=
  by
  intro c hc i hi x ε ε_pos
  haveI : Fact (k ≤ k') := hk
  obtain ⟨i', j, hi', hj, y, hy⟩ := hC c ⟨hc₀.out.trans hc.out⟩ i (hi.trans hm) (res x) ε ε_pos
  use i', j, hi', hj, y
  simp only [res_res] at hy 
  refine' le_trans hy _
  rw [d_res]
  apply add_le_add_right
  exact
    mul_le_mul hK.out (hC_adm.res_normNoninc _ _ _ _ (C.d _ _ x)) (norm_nonneg _)
      ((zero_le K).trans hK.out)

theorem ofIso (h : C₁.IsWeakBoundedExact k K m c₀) (f : C₁ ≅ C₂)
    (hf : ∀ c i, @Isometry (C₁ c i) (C₂ c i) _ _ (f.hom.apply : C₁ c i ⟶ C₂ c i)) :
    C₂.IsWeakBoundedExact k K m c₀ := by
  intro c hc i hi x ε hε
  obtain ⟨i', j, hi', hj, y, hy⟩ := h c hc i hi (f.inv.apply x) ε hε
  refine' ⟨i', j, hi', hj, f.hom y, _⟩
  -- Porting note: the final `calc` step with a tactic-block placeholder was split off
  have h2 : ‖(C₁.d i j (f.inv x))‖ = ‖C₂.d _ _ x‖ :=
    calc
      ‖(C₁.d i j (f.inv x))‖ = ‖(f.inv (C₂.d i j x))‖ := by rw [d_apply]
      _ = ‖(f.hom (f.inv (C₂.d _ _ x)))‖ :=
        (NormedAddGroupHom.norm_eq_of_isometry (hf _ _) _).symm
      _ = ‖C₂.d _ _ x‖ := by rw [hom_apply_inv_apply]
  calc
    ‖(res x - C₂.d _ _ (f.hom y))‖ = ‖(res x - f.hom (C₁.d _ _ y))‖ := by
      rw [d_apply]
    _ = ‖(f.hom (f.inv (res x)) - f.hom (C₁.d _ _ y))‖ := by rw [hom_apply_inv_apply]
    _ = ‖(f.hom (f.inv (res x) - C₁.d _ _ y))‖ := by
      congr <;> exact (SystemOfComplexes.map_sub _ _ _).symm
    _ = ‖(f.inv (res x) - C₁.d _ _ y)‖ := (NormedAddGroupHom.norm_eq_of_isometry (hf _ _) _)
    _ = ‖(res (f.inv x) - C₁.d _ _ y)‖ := by rw [res_apply]
    _ ≤ K * ‖(C₁.d _ _ (f.inv x))‖ + ε := hy
    _ = K * ‖C₂.d _ _ x‖ + ε := by rw [h2]

theorem iff_of_iso (f : C₁ ≅ C₂)
    (hf : ∀ c i, @Isometry (C₁ c i) (C₂ c i) _ _ (f.hom.apply : C₁ c i ⟶ C₂ c i)) :
    C₁.IsWeakBoundedExact k K m c₀ ↔ C₂.IsWeakBoundedExact k K m c₀ :=
  by
  refine' ⟨fun h => h.ofIso f hf, fun h => h.ofIso f.symm _⟩
  -- TODO: factor this out into a lemma
  intro c n
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  rw [← NormedAddGroupHom.norm_eq_of_isometry (hf c n)]
  -- Porting note: `simp only` no longer closes this goal; use the defeq `hom_apply_inv_apply`
  exact congrArg norm (hom_apply_inv_apply n f c v)

end IsWeakBoundedExact

namespace IsBoundedExact

variable {C C₁ C₂}

variable {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0} [Fact (1 ≤ k)] [Fact (1 ≤ k')]

theorem ofLe (hC : C.IsBoundedExact k K m c₀) (hC_adm : C.Admissible) (hk : k ≤ k') (hK : K ≤ K')
    (hm : m' ≤ m) (hc₀ : c₀ ≤ c₀') : C.IsBoundedExact k' K' m' c₀' :=
  by
  intro c hc i hi x
  haveI : Fact (k ≤ k') := ⟨hk⟩
  obtain ⟨i', j, hi', hj, y, hy⟩ := hC c ⟨hc₀.trans hc.out⟩ i (hi.trans hm) (res x)
  use i', j, hi', hj, y
  simp only [res_res] at hy 
  refine' le_trans hy _
  rw [d_res]
  exact
    mul_le_mul hK (hC_adm.res_normNoninc _ _ _ _ (C.d _ _ x)) (norm_nonneg _)
      ((zero_le K).trans hK)

theorem ofIso (h : C₁.IsBoundedExact k K m c₀) (f : C₁ ≅ C₂)
    (hf : ∀ c i, @Isometry (C₁ c i) (C₂ c i) _ _ (f.hom.apply : C₁ c i ⟶ C₂ c i)) :
    C₂.IsBoundedExact k K m c₀ := by
  intro c hc i hi x
  obtain ⟨i', j, hi', hj, y, hy⟩ := h c hc i hi (f.inv.apply x)
  refine' ⟨i', j, hi', hj, f.hom y, _⟩
  -- Porting note: the final `calc` step with a tactic-block placeholder was split off
  have h2 : ‖(C₁.d i j (f.inv x))‖ = ‖C₂.d _ _ x‖ :=
    calc
      ‖(C₁.d i j (f.inv x))‖ = ‖(f.inv (C₂.d i j x))‖ := by rw [d_apply]
      _ = ‖(f.hom (f.inv (C₂.d _ _ x)))‖ :=
        (NormedAddGroupHom.norm_eq_of_isometry (hf _ _) _).symm
      _ = ‖C₂.d _ _ x‖ := by rw [hom_apply_inv_apply]
  calc
    ‖(res x - C₂.d _ _ (f.hom y))‖ = ‖(res x - f.hom (C₁.d _ _ y))‖ := by
      rw [d_apply]
    _ = ‖(f.hom (f.inv (res x)) - f.hom (C₁.d _ _ y))‖ := by rw [hom_apply_inv_apply]
    _ = ‖(f.hom (f.inv (res x) - C₁.d _ _ y))‖ := by
      congr <;> exact (SystemOfComplexes.map_sub _ _ _).symm
    _ = ‖(f.inv (res x) - C₁.d _ _ y)‖ := (NormedAddGroupHom.norm_eq_of_isometry (hf _ _) _)
    _ = ‖(res (f.inv x) - C₁.d _ _ y)‖ := by rw [res_apply]
    _ ≤ K * ‖(C₁.d _ _ (f.inv x))‖ := hy
    _ = K * ‖C₂.d _ _ x‖ := by rw [h2]

end IsBoundedExact

namespace IsWeakBoundedExact

variable {C C₁ C₂}

variable {k k' K K' : ℝ≥0} {m m' : ℕ} {c₀ c₀' : ℝ≥0} [Fact (1 ≤ k)] [Fact (1 ≤ k')]

theorem toExact (hC : C.IsWeakBoundedExact k K m c₀) [∀ c i, SeparatedSpace (C c i)] {δ : ℝ≥0}
    (hδ : 0 < δ)
    (H :
      ∀ c ≥ c₀,
        ∀ i ≤ m,
          ∀ x : C (k * c) i,
            ∀ j,
              i + 1 = j →
                C.d _ j x = 0 → ∃ (i₀ : ℕ) (hi₀ : i₀ = i - 1) (y : C c i₀), res x = C.d _ _ y) :
    C.IsBoundedExact k (K + δ) m c₀ := by
  intro c hc i hi x
  by_cases hdx : C.d _ (i + 1) x = 0
  · rcases H c hc.out i hi x _ rfl hdx with ⟨i₀, hi₀, y, hy⟩
    exact ⟨i₀, _, hi₀, rfl, y, by simp [hy, hdx]⟩
  · obtain ⟨i', j, hi', rfl, y, hy⟩ :=
      hC c hc _ hi x (δ * ‖(C.d _ (i + 1) x)‖)
        (mul_pos (by exact_mod_cast hδ) <| norm_pos_iff'.mpr hdx)
    refine' ⟨i', _, hi', rfl, y, _⟩
    have :
      ((K + δ : ℝ≥0) : ℝ) * ‖(C.d _ (i + 1) x)‖ =
        K * ‖(C.d _ (i + 1) x)‖ + δ * ‖(C.d _ (i + 1) x)‖ := by
      push_cast
      ring
    rwa [this]

end IsWeakBoundedExact

section Quotient

open NormedAddGroupHom

variable {M M'}

/-- The quotient of a system of complexes. -/
def IsQuotient (f : M ⟶ M') : Prop :=
  ∀ c i, (f.apply : M c i ⟶ M' c i).IsQuotient

-- The next three lemmas restate lemmas about normed_add_group_hom.is_quotient in terms of the coercion
-- of `M ⟶ M'` to functions.
theorem IsQuotient.surjective {f : M ⟶ M'} (h : IsQuotient f) {c i} (m' : M' c i) :
    ∃ m : M c i, f m = m' :=
  (h c i).surjective m'

theorem IsQuotient.norm_lift {f : M ⟶ M'} (h : IsQuotient f) {ε : ℝ} (hε : 0 < ε) {c i}
    (n : M' c i) : ∃ m : M c i, f m = n ∧ ‖m‖ < ‖n‖ + ε :=
  (h c i).norm_lift hε n

theorem IsQuotient.norm_le {f : M ⟶ M'} (h : IsQuotient f) {c i} (m : M c i) :
    ‖f m‖ ≤ ‖m‖ :=
  (h c i).norm_le _

/-- The quotient of an admissible system of complexes is admissible. -/
theorem admissibleOfQuotient {f : M ⟶ M'} (hquot : IsQuotient f) (hadm : M.Admissible) :
    M'.Admissible := by
  constructor
  · intro c i j h m'
    refine' le_of_forall_pos_le_add _
    intro ε hε
    obtain ⟨m, hm : f m = m' ∧ ‖m‖ < ‖m'‖ + ε⟩ := hquot.norm_lift hε m'
    rw [← hm.1, d_apply]
    calc
      ‖(f (M.d _ _ m))‖ ≤ ‖M.d _ _ m‖ := hquot.norm_le _
      _ ≤ ‖m‖ := (hadm.d_normNoninc _ _ _ _ m)
      _ ≤ ‖m'‖ + ε := (le_of_lt hm.2)
      _ = ‖f m‖ + ε := by rw [hm.1]
  · intro c' c i hc m'
    letI h := hc
    refine' le_of_forall_pos_le_add _
    intro ε hε
    obtain ⟨m, hm⟩ := hquot.norm_lift hε m'
    rw [← hm.1, res_apply]
    calc
      ‖(f (res m))‖ ≤ ‖res m‖ := hquot.norm_le _
      _ ≤ ‖m‖ := (hadm.res_normNoninc c' c _ hc m)
      _ ≤ ‖m'‖ + ε := (le_of_lt hm.2)
      _ = ‖f m‖ + ε := by rw [hm.1]

end Quotient

-- move me
instance SemiNormedGroup.forget₂Ab : HasForget₂ SemiNormedGroupCat Ab
    where
  forget₂ :=
    { obj := fun V => AddCommGroupCat.of V
      map := fun f => f.toAddMonoidHom }
  forget_comp := rfl

instance SemiNormedGroup.forget₂Ab_additive : (forget₂ SemiNormedGroupCat Ab).Additive where
  map_add := by
    intros
    ext
    rfl

def toAb (C : SystemOfComplexes) : ℝ≥0ᵒᵖ ⥤ CochainComplex Ab ℕ :=
  C ⋙ Functor.mapHomologicalComplex (forget₂ _ _) _

end SystemOfComplexes

-- #lint- only unused_arguments def_lemma doc_blame
