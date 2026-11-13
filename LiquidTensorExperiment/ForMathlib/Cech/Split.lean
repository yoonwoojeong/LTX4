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
import Mathlib.AlgebraicTopology.CechNerve
import LiquidTensorExperiment.ForMathlib.Simplicial.Complex
import LiquidTensorExperiment.ForMathlib.Arrow.Split

#align_import for_mathlib.Cech.split

namespace CategoryTheory

universe v u v' u'

namespace Arrow

noncomputable section

open scoped Simplicial

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (f : Arrow C)

variable [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.hom]

/-- The splittings of the Cech nerve associated to a split arrow. -/
def cechSplitting [Split f] (n : ℕ) : f.cechNerve _[n] ⟶ f.cechNerve _[n + 1] :=
  WidePullback.lift (WidePullback.base _)
    (fun i => if h : i = 0 then WidePullback.base _ ≫ Split.σ else WidePullback.π _ (i.pred h))
    (by
      rintro ⟨j⟩
      split_ifs
      tidy)

theorem cechSplitting_face_zero [Split f] (n : ℕ) : f.cechSplitting n ≫ f.cechNerve.δ 0 = 𝟙 _ :=
  by
  ext j
  dsimp [cech_splitting, simplicial_object.δ]
  simp only [category.id_comp, category.assoc, wide_pullback.lift_π]
  split_ifs
  · exfalso
    exact Fin.succ_ne_zero _ h
  · congr
    dsimp [simplicial_object.δ, SimplexCategory.δ]
    simp
  · dsimp [simplicial_object.δ, cech_splitting]
    simp

theorem face_π (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (f.cechNerve.δ j : f.cechNerve _[n + 1] ⟶ _) ≫ WidePullback.π _ i =
      WidePullback.π _ (j.succAboveEmb i) :=
  by
  change wide_pullback.lift _ _ _ ≫ _ = _
  simpa

theorem cechSplitting_face [Split f] (n : ℕ) (j : Fin (n + 3)) (hj : j ≠ 0) :
    f.cechSplitting (n + 1) ≫ f.cechNerve.δ j = f.cechNerve.δ (j.pred hj) ≫ f.cechSplitting n :=
  by
  ext k
  swap
  · dsimp [cech_splitting, simplicial_object.δ]
    simp
  · dsimp [cech_splitting, simplicial_object.δ]
    simp only [category.assoc, limits.wide_pullback.lift_π]
    split_ifs with h1 h2
    · simp
    · refine' False.elim (h2 _)
      change j.succ_above k = 0 at h1 
      change k = 0
      rwa [← Fin.succAbove_eq_zero_iff hj]
    · refine' False.elim (h1 _)
      erw [h]
      change j.succ_above 0 = 0
      rw [Fin.succAbove_eq_zero_iff hj]
    · simp only [CategoryTheory.Limits.WidePullback.lift_π]
      congr
      change (j.succ_above k).pred h1 = (j.pred hj).succAboveEmb (k.pred h)
      rw [Fin.pred_succAbove_pred]
      rfl

end Arrow

namespace Arrow

section ContractingHomotopy

open CategoryTheory.Limits Opposite

-- Note: Universe restrictions! I hope this doesn't pose any issues later...
-- jmc: seems like it might! I removed them.
variable {P : Type u} {N : Type u'} [Category.{v} P] [Category.{v'} N] (M : Pᵒᵖ ⥤ N)

variable (f : Arrow P)

variable [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.hom]

/-- The augmented Cech conerve induced by applying M to `f.augmented_cech_nerve`. -/
abbrev conerve : CosimplicialObject.Augmented N :=
  ((CosimplicialObject.Augmented.whiskering _ _).obj M).obj f.augmentedCechNerve.rightOp

variable [Arrow.Split f] [Preadditive N]

/-- The morphisms yielding the contracting homotopy. -/
def contractingHomotopy :
    ∀ n : ℕ, (f.conerve M).toCocomplex.pt (n + 1) ⟶ (f.conerve M).toCocomplex.pt n
  | 0 => M.map (WidePullback.lift (𝟙 _) (fun i => (Split.σ : f.right ⟶ _)) (by simp)).op
  | n + 1 => M.map (f.cechSplitting n).op

open CosimplicialObject.Augmented

open scoped BigOperators

theorem is_contractingHomotopy_zero :
    (f.conerve M).toCocomplex.d 0 1 ≫ f.contractingHomotopy M 0 = 𝟙 _ :=
  by
  dsimp
  rw [if_pos]
  swap; · simp
  delta conerve
  dsimp [to_cocomplex_d, to_cocomplex_obj, contracting_homotopy]
  simp only [category.id_comp, category.comp_id]
  simp_rw [← M.map_comp, ← op_comp, ← M.map_id, ← op_id]
  congr 2
  simp

theorem is_contractingHomotopy_one :
    (f.conerve M).toCocomplex.d 1 2 ≫ f.contractingHomotopy M 1 +
        f.contractingHomotopy M 0 ≫ (f.conerve M).toCocomplex.d 0 1 =
      𝟙 _ :=
  by
  rw [← add_zero (𝟙 ((conerve M f).toCocomplex.pt 1))]
  dsimp only [to_cocomplex, CochainComplex.of]
  rw [dif_pos]
  swap; · decide
  rw [dif_pos]
  swap; · decide
  dsimp
  delta conerve
  dsimp only [to_cocomplex_d, cosimplicial_object.coboundary, whiskering, whiskering_obj, drop,
    to_cocomplex_obj, comma.snd, cosimplicial_object.whiskering, whiskering_right,
    contracting_homotopy]
  simp_rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.sum_univ_zero, Fin.val_one, one_zsmul, preadditive.add_comp, pow_one,
    Fin.succ_zero_eq_one', category.id_comp, neg_smul, category.comp_id, preadditive.neg_comp,
    pow_zero]
  rw [add_assoc]
  congr 1
  · dsimp [cosimplicial_object.δ]
    simp_rw [← M.map_comp, ← M.map_id, ← op_id, ← op_comp]
    congr 2
    dsimp [cech_splitting]
    ext j
    · simp only [wide_pullback.lift_π, category.id_comp, category.assoc]
      split_ifs
      · cases j
        injection h with hh
        simp only [Nat.succ_ne_zero] at hh 
        cases hh
      · congr; have hj : j = 0 := Subsingleton.elim j 0; subst j
        dsimp only [SimplexCategory.δ]
        simp only [SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
          OrderEmbedding.toOrderHom_coe, Fin.zero_succAbove, Fin.succ_zero_eq_one',
          Fin.one_eq_zero_iff, Nat.one_ne_zero]
        rfl
    · simp only [wide_pullback.lift_base, category.assoc, category.id_comp]
  · dsimp [cosimplicial_object.δ]
    rw [add_assoc, neg_add_eq_zero, ← M.map_comp]
    simp only [zero_comp, category.id_comp, zero_add, functor.map_comp, ← M.map_comp, ← op_comp]
    congr 2
    dsimp [cech_splitting]
    ext j
    · simp only [wide_pullback.lift_π, category.assoc]
      split_ifs
      · rfl
      · refine' False.elim (h _)
        change (1 : Fin 2).succAboveEmb j = 0
        rw [Fin.succAbove_eq_zero_iff]
        · simp
        · exact top_ne_bot
    · simp only [wide_pullback.lift_base, category.assoc, category.comp_id]

theorem is_contractingHomotopy (n : ℕ) :
    (f.conerve M).toCocomplex.d (n + 2) (n + 3) ≫ f.contractingHomotopy M (n + 2) +
        f.contractingHomotopy M (n + 1) ≫ (f.conerve M).toCocomplex.d (n + 1) (n + 2) =
      𝟙 _ :=
  by
  dsimp
  erw [if_pos]
  swap; rfl
  dsimp only [to_cocomplex_d]
  rw [if_pos]
  swap; rfl
  dsimp only [cosimplicial_object.coboundary]
  simp only [preadditive.sum_comp, preadditive.comp_sum]
  erw [Fin.sum_univ_succ, add_assoc, ← Finset.sum_add_distrib]
  rw [← add_zero (𝟙 ((conerve M f).toCocomplexObj (n + 2)))]
  dsimp only [cosimplicial_object.δ]
  congr 1
  · delta conerve
    dsimp [to_cocomplex_obj, contracting_homotopy]
    simp only [CategoryTheory.Category.comp_id, one_zsmul, pow_zero]
    simp_rw [← M.map_id, ← M.map_comp, ← op_comp, ← op_id]
    congr 2
    apply cech_splitting_face_zero
  · apply Fintype.sum_eq_zero
    intro i
    simp only [category.comp_id, add_zero, functor.comp_map, Fin.val_succ, preadditive.comp_zsmul,
      preadditive.zsmul_comp]
    suffices
      (drop.obj (conerve M f)).map (SimplexCategory.δ i.succ) ≫ contracting_homotopy M f (n + 2) =
        contracting_homotopy M f (n + 1) ≫ (drop.obj (conerve M f)).map (SimplexCategory.δ i)
      by
      rw [this, pow_succ]
      simp
    delta conerve
    dsimp [contracting_homotopy]
    simp_rw [← M.map_comp, ← op_comp]
    congr 2
    convert cech_splitting_face _ _ _ (Fin.succ_ne_zero _)
    funext
    congr
    simp

end ContractingHomotopy

section CovariantContractingHomotopy

open CategoryTheory.Limits Opposite

variable {P : Type u} {N : Type u'} [Category.{v} P] [Category.{v'} N] (M : P ⥤ N)

variable (f : Arrow P)

variable [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.hom]

/-- The augmented Cech nerve induced by applying M to `f.augmented_cech_nerve`. -/
abbrev nerve : SimplicialObject.Augmented N :=
  ((SimplicialObject.Augmented.whiskering _ _).obj M).obj f.augmentedCechNerve

variable [Arrow.Split f] [Preadditive N]

open SimplicialObject.Augmented

open scoped BigOperators

def covariantContractingHomotopy :
    ∀ n : ℕ, (f.nerve M).toComplex.pt n ⟶ (f.nerve M).toComplex.pt (n + 1)
  | 0 => M.map <| WidePullback.lift (𝟙 _) (fun i => (Split.σ : f.right ⟶ _)) (by simpa)
  | n + 1 => M.map <| f.cechSplitting n

theorem covariant_is_contracting_homotopy_zero :
    f.covariantContractingHomotopy M 0 ≫ (f.nerve M).toComplex.d 1 0 = 𝟙 _ :=
  by
  dsimp
  rw [if_pos]
  swap; · simp
  delta nerve
  dsimp [to_complex_obj, to_complex_d, covariant_contracting_homotopy]
  simp only [category.id_comp, category.comp_id]
  simp_rw [← M.map_comp, ← M.map_id]
  congr 2
  simp

theorem covariant_is_contracting_homotopy_one :
    f.covariantContractingHomotopy M 1 ≫ (f.nerve M).toComplex.d 2 1 +
        (f.nerve M).toComplex.d 1 0 ≫ f.covariantContractingHomotopy M 0 =
      𝟙 _ :=
  by
  dsimp [covariant_contracting_homotopy]
  rw [if_pos]; rw [if_pos]; any_goals decide
  dsimp [to_complex_d, simplicial_object.boundary, simplicial_object.δ]
  delta nerve
  dsimp [to_complex_obj]
  simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_zsmul, Fintype.univ_ofSubsingleton,
    Nat.add_def, Fin.mk_zero, Fin.val_succ, pow_one, neg_smul, Finset.sum_singleton,
    preadditive.comp_add, category.id_comp, preadditive.comp_neg, category.comp_id]
  simp only [← M.map_comp]
  rw [add_assoc]
  convert add_zero _
  swap
  · symm
    convert M.map_id _
    dsimp [arrow.cech_splitting]
    ext ⟨j, hj⟩; simp
    rw [dif_neg]; rfl
    dsimp [SimplexCategory.δ]
    have : j = 0 := by simpa using hj; subst this; decide
    simp
  · rw [neg_add_eq_zero]
    congr 1
    dsimp [cech_splitting]
    ext ⟨j, hj⟩
    · simp only [category.assoc, wide_pullback.lift_π]; dsimp [SimplexCategory.δ]
      rw [dif_pos]; have : j = 0 := by simpa using hj; subst this
      dsimp [SimplexCategory.δ]; decide
    · simp

theorem covariant_is_contracting_homotopy (n : ℕ) :
    f.covariantContractingHomotopy M (n + 2) ≫ (f.nerve M).toComplex.d (n + 3) (n + 2) +
        (f.nerve M).toComplex.d (n + 2) (n + 1) ≫ f.covariantContractingHomotopy M (n + 1) =
      𝟙 _ :=
  by
  dsimp; rw [if_pos]; rw [if_pos]; swap; · rfl; swap; · rfl
  simp only [category.comp_id, category.id_comp]
  dsimp only [to_complex_d, simplicial_object.boundary]
  simp only [preadditive.sum_comp, preadditive.comp_sum]
  rw [Fin.sum_univ_succ, add_assoc, ← Finset.sum_add_distrib]
  convert add_zero _
  · apply Fintype.sum_eq_zero; intro j
    have : ((j.succ : Fin _) : ℕ) = (j : ℕ) + 1 := by simp; rw [this]; clear this
    rw [pow_succ]
    simp only [neg_mul, one_mul, neg_smul, preadditive.comp_neg]
    rw [neg_add_eq_zero]
    simp only [preadditive.comp_zsmul, preadditive.zsmul_comp]
    congr 1
    dsimp [covariant_contracting_homotopy, simplicial_object.δ]
    delta nerve
    dsimp [whiskering]
    simp only [← M.map_comp]
    congr 1
    convert cech_splitting_face _ _ _ (Fin.succ_ne_zero _); funext i
    congr; simp
  · dsimp [covariant_contracting_homotopy]
    simp only [pow_zero, one_zsmul]
    delta nerve
    dsimp [arrow.cech_splitting, simplicial_object.whiskering, simplicial_object.δ]
    rw [← M.map_comp]; symm
    convert M.map_id _
    ext ⟨j, hj⟩
    simp only [category.assoc, wide_pullback.lift_π]
    rw [dif_neg]; dsimp; simpa; dsimp [SimplexCategory.δ]
    intro c; apply_fun fun e => e.1 at c ; simpa using c
    simp; dsimp; simp

end CovariantContractingHomotopy

end Arrow

end CategoryTheory

