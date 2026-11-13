import Mathlib.Algebra.Homology.Functor
import LiquidTensorExperiment.ForMathlib.Simplicial.Complex
import LiquidTensorExperiment.PolyhedralLattice.Cosimplicial
import LiquidTensorExperiment.PolyhedralLattice.Hom
import LiquidTensorExperiment.PseudoNormedGroup.SystemOfComplexes
import LiquidTensorExperiment.SystemOfComplexes.Rescale
import LiquidTensorExperiment.NormedSpectral
import LiquidTensorExperiment.Thm95.ModifyComplex
import LiquidTensorExperiment.Thm95.PolyhedralIso

#align_import thm95.double_complex

/-!
# The double complex that is the protagonist in the proof of Theorem 9.5
-/


noncomputable section

open scoped NNReal BigOperators

open CategoryTheory Opposite SimplexCategory

universe u v

namespace Thm95

variable (BD : BreenDeligne.Data) (κ : ℕ → ℝ≥0) [BD.Suitable κ]

variable (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' ≤ 1)]

variable (V : SemiNormedGroupCat.{v}) [NormedWithAut r V]

variable (Λ : PolyhedralLatticeCat.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (N : ℕ) [Fact (0 < N)]

section

open PolyhedralLatticeCat

def cechNerve : CosimplicialObject.Augmented (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ :=
  (CosimplicialObject.Augmented.whiskeringObj _ _ (hom.{u, u} M).rightOp).obj
    (augmentedCosimplicial.{u} Λ N)

def cechAugmentationMap : ((cechNerve r' Λ M N).right.obj (mk 0)).unop ⟶ (hom M).obj (op Λ) :=
  (hom M).map (cosimplicialAugmentationMap Λ N).op

theorem cechNerve_hom_zero :
    (cechNerve.{u} r' Λ M N).Hom.app (mk 0) = (cechAugmentationMap.{u} r' Λ M N).op :=
  by
  dsimp only [Cech_nerve, Cech_augmentation_map, cosimplicial_object.augmented.whiskering_obj]
  simp only [whisker_right_app, category.id_comp, functor.right_op_map, nat_trans.comp_app,
    functor.const_comp_inv_app]
  congr 2
  dsimp only [augmented_cosimplicial, augmented_Cech_conerve]
  rw [cosimplicial_object.augment_hom_zero]
  rfl

theorem PolyhedralLatticeCat.cechAugmentationMap_eq_homSum :
    (Λ.homCosimplicialZeroIso N r' M (↑N) rfl).inv ≫ Thm95.cechAugmentationMap r' Λ M N =
      homSum Λ N r' M :=
  by
  dsimp only [Thm95.cechAugmentationMap, Hom_cosimplicial_zero_iso,
    Hom_cosimplicial_zero_iso_aux_rfl, Hom_cosimplicial_zero_iso']
  rw [iso.refl_trans, iso.refl_trans]
  dsimp only [iso.trans_inv, functor.map_iso_hom, functor.map_iso_inv, iso.symm_inv, op_comp]
  simp only [category.assoc, ← (Hom M).map_comp, augmentation_eq_diagonal, iso.op_hom, ← op_comp]
  dsimp only [Hom_rescale_iso, Hom_finsupp_iso]
  ext f l : 2
  exact finsupp_sum_diagonal_embedding Λ N r' M f l

def cosimplicialSystemOfComplexes : CosimplicialObject.Augmented SystemOfComplexes :=
  (CosimplicialObject.Augmented.whiskeringObj.{u} _ _ (BD.system κ r V r')).obj (cechNerve r' Λ M N)

theorem cosimplicialSystemOfComplexes_hom_zero :
    (cosimplicialSystemOfComplexes BD κ r r' V Λ M N).Hom.app (mk 0) =
      (BD.system κ r V r').map (cechAugmentationMap.{u} r' Λ M N).op :=
  by
  ext : 2; dsimp [cosimplicial_system_of_complexes]
  rw [category.id_comp, Cech_nerve_hom_zero]

@[simps pt d]
def doubleComplexAux : CochainComplex SystemOfComplexes ℕ :=
  (cosimplicialSystemOfComplexes BD κ r r' V Λ M N).toCocomplex

@[simps obj map]
def doubleComplex' : SystemOfDoubleComplexes :=
  (doubleComplexAux BD κ r r' V Λ M N).asFunctor

end

section

open PolyhedralLattice

open PolyhedralLatticeCat (of cosimplicial)

open scoped Nat

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
-- we now have a `cochain_complex` of `system_of_complexes`
-- so we need to reorganize the data, to get a `system_of_double_complexes`
-- this is what `.as_functor` does, in the definition `double_complex` below
-- but before we do this, we need to rescale the norms in all the rows,
-- so that the vertical differentials become norm-nonincreasing
set_option pp.universes true

@[simps pt d]
def doubleComplexAuxRescaled : CochainComplex SystemOfComplexes ℕ :=
  @HomologicalComplex.modify _ _ _ _ _ _ _ _ (doubleComplexAux BD κ r r' V Λ M N)
    SystemOfComplexes.rescaleFunctor SystemOfComplexes.rescaleNatTrans
    SystemOfComplexes.rescaleFunctor.additive

@[simps obj map]
def doubleComplex : SystemOfDoubleComplexes :=
  (doubleComplexAuxRescaled BD κ r r' V Λ M N).asFunctor

theorem doubleComplex.row_zero :
    (doubleComplex BD κ r r' V Λ M N).row 0 = (BD.system κ r V r').obj (op <| hom Λ M) :=
  rfl

theorem doubleComplex.row_one :
    (doubleComplex BD κ r r' V Λ M N).row 1 =
      (BD.system κ r V r').obj (op <| hom ((cosimplicial Λ N).obj (mk 0)) M) :=
  rfl

theorem doubleComplex.rowMap_zero_one :
    (doubleComplex BD κ r r' V Λ M N).rowMap 0 1 =
      (BD.system κ r V r').map (cechAugmentationMap r' Λ M N).op :=
  by
  ext c i : 4
  dsimp only [SystemOfDoubleComplexes.rowMap_app_f, SystemOfDoubleComplexes.d, double_complex,
    HomologicalComplex.asFunctor_obj, double_complex_aux_rescaled, HomologicalComplex.modify,
    SystemOfComplexes.rescaleNatTrans, nat_trans.id_app, SystemOfComplexes.rescaleFunctor,
    functor.id_map, double_complex_aux, op_unop]
  erw [category.comp_id, ← Cech_nerve_hom_zero]
  simp only [dite_eq_ite, BreenDeligne.Data.system_map, if_true, eq_self_iff_true,
    cosimplicial_object.augmented.to_cocomplex_d_2, eq_to_hom_refl, category.comp_id]
  dsimp only [cosimplicial_object.augmented.to_cocomplex_d, cosimplicial_system_of_complexes,
    cosimplicial_object.augmented.whiskering_obj]
  simp only [BreenDeligne.Data.system_map, whisker_right_app, category.id_comp, nat_trans.comp_app,
    functor.const_comp_inv_app]
  rfl

theorem doubleComplex.row (m : ℕ) :
    (doubleComplex BD κ r r' V Λ M N).row (m + 2) =
      (SystemOfComplexes.rescaleFunctor (m + 2)).obj
        ((BD.system κ r V r').obj (op <| hom ((cosimplicial Λ N).obj (mk (m + 1))) M)) :=
  rfl

end

end Thm95

namespace Thm95

variable (BD : BreenDeligne.Data)

variable (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' ≤ 1)]

variable (V : SemiNormedGroupCat.{v}) [NormedWithAut r V]

variable (κ : ℕ → ℝ≥0) [BD.VerySuitable r r' κ]

variable (Λ : PolyhedralLatticeCat.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (N : ℕ) [Fact (0 < N)]

variable {r r' V κ Λ M N}

theorem doubleComplex.rowAdmissible : ∀ m, ((doubleComplex BD κ r r' V Λ M N).row m).Admissible
  | 0 => BD.systemAdmissible
  | 1 => BD.systemAdmissible
  | m + 2 => SystemOfComplexes.rescaleAdmissible _ _ BD.systemAdmissible

theorem doubleComplex.d_one_normNoninc (c : ℝ≥0) (q : ℕ) :
    (@SystemOfDoubleComplexes.d (doubleComplex BD κ r r' V Λ M N) c 1 2 q).NormNoninc :=
  by
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
  refine' NormedAddGroupHom.norm_comp_le_of_le' 2 _ 1 _ (SemiNormedGroupCat.norm_toRescale_le _ _) _
  · norm_num
  have : (2 : ℝ) = ∑ i : Fin 2, 1 := by
    simp only [Finset.card_fin, mul_one, Nat.cast_bit0, Finset.sum_const, nsmul_eq_mul,
      Nat.cast_one]
  dsimp [SystemOfComplexes.rescaleFunctor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d]
  erw [category.comp_id, if_pos rfl]
  dsimp [cosimplicial_object.coboundary]
  simp only [← nat_trans.app_hom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul, ←
    HomologicalComplex.Hom.fAddMonoidHom_apply, this]
  apply norm_sum_le_of_le
  rintro i -
  refine' le_trans (norm_zsmul_le _ _) _
  rw [← Int.norm_cast_real, Int.cast_pow, norm_pow, Int.cast_neg, Int.cast_one, norm_neg, norm_one,
    one_pow, one_mul]
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
  apply BreenDeligne.Data.complex.map_normNoninc

theorem doubleComplex.d_two_normNoninc (c : ℝ≥0) (p q : ℕ) :
    (@SystemOfDoubleComplexes.d (doubleComplex BD κ r r' V Λ M N) c (p + 2) (p + 3) q).NormNoninc :=
  by
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
  refine'
    NormedAddGroupHom.norm_comp_le_of_le' (p + 3 : ℕ) _ 1 _ (SemiNormedGroupCat.norm_scale_le _ _ _)
      _
  · simp only [add_zero, Nat.add_def, ← Nat.cast_succ]
    norm_cast
    rw [mul_comm, ← mul_div_assoc, eq_comm, ← Nat.cast_mul, Nat.factorial_succ]; apply div_self
    norm_num [Nat.factorial_ne_zero]
  apply SemiNormedGroupCat.norm_rescale_map_le
  have : ((p + 3 : ℕ) : ℝ) = ∑ i : Fin (p + 3), 1 := by
    simp only [Finset.card_fin, mul_one, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.cast_bit1,
      Nat.cast_add, Nat.cast_one]
  dsimp [SystemOfComplexes.rescaleFunctor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d]
  erw [category.comp_id, if_pos rfl]
  dsimp [cosimplicial_object.coboundary]
  simp only [← nat_trans.app_hom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul, ←
    HomologicalComplex.Hom.fAddMonoidHom_apply, this]
  apply norm_sum_le_of_le
  rintro i -
  refine' le_trans (norm_zsmul_le _ _) _
  rw [← Int.norm_cast_real, Int.cast_pow, norm_pow, Int.cast_neg, Int.cast_one, norm_neg, norm_one,
    one_pow, one_mul]
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
  apply BreenDeligne.Data.complex.map_normNoninc

theorem doubleComplex.d_normNoninc (c : ℝ≥0) (q : ℕ) :
    ∀ p, (@SystemOfDoubleComplexes.d (doubleComplex BD κ r r' V Λ M N) c p (p + 1) q).NormNoninc
  | 0 => BreenDeligne.Data.complex.map_normNoninc _ _ _ _ _ _ _ _
  | 1 => doubleComplex.d_one_normNoninc _ _ _
  | p + 2 => doubleComplex.d_two_normNoninc _ _ _ _

-- see above: currently we can only prove this for the columns
theorem doubleComplexAdmissible : (doubleComplex BD κ r r' V Λ M N).Admissible :=
  SystemOfDoubleComplexes.Admissible.mk' (doubleComplex.rowAdmissible _)
    (by rintro _ _ _ _ rfl; apply double_complex.d_norm_noninc)

end Thm95

