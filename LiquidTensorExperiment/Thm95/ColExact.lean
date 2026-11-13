import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import LiquidTensorExperiment.ForMathlib.Cech.Adjunction
import LiquidTensorExperiment.ForMathlib.Simplicial.Iso
import LiquidTensorExperiment.PolyhedralLattice.CosimplicialExtra
import LiquidTensorExperiment.Prop92.Prop92
import LiquidTensorExperiment.NormedSnakeDual
import LiquidTensorExperiment.Thm95.DoubleComplex
import LiquidTensorExperiment.Thm95.ColExactPrep
import LiquidTensorExperiment.Thm95.PfpngIso

#align_import thm95.col_exact

noncomputable section

open scoped NNReal BigOperators Nat

open CategoryTheory Opposite SimplexCategory

attribute [local instance] typePow

universe u v u₀ uₘ

-- set_option pp.universes true
namespace Thm95

variable (BD : BreenDeligne.Data) (κ : ℕ → ℝ≥0) [BD.Suitable κ]

variable (r r' : ℝ≥0)

variable (V : SemiNormedGroupCat.{v})

variable (Λ : PolyhedralLatticeCat.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (N : ℕ) [Fact (0 < N)] (n : ℕ)

@[simps obj map]
def scaleFactorial : SystemOfComplexes.{u} ⥤ SystemOfComplexes.{u} :=
  (whiskeringRight _ _ _).obj <|
    HomologicalComplex.modifyFunctor (fun m => SemiNormedGroupCat.rescale m !) fun m₁ m₂ =>
      SemiNormedGroupCat.scale _ _

namespace ScaleFactorial

open SystemOfComplexes SemiNormedGroupCat HomologicalComplex

theorem isWeakBoundedExact {C : SystemOfComplexes} {k K : ℝ≥0} [Fact (1 ≤ k)] {m : ℕ} {c₀ : ℝ≥0}
    (hC : C.IsWeakBoundedExact k K m c₀) :
    (scaleFactorial.obj C).IsWeakBoundedExact k (K * (m + 1)) m c₀ :=
  by
  intro c hc i hi x ε hε
  let δ := ε * i !
  have hδ : 0 < δ := mul_pos hε (Nat.cast_pos.2 (Nat.factorial_pos i))
  have hifact : ¬(↑i ! : ℝ) = 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have him : 1 ≤ (↑m + 1) * ((↑i : ℝ) + 1)⁻¹ :=
    by
    refine'
      le_trans _
        (mul_le_mul_of_nonneg_right
          (show (↑i : ℝ) + 1 ≤ ↑m + 1 by rwa [add_le_add_iff_right, Nat.cast_le])
          (inv_nonneg.2 (add_nonneg (@Nat.cast_nonneg ℝ _ i) zero_le_one)))
    rw [mul_inv_cancel
        (ne_of_lt (add_pos_of_nonneg_of_pos (@Nat.cast_nonneg ℝ _ i) zero_lt_one)).symm]
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc i hi ((of_rescale i !).app _ x) δ hδ
  refine' ⟨_, _, rfl, rfl, (SemiNormedGroupCat.toRescale (i - 1)!).app _ y, _⟩
  erw [Rescale.norm_def, Rescale.norm_def]
  simp only [NNReal.coe_nat_cast, NNReal.coe_add, Nat.cast_succ, Nat.factorial_succ, Nat.cast_mul,
    NNReal.coe_one, NNReal.coe_mul, div_eq_mul_inv]
  rw [mul_inv_le_iff]; swap; · exact_mod_cast Nat.factorial_pos i
  refine' hy.trans _
  rw [left_distrib, mul_inv, ← mul_assoc ↑i !, mul_comm ↑i !, mul_assoc _ ↑i !, mul_comm ↑i !,
    mul_assoc _ _ ↑i !, inv_mul_cancel_right₀ hifact, mul_comm _ ε, add_le_add_iff_right,
    mul_assoc ↑K]
  refine' mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  rw [mul_comm _ ((↑i : ℝ) + 1)⁻¹, ← mul_assoc]
  refine'
    le_trans (le_mul_of_one_le_left (by simp only [one_mul, norm_nonneg]) him)
      (mul_le_mul_of_nonneg_left _
        (mul_nonneg (add_nonneg (Nat.cast_nonneg m) zero_le_one)
          (inv_nonneg.2 (add_nonneg (Nat.cast_nonneg i) zero_le_one))))
  simpa using le_refl _

end ScaleFactorial

section

open PolyhedralLatticeCat

def cLCFP' : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ ℝ≥0ᵒᵖ ⥤ SemiNormedGroupCat :=
  (ProFiltPseuNormGrpWithTinv.pow r' n ⋙ (filtration r').flip).op ⋙
    Functor.opHom _ _ ⋙ (whiskeringRight ℝ≥0ᵒᵖ Profiniteᵒᵖ _).obj (cLC V)

theorem cLCFP'_map_app {M₁ M₂ : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (f : M₁ ⟶ M₂) (c : ℝ≥0ᵒᵖ) :
    ((cLCFP' r' V n).map f).app c = (cLCFP V r' c.unop n).map f :=
  rfl

theorem cLCFP'_obj_map (M₁ : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
    ((cLCFP' r' V n).obj M₁).map h =
      haveI : Fact (c₂.unop ≤ c₁.unop) := ⟨le_of_hom h.unop⟩
      (cLCFP.res V r' c₁.unop c₂.unop n).app M₁ :=
  rfl

theorem FLC_arrow_hom' {M₁ M₂ : ProFiltPseuNormGrpWithTinv r'} (f : M₁ ⟶ M₂) (c : ℝ≥0) :
    (fLCComplexArrow f.toComphausFilteredPseudoNormedGroupHom f.Strict c).Hom =
      ((filtration r').obj c).map f :=
  rfl

section

variable [Fact (0 < r')] [Fact (r' ≤ 1)]

def cechNerve' : CosimplicialObject.Augmented (ℝ≥0ᵒᵖ ⥤ SemiNormedGroupCat) :=
  (CosimplicialObject.Augmented.whiskeringObj.{u} _ _ (cLCFP' r' V n)).obj (cechNerve r' Λ M N)

theorem cechNerve'_hom_zero :
    (cechNerve'.{u} r' V Λ M N n).Hom.app (mk 0) =
      (cLCFP' r' V n).map (cechAugmentationMap.{u} r' Λ M N).op :=
  by
  dsimp only [Cech_nerve', cosimplicial_object.augmented.whiskering_obj]
  simp only [whisker_right_app, category.id_comp, functor.right_op_map, nat_trans.comp_app,
    functor.const_comp_inv_app, Cech_nerve_hom_zero]

@[simps obj map]
def cechNerveLevel : ℝ≥0 ⥤ SimplicialObject.Augmented Profinite.{u} :=
  (ProFiltPseuNormGrpWithTinv.pow r' n ⋙ (filtration r').flip).flip ⋙
    (SimplicialObject.Augmented.whiskering _ _).flip.obj (cechNerve.{u} r' Λ M N).leftOp

theorem cechNerveLevel_left_map (c : ℝ≥0) (i j : SimplexCategoryᵒᵖ) (g : i ⟶ j) :
    ((cechNerveLevel r' Λ M N n).obj c).left.map g =
      ((filtration r').obj c).map
        ((ProFiltPseuNormGrpWithTinv.pow r' n).map
          ((hom M).map ((cechConerve (Λ.diagonalEmbedding N)).map g.unop).op)) :=
  rfl

theorem cechNerveLevel_left_map' (c : ℝ≥0) (i j : SimplexCategoryᵒᵖ) (g : i ⟶ j)
    (x : ((cechNerveLevel r' Λ M N n).obj c).left.obj i) (k : Fin n) :
    (((cechNerveLevel r' Λ M N n).obj c).left.map g x).1 k =
      AddMonoidHom.comp (x.1 k)
        (PolyhedralLattice.Conerve.map (Λ.diagonalEmbedding N)
            ⇑(Hom.toOrderHom g.unop)).toAddMonoidHom :=
  rfl

theorem cechNerveLevel_hom_app (c : ℝ≥0) :
    ((cechNerveLevel r' Λ M N n).obj c).Hom.app (op (mk 0)) =
      ((filtration r').obj c).map
        ((ProFiltPseuNormGrpWithTinv.pow r' n).map (cechAugmentationMap r' Λ M N)) :=
  by
  dsimp only [Cech_nerve_level_obj, nat_trans.comp_app, whisker_right_app,
    functor.const_comp_hom_app]
  erw [category.comp_id]
  dsimp only [nat_trans.left_op_app, unop_op]
  rw [Cech_nerve_hom_zero]
  dsimp only [functor.flip_obj_map, functor.comp_map, Quiver.Hom.unop_op, functor.flip_map_app]
  rfl

@[simps pt d]
def colComplexAux : CochainComplex (ℝ≥0ᵒᵖ ⥤ SemiNormedGroupCat) ℕ :=
  (cechNerve' r' V Λ M N n).toCocomplex

@[simps obj obj_d map]
def colComplexLevel : SystemOfComplexes :=
  ((whiskeringRight _ _ _).obj <| fLCFunctor' V).obj (cechNerveLevel r' Λ M N n).op

@[simps obj obj_d map]
def colComplex : SystemOfComplexes :=
  (colComplexAux r' V Λ M N n).asFunctor

def colComplexLevelIsoObjX (c : ℝ≥0ᵒᵖ) :
    ∀ i : ℕ, ((colComplexLevel r' V Λ M N n).obj c).pt i ≅ ((colComplex r' V Λ M N n).obj c).pt i
  | 0 => Iso.refl _
  | i + 1 => Iso.refl _

theorem colComplexLevel_iso_obj_comm (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    (colComplexLevelIsoObjX r' V Λ M N n c i).Hom ≫ ((colComplex r' V Λ M N n).obj c).d i (i + 1) =
      ((colComplexLevel r' V Λ M N n).obj c).d i (i + 1) ≫
        (colComplexLevelIsoObjX r' V Λ M N n c (i + 1)).Hom :=
  by
  cases i
  all_goals
    dsimp only [col_complex_level_iso_obj_X]
    simp only [iso.refl_hom, category.id_comp, category.comp_id]
    dsimp only [col_complex_obj_d, col_complex_level_obj_d, cosimplicial_object.augmented.cocomplex,
      cosimplicial_object.augmented.to_cocomplex_d_2, cosimplicial_object.augmented.to_cocomplex_d,
      functor.const_comp_hom_app, functor.const_comp_inv_app, nat_trans.comp_app, whisker_right_app,
      nat_trans.right_op_app, nat_trans.left_op_app, cosimplicial_object.augmented.drop_obj,
      cosimplicial_object.coboundary, cosimplicial_object.δ,
      cosimplicial_object.whiskering_obj_obj_map]
    rw [dif_pos rfl, eq_to_hom_refl, category.comp_id, dif_pos rfl, eq_to_hom_refl,
      category.comp_id]
  · erw [Cech_nerve'_hom_zero, SemiNormedGroupCat.lCC_obj_map', category.id_comp]
    dsimp only [unop_op]
    erw [Cech_nerve_hom_zero, op_id, category.id_comp]
    rfl
  · simp only [nat_trans.app_sum, nat_trans.app_zsmul]
    apply Fintype.sum_congr; intro j; congr 1
    rw [SemiNormedGroupCat.lCC_obj_map']
    rfl

def colComplexLevelIsoObj (c : ℝ≥0ᵒᵖ) :
    (colComplexLevel r' V Λ M N n).obj c ≅ (colComplex r' V Λ M N n).obj c :=
  HomologicalComplex.Hom.isoOfComponents (colComplexLevelIsoObjX r' V Λ M N n c)
    (by rintro i j (rfl : i + 1 = j); apply col_complex_level_iso_obj_comm)

theorem colComplexLevel_iso_comm (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
    ((colComplexLevel r' V Λ M N n).map h ≫ (colComplexLevelIsoObj r' V Λ M N n c₂).Hom).f i =
      ((colComplexLevelIsoObj r' V Λ M N n c₁).Hom ≫ (colComplex r' V Λ M N n).map h).f i :=
  by
  cases i
  all_goals
    dsimp only [col_complex_level_iso_obj, col_complex_level_iso_obj_X, HomologicalComplex.comp_f,
      HomologicalComplex.Hom.isoOfComponents_hom_f, iso.refl_hom]
    rw [category.id_comp, category.comp_id]
    dsimp only [col_complex_level_map, col_complex_map, whisker_right_app,
      cosimplicial_object.augmented.cocomplex, cosimplicial_object.augmented.point_map,
      cosimplicial_object.augmented.drop_map]
    rw [SemiNormedGroupCat.lCC_obj_map']; rfl

def colComplexLevelIso : colComplexLevel r' V Λ M N n ≅ colComplex r' V Λ M N n :=
  NatIso.ofComponents (colComplexLevelIsoObj r' V Λ M N n)
    (by intro c₁ c₂ h; ext i : 2; apply col_complex_level_iso_comm)

theorem colComplexLevelIso_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Isometry (((colComplexLevelIso r' V Λ M N n).Hom.app c).f i) := by cases i <;> exact isometry_id

def augMap :=
  ((ProFiltPseuNormGrpWithTinv.pow r' n).map
      (cechAugmentationMap r' Λ M N)).toComphausFilteredPseudoNormedGroupHom

section

open ComphausFilteredPseudoNormedGroupWithTinvHom

theorem augMapStrict : (augMap r' Λ M N n).Strict :=
  toProfinitelyFilteredPseudoNormedGroupHomStrict _

end

section

open CategoryTheory.SimplicialObject

@[simps left right]
def cechNerveLevelHom' (c : ℝ≥0) :
    Augmented.toArrow.obj ((cechNerveLevel r' Λ M N n).obj c) ⟶
      fLCComplexArrow _ (augMapStrict r' Λ M N n) c :=
  @Arrow.homMk _ _ (Augmented.toArrow.obj ((cechNerveLevel r' Λ M N n).obj c))
    (fLCComplexArrow _ (augMapStrict r' Λ M N n) c) (𝟙 _) (𝟙 _)
    (by
      erw [category.comp_id, category.id_comp, augmented.to_arrow_obj_hom]
      dsimp only [Cech_nerve_level_obj, nat_trans.comp_app, whisker_right_app,
        functor.const_comp_hom_app, nat_trans.left_op_app, unop_op, functor.flip_obj_map,
        functor.comp_map, functor.flip_map_app]
      erw [category.comp_id, Cech_nerve_hom_zero]
      rfl)

@[simps left right]
def cechNerveLevelInv' (c : ℝ≥0) :
    fLCComplexArrow _ (augMapStrict r' Λ M N n) c ⟶
      Augmented.toArrow.obj ((cechNerveLevel r' Λ M N n).obj c) :=
  @Arrow.homMk _ _ (fLCComplexArrow _ (augMapStrict r' Λ M N n) c)
    (Augmented.toArrow.obj ((cechNerveLevel r' Λ M N n).obj c)) (𝟙 _) (𝟙 _)
    (by
      erw [category.comp_id, category.id_comp, augmented.to_arrow_obj_hom]
      dsimp only [Cech_nerve_level_obj, nat_trans.comp_app, whisker_right_app,
        functor.const_comp_hom_app, nat_trans.left_op_app, unop_op, functor.flip_obj_map,
        functor.comp_map, functor.flip_map_app]
      erw [category.comp_id, Cech_nerve_hom_zero]
      rfl)

@[simps left right]
def cechNerveLevelHom (c : ℝ≥0) :
    (cechNerveLevel r' Λ M N n).obj c ⟶
      (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).augmentedCechNerve :=
  equivalenceLeftToRight _ _ <| cechNerveLevelHom' _ _ _ _ _ _

theorem cechNerveLevel_hom_injective' (c : ℝ≥0) (i : SimplexCategoryᵒᵖ)
    (x y : ((cechNerveLevel r' Λ M N n).obj c).left.obj i)
    (h :
      ∀ j : Fin ((unop i).len + 1),
        (((cechNerveLevel r' Λ M N n).obj c).left.map ((unop i).const j).op) x =
          (((cechNerveLevel r' Λ M N n).obj c).left.map ((unop i).const j).op) y) :
    x = y := by
  ext j : 2
  let π := (PolyhedralLattice.Conerve.π (Λ.diagonal_embedding N) (i.unop.len + 1)).toAddMonoidHom
  have hπ : Function.Surjective π := PolyhedralLattice.Conerve.π_surjective _ _
  rw [← AddMonoidHom.cancel_right hπ]
  -- Bingo!
  apply Finsupp.addHom_ext'
  intro k; specialize h k
  rw [Subtype.ext_iff] at h 
  replace h := congr_fun h j
  rw [AddMonoidHom.ext_iff] at h ⊢
  intro l; specialize h ((Cech_conerve.obj_zero_iso _).inv l)
  dsimp only [Cech_nerve_level_obj, Cech_nerve_level_map, whiskering_obj_obj_map,
    functor.flip_obj_map, functor.flip_map_app, functor.comp_map, functor.left_op_map,
    Quiver.Hom.unop_op, Cech_nerve, cosimplicial_object.augmented.whiskering_obj,
    cosimplicial_object.whiskering, whiskering_right_obj_obj, whiskering_right_obj_map,
    functor.right_op_map, unop_op, cosimplicial_object.augmented.drop_obj,
    cosimplicial_object.augmented.drop_map, augmented_cosimplicial, augmented_Cech_conerve,
    cosimplicial_object.augment_right, Cech_conerve_map, filtration_obj_map_apply,
    ProFiltPseuNormGrpWithTinv.pow_map, Hom_obj, Hom_map_to_fun, PolyhedralLattice.hom,
    ComphausFilteredPseudoNormedGroupWithTinvHom.level,
    ProfinitelyFilteredPseudoNormedGroupWithTinv.piMap_to_fun,
    ProfinitelyFilteredPseudoNormedGroupWithTinv.piLift_to_fun,
    ComphausFilteredPseudoNormedGroupWithTinvHom.comp_toFun, PseudoNormedGroup.level,
    Finsupp.singleAddHom_apply, Subtype.coe_mk, AddMonoidHom.coe_mkFromPi,
    AddMonoidHom.comp_apply] at h ⊢
  erw [Cech_conerve.map_const_obj_zero_iso] at h 
  exact h

open CategoryTheory.Limits.widePullback

theorem cechNerveLevelHom_injective (c : ℝ≥0) (i : SimplexCategoryᵒᵖ) :
    Function.Injective ⇑((cechNerveLevelHom r' Λ M N n c).left.app i) :=
  by
  let F := FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c
  let G := (Cech_nerve_level_hom r' Λ M N n c).left.app i
  intro x y h
  replace h : ∀ j, π (fun i => F.hom) j (G x) = π (fun i => F.hom) j (G y); · intro j; rw [h]
  have aux := fun j => (augmented_cech_nerve.left_map_comp_obj_zero_iso F i.unop j).symm
  dsimp only [unop_op] at aux 
  simp only [← comp_apply, aux] at h 
  have aux' := (Cech_nerve_level_hom r' Λ M N n c).left.naturality
  simp only [← category.assoc, ← aux'] at h ; clear aux aux'
  simp only [category.assoc, Cech_nerve_level_hom, augmented_cech_nerve.left_obj_zero_iso_hom,
    equivalence_left_to_right_left_app_zero_comp_π, Cech_nerve_level_hom'_left, coe_comp,
    Function.comp, id_apply] at h 
  apply Cech_nerve_level_hom_injective'
  exact h

namespace CechNerveLevelHom

/-! The goal is to build a section to `Cech_nerve_level_hom` -/


variable {r' Λ M N n}

variable {c : ℝ≥0} {i : SimplexCategoryᵒᵖ}

variable (y : (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).augmentedCechNerve.left.obj i)

def z₀' :=
  Limits.WidePullback.base (fun _ => (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).Hom) y

def z' := fun j =>
  Limits.WidePullback.π (fun _ => (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).Hom) j y

theorem hz' : ∀ j, (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).Hom (z' y j) = z₀' y :=
  by
  intro j
  dsimp only [z₀', z']
  rw [← comp_apply, limits.wide_pullback.π_arrow]

def z₀ :=
  (cechNerveLevelInv' r' Λ M N n c).right (z₀' y)

def z := fun j => (cechNerveLevelInv' r' Λ M N n c).left (z' y j)

theorem hz : ∀ j, (Augmented.toArrow.obj ((cechNerveLevel r' Λ M N n).obj c)).Hom (z y j) = z₀ y :=
  by
  intro j; dsimp only [z₀, z]
  have := (Cech_nerve_level_inv' r' Λ M N n c).w
  simp only [functor.id_map, augmented.to_arrow_obj_hom] at this 
  erw [← comp_apply, this, comp_apply, hz']
  rfl

def s' (y : (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).augmentedCechNerve.left.obj i) :
    (ProFiltPseuNormGrpWithTinv.pow r' n).obj
      ((Augmented.drop.obj (cechNerve r' Λ M N).leftOp).obj i) :=
  by
  refine' fun k =>
    cosimplicial_lift Λ N _ ((z₀ y).1 k)
      (fun j =>
        AddMonoidHom.comp ((z y j).1 k)
          (Cech_conerve.obj_zero_iso (Λ.diagonal_embedding N)).inv.toAddMonoidHom)
      _
  intro j l
  dsimp only [AddMonoidHom.comp_apply, Subtype.coe_mk, PolyhedralLatticeHom.coe_toAddMonoidHom]
  rw [← hz y j]
  dsimp only [augmented.to_arrow_obj_hom]
  rw [Cech_nerve_level_hom_app]
  dsimp only [filtration_obj_map_apply, Cech_augmentation_map,
    ComphausFilteredPseudoNormedGroupWithTinvHom.level, PseudoNormedGroup.level,
    ProFiltPseuNormGrpWithTinv.pow_map, ProfinitelyFilteredPseudoNormedGroupWithTinv.piMap_to_fun,
    cosimplicial_augmentation_map, Hom_map_to_fun, AddMonoidHom.comp_apply, Subtype.coe_mk,
    PolyhedralLatticeHom.coe_toAddMonoidHom, Quiver.Hom.unop_op,
    PolyhedralLatticeCat.cechAugmentationMap]
  rfl

def s (y : (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).augmentedCechNerve.left.obj i) :
    ((cechNerveLevel r' Λ M N n).obj c).left.obj i :=
  by
  refine' ⟨s' y, _⟩
  intro k
  apply cosimplicial_lift_mem_filtration
  intro j c' l hl
  dsimp only [AddMonoidHom.comp_apply, PolyhedralLatticeHom.coe_toAddMonoidHom]
  apply (z y j).property
  rw [SeminormedAddCommGroup.mem_filtration_iff] at hl ⊢
  refine' le_trans _ hl
  exact (Cech_conerve.obj_zero_iso (Λ.diagonal_embedding N)).inv.Strict l

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem surjective (c : ℝ≥0) (i : SimplexCategoryᵒᵖ) :
    Function.Surjective ⇑((cechNerveLevelHom r' Λ M N n c).left.app i) :=
  by
  let F := FLC_complex_arrow (aug_map r' Λ M N n) _ c
  intro y
  refine' ⟨Cech_nerve_level_hom.s y, _⟩
  · apply Limits.Concrete.widePullback_ext'.{0} fun i => F.hom
    rotate_left; · infer_instance
    · haveI := Limits.preservesLimitsOfSizeShrink.{0, u, 0, u} (forget.{u + 1} Profinite.{u})
      infer_instance
    intro j
    erw [← augmented_cech_nerve.left_map_comp_obj_zero_iso _ _ j, ← comp_apply, ← category.assoc, ←
      (Cech_nerve_level_hom r' Λ M N n c).left.naturality,
      augmented_cech_nerve.left_map_comp_obj_zero_iso _ _ j, category.assoc]
    dsimp only [Cech_nerve_level_hom, augmented_cech_nerve.left_obj_zero_iso]
    erw [equivalence_left_to_right_left_app_zero_comp_π, Cech_nerve_level_hom'_left,
      category.comp_id]
    apply Subtype.ext; apply funext; rintro k
    -- ext k : 2
    have := Cech_nerve_level_left_map' r' Λ M N n c i _ (i.unop.const j).op
    simp only [Subtype.val_eq_coe] at this 
    erw [this _ k]; clear this
    apply AddMonoidHom.ext; rintro l'
    -- ext1 l'
    obtain ⟨l, rfl⟩ : ∃ l, QuotientAddGroup.mk l = l' := Quotient.surjective_Quotient_mk'' l'
    dsimp only [z₀, z, s', s, AddMonoidHom.comp_apply, Subtype.coe_mk,
      PolyhedralLatticeHom.coe_toAddMonoidHom, PolyhedralLattice.Conerve.map_apply,
      AddMonoidHom.toFun_eq_coe, PolyhedralLattice.Conerve.mapAddHom_mk, cosimplicial_lift,
      PolyhedralLattice.Conerve.lift']
    refine'
      (QuotientAddGroup.lift_mk'
            (PolyhedralLattice.Conerve.l (Λ.diagonal_embedding N) ((unop i).len + 1)) _ _).trans
        _
    dsimp only [Finsupp.liftAddHom_apply, Finsupp.mapDomain.addMonoidHom_apply, unop_op]
    rw [Finsupp.sum_mapDomain_index_addMonoidHom, Finsupp.sum_fintype, Fin.sum_univ_succ,
      Finset.sum_eq_zero, add_zero]
    swap; · intro m hm; exfalso; change Fin 0 at m ; exact Nat.not_lt_zero m m.2
    swap; · intro; rw [AddMonoidHom.map_zero]
    dsimp only [AddMonoidHom.comp_apply, Subtype.coe_mk, PolyhedralLatticeHom.coe_toAddMonoidHom,
      Cech_nerve_level_inv'_left, Cech_conerve.obj_zero_iso, iso.trans_inv, Subtype.val_eq_coe,
      Quiver.Hom.unop_op]
    rw [id_apply, comp_apply, Cech_conerve.obj_zero_iso'_inv, Cech_conerve.finsupp_fin_one_iso_inv]
    suffices Finsupp.singleAddHom 0 (l 0) = l by cases j; rw [this]; rfl
    apply Finsupp.ext; rintro m; apply Finsupp.ext; rintro o
    -- ext m o
    change Fin 1 at m 
    have hm : m = 0 := Subsingleton.elim _ _
    simp only [hm, Finsupp.singleAddHom_apply, Finsupp.single_apply, if_pos rfl]

end CechNerveLevelHom

instance cechNerveLevelHom_isIso (c : ℝ≥0) : IsIso (cechNerveLevelHom r' Λ M N n c) :=
  by
  refine' @simplicial_object.augmented.is_iso_of _ _ _ _ _ (id _) (id _)
  swap; · exact is_iso.id _
  intro i
  apply Profinite.isIso_of_bijective
  exact ⟨Cech_nerve_level_hom_injective r' Λ M N n c i, Cech_nerve_level_hom.surjective c i⟩

def cechNerveLevelIso (c : ℝ≥0) :
    (cechNerveLevel r' Λ M N n).obj c ≅
      (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).augmentedCechNerve :=
  asIso (cechNerveLevelHom r' Λ M N n c)

def fLCComplexAugIsoObj (c : ℝ≥0ᵒᵖ) :
    (fLCComplex V _ (augMapStrict r' Λ M N n)).obj c ≅ (colComplexLevel r' V Λ M N n).obj c :=
  (fLCFunctor' V).mapIso (cechNerveLevelIso r' Λ M N n c.unop).op

def fLCComplexAugIso : fLCComplex V _ (augMapStrict r' Λ M N n) ≅ colComplexLevel r' V Λ M N n :=
  NatIso.ofComponents (fLCComplexAugIsoObj r' V Λ M N n)
    (by
      intro c₁ c₂ h
      dsimp only [FLC_complex, col_complex_level, fLCFunctor, FLC_complex_aug_iso_obj,
        functor.comp_map, functor.map_iso_hom, whiskering_right_obj_obj, Cech_nerve_level_iso,
        iso.op_hom, as_iso_hom, functor.op_map]
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, Quiver.Hom.unop_op]
      congr 2
      apply simplicial_object.hom_ext
      · dsimp only [unop_op]
        let f := FLC_complex_arrow _ (aug_map_strict r' Λ M N n) (unop c₁)
        rw [← cancel_mono (augmented_cech_nerve.left_obj_zero_iso f).Hom]
        dsimp only [comma.comp_left, nat_trans.comp_app, Cech_nerve_level_hom,
          augmented_cech_nerve_map, arrow.map_augmented_cech_nerve_left, cech_nerve_map,
          arrow.map_cech_nerve_app, arrow.hom_mk_right, arrow.hom_mk_left,
          augmented_cech_nerve.left_obj_zero_iso_hom]
        simp only [category.assoc, limits.wide_pullback.lift_π,
          simplicial_object.equivalence_left_to_right_left_app_zero_comp_π]
        erw [← category.assoc, simplicial_object.equivalence_left_to_right_left_app_zero_comp_π]
        rfl
      · dsimp only [equivalence_right_to_left_right, comma.comp_right, Cech_nerve_level_hom_right]
        erw [category.comp_id, category.id_comp]
        rfl)

end

theorem fLCComplexAugIso_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Isometry (((fLCComplexAugIso r' V Λ M N n).Hom.app c).f i) :=
  by
  rw [← iso.app_hom, ← HomologicalComplex.Hom.isoApp_hom]
  refine' SemiNormedGroupCat.iso_isometry_of_normNoninc _ _ _ <;>
      [rw [HomologicalComplex.Hom.isoApp_hom, iso.app_hom];
      rw [HomologicalComplex.Hom.isoApp_inv, iso.app_inv]] <;>
    ·
      apply CosimplicialObject.Augmented.cocomplex_map_normNoninc <;> intros <;>
        apply SemiNormedGroupCat.lCC_obj_map_normNoninc

def colComplexObjIsoXZero (c : ℝ≥0ᵒᵖ) :
    ((colComplex r' V Λ M N n).obj c).pt 0 ≅
      ((fLCFunctor V).obj (op <| fLCComplexArrow _ (augMapStrict r' Λ M N n) c.unop)).pt 0 :=
  Iso.refl _

section

open ProfinitelyFilteredPseudoNormedGroup

def fLCArrowIsoAux :
    (ProFiltPseuNormGrpWithTinv.pow r' n).obj (unop ((cechNerve r' Λ M N).right.obj (mk 0))) ≅
      ProFiltPseuNormGrpWithTinv.of r' (Rescale (↑N) (((↥Λ →+ (↥M : Type u)) ^ n) ^ N)) :=
  (ProFiltPseuNormGrpWithTinv.pow r' n).mapIso (homCosimplicialZeroIso Λ N r' M N rfl) ≪≫
    (ProFiltPseuNormGrpWithTinv.powRescalePowIso.{u, u} r' N N n).app
      (PolyhedralLattice.hom (↥Λ) (↥M : Type u))

section

open ProFiltPseuNormGrpWithTinv

--move this
attribute [simps] LinearEquiv.toAddEquiv

theorem FLC_arrow_iso_w (c : ℝ≥0) :
    ((((filtration r').obj c).mapIso (fLCArrowIsoAux r' Λ M N n)).Hom ≫
          (fLCComplexArrow _ (sumHomStrict ((↥Λ →+ ↥M) ^ n) N) c).Hom :
        _) =
      (fLCComplexArrow _ (augMapStrict r' Λ M N n) c).Hom :=
  by
  rw [← iso.eq_inv_comp]
  ext x i l
  dsimp only [FLC_arrow_iso_aux, iso.trans_inv, functor.map_iso_inv, aug_map, Pow_rescale_Pow_iso,
    iso.app_inv, iso.symm_inv, nat_trans.comp_app, functor.associator_hom_app,
    functor.associator_inv_app, iso_whisker_left_inv, iso_whisker_right_inv, whisker_left_app,
    whisker_right_app, Pow_comm, Pow_rescale, FLC_arrow_hom']
  erw [category.id_comp, category.id_comp, FLC_arrow_hom', ← ((filtration r').obj c).map_comp,
    category.assoc, ← (pow r' n).map_comp, Cech_augmentation_map_eq_Hom_sum]
  dsimp only [FLC_complex_arrow, arrow.mk_hom, filtration_obj_map_apply, comp_apply,
    ContinuousMap.coe_mk, PseudoNormedGroup.level, Subtype.coe_mk,
    ComphausFilteredPseudoNormedGroupWithTinvHom.toComphausFilteredPseudoNormedGroupHom,
    ComphausFilteredPseudoNormedGroupHom.mkOfStrict, ComphausFilteredPseudoNormedGroupHom.mkOfBound,
    ComphausFilteredPseudoNormedGroupHom.coe_mk, AddMonoidHom.toFun_eq_coe,
    ComphausFilteredPseudoNormedGroupWithTinvHom.coe_toAddMonoidHom,
    ProFiltPseuNormGrpWithTinv.pow_map, nat_iso.of_components_hom_app, id,
    ComphausFilteredPseudoNormedGroupWithTinvHom.level_coe]
  erw [comp_apply, comp_apply, iso_of_equiv_of_strict'_hom_apply]
  dsimp only [ProfinitelyFilteredPseudoNormedGroupWithTinv.piMap_to_fun,
    ProFiltPseuNormGrpWithTinv.powMul_inv, Pow_comm, Pow_mul_comm, Pow_mul_comm_obj_hom_to_fun,
    Pow_mul_comm_obj_inv_to_fun, nat_iso.of_components_inv_app, Pow_rescale_aux_apply]
  simp only [comp_apply, Rescale.of, Equiv.refl_apply, Equiv.refl_symm,
    nat_iso.of_components_inv_app, id, iso_of_equiv_of_strict'_inv_apply, rescale_map,
    Rescale.mapComphausFilteredPseudoNormedGroupWithTinvHom_to_fun,
    ProFiltPseuNormGrpWithTinv.powMul_hom, Equiv.symm_apply_apply,
    ProFiltPseuNormGrpWithTinv.powPowX_hom_to_fun, ProFiltPseuNormGrpWithTinv.powPowX_inv_to_fun,
    Pow_Pow_X_equiv_apply, Pow_Pow_X_equiv_symm_apply, Pow_mul_comm_obj_hom_to_fun,
    Pow_mul_comm_obj_inv_to_fun]
  rw [sum_hom_apply, Hom_sum_apply, Finset.sum_apply]
  congr 1
  refine' Fintype.sum_congr _ _ _
  intro j
  simp only [Function.comp_apply, Equiv.refl_apply, comp_apply]
  simp only [Pow_Pow_X_equiv_apply, Pow_Pow_X_equiv_symm_apply,
    ProFiltPseuNormGrpWithTinv.powPowX_hom_to_fun, ProFiltPseuNormGrpWithTinv.powPowX_inv_to_fun,
    Pow_mul_comm_obj_hom_to_fun, Pow_mul_comm_obj_inv_to_fun, comp_apply, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.curry_apply, Equiv.curry_symm_apply, Function.curry, Function.uncurry,
    Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Function.comp, Equiv.refl_apply, Equiv.refl_symm,
    Equiv.trans_apply, LinearEquiv.toAddEquiv_symm_apply, Equiv.prodComm_apply,
    LinearEquiv.invFun_eq_symm, Equiv.invFun_as_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_trans_apply, LinearEquiv.funCongrLeft_symm,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Equiv.prodComm_symm]
  rfl

end

def fLCArrowIso (c : ℝ≥0) :
    fLCComplexArrow _ (augMapStrict r' Λ M N n) c ≅
      fLCComplexArrow _ (sumHomStrict ((↥Λ →+ ↥M) ^ n) N) c :=
  Arrow.isoMk (((filtration r').obj c).mapIso (fLCArrowIsoAux r' Λ M N n)) (Iso.refl _)
    (by
      erw [functor.map_iso_hom, iso.refl_hom, category.comp_id]
      exact (FLC_arrow_iso_w r' Λ M N n c : _))

-- lemma FLC_arrow_iso_left_eq (c₁ c₂ : ℝ≥0) {_ : fact (c₁ ≤ c₂)}
--   (x : ((FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c₁).left.to_Top)) :
--   pseudo_normed_group.cast_le (((FLC_arrow_iso r' Λ M N n c₁).hom.left) x) =
--     ((FLC_arrow_iso r' Λ M N n c₂).hom.left) (pseudo_normed_group.cast_le x) :=
-- by admit
-- lemma FLC_arrow_iso_right_eq (c₁ c₂ : ℝ≥0) {_ : fact (c₁ ≤ c₂)}
--   (x : ((FLC_complex_arrow _ (aug_map_strict r' Λ M N n) c₁).right.to_Top)) :
--   pseudo_normed_group.cast_le (((FLC_arrow_iso r' Λ M N n c₁).hom.right) x) =
--     ((FLC_arrow_iso r' Λ M N n c₂).hom.right) (pseudo_normed_group.cast_le x) :=
-- by admit
def colComplexIsoObj (c : ℝ≥0ᵒᵖ) :
    (fLCComplex V _ (sumHomStrict ((↥Λ →+ ↥M) ^ n) N)).obj c ≅
      (fLCComplex V _ (augMapStrict r' Λ M N n)).obj c :=
  by
  refine' cosimplicial_object.augmented.cocomplex.map_iso _
  refine' functor.map_iso _ _
  refine' functor.map_iso _ _
  refine' functor.map_iso _ _
  refine' iso.op _
  exact FLC_arrow_iso r' Λ M N n c.unop

def colComplexIsoAux2 :
    fLCComplex V _ (sumHomStrict ((↥Λ →+ ↥M) ^ n) N) ≅ fLCComplex V _ (augMapStrict r' Λ M N n) :=
  NatIso.ofComponents (colComplexIsoObj r' V Λ M N n)
    (by
      intro c₁ c₂ h
      dsimp only [FLC_complex, fLCFunctor, fLCFunctor', col_complex_iso_obj, functor.comp_map,
        functor.map_iso_hom, iso.op_hom]
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp]
      rfl)

section

open CosimplicialObject

theorem colComplexIsoAux2_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Isometry (((colComplexIsoAux2 r' V Λ M N n).Hom.app c).f i) :=
  by
  rw [← iso.app_hom, ← HomologicalComplex.Hom.isoApp_hom]
  refine' SemiNormedGroupCat.iso_isometry_of_normNoninc _ _ _ <;>
      [rw [HomologicalComplex.Hom.isoApp_hom, iso.app_hom];
      rw [HomologicalComplex.Hom.isoApp_inv, iso.app_inv]] <;>
    · dsimp only [col_complex_iso_aux2, col_complex_iso_obj, nat_iso.of_components,
        functor.comp_map, functor.map_iso_hom, iso.op_hom, Quiver.Hom.unop_op, functor.op_map,
        cosimplicial_object.augmented.whiskering_obj_2,
        cosimplicial_object.augmented.whiskering_obj]
      apply augmented.cocomplex_map_norm_noninc <;>
        · intros; apply SemiNormedGroupCat.lCC_obj_map_normNoninc

end

def colComplexIso : fLCComplex V _ (sumHomStrict ((↥Λ →+ ↥M) ^ n) N) ≅ colComplex r' V Λ M N n :=
  colComplexIsoAux2 r' V Λ M N n ≪≫ fLCComplexAugIso r' V Λ M N n ≪≫ colComplexLevelIso r' V Λ M N n

theorem colComplexIso_strict (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Isometry (((colComplexIso r' V Λ M N n).Hom.app c).f i) :=
  by
  refine' Isometry.comp _ (col_complex_iso_aux2_strict r' V Λ M N n c i)
  exact
    (col_complex_level_iso_strict r' V Λ M N n c i).comp
      (FLC_complex_aug_iso_strict r' V Λ M N n c i)

end

theorem colComplex.isWeakBoundedExact (d : ℝ≥0) [PseudoNormedGroup.Splittable ((Λ →+ M) ^ n) N d]
    (k : ℝ≥0) [Fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
    (colComplex r' V Λ M N n).IsWeakBoundedExact k 1 m c₀ :=
  haveI key := FLC_complex.weak_bounded_exact V ((Λ →+ M) ^ n) N d k m c₀ hdkc₀N
  key.of_iso _ fun c => col_complex_iso_strict r' V Λ M N n (op c)

@[simps obj map]
def colComplexRescaled : SystemOfComplexes :=
  scaleFactorial.obj (colComplex r' V Λ M N n)

theorem colComplexRescaled.isWeakBoundedExact (d : ℝ≥0)
    [PseudoNormedGroup.Splittable ((Λ →+ M) ^ n) N d] (k : ℝ≥0) [Fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0)
    (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
    (colComplexRescaled r' V Λ M N n).IsWeakBoundedExact k (m + 1) m c₀ :=
  by
  have :=
    scale_factorial.is_weak_bounded_exact
      (col_complex.is_weak_bounded_exact r' V Λ M N n d k m c₀ hdkc₀N)
  rwa [one_mul] at this 

end

end

namespace ColComplexRescaled

open PolyhedralLattice (hom)

open PolyhedralLatticeCat (cosimplicial)

instance move_pls (r' : ℝ≥0) (c : ℝ≥0ᵒᵖ) : Fact (unop (r'.mulLeft.op.obj c) ≤ r' * unop c) :=
  ⟨le_rfl⟩

instance move_pls2 [Fact (r' < 1)] (c : ℝ≥0ᵒᵖ) : Fact (unop (r'.mulLeft.op.obj c) ≤ unop c) := by
  dsimp [NNReal.mulLeft]; infer_instance

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r' < 1)]

def tInvSubTinvFSucc [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    ((colComplexRescaled.{u} r' V Λ M N n).obj c).pt (i + 1) ⟶
      (((colComplexRescaled.{u} r' V Λ M N n).scaleIndexLeft r').obj c).pt (i + 1) :=
  (SemiNormedGroupCat.rescale (i + 1)!).map <| (cLCFP.tInvSubTinv r r' V _ _ n).app _

def tInvSubTinvF [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    ∀ i,
      ((colComplexRescaled.{u} r' V Λ M N n).obj c).pt i ⟶
        (((colComplexRescaled.{u} r' V Λ M N n).scaleIndexLeft r').obj c).pt i
  | 0 => (SemiNormedGroupCat.rescale 0!).map <| (cLCFP.tInvSubTinv r r' V _ _ n).app _
  | i + 1 => tInvSubTinvFSucc r r' V Λ M N n c i

section

open SystemOfComplexes CategoryTheory.Preadditive CategoryTheory.CosimplicialObject
  HomologicalComplex

theorem T_inv_sub_Tinv_comm_zero [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    tInvSubTinvF r r' V Λ M N n c 0 ≫
        (((colComplexRescaled r' V Λ M N n).scaleIndexLeft r').obj c).d 0 1 =
      ((colComplexRescaled r' V Λ M N n).obj c).d 0 1 ≫ tInvSubTinvF r r' V Λ M N n c 1 :=
  by
  dsimp only [T_inv_sub_Tinv_f, T_inv_sub_Tinv_f_succ, scale_index_left, col_complex_rescaled]
  refine' SemiNormedGroupCat.scale_comm _ _ _ _ _ _ _
  dsimp
  rw [if_pos rfl, category.comp_id]
  dsimp only [augmented.to_cocomplex_d]
  erw [Cech_nerve'_hom_zero]
  dsimp only [CLCFP'_map_app]
  erw [nat_trans.naturality]
  rfl

theorem T_inv_sub_Tinv_comm_succ [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    tInvSubTinvF r r' V Λ M N n c (i + 1) ≫
        (((colComplexRescaled r' V Λ M N n).scaleIndexLeft r').obj c).d (i + 1) (i + 2) =
      ((colComplexRescaled r' V Λ M N n).obj c).d (i + 1) (i + 2) ≫
        tInvSubTinvF r r' V Λ M N n c (i + 2) :=
  by
  dsimp only [T_inv_sub_Tinv_f, T_inv_sub_Tinv_f_succ, scale_index_left, col_complex_rescaled]
  refine' SemiNormedGroupCat.scale_comm _ _ _ _ _ _ _
  dsimp
  rw [if_pos rfl, category.comp_id]
  dsimp only [augmented.to_cocomplex_d, coboundary, augmented.drop_obj, Cech_nerve',
    augmented.whiskering_obj_2, augmented.whiskering_obj, cosimplicial_object.δ,
    whiskering_obj_obj_map]
  simp only [nat_trans.app_sum, nat_trans.app_zsmul, sum_comp, comp_sum, zsmul_comp, comp_zsmul]
  apply Fintype.sum_congr
  intro j
  congr 1
  dsimp only [CLCFP'_map_app]
  erw [nat_trans.naturality]
  rfl

theorem T_inv_sub_Tinv_naturality_zero [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
    ((colComplexRescaled r' V Λ M N n).map h).f 0 ≫ tInvSubTinvF r r' V Λ M N n c₂ 0 =
      tInvSubTinvF r r' V Λ M N n c₁ 0 ≫
        (((colComplexRescaled r' V Λ M N n).scaleIndexLeft r').map h).f 0 :=
  by
  dsimp only [T_inv_sub_Tinv_f, scale_index_left, ScaleIndexLeft_obj_map, col_complex_rescaled,
    scale_factorial_obj, functor.comp_map, modify_functor_map_f, col_complex_map,
    augmented.to_cocomplex_obj, augmented.point_obj, Cech_nerve', augmented.whiskering_obj]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  dsimp only [CLCFP'_obj_map, cLCFP.tInvSubTinv, NNReal.mulLeft, functor.op_obj, unop_op]
  simp only [nat_trans.app_sub, comp_sub, sub_comp, ← nat_trans.comp_app]
  congr 2
  · rw [category.assoc, ← cLCFP.res_comp_tInv]
    haveI : Fact (c₂.unop ≤ c₁.unop) := ⟨le_of_hom h.unop⟩
    simp only [← category.assoc, cLCFP.res_comp_res]
  · dsimp only [cLCFP.tinv, cLCFP.res, cLC, lC]
    simp only [← whisker_right_comp, ← nat_trans.op_comp]
    rfl

theorem T_inv_sub_Tinv_naturality_succ [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
    ((colComplexRescaled r' V Λ M N n).map h).f (i + 1) ≫ tInvSubTinvF r r' V Λ M N n c₂ (i + 1) =
      tInvSubTinvF r r' V Λ M N n c₁ (i + 1) ≫
        (((colComplexRescaled r' V Λ M N n).scaleIndexLeft r').map h).f (i + 1) :=
  by
  dsimp only [T_inv_sub_Tinv_f, T_inv_sub_Tinv_f_succ, scale_index_left, ScaleIndexLeft_obj_map,
    col_complex_rescaled, scale_factorial_obj, functor.comp_map, modify_functor_map_f,
    col_complex_map, augmented.to_cocomplex_obj, augmented.drop_obj, Cech_nerve',
    augmented.whiskering_obj, whiskering_obj_obj_obj]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  dsimp only [CLCFP'_obj_map, cLCFP.tInvSubTinv, NNReal.mulLeft, functor.op_obj, unop_op]
  simp only [nat_trans.app_sub, comp_sub, sub_comp]
  erw [← nat_trans.comp_app, ← nat_trans.comp_app, ← nat_trans.comp_app, ← nat_trans.comp_app]
  congr 2
  · rw [category.assoc, ← cLCFP.res_comp_tInv]
    haveI : Fact (c₂.unop ≤ c₁.unop) := ⟨le_of_hom h.unop⟩
    simp only [← category.assoc, cLCFP.res_comp_res]
  · dsimp only [cLCFP.tinv, cLCFP.res, cLC, lC]
    simp only [← whisker_right_comp, ← nat_trans.op_comp]
    rfl

end

def tInvSubTinv [NormedWithAut r V] :
    colComplexRescaled r' V Λ M N n ⟶ (colComplexRescaled r' V Λ M N n).scaleIndexLeft r'
    where
  app c :=
    { f := tInvSubTinvF r r' V Λ M N n c
      comm' := by
        rintro i j (rfl : i + 1 = j)
        cases i; · apply T_inv_sub_Tinv_comm_zero; · apply T_inv_sub_Tinv_comm_succ }
  naturality' := by
    intro c₁ c₂ h; ext i : 2; cases i
    · apply T_inv_sub_Tinv_naturality_zero
    · apply T_inv_sub_Tinv_naturality_succ

def tInvSubTinv' (c : ℝ≥0) [NormedWithAut r V] :=
  (SystemOfComplexes.scaleIndexRight c).map (colComplexRescaled.tInvSubTinv r r' V Λ M N n)

end ColComplexRescaled

namespace DoubleComplex

open PolyhedralLattice (hom)

attribute [local semireducible] cLCFPTinv cLCFPTinv₂ cLCFP

-- CLCTinv
variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' < 1)]

@[simps obj map]
def col'Aux [NormedWithAut r V] (n : ℕ) : SystemOfComplexes :=
  (doubleComplex' BD κ r r' V Λ M N).col n

@[simps obj map]
def col' [NormedWithAut r V] (n : ℕ) : SystemOfComplexes :=
  scaleFactorial.obj (col'Aux BD κ r r' V Λ M N n)

def colIsoObjX [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    ∀ m,
      (((doubleComplex.{u} BD κ r r' V Λ M N).col n).obj c).pt m ≅
        ((col'.{u} BD κ r r' V Λ M N n).obj c).pt m
  | 0 => (SemiNormedGroupCat.isoRescale _).app _
  | 1 => (SemiNormedGroupCat.isoRescale _).app _
  | m + 2 => Iso.refl _

section

open HomologicalComplex SystemOfComplexes

theorem col_iso_comm₁_0 [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    (colIsoObjX BD κ r r' V Λ M N n c 0).Hom ≫ ((col' BD κ r r' V Λ M N n).obj c).d 0 1 =
      (((doubleComplex BD κ r r' V Λ M N).col n).obj c).d 0 1 ≫
        (colIsoObjX BD κ r r' V Λ M N n c 1).Hom :=
  by dsimp only [col_iso_obj_X]; ext; rfl

theorem col_iso_comm₁_1 [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    (colIsoObjX BD κ r r' V Λ M N n c 1).Hom ≫ ((col' BD κ r r' V Λ M N n).obj c).d 1 2 =
      (((doubleComplex BD κ r r' V Λ M N).col n).obj c).d 1 2 ≫
        (colIsoObjX BD κ r r' V Λ M N n c 2).Hom :=
  by
  delta col_iso_obj_X
  simp only [iso.refl_hom, Nat.rec_add_one, category.id_comp, category.comp_id,
    SystemOfDoubleComplexes.col_obj_d]
  dsimp only [col'_obj, col'_aux_obj, double_complex', double_complex, double_complex_aux_rescaled,
    as_functor_obj, modify_d, eval_obj, eval_map, functor.map_homological_complex_obj_d,
    functor.map_homological_complex_obj_X, nat_trans.comp_app, comp_f, rescale_functor,
    rescale_nat_trans, SystemOfComplexes.rescale, scale]
  rfl

theorem col_iso_comm₂_0 [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
    (((doubleComplex.{u} BD κ r r' V Λ M N).col n).map h).f 0 ≫
        (colIsoObjX BD κ r r' V Λ M N n c₂ 0).Hom =
      (colIsoObjX BD κ r r' V Λ M N n c₁ 0).Hom ≫ ((col'.{u} BD κ r r' V Λ M N n).map h).f 0 :=
  by dsimp only [col_iso_obj_X]; ext; rfl

theorem col_iso_comm₂_1 [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
    (((doubleComplex.{u} BD κ r r' V Λ M N).col n).map h).f 1 ≫
        (colIsoObjX BD κ r r' V Λ M N n c₂ 1).Hom =
      (colIsoObjX BD κ r r' V Λ M N n c₁ 1).Hom ≫ ((col'.{u} BD κ r r' V Λ M N n).map h).f 1 :=
  by dsimp only [col_iso_obj_X]; ext; rfl

theorem col_iso_comm₁_succ [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    (colIsoObjX BD κ r r' V Λ M N n c i.succ.succ).Hom ≫
        ((col'.{u} BD κ r r' V Λ M N n).obj c).d i.succ.succ (i.succ.succ + 1) =
      (((doubleComplex.{u} BD κ r r' V Λ M N).col n).obj c).d i.succ.succ (i.succ.succ + 1) ≫
        (colIsoObjX BD κ r r' V Λ M N n c (i.succ.succ + 1)).Hom :=
  by
  dsimp only [col_iso_obj_X, iso.refl_hom]
  simp only [category.id_comp, category.comp_id, SystemOfDoubleComplexes.col_obj_d]
  rfl

theorem col_iso_comm₂_succ [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
    (((doubleComplex.{u} BD κ r r' V Λ M N).col n).map h).f (i + 2) ≫
        (colIsoObjX BD κ r r' V Λ M N n c₂ (i + 2)).Hom =
      (colIsoObjX BD κ r r' V Λ M N n c₁ (i + 2)).Hom ≫
        ((col'.{u} BD κ r r' V Λ M N n).map h).f (i + 2) :=
  by
  dsimp only [col_iso_obj_X, iso.refl_hom]
  simp only [category.id_comp, category.comp_id, SystemOfDoubleComplexes.col_obj_d]
  rfl

theorem col_iso_comm₂ [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
    ∀ i,
      (((doubleComplex.{u} BD κ r r' V Λ M N).col n).map h).f i ≫
          (colIsoObjX BD κ r r' V Λ M N n c₂ i).Hom =
        (colIsoObjX BD κ r r' V Λ M N n c₁ i).Hom ≫ ((col'.{u} BD κ r r' V Λ M N n).map h).f i
  | 0 => col_iso_comm₂_0 _ _ _ _ _ _ _ _ _ _ _ _
  | 1 => col_iso_comm₂_1 _ _ _ _ _ _ _ _ _ _ _ _
  | i + 2 => col_iso_comm₂_succ _ _ _ _ _ _ _ _ _ _ _ _ _

end

section

open HomologicalComplex

-- set_option pp.universes true
@[simps]
def colIso [NormedWithAut r V] :
    (doubleComplex.{u} BD κ r r' V Λ M N).col n ≅ col'.{u} BD κ r r' V Λ M N n :=
  NatIso.ofComponents
    (fun c =>
      Hom.isoOfComponents (colIsoObjX.{u} BD κ r r' V Λ M N n _)
        (by
          rintro i j (rfl : i + 1 = j)
          cases i; · exact col_iso_comm₁_0 BD κ r r' V Λ M N n c
          cases i; · exact col_iso_comm₁_1 BD κ r r' V Λ M N n c
          · exact col_iso_comm₁_succ BD κ r r' V Λ M N n c i))
    (by
      intro c₁ c₂ h; ext i : 2
      dsimp only [comp_f, hom.iso_of_components_hom_f]
      exact col_iso_comm₂ BD κ r r' V Λ M N n c₁ c₂ h i)

theorem colIso_strict [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Isometry (Hom.isoApp ((colIso BD κ r r' V Λ M N n).app c) i).Hom :=
  by
  dsimp only [hom.iso_app_hom, nat_iso.app_hom, col_iso_hom_app_f]
  cases i; · delta col_iso_obj_X; apply SemiNormedGroupCat.isoRescale_isometry; exact Nat.cast_one
  cases i; · delta col_iso_obj_X; apply SemiNormedGroupCat.isoRescale_isometry; exact Nat.cast_one
  · delta col_iso_obj_X; exact isometry_id

theorem colIso_inv_strict [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    Isometry (Hom.isoApp ((colIso BD κ r r' V Λ M N n).app c) i).inv :=
  (colIso_strict BD κ r r' V Λ M N n c i).right_inv fun x => by
    rw [← comp_apply, iso.inv_hom_id, id_apply]

end

theorem col_obj_x_zero [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    (((doubleComplex BD κ r r' V Λ M N).col n).obj c).pt 0 =
      (cLCFPTinv r V r' (c.unop * κ n) (BD.pt n)).obj (op <| hom Λ M) :=
  rfl

-- local attribute [semireducible] opposite
def colιFSucc [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    ((col'.{u} BD κ r r' V Λ M N n).obj c).pt (i + 1) ⟶
      (((colComplexRescaled.{u} r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).obj c).pt (i + 1) :=
  (SemiNormedGroupCat.rescale (i + 1)!).map (cLCTinv.ι r V _ _)

def colιF [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    ∀ i,
      ((col'.{u} BD κ r r' V Λ M N n).obj c).pt i ⟶
        (((colComplexRescaled.{u} r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).obj c).pt i
  | 0 => (SemiNormedGroupCat.rescale 0!).map (cLCTinv.ι r V _ _)
  | i + 1 => colιFSucc _ _ _ _ _ _ _ _ _ _ i

section

open HomologicalComplex SystemOfComplexes BreenDeligne

theorem colιF_comm_zero [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    colιF BD κ r r' V Λ M N n c 0 ≫
        (((colComplexRescaled r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).obj c).d 0 1 =
      ((col' BD κ r r' V Λ M N n).obj c).d 0 1 ≫ colιF BD κ r r' V Λ M N n c 1 :=
  by
  dsimp only [col_ι_f, col_ι_f_succ, col'_obj, functor.map_homological_complex_obj_d, modify_d,
    eval_map, scale_index_right, ScaleIndexRight_obj_obj, col_complex_rescaled_obj, scale'_app]
  refine' SemiNormedGroupCat.scale_comm _ _ _ _ _ _ _
  rw [dif_pos rfl, dif_pos rfl]
  simp only [cosimplicial_object.augmented.to_cocomplex_d, eq_to_hom_refl, category.comp_id]
  erw [Cech_nerve'_hom_zero, cosimplicial_system_of_complexes_hom_zero]
  dsimp only [data.system_map, data.complex, data.complex₂_map_f, cLCFPTinv₂, cLCTinv.f_map]
  symm
  apply cLCTinv.map_comp_ι

section

open CategoryTheory.Preadditive

theorem colιF_comm_succ [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    colιF BD κ r r' V Λ M N n c (i + 1) ≫
        (((colComplexRescaled r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).obj c).d (i + 1)
          (i + 2) =
      ((col' BD κ r r' V Λ M N n).obj c).d (i + 1) (i + 2) ≫ colιF BD κ r r' V Λ M N n c (i + 2) :=
  by
  dsimp only [col_ι_f, col_ι_f_succ, col'_obj, functor.map_homological_complex_obj_d, modify_d,
    eval_map, scale_index_right, ScaleIndexRight_obj_obj, col_complex_rescaled_obj, scale'_app]
  refine' SemiNormedGroupCat.scale_comm _ _ _ _ _ _ _
  rw [dif_pos rfl, dif_pos rfl]
  simp only [cosimplicial_object.augmented.to_cocomplex_d, eq_to_hom_refl, category.comp_id,
    cosimplicial_object.coboundary, nat_trans.app_sum, nat_trans.app_zsmul, ←
    HomologicalComplex.Hom.fAddMonoidHom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul,
    sum_comp, comp_sum, zsmul_comp, comp_zsmul]
  symm
  apply Fintype.sum_congr
  intro j
  rfl

end

theorem colιF_comm [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) :
    ∀ i,
      colιF BD κ r r' V Λ M N n c i ≫
          (((colComplexRescaled r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).obj c).d i (i + 1) =
        ((col' BD κ r r' V Λ M N n).obj c).d i (i + 1) ≫ colιF BD κ r r' V Λ M N n c (i + 1)
  | 0 => by apply col_ι_f_comm_zero
  | i + 1 => by apply col_ι_f_comm_succ

section

open CategoryTheory.CosimplicialObject

theorem col_ι_naturality_zero [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) :
    ((col' BD κ r r' V Λ M N n).map h).f 0 ≫ colιF BD κ r r' V Λ M N n c₂ 0 =
      colιF BD κ r r' V Λ M N n c₁ 0 ≫
        (((colComplexRescaled r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).map h).f 0 :=
  by
  dsimp only [col'_map, functor.map_homological_complex_map_f, eval_map, modify_functor_map_f,
    col_ι_f, scale_index_right, ScaleIndexRight_obj_map, col_complex_rescaled_map]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  dsimp only [augmented.to_cocomplex_obj, augmented.point_obj, cosimplicial_system_of_complexes,
    Cech_nerve', augmented.whiskering_obj, CLCFP', data.system_obj, data.complex,
    data.complex₂_obj_X, cLCFPTinv₂.res, cLCTinv.mapNat, functor.comp_obj, functor.comp_map,
    functor.op_obj, functor.op_map, whiskering_right_obj_obj, functor.op_hom_obj, unop_op,
    functor.flip_obj_map]
  apply cLCTinv.map_comp_ι

theorem col_ι_naturality_succ [NormedWithAut r V] (c₁ c₂ : ℝ≥0ᵒᵖ) (h : c₁ ⟶ c₂) (i : ℕ) :
    ((col' BD κ r r' V Λ M N n).map h).f (i + 1) ≫ colιF BD κ r r' V Λ M N n c₂ (i + 1) =
      colιF BD κ r r' V Λ M N n c₁ (i + 1) ≫
        (((colComplexRescaled r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)).map h).f (i + 1) :=
  by
  dsimp only [col'_map, functor.map_homological_complex_map_f, eval_map, modify_functor_map_f,
    col_ι_f, col_ι_f_succ, scale_index_right, ScaleIndexRight_obj_map, col_complex_rescaled_map]
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  dsimp only [augmented.to_cocomplex_obj, augmented.drop_obj, cosimplicial_system_of_complexes,
    Cech_nerve', augmented.whiskering_obj, CLCFP', whiskering_obj_obj_obj, data.system_obj,
    data.complex, data.complex₂_obj_X, cLCFPTinv₂.res, cLCTinv.mapNat, functor.comp_obj,
    functor.comp_map, functor.op_obj, functor.op_map, whiskering_right_obj_obj, functor.op_hom_obj,
    unop_op, functor.flip_obj_map]
  apply cLCTinv.map_comp_ι

end

end

def colι [NormedWithAut r V] :
    col'.{u} BD κ r r' V Λ M N n ⟶
      (colComplexRescaled.{u} r' V Λ M N (BD.pt n)).scaleIndexRight (κ n)
    where
  app c :=
    { f := colιF BD κ r r' V Λ M N n c
      comm' := by rintro i j (rfl : i + 1 = j); apply col_ι_f_comm }
  naturality' := by
    intro c₁ c₂ h; ext i : 2
    cases i
    · apply col_ι_naturality_zero
    · apply col_ι_naturality_succ

variable [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ)

theorem colι_range :
    (((doubleComplex.colι BD κ r r' V Λ M N n).app c).f i).range =
      (((colComplexRescaled.tInvSubTinv' r r' V Λ M N (BD.pt n) (κ n)).app c).f i).ker :=
  by
  cases i <;>
    · refine' SemiNormedGroupCat.rescale_exact _ _ _ _
      rw [cLCTinv.ι_range']
      ext1 x
      rfl

theorem colι_isometry : Isometry (((doubleComplex.colι BD κ r r' V Λ M N n).app c).f i) := by
  cases i <;>
    · refine' SemiNormedGroupCat.rescale_map_isometry _ _
      apply AddMonoidHomClass.isometry_of_norm
      intro; rfl

end DoubleComplex

namespace ColComplexRescaled

variable [Fact (0 < r')] [Fact (r' ≤ 1)]

theorem d_zero_normNoninc (c : ℝ≥0) :
    (@SystemOfComplexes.d (colComplexRescaled r' V Λ M N n) c 0 1).NormNoninc :=
  by
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
  refine'
    NormedAddGroupHom.norm_comp_le_of_le' (1 : ℕ) _ 1 _ (SemiNormedGroupCat.norm_scale_le _ _ _) _
  ·
    simp only [mul_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one,
      NNReal.coe_one]
  apply SemiNormedGroupCat.norm_rescale_map_le
  have : (1 : ℝ) = ∑ i : Fin 1, 1 := by
    simp only [Finset.card_fin, mul_one, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.cast_bit1,
      Nat.cast_add, Nat.cast_one]
  dsimp [SystemOfComplexes.rescaleFunctor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d]
  erw [category.comp_id, if_pos rfl, Cech_nerve'_hom_zero, Nat.cast_one]
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
  apply cLC.map_normNoninc

theorem d_succ_normNoninc (c : ℝ≥0) (p : ℕ) :
    (@SystemOfComplexes.d (colComplexRescaled r' V Λ M N n) c (p + 1) (p + 2)).NormNoninc :=
  by
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
  refine'
    NormedAddGroupHom.norm_comp_le_of_le' (p + 2 : ℕ) _ 1 _ (SemiNormedGroupCat.norm_scale_le _ _ _)
      _
  · norm_cast
    rw [mul_comm, ← mul_div_assoc, eq_comm, ← Nat.cast_mul, Nat.factorial_succ]; apply div_self
    norm_num [Nat.factorial_ne_zero]
  apply SemiNormedGroupCat.norm_rescale_map_le
  have : (p + 1 + 1 : ℝ) = ∑ i : Fin (p + 1 + 1), 1 := by
    simp only [Finset.card_fin, mul_one, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.cast_bit1,
      Nat.cast_add, Nat.cast_one]
  dsimp [SystemOfComplexes.rescaleFunctor, double_complex_aux,
    cosimplicial_object.augmented.to_cocomplex_d]
  erw [category.comp_id, if_pos rfl]
  dsimp [cosimplicial_object.coboundary]
  rw [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] at this 
  simp only [← nat_trans.app_hom_apply, AddMonoidHom.map_sum, AddMonoidHom.map_zsmul, ←
    HomologicalComplex.Hom.fAddMonoidHom_apply, Nat.cast_add, Nat.cast_bit0, Nat.cast_one, this]
  apply norm_sum_le_of_le
  rintro i -
  refine' le_trans (norm_zsmul_le _ _) _
  rw [← Int.norm_cast_real, Int.cast_pow, norm_pow, Int.cast_neg, Int.cast_one, norm_neg, norm_one,
    one_pow, one_mul]
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
  apply cLC.map_normNoninc

theorem admissible : (colComplexRescaled r' V Λ M N n).Admissible :=
  { d_norm_noninc' := by
      rintro c i j rfl; cases i
      · apply d_zero_norm_noninc
      · apply d_succ_norm_noninc
    res_normNoninc := by
      intro c₁ c₂ i h
      apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2
      cases i <;>
        · apply SemiNormedGroupCat.norm_rescale_map_le
          apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
          apply cLC.map_normNoninc }

end ColComplexRescaled

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r' < 1)]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem col_exact'_aux1 [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    ∀ x,
      «expr∥ ∥» ((((colComplexRescaled.tInvSubTinv' r r' V Λ M N (BD.pt n) (κ n)).app c).f i) x) ≤
        (1 + r⁻¹) * «expr∥ ∥» x :=
  by
  intro x
  cases i <;>
    · apply NormedAddGroupHom.le_of_opNorm_le
      refine' @SemiNormedGroupCat.norm_rescale_map_le _ _ _ _ _ (1 + r⁻¹) _
      exact cLCFP.norm_tInvSubTinv_le _ _ _ _ _ _ _

variable [Fact (r < r')]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem col_exact'_aux2 [NormedWithAut r V] (c : ℝ≥0ᵒᵖ) (i : ℕ) :
    ∀ y,
      ∃ x,
        (((colComplexRescaled.tInvSubTinv' r r' V Λ M N (BD.pt n) (κ n)).app c).f i) x = y ∧
          «expr∥ ∥» x ≤ ↑(r / (1 - r) + 1) * «expr∥ ∥» y :=
  by
  haveI : Fact (r < 1) := ⟨@lt_trans _ _ r r' 1 (Fact.out _) (Fact.out _)⟩
  cases i <;>
    · refine' SemiNormedGroupCat.rescale_exists_norm_le _ _ _ _
      intro y
      obtain ⟨x, h1, h2⟩ := cLCFP.tInvSubTinv_exists_preimage r r' y 1 zero_lt_one
      refine' ⟨x, h1, _⟩
      rwa [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sub]
      exact Fact.out _

theorem colExact' [NormedWithAut r V] [Fact (r < 1)] (d : ℝ≥0)
    [PseudoNormedGroup.Splittable (Λ →+ M) N d] (k : ℝ≥0) [Fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0)
    (hdkc₀N : d ≤ (k - 1) * c₀ / N) (k' K' : ℝ≥0) [Fact (1 ≤ k')] (hk' : k * k ≤ k')
    (hK' : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2) ^ 2 : ℝ≥0) ≤ K') (c₁ c₂ : ℝ≥0)
    [Fact (c₀ ≤ r' * c₁)] [Fact (c₀ ≤ κ n * c₂)] [Fact (c₁ ≤ κ n * c₂)] :
    (doubleComplex.col'.{u} BD κ r r' V Λ M N n).IsWeakBoundedExact k' K' m c₂ :=
  by
  have adm := colComplexRescaled.admissible.{u} r' V Λ M N (BD.X n)
  have adm2 := adm.scale_index_left r'
  let T_T := col_complex_rescaled.T_inv_sub_Tinv' r r' V Λ M N (BD.X n) (κ n)
  have H := colComplexRescaled.isWeakBoundedExact.{u} r' V Λ M N (BD.X n) d k (m + 1) c₀ hdkc₀N
  have H1 := H.scale_index_right _ c₂ (κ n) adm
  have H2 := (H.scale_index_left _ c₁ r' adm).scaleIndexRight _ c₂ (κ n) adm2
  have key :=
    weakNormedSnakeDual (doubleComplex.col'.{u} BD κ r r' V Λ M N n) _ _
      (double_complex.col_ι BD κ r r' V Λ M N n) T_T k _ (m + 1 + 1) _ (1 + r⁻¹) (r / (1 - r) + 1)
      (by simpa using H1) H2 (adm.scale_index_right _)
  have h_isom : _ := _
  apply (key _ _ _ h_isom).of_le _ ⟨hk'⟩ _ le_rfl ⟨le_rfl⟩
  any_goals clear key adm2 H1 H2
  · intros; apply col_exact'_aux1
  · intros; apply col_exact'_aux2
  · intro c i; apply double_complex.col_ι_range
  · apply SystemOfComplexes.admissibleOfIsometry (adm.scale_index_right _) h_isom
  · refine' ⟨le_trans (le_of_eq _) hK'⟩
    rw [pow_two, ← mul_assoc]
    simp only [Nat.cast_add, Nat.cast_one, bit0, ← add_assoc, or_false_iff, add_eq_zero_iff,
      one_ne_zero, add_right_inj, mul_eq_mul_right_iff, and_false_iff, div_eq_mul_inv]
    have hr0 : r ≠ 0 := ne_of_gt (Fact.out _)
    have h1r : 1 - r ≠ 0 :=
      by
      rw [← nnreal.coe_injective.ne_iff, NNReal.coe_sub, NNReal.coe_zero, sub_ne_zero]
      · norm_cast; exact ne_of_gt (Fact.out _)
      · exact Fact.out _
    calc
      (1 + r⁻¹) * (r * (1 - r)⁻¹ + 1) = (1 + r⁻¹) * (r * (1 - r)⁻¹ + (1 - r) * (1 - r)⁻¹) := by
        rw [mul_inv_cancel h1r]
      _ = (1 + r⁻¹) * (1 - r)⁻¹ := (congr_arg _ _)
      _ = (1 + r⁻¹) * (r * r⁻¹) * (1 - r)⁻¹ := by rw [mul_inv_cancel hr0, mul_one]
      _ = (1 + r⁻¹) * r * (r⁻¹ * (1 - r)⁻¹) := by simp only [mul_assoc]
      _ = (r + 1) * (r * (1 - r))⁻¹ := _
    · rw [← add_mul, add_comm, tsub_add_cancel_of_le, one_mul]; exact Fact.out _
    · rw [add_mul, one_mul, inv_mul_cancel, mul_inv]
      exact ne_of_gt (Fact.out _)
  · intro c i; apply double_complex.col_ι_isometry

theorem colExact [NormedWithAut r V] [Fact (r < 1)] (d : ℝ≥0)
    [PseudoNormedGroup.Splittable (Λ →+ M) N d] (k : ℝ≥0) [Fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0)
    (hdkc₀N : d ≤ (k - 1) * c₀ / N) (k' K' : ℝ≥0) [Fact (1 ≤ k')] (hk' : k * k ≤ k')
    (hK' : (m + 2 + (r + 1) / (r * (1 - r)) * (m + 2) ^ 2 : ℝ≥0) ≤ K') (c₁ c₂ : ℝ≥0)
    (_ : Fact (c₀ ≤ r' * c₁)) (_ : Fact (c₀ ≤ κ n * c₂)) (_ : Fact (c₁ ≤ κ n * c₂)) :
    ((doubleComplex.{u} BD κ r r' V Λ M N).col n).IsWeakBoundedExact k' K' m c₂ :=
  by
  have key := col_exact' BD κ r r' V Λ M N n d k m c₀ hdkc₀N k' K' hk' hK' c₁ c₂
  apply key.of_iso (double_complex.col_iso BD κ r r' V Λ M N n).symm
  intros
  apply double_complex.col_iso_inv_strict

end Thm95

