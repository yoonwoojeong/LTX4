import LiquidTensorExperiment.PseudoNormedGroup.FP
import LiquidTensorExperiment.SystemOfComplexes.Basic
import LiquidTensorExperiment.Prop819
import LiquidTensorExperiment.PseudoNormedGroup.SumHom
import LiquidTensorExperiment.PseudoNormedGroup.Splittable

#align_import thm95.col_exact_prep

noncomputable section

open scoped NNReal BigOperators

open CategoryTheory Opposite SimplexCategory

attribute [local instance] typePow

universe u v u₀ uₘ

-- set_option pp.universes true
namespace SystemOfComplexes

variable (C : SystemOfComplexes)

def NormExactComplex (D : CochainComplex SemiNormedGroupCat ℕ) : Prop :=
  ∀ (m : ℕ) (ε : ℝ≥0) (hε : 0 < ε) (x : D.pt m) (hx : D.d _ (m + 1) x = 0),
    ∃ y : D.pt (m - 1), D.d _ _ y = x ∧ ‖y‖₊ ≤ (1 + ε) * ‖x‖₊

theorem weakExactOfFactorExact (k : ℝ≥0) [Fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0)
    (D : ℝ≥0 → CochainComplex SemiNormedGroupCat ℕ) (hD : ∀ c, c₀ ≤ c → NormExactComplex (D c))
    (f : ∀ c, C.obj (op <| k * c) ⟶ D c) (g : ∀ c, D c ⟶ C.obj (op c))
    (hf : ∀ c i, ((f c).f i).NormNoninc) (hg : ∀ c i, ((g c).f i).NormNoninc)
    (hfg : ∀ c, c₀ ≤ c → f c ≫ g c = C.map (homOfLE (Fact.out _ : c ≤ k * c)).op) :
    C.IsWeakBoundedExact k 1 m c₀ := by
  intro c hc i hi x ε' hε'
  let dx := C.d _ (i + 1) x
  let fx := (f _).f _ x
  let fdx := (f c).f _ dx
  let dfx := (D _).d _ (i + 1) fx
  have fdx_dfx : fdx = dfx := by simp only [fdx, dfx, fx, ← comp_apply]; congr 1;
    exact ((f _).comm _ _).symm
  have hfdx : (D _).d _ (i + 2) fdx = 0 := by
    calc
      (D _).d _ (i + 2) fdx = (D _).d _ (i + 2) ((D _).d _ (i + 1) fx) := congr_arg _ fdx_dfx
      _ = ((D _).d _ (i + 1) ≫ (D _).d _ (i + 2)) fx := rfl
      _ = 0 := by rw [(D c).d_comp_d _ _ _]; rfl
  let ε : ℝ≥0 := ⟨ε', hε'.le⟩
  have hε : 0 < ε := hε'
  let δ : ℝ≥0 := ε / (‖dx‖₊ + 1)
  have hδ : 0 < δ := by
    rw [← NNReal.coe_lt_coe]
    exact div_pos hε (lt_of_le_of_lt (NNReal.coe_nonneg _) (lt_add_one _))
  obtain ⟨x' : (D c).pt i, hdx' : (D c).d i (i + 1) x' = fdx, hnorm_x'⟩ := (hD _ hc.1) _ δ hδ _ hfdx
  let gx' := (g _).f _ x'
  have hdfxx' : (D _).d _ (i + 1) (fx - x') = 0 := by rw [_root_.map_sub, hdx', fdx_dfx];
    exact sub_self _
  obtain ⟨y, hdy, -⟩ := (hD _ hc.1) _ δ hδ _ hdfxx'
  let gy := (g _).f _ y
  let dgy := C.d _ i gy
  let gdy := (g _).f _ ((D _).d _ i y)
  have gdy_dgy : gdy = dgy := by simp only [gdy, dgy, gy, ← comp_apply]; congr 1;
    exact ((g _).comm _ _).symm
  refine' ⟨i - 1, i + 1, rfl, rfl, gy, _⟩
  simp only [NNReal.coe_one, one_mul]
  have hxdgy : res x - C.d _ _ gy = gx' :=
    by
    calc
      res x - dgy = (g _).f _ ((f _).f _ x) - gdy := _
      _ = gx' := by rw [← _root_.map_sub, hdy, sub_sub_cancel]
    rw [gdy_dgy, ← comp_apply, ← HomologicalComplex.comp_f, hfg _ hc.1]; rfl
  rw [hxdgy]
  change (‖gx'‖₊ : ℝ) ≤ ‖dx‖₊ + ε
  simp only [← NNReal.coe_add, NNReal.coe_le_coe]
  calc
    ‖gx'‖₊ ≤ ‖x'‖₊ := hg _ _ _
    _ ≤ (1 + δ) * ‖fdx‖₊ := hnorm_x'
    _ ≤ (1 + δ) * ‖dx‖₊ := (mul_le_mul' le_rfl (hf _ _ _))
    _ ≤ ‖dx‖₊ + δ * ‖dx‖₊ := by rw [add_mul, one_mul]
    _ ≤ ‖dx‖₊ + ε * 1 := (add_le_add le_rfl _)
    _ ≤ ‖dx‖₊ + ε := by rw [mul_one]
  dsimp only [δ]
  rw [div_eq_mul_inv, mul_assoc]
  refine' mul_le_mul' le_rfl _
  rw [NNReal.mul_le_iff_le_inv, inv_inv, mul_one]
  · exact (lt_add_one _).le
  · refine' inv_ne_zero (lt_of_le_of_lt _ (lt_add_one _)).ne'
    exact zero_le'

end SystemOfComplexes

namespace Thm95

variable (r' : ℝ) (V : SemiNormedGroupCat.{v}) (M : Type u) {M₁ M₂ : Type u} (N : ℕ) (d : ℝ≥0)

variable [ProfinitelyFilteredPseudoNormedGroup M] [PseudoNormedGroup.Splittable M N d]

variable [ProfinitelyFilteredPseudoNormedGroup M₁]

variable [ProfinitelyFilteredPseudoNormedGroup M₂]

variable (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) (hf : f.strict)

section

open Profinite PseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup

@[simps left right]
def fLCComplexArrow (c : ℝ≥0) : Arrow Profinite :=
  @Arrow.mk _ _ (filtrationObj M₁ c) (filtrationObj M₂ c) <|
    { toFun := PseudoNormedGroup.level f hf c
      continuous_toFun := f.continuous _ fun _ => rfl }

end

section

open ProfinitelyFilteredPseudoNormedGroup ComphausFilteredPseudoNormedGroup

@[simps obj map]
def fLCComplex : SystemOfComplexes
    where
  obj c := (fLCFunctor V).obj (op <| fLCComplexArrow f hf c.unop)
  map c₁ c₂ h :=
    (fLCFunctor V).map <|
      Quiver.Hom.op <|
        @Arrow.homMk _ _ (fLCComplexArrow f hf c₂.unop) (fLCComplexArrow f hf c₁.unop)
          ⟨_, (@embedding_castLe _ _ _ _ ⟨leOfHom h.unop⟩).continuous⟩
          ⟨_, (@embedding_castLe _ _ _ _ ⟨leOfHom h.unop⟩).continuous⟩ (by ext; rfl)
  map_id c := by
    convert (fLCFunctor V).map_id _
    simp only [unop_id, ← op_id, quiver.hom.op_inj.eq_iff, NatTrans.id_app]
    ext <;> rfl
  map_comp c₁ c₂ c₃ h1 h2 := by
    convert (fLCFunctor V).map_comp _ _
    simp only [← op_comp, quiver.hom.op_inj.eq_iff, NatTrans.comp_app]
    ext <;> rfl

end

namespace FLCComplex

open PseudoNormedGroup

variable (c₁ c₂ : ℝ≥0) [Fact (c₁ ≤ c₂)]

def AuxSpace (c₁ c₂ : ℝ≥0) [Fact (c₁ ≤ c₂)] :=
  { p : filtration M₂ c₁ × filtration M₁ c₂ // castLe p.1 = level f hf c₂ p.2 }

namespace AuxSpace

open ProfinitelyFilteredPseudoNormedGroup ComphausFilteredPseudoNormedGroup

instance : TopologicalSpace (AuxSpace f hf c₁ c₂) := by delta Thm95.fLCComplex.AuxSpace; infer_instance

instance : T2Space (AuxSpace f hf c₁ c₂) := by delta Thm95.fLCComplex.AuxSpace; infer_instance

instance : TotallyDisconnectedSpace (AuxSpace f hf c₁ c₂) :=
  Subtype.totallyDisconnectedSpace

instance : CompactSpace (AuxSpace f hf c₁ c₂)
    where compact_univ :=
    by
    rw [embedding_subtype_coe.isCompact_iff]
    simp only [Set.image_univ, Subtype.range_coe_subtype]
    refine' IsClosed.isCompact _
    refine'
      isClosed_eq ((ComphausFilteredPseudoNormedGroup.embedding_castLe _ _).continuous.comp continuous_fst)
        ((f.continuous _ _).comp continuous_snd)
    intro; rfl

end AuxSpace

def auxSpace : Profinite :=
  Profinite.of (AuxSpace f hf c₁ c₂)

namespace AuxSpace

open ProfinitelyFilteredPseudoNormedGroup

@[simps]
def ι : filtrationObj M₁ c₁ ⟶ auxSpace f hf c₁ c₂
    where
  toFun x := ⟨⟨level f hf c₁ x, Filtration.castLe M₁ c₁ c₂ x⟩, rfl⟩
  continuous_toFun := by
    rw [continuous_induced_rng]
    refine' Continuous.prod_mk (f.continuous _ fun _ => rfl) (Filtration.castLe M₁ c₁ c₂).continuous

@[simps]
def fst : auxSpace f hf c₁ c₂ ⟶ filtrationObj M₂ c₁
    where
  toFun := _
  continuous_toFun := continuous_fst.comp continuous_subtype_val

@[simps]
def snd : auxSpace f hf c₁ c₂ ⟶ filtrationObj M₁ c₂
    where
  toFun := _
  continuous_toFun := continuous_snd.comp continuous_subtype_val

@[simps left right]
def fstₐ : Arrow Profinite :=
  Arrow.mk (fst f hf c₁ c₂)

theorem fst_surjective [Fact (0 < N)] (h : c₁ / N + d ≤ c₂ * N⁻¹) :
    Function.Surjective (fst _ (sumHomStrict M N) c₁ c₂) :=
  by
  intro y
  dsimp at y 
  obtain ⟨x, hx1, hx2⟩ := exists_sum N d _ _ y.2
  simp only [fst_apply, Function.comp_apply]
  refine' ⟨⟨⟨y, ⟨x, _⟩⟩, _⟩, rfl⟩
  · erw [Rescale.mem_filtration]; refine' filtration_mono h hx2
  · simp only [PseudoNormedGroup.level, sum_hom_apply, Subtype.coe_mk, ← hx1]; rfl

end AuxSpace

open AuxSpace ProfinitelyFilteredPseudoNormedGroup

@[simps]
def sumHom₀ [Fact (0 < N)] (c : ℝ≥0) : filtrationObj (Rescale N (M ^ N)) c ⟶ filtrationObj M c :=
  ⟨PseudoNormedGroup.level (sumHom M N) (sumHomStrict M N) c,
    (sumHom M N).continuous _ fun _ => rfl⟩

@[simps left right hom]
def sumHomₐ [Fact (0 < N)] (c : ℝ≥0) : Arrow Profinite :=
  Arrow.mk (sumHom₀ M N c)

def sumHomₐFstₐ [Fact (0 < N)] : sumHomₐ M N c₁ ⟶ fstₐ _ (sumHomStrict M N) c₁ c₂
    where
  left := auxSpace.ι _ _ _ _
  right := 𝟙 _

def fstₐSumHomₐ [Fact (0 < N)] : fstₐ _ (sumHomStrict M N) c₁ c₂ ⟶ sumHomₐ M N c₂
    where
  left := snd _ _ _ _
  right := Filtration.castLe _ _ _
  w' := by ext1 ⟨x, h⟩; exact h.symm

theorem weakBoundedExact (k : ℝ≥0) [hk : Fact (1 ≤ k)] (m : ℕ) (c₀ : ℝ≥0) [Fact (0 < N)]
    (hdkc₀N : d ≤ (k - 1) * c₀ / N) :
    (fLCComplex V _ (sumHomStrict M N)).IsWeakBoundedExact k 1 m c₀ :=
  by
  let D c := (fLCFunctor V).obj (op <| fstₐ _ (ProfinitelyFilteredPseudoNormedGroup.sumHomStrict M N) c (k * c))
  let f c := (fLCFunctor V).map (fstₐ_sum_homₐ M N c (k * c)).op
  let g c := (fLCFunctor V).map (sum_homₐ_fstₐ M N c (k * c)).op
  refine' SystemOfComplexes.weakExactOfFactorExact _ k m c₀ D _ f g _ _ _
  · intro c hc
    suffices Function.Surjective (unop (op (fstₐ (sum_hom M N) _ c (k * c)))).hom
      by
      intro i ε hε x hx; cases i
      · simp only [Nat.one_ne_zero, HomologicalComplex.shape, ComplexShape.up_Rel, exists_and_left,
          not_false_iff, NormedAddGroupHom.zero_apply]
        refine' ⟨(prop819_degree_zero _ this _ x hx).symm, 0, _⟩
        simp only [nnnorm_zero, zero_le']
      exact prop819 _ this _ ε hε x hx
    refine' fst_surjective M N d c (k * c) _
    calc
      c / N + d ≤ c / N + (k - 1) * c₀ / N := add_le_add le_rfl hdkc₀N
      _ ≤ c / N + (k - 1) * c / N := (add_le_add le_rfl _)
      _ ≤ 1 * c / N + (k - 1) * c / N := by rw [one_mul]
      _ = k * c / N := _
    · simp only [div_eq_mul_inv]
      refine' mul_le_mul' (mul_le_mul' le_rfl hc) le_rfl
    · simp only [div_eq_mul_inv, mul_assoc]
      rw [← add_mul]; congr
      rw [← NNReal.eq_iff, NNReal.coe_add, NNReal.coe_sub hk.1, add_sub_cancel'_right]
  · intro c i; exact fLCFunctor_map_normNoninc _ _ _
  · intro c i; exact fLCFunctor_map_normNoninc _ _ _
  · intro c hc
    dsimp only [f, g, FLC_complex_map]
    rw [← CategoryTheory.Functor.map_comp, ← op_comp]
    rfl

end FLCComplex

end Thm95

