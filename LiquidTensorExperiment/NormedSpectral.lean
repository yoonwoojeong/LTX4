import LiquidTensorExperiment.SystemOfComplexes.Double
import LiquidTensorExperiment.SystemOfComplexes.Truncate
import LiquidTensorExperiment.NormedSnake
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import LiquidTensorExperiment.Thm95.Constants.SpectralConstants

#align_import SystemOfDoubleComplexes.normedSpectral

noncomputable section

open scoped NNReal

open CategoryTheory

universe u

namespace SystemOfDoubleComplexes

@[simps]
def truncate : SystemOfDoubleComplexes.{u} ⥤ SystemOfDoubleComplexes.{u} :=
  (whiskeringRight _ _ _).obj <|
    @Functor.mapHomologicalComplex _ _ _ _ _ _ _ _ SemiNormedGroupCat.truncate.additive.{u} _

-- TODO: why do I need to give the instance manually? ↑ ↑ ↑
namespace Truncate

variable (M : SystemOfDoubleComplexes.{u})

-- defeq abuse for the win!!!
theorem row (p : ℕ) : (Truncate.obj M).row p = SystemOfComplexes.truncate.obj (M.row p) :=
  rfl

theorem col_pos (q : ℕ) : (Truncate.obj M).col (q + 1) = M.col (q + 1 + 1) :=
  rfl

@[simp]
theorem d'_zero_one (c : ℝ≥0) (p : ℕ) (x : M.pt c p 1) :
    (Truncate.obj M).d' 0 1 (SemiNormedGroupCat.explicitCokernelπ _ x) = M.d' 1 2 x :=
  rfl

@[simp]
theorem d_π (c : ℝ≥0) (p p' : ℕ) (x : M.pt c p 1) :
    @d (Truncate.obj M) _ p p' 0 (SemiNormedGroupCat.explicitCokernelπ _ x) =
      SemiNormedGroupCat.explicitCokernelπ _ (M.d p p' x) :=
  rfl

@[simp]
theorem res_π (c₁ c₂ : ℝ≥0) (p : ℕ) (h : Fact (c₁ ≤ c₂)) (x : M.pt c₂ p 1) :
    @res (Truncate.obj M) _ _ p 0 h (SemiNormedGroupCat.explicitCokernelπ _ x) =
      SemiNormedGroupCat.explicitCokernelπ _ (M.res x) :=
  rfl

def quotientMap : M.col 1 ⟶ (Truncate.obj M).col 0
    where
  app c :=
    { f := fun p => SemiNormedGroupCat.explicitCokernelπ _
      comm' := fun p p' _ => by ext; rfl }
  naturality := by intros; ext; rfl

theorem admissible (hM : M.Admissible) : (Truncate.obj M).Admissible :=
  { d_norm_noninc' := fun c p' p q h => by
      cases q
      · apply SemiNormedGroupCat.explicitCokernelDesc_normNoninc
        exact (SemiNormedGroupCat.normNoninc_explicitCokernelπ _).comp (hM.d_normNoninc _ _ _ _)
      · exact hM.d_normNoninc c p' p _
    d'_norm_noninc' := fun c p => ((M.row p).truncateAdmissible (hM.row p)).d_norm_noninc' c
    res_normNoninc := fun c₁ c₂ p =>
      ((M.row p).truncateAdmissible (hM.row p)).res_normNoninc c₁ c₂ }

end Truncate

open Opposite

structure NormedSpectralHomotopy {row₀ row₁ : SystemOfComplexes.{u}} (d : row₀ ⟶ row₁) (m : ℕ)
    (k' ε : ℝ≥0) [Fact (1 ≤ k')] (c₀ H : ℝ≥0) [Fact (0 < H)] where
  h : ∀ (q : ℕ) {q' : ℕ} {c}, row₀ (k' * c) q' ⟶ row₁ c q
  norm_h_le :
    ∀ (q q' : ℕ) (hq : q ≤ m) (hq' : q + 1 = q') (c) [Fact (c₀ ≤ c)],
      ‖(h q : row₀ (k' * c) q' ⟶ row₁ c q)‖ ≤ H
  δ : ∀ c : ℝ≥0, row₀.obj (op <| c) ⟶ row₁.obj (op <| k' * c)
  hδ :
    ∀ (c : ℝ≥0) [Fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m),
      (SystemOfComplexes.res : row₀ (k' * (k' * c)) q ⟶ _) ≫ (δ c).f q =
        d.apply ≫ SystemOfComplexes.res + row₀.d q (q + 1) ≫ h q + h (q - 1) ≫ row₁.d (q - 1) q
  norm_δ_le : ∀ (c : ℝ≥0) [Fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m), ‖((δ c).f q)‖ ≤ ε

theorem NormedSpectralHomotopy.hδ_apply {row₀ row₁ : SystemOfComplexes.{u}} {d : row₀ ⟶ row₁}
    {m : ℕ} {k' ε : ℝ≥0} [Fact (1 ≤ k')] {c₀ H : ℝ≥0} [Fact (0 < H)]
    (NSH : NormedSpectralHomotopy d m k' ε c₀ H) (c : ℝ≥0) [Fact (c₀ ≤ c)] (q : ℕ) (hq : q ≤ m)
    (x : row₀ (k' * (k' * c)) q) :
    (NSH.δ c).f q (SystemOfComplexes.res x) =
      SystemOfComplexes.res (d x) + NSH.h q (row₀.d q (q + 1) x) +
        row₁.d (q - 1) q (NSH.h (q - 1) x) :=
  by
  show ((SystemOfComplexes.res : row₀ (k' * (k' * c)) q ⟶ _) ≫ (NSH.δ c).f q) x = _
  rw [NSH.hδ c q hq]
  dsimp; rfl

def NormedSpectralHomotopy.ofIso {row₀ row₁ : SystemOfComplexes.{u}} {d : row₀ ⟶ row₁} {m : ℕ}
    {k' ε : ℝ≥0} [Fact (1 ≤ k')] {c₀ H : ℝ≥0} [Fact (0 < H)]
    (NSH : NormedSpectralHomotopy d m k' ε c₀ H) (row'₀ row'₁ : SystemOfComplexes.{u})
    (d' : row'₀ ⟶ row'₁) (φ₀ : row₀ ≅ row'₀) (φ₁ : row₁ ≅ row'₁)
    (hφ₀ : ∀ (c i) (x : row'₀ c i), ‖φ₀.inv x‖ = ‖x‖)
    (hφ₁ : ∀ (c i) (x : row₁ c i), ‖φ₁.hom x‖ = ‖x‖)
    (hcomm : d' = φ₀.inv ≫ d ≫ φ₁.hom) : NormedSpectralHomotopy d' m k' ε c₀ H
    where
  h q q' c := φ₀.inv.apply ≫ NSH.h q ≫ φ₁.hom.apply
  δ c := φ₀.inv.app (op <| c) ≫ NSH.δ c ≫ φ₁.hom.app (op <| k' * c)
  norm_h_le := by
    intro q q' hqm hq' c hc
    refine' NormedAddGroupHom.opNorm_le_bound _ (NNReal.coe_nonneg H) fun x => _
    calc
      ‖(φ₁.hom (NSH.h q (φ₀.inv x)))‖ = ‖(NSH.h q (φ₀.inv x))‖ := hφ₁ _ _ _
      _ ≤ ↑H * ‖φ₀.inv x‖ :=
        (NormedAddGroupHom.le_of_opNorm_le _ (NSH.norm_h_le _ _ hqm hq' _) (φ₀.inv x))
      _ = ↑H * ‖x‖ := congr_arg _ (hφ₀ _ _ _)
  hδ := by
    intro c hc q hq
    ext1 x
    have := congr_arg (fun x => φ₁.hom x) (NSH.hδ_apply c q hq (φ₀.inv x))
    simp only [coe_comp, hcomm, SystemOfComplexes.res_apply, SystemOfComplexes.d_apply] at this ⊢
    refine' this.trans _; clear this
    calc
      φ₁.hom
            (d (φ₀.inv (SystemOfComplexes.res x)) + (NSH.h q) (φ₀.inv (row'₀.d q (q + 1) x)) +
              (row₁.d (q - 1) q) (NSH.h (q - 1) (φ₀.inv x))) =
          φ₁.hom (d (φ₀.inv (SystemOfComplexes.res x)) + (NSH.h q) (φ₀.inv (row'₀.d q (q + 1) x))) +
            φ₁.hom ((row₁.d (q - 1) q) (NSH.h (q - 1) (φ₀.inv x))) :=
        _
      _ = _ := _
    · apply NormedAddGroupHom.map_add'
    congr 1
    · refine' (NormedAddGroupHom.map_add' _ _ _).trans _
      simp only [← comp_apply, ← SystemOfComplexes.res_comp_apply]; rfl
    · erw [SystemOfComplexes.d_apply]; rfl
  norm_δ_le c hc q hq := by
    skip
    refine' NormedAddGroupHom.opNorm_le_bound _ (NNReal.coe_nonneg ε) _
    rintro (x : row'₀ c q)
    calc
      ‖(φ₁.hom ((NSH.δ c).f q (φ₀.inv x)))‖ = ‖((NSH.δ c).f q (φ₀.inv x))‖ :=
        hφ₁ _ _ _
      _ ≤ ↑ε * ‖φ₀.inv x‖ :=
        (NormedAddGroupHom.le_of_opNorm_le _ (NSH.norm_δ_le _ _ hq) (φ₀.inv x))
      _ = ↑ε * ‖x‖ := congr_arg _ (hφ₀ _ _ _)

/-- The assumptions on `M` in Proposition 9.6 bundled into a structure. -/
structure NormedSpectralConditions (M : SystemOfDoubleComplexes.{u}) (m : ℕ) (k K k' ε : ℝ≥0)
    [Fact (1 ≤ k)] [Fact (1 ≤ k')] (c₀ H : ℝ≥0) [Fact (0 < H)] where
  rowExact : 0 < m → ∀ i ≤ m + 1, (M.row i).IsWeakBoundedExact k K (m - 1) c₀
  colExact : ∀ j ≤ m, (M.col j).IsWeakBoundedExact k K m c₀
  htpy : NormedSpectralHomotopy (M.rowMap 0 1) m k' ε c₀ H
  -- ergonomics: we bundle this assumption, instead of passing it around separately
  Admissible : M.Admissible

namespace NormedSpectralConditions

variable {M : SystemOfDoubleComplexes.{u}}

variable {m : ℕ} {k K k' ε k₀ : ℝ≥0}

variable [Fact (1 ≤ k)] [Fact (1 ≤ k₀)] [Fact (k₀ ≤ k')] [Fact (1 ≤ k')]

variable {c₀ H : ℝ≥0} [Fact (0 < H)]

theorem truncateAdmissible (condM : M.NormedSpectralConditions m k K k' ε c₀ H) :
    (Truncate.obj M).Admissible :=
  truncate.admissible _ condM.Admissible

variable (condM : M.NormedSpectralConditions (m + 1) k K k' ε c₀ H)

theorem colZeroExact :
    ((Truncate.obj M).col 0).IsWeakBoundedExact (k * k * k) (K * (K * K + 1)) m c₀ :=
  by
  apply
    weakNormedSnake (M.col 0) (M.col 1) ((Truncate.obj M).col 0) (M.col_map 0 1)
      (truncate.quotientMap M) (condM.colExact 0 (by decide)) (condM.colExact 1 (by decide))
      (condM.admissible.col 1)
  · intro c p; exact condM.admissible.d'_normNoninc c p 0 1
  · intro c hc i hi x
    apply le_of_forall_pos_le_add
    intro ε' hε'
    -- should we factor out a dedicated `weak_bounded_in_degrees_le_zero` lemma?
    simpa only [exists_prop, row_res, d'_self_apply, exists_eq_left, sub_zero, exists_and_left,
      zero_add, row_d, exists_eq_left', exists_const] using
      condM.row_exact (Nat.zero_lt_succ _) i hi c hc 0 (Nat.zero_le _) x ε' hε'
  · intro c i; apply QuotientAddGroup.ker_mk'
  · intro c p; exact SemiNormedGroupCat.isQuotient_explicitCokernelπ _

-- morally `q'` is `q + 1`
def hTruncate :
    ∀ (q : ℕ) {q' : ℕ} {c : ℝ≥0}, (Truncate.obj M).pt (k' * c) 0 q' ⟶ (Truncate.obj M).pt c 1 q
  | 0, 1, c => condM.htpy.h 1 ≫ SemiNormedGroupCat.explicitCokernelπ _
  | q + 1, q' + 1, c => condM.htpy.h (q + 2)
  | _, _, _ => 0

@[simp]
theorem hTruncate_zero {c : ℝ≥0} (x : (Truncate.obj M).pt (k' * c) 0 1) :
    condM.hTruncate 0 x = SemiNormedGroupCat.explicitCokernelπ _ (condM.htpy.h 1 x) :=
  rfl

theorem norm_hTruncate_le :
    ∀ q q' : ℕ,
      q ≤ m →
        q + 1 = q' →
          ∀ c : ℝ≥0,
            Fact (c₀ ≤ c) →
              ‖(condM.hTruncate q : (Truncate.obj M).pt (k' * c) 0 q' ⟶ _)‖ ≤ H
  | q + 1, q' + 1, hq, rfl =>
    condM.htpy.norm_h_le _ _ (Nat.succ_le_succ hq) (by simp only [Nat.add_def, add_zero])
  | 0, 1, hq, rfl => by
    intro c hc
    refine' NormedAddGroupHom.opNorm_le_bound _ (NNReal.coe_nonneg H) fun x => _
    calc
      _ = ‖(SemiNormedGroupCat.explicitCokernelπ _ (condM.htpy.h 1 x))‖ := rfl
      _ ≤ ‖condM.htpy.h 1 x‖ :=
        ((SemiNormedGroupCat.isQuotient_explicitCokernelπ _).norm_le _)
      _ ≤ H * ‖x‖ :=
        NormedAddGroupHom.le_of_opNorm_le _ (condM.htpy.norm_h_le 1 2 (by decide) rfl c) x

def δTruncate (c : ℝ≥0) :
    ((Truncate.obj M).row 0).obj (op <| c) ⟶ ((Truncate.obj M).row 1).obj (op <| k' * c) :=
  SemiNormedGroupCat.Truncate.map (condM.htpy.δ c)

theorem hδ_truncate (c : ℝ≥0) [Fact (c₀ ≤ c)] :
    ∀ (q : ℕ) (hq : q ≤ m),
      (Truncate.obj M).res ≫ (condM.δTruncate c).f q =
        d _ 0 1 ≫ (Truncate.obj M).res + d' _ q (q + 1) ≫ condM.hTruncate q +
          condM.hTruncate (q - 1) ≫ d' _ (q - 1) q
  | 1, h => condM.htpy.hδ _ _ (Nat.succ_le_succ h)
  | q + 2, h => condM.htpy.hδ _ _ (Nat.succ_le_succ h)
  | 0, h => by
    ext x; dsimp
    let π c p := SemiNormedGroupCat.explicitCokernelπ (@d' M c p 0 1)
    obtain ⟨y, hy⟩ : ∃ x', π _ _ x' = SemiNormedGroupCat.explicitCokernelπ _ x :=
      SemiNormedGroupCat.explicitCokernelπ_surjective (SemiNormedGroupCat.explicitCokernelπ _ x)
    trans π _ _ ((condM.htpy.δ c).f 1 (M.res x)); · rfl
    erw [condM.htpy.hδ_apply _ _ (Nat.succ_le_succ h) x]
    simp only [Nat.zero_sub, d'_self_apply, add_zero, row_d, truncate.d_π, truncate.res_π,
      truncate.d'_zero_one, SystemOfDoubleComplexes.NormedSpectralConditions.hTruncate_zero, map_add,
      SemiNormedGroupCat.explicitCokernelπ_apply_dom_eq_zero]
    rfl

theorem norm_δTruncate_le (c : ℝ≥0) [Fact (c₀ ≤ c)] :
    ∀ (q : ℕ) (hq : q ≤ m), ‖((condM.δTruncate c).f q)‖ ≤ ε
  | q + 1, h => condM.htpy.norm_δ_le c (q + 2) (Nat.succ_le_succ h)
  | 0, h =>
    by
    refine'
      SemiNormedGroupCat.explicitCokernelDesc_norm_le_of_norm_le _ _
        (NormedAddGroupHom.opNorm_le_bound _ (NNReal.coe_nonneg ε) fun x => _)
    refine' (SemiNormedGroupCat.normNoninc_explicitCokernelπ _ _).trans _
    exact NormedAddGroupHom.le_of_opNorm_le _ (condM.htpy.norm_δ_le c _ (Nat.succ_le_succ h)) _

def truncate : (Truncate.obj M).NormedSpectralConditions m (k * k * k) (K * (K * K + 1)) k' ε c₀ H
    where
  rowExact := by
    intro hm i hi
    cases m; · exact (Nat.not_lt_zero _ hm).elim
    suffices ((Truncate.obj M).row i).IsWeakBoundedExact k K m c₀ by
      apply this.of_le (condM.truncateAdmissible.row i) _ _ le_rfl ⟨le_rfl⟩ <;> infer_instance
    rw [truncate.row]
    apply (M.row i).truncateIsWeakBoundedExact
    · refine' condM.row_exact (Nat.zero_lt_succ _) i (hi.trans (Nat.le_succ _))
  colExact := by
    rintro (j | j) hj
    · exact condM.colZeroExact
    · rw [truncate.col_pos]
      refine'
          (condM.colExact (j + 2) (Nat.succ_le_succ hj)).of_le (condM.admissible.col (j + 2)) _ _
            m.le_succ ⟨le_rfl⟩ <;>
        infer_instance
  htpy :=
    { h := condM.hTruncate
      norm_h_le := condM.norm_hTruncate_le
      δ := condM.δTruncate
      hδ := condM.hδ_truncate
      norm_δ_le := condM.norm_δTruncate_le }
  Admissible := condM.truncateAdmissible

variable {m_ : ℕ} {k_ K_ : ℝ≥0} [Fact (1 ≤ k_)]

variable {ε_ : ℝ≥0} {k₀_ : ℝ≥0} [Fact (1 ≤ k₀_)]

variable [Fact (k₀_ ≤ k')] {c₀_ H_ : ℝ≥0} [Fact (0 < H_)]

def ofLe (cond : M.NormedSpectralConditions m k K k' ε c₀ H) (hm : m_ ≤ m) (hk : Fact (k ≤ k_))
    (hK : Fact (K ≤ K_)) (hε : ε ≤ ε_) (hc₀ : Fact (c₀ ≤ c₀_)) (hH : H ≤ H_) :
    M.NormedSpectralConditions m_ k_ K_ k' ε_ c₀_ H_
    where
  colExact j hj := (cond.colExact j (hj.trans hm)).of_le (cond.Admissible.col j) hk hK hm hc₀
  rowExact hm_ i hi :=
    (cond.rowExact (hm_.trans_le hm) i (hi.trans <| Nat.succ_le_succ hm)).of_le
      (cond.Admissible.row i) hk hK (Nat.pred_le_pred hm) hc₀
  htpy :=
    { h := cond.htpy.h
      norm_h_le := fun q q' hq hq' c hc =>
        by
        have : Fact (c₀ ≤ c) := ⟨hc₀.out.trans hc.out⟩
        refine' NormedAddGroupHom.opNorm_le_bound _ (NNReal.coe_nonneg H_) fun x => _
        calc
          ‖cond.htpy.h q x‖ ≤ H * ‖x‖ :=
            NormedAddGroupHom.le_of_opNorm_le _ (cond.htpy.norm_h_le q q' (hq.trans hm) hq' c) x
          _ ≤ H_ * ‖x‖ := mul_le_mul_of_nonneg_right hH (norm_nonneg x)
      δ := cond.htpy.δ
      hδ := fun c hc q hq =>
        have : Fact (c₀ ≤ c) := ⟨hc₀.out.trans hc.out⟩
        cond.htpy.hδ c q (hq.trans hm)
      norm_δ_le := fun c hc q hq =>
        by
        have : Fact (c₀ ≤ c) := ⟨hc₀.out.trans hc.out⟩
        refine' NormedAddGroupHom.opNorm_le_bound _ (NNReal.coe_nonneg ε_) fun x => _
        refine' NormedAddGroupHom.le_of_opNorm_le _ _ x
        exact le_trans (cond.htpy.norm_δ_le c q (hq.trans hm)) hε }
  Admissible := cond.Admissible

end NormedSpectralConditions

namespace NormedSpectral

/-- Base case of the induction for Proposition 9.6. -/
theorem base (c₀ H : ℝ≥0) [Fact (0 < H)] (M : SystemOfDoubleComplexes.{u}) (k K k' : ℝ≥0)
    [hk : Fact (1 ≤ k)] [hK : Fact (1 ≤ K)] [Fact (k₀ 0 k ≤ k')] [Fact (1 ≤ k')]
    (cond : M.NormedSpectralConditions 0 k K k' (ε 0 K) c₀ H) :
    (M.row 0).IsWeakBoundedExact (k' * k') (2 * k₀ 0 K * H) 0 c₀ :=
  by
  dsimp [k₀, K₀]
  intro c hc i hi
  interval_cases; clear hi
  intro x ε' hε'
  let φ : ℝ := ε' / 2
  have hφ : 0 < φ := div_pos hε' zero_lt_two
  have hδφ : ε' = φ + φ := by dsimp [φ]; rw [← add_div, half_add_self]
  haveI : Fact (k' * (k' * c) ≤ k' * k' * c) := by rw [mul_assoc]; exact ⟨le_rfl⟩
  have Hx1 :=
    (cond.colExact 0 le_rfl).of_le (cond.admissible.col 0) ‹_› ⟨le_rfl⟩ le_rfl ⟨le_rfl⟩ c hc 0
      le_rfl
  have Hx2 := NormedAddGroupHom.le_of_opNorm_le _ (cond.htpy.norm_δ_le c 0 le_rfl) (M.res x)
  have aux := cond.htpy.hδ_apply c 0 le_rfl (M.res x)
  erw [res_res] at aux 
  rw [aux] at Hx2 
  simp only [row_d, col_d, d_self_apply, d'_self_apply, sub_zero, add_zero, smul_zero, d_res,
    d'_res, res_res, one_div, row_res, Units.val_one, one_smul, SystemOfDoubleComplexes.rowMap_apply] at Hx1 Hx2 ⊢
  refine' ⟨0, 1, rfl, rfl, 0, _⟩
  obtain ⟨i, j, hi, hj, y1, hx1⟩ := Hx1 (M.res x) φ hφ
  simp [← eq_neg_iff_add_eq_zero] at hi hj ; subst i; subst j
  simp only [d_self_apply, d'_self_apply, sub_zero, NNReal.coe_mul, NNReal.coe_bit0, NNReal.coe_one,
    d_res] at hx1 ⊢
  erw [res_res] at hx1 
  clear y1 Hx1
  replace Hx1 := mul_le_mul_of_nonneg_left hx1 (ε 0 K).coe_nonneg
  replace Hx2 := (norm_le_add_norm_add _ _).trans (add_le_add (Hx2.trans Hx1) le_rfl)
  dsimp [ε] at Hx2 
  have K0 : (K : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK.out)
  simp only [mul_add, add_assoc, mul_inv, mul_assoc, inv_mul_cancel_left₀ K0] at Hx2 
  simp only [← div_eq_inv_mul, sub_half, ← sub_le_iff_le_add'] at Hx2 
  simp only [sub_le_iff_le_add', div_le_iff' (zero_lt_two : (0 : ℝ) < 2)] at Hx2 
  replace Hx2 := mul_le_mul_of_nonneg_left Hx2 K.coe_nonneg
  simp only [mul_add, div_eq_inv_mul, add_comm φ, mul_inv_cancel_left₀ (two_ne_zero : (2 : ℝ) ≠ 0),
    mul_inv_cancel_left₀ K0] at Hx2 
  refine' hx1.trans _
  simp only [mul_comm (2 : ℝ) K, mul_assoc, hδφ, ← add_assoc, ← mul_add, add_le_add_iff_right]
  refine' Hx2.trans _
  simp only [add_le_add_iff_right]
  refine' mul_le_mul_of_nonneg_left _ K.coe_nonneg
  refine' mul_le_mul_of_nonneg_left _ zero_le_two
  refine' le_trans (NormedAddGroupHom.le_of_opNorm_le _ (cond.htpy.norm_h_le _ _ le_rfl rfl _) _) _
  refine' mul_le_mul_of_nonneg_left (le_of_eq _) H.coe_nonneg
  apply norm_res_of_eq
  rw [mul_assoc]

end NormedSpectral

open NormedSpectral

/-- Proposition 9.6 in [Analytic] -/
theorem normedSpectral {m : ℕ} {c₀ H : ℝ≥0} [Fact (0 < H)] {M : SystemOfDoubleComplexes.{u}}
    {k K k' : ℝ≥0} [Fact (1 ≤ k)] [hK : Fact (1 ≤ K)] [Fact (k₀ m k ≤ k')] [Fact (1 ≤ k')]
    (cond : M.NormedSpectralConditions m k K k' (ε m K) c₀ H) :
    (M.row 0).IsWeakBoundedExact (k' * k') (2 * k₀ m K * H) m c₀ :=
  by
  revert M k K k'
  induction' m with m IH; · exact base c₀ H
  dsimp [ε, k₀, K₀]
  intro M k K k' _ _ _ _ cond
  rw [← SystemOfComplexes.truncate_isWeakBoundedExact_iff]
  · exact IH cond.truncate
  · refine'
      @IH M (k * k * k) (K * (K * K + 1)) k' _ _ _ _
        (cond.of_le m.le_succ _ _ le_rfl ⟨le_rfl⟩ le_rfl)
    all_goals infer_instance

end SystemOfDoubleComplexes

