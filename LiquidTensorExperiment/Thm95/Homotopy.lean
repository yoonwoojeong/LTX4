import LiquidTensorExperiment.PolyhedralLattice.Hom
import LiquidTensorExperiment.Lbar.PseudoNormedGroup
import LiquidTensorExperiment.NormedSpectral
import LiquidTensorExperiment.PseudoNormedGroup.Homotopy
import LiquidTensorExperiment.Thm95.DoubleComplex
import LiquidTensorExperiment.Thm95.Constants.Default

#align_import thm95.homotopy

noncomputable section

universe u v

open scoped NNReal

-- enable the notation `ℝ≥0` for the nonnegative real numbers.
open PolyhedralLattice Opposite

open Thm95.UniversalConstants SystemOfDoubleComplexes CategoryTheory BreenDeligne

open ProFiltPseuNormGrpWithTinv (of)

section

variable (BD : Package)

variable (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' ≤ 1)]

variable (V : SemiNormedGroupCat.{v}) [NormedWithAut r V]

variable (κ κ' : ℕ → ℝ≥0) [BD.data.VerySuitable r r' κ]

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (m : ℕ)

variable (Λ : PolyhedralLatticeCat.{u})

def NSHAuxType (N : ℕ) (M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ) :=
  NormedSpectralHomotopy
    ((bDSystemMap (BD.data.Sum (2 ^ N)) κ (rescaleConstants κ (2 ^ N)) r V).app M) m (k' κ' m)
    (ε r r' BD κ' m) (c₀ r r' BD κ κ' m Λ) (h r r' BD κ' m)

section

variable {BD r r' V κ κ' m}

section nSHH

variable [Package.Adept BD κ κ']

def nSHH {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (q q' : ℕ) (c : ℝ≥0) :
    ((BD.data.system κ r V r').obj M) (k' κ' m * c) q' ⟶
      ((((Data.mul (2 ^ n₂ r r' BD κ' m)).obj BD.data).system
              (rescaleConstants κ (2 ^ n₂ r r' BD κ' m)) r V r').obj
          M)
        c q :=
  if hqm : q' ≤ m + 1 then
    by
    refine' (UniversalMap.evalCLCFPTinv _ _ _ _ _ _).app _
    · exact (Data.homotopyMul BD.data BD.homotopy (N₂ r r' BD κ' m)).hom q q'
    · dsimp
      refine' UniversalMap.Suitable.le _ _ (c * (κ' q' * κ q')) _ inferInstance le_rfl _
      calc
        c * (κ' q' * κ q') = κ' q' * (c * κ q') := mul_left_comm _ _ _
        _ ≤ k' κ' m * (c * κ q') := (mul_le_mul' (κ'_le_k' _ _ hqm) le_rfl)
        _ = k' κ' m * c * κ q' := (mul_assoc _ _ _).symm
  else 0

theorem norm_nSHH_le {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (q : ℕ) (hqm : q ≤ m) (c : ℝ≥0) :
    ‖(@nSHH BD r r' _ _ _ _ V _ κ κ' _ m _ M q (q + 1) c)‖ ≤ h r r' BD κ' m :=
  by
  rw [nSHH, dif_pos (Nat.succ_le_succ hqm)]
  apply UniversalMap.norm_evalCLCFPTinv₂_le
  exact bound_by_H r r' BD κ' _ hqm

end nSHH

instance NSH_δ_res' (N i : ℕ) (c : ℝ≥0) [hN : Fact (k' κ' m ≤ 2 ^ N)] :
    Fact (k' κ' m * c * rescaleConstants κ (2 ^ N) i ≤ c * κ i) :=
  by
  refine' ⟨_⟩
  calc
    k' κ' m * c * (κ i * (2 ^ N)⁻¹) = k' κ' m * (2 ^ N)⁻¹ * (c * κ i) := by ring1
    _ ≤ 1 * (c * κ i) := (mul_le_mul' _ le_rfl)
    _ = c * κ i := one_mul _
  apply mul_inv_le_of_le_mul
  rw [one_mul]
  exact hN.1

variable (κ')

@[simps f]
def nSHδRes {BD : Data} [BD.Suitable κ] {r r' : ℝ≥0} [Fact (0 < r)] [Fact (0 < r')] [Fact (r' ≤ 1)]
    {V : SemiNormedGroupCat.{u}} [NormedWithAut r V] (N : ℕ) [Fact (k' κ' m ≤ 2 ^ N)] (c : ℝ≥0)
    {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} :
    ((BD.system κ r V r').obj M).obj (op c) ⟶
      ((BD.system (rescaleConstants κ (2 ^ N)) r V r').obj M).obj (op (k' κ' m * c))
    where
  f i := (@cLCFPTinv.res r V _ _ r' _ _ _ _ _ (NSH_δ_res' _ _ _)).app M
  comm' := by
    intro i j hij
    dsimp [Data.system_obj, Data.complex]
    exact NatTrans.congr_app (UniversalMap.res_comp_evalCLCFPTinv r V r' _ _ _ _ _) M

variable {κ'}

def nSHδ {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) :
    ((BD.data.system κ r V r').obj M).obj (op c) ⟶
      ((((Data.mul (2 ^ n₂ r r' BD κ' m)).obj BD.data).system
                (rescaleConstants κ (2 ^ n₂ r r' BD κ' m)) r V r').obj
            M).obj
        (op (k' κ' m * c)) :=
  nSHδRes κ' (n₂ r r' BD κ' m) _ ≫ (bDMap (BD.data.proj (2 ^ n₂ r r' BD κ' m)) _ _ r V _).app M

theorem norm_nSHδ_le {M : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (c : ℝ≥0) (q : ℕ) :
    ‖((@nSHδ BD r r' _ _ _ _ V _ κ κ' _ m M c).f q)‖ ≤ ε r r' BD κ' m :=
  by
  refine'
    le_trans
      (NormedAddGroupHom.norm_comp_le_of_le' (r ^ b r r' BD κ' m) (N r r' BD κ' m) _ (mul_comm _ _)
        _ _)
      _
  · apply UniversalMap.norm_evalCLCFPTinv₂_le
    apply UniversalMap.proj_boundBy
  · refine' @cLCFPTinv.norm_res_le_pow r V _ _ r' _ _ _ _ _ _ _ ⟨_⟩ _
    dsimp only [unop_op, rescaleConstants]
    simp only [← mul_assoc, mul_right_comm _ c]
    simp only [mul_right_comm _ (κ q)]
    refine' mul_le_mul' _ le_rfl
    refine' mul_le_mul' _ le_rfl
    apply Thm95.UniversalConstants.n₂_spec
  · apply_mod_cast r_pow_b_le_ε

variable (V κ' m)

open HomologicalComplex CategoryTheory.Preadditive

end

variable [Package.Adept BD κ κ']

def nSHAux' (M) (hδ) : NSHAuxType BD r r' V κ κ' m Λ (n₂ r r' BD κ' m) M :=
  { h := fun q q' c => nSHH q q' c
    norm_h_le := by rintro q q' hqm rfl c hc; rw [NNReal.coe_nat_cast]; exact norm_nSHH_le q hqm c
    δ := nSHδ
    hδ
    norm_δ_le := fun c hc q hqm => by apply norm_nSHδ_le }

def nSHAux (M) : NSHAuxType BD r r' V κ κ' m Λ (n₂ r r' BD κ' m) M :=
  nSHAux' BD r r' V κ κ' m Λ M
    (by
      intro c hc q hqm
      haveI hqm_ : Fact (q ≤ m) := ⟨hqm⟩
      rw [nSHδ, nSHH, nSHH, dif_pos (Nat.succ_le_succ hqm), dif_pos (hqm.trans (Nat.le_succ _))]
      erw [HomologicalComplex.comp_f]
      dsimp only [unop_op, nSHδRes_f, Data.system_res_def, Quiver.Hom.apply, BD_system_map_app_app,
        BD_map_app_f, Data.system_obj_d]
      simp only [← UniversalMap.evalCLCFPTinv_def]
      have hcomm := (Data.homotopyMul BD.data BD.homotopy (N₂ r r' BD κ' m)).comm q
      simp only [UniversalMap.res_comp_evalCLCFPTinv_absorb, hcomm, ← NatTrans.app_add,
        add_assoc, ← NatTrans.comp_app, ← Category.assoc, ← UniversalMap.evalCLCFPTinv_comp,
        UniversalMap.evalCLCFPTinv_comp_res_absorb, ← UniversalMap.evalCLCFPTinv_add]
      congr 2
      rw [← add_assoc, add_comm, @prevD_eq _ _ _ _ _ _ _ _ q (q + 1)]
      swap; · dsimp; rfl
      congr 1
      rw [add_comm]
      congr 1
      rw [dNext_nat])

end

