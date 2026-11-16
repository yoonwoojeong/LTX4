import Mathlib.Algebra.Homology.Homotopy
import LiquidTensorExperiment.BreenDeligne.Category
import LiquidTensorExperiment.BreenDeligne.Suitable

#align_import breen_deligne.homotopy

namespace BreenDeligne

open CategoryTheory CategoryTheory.Limits FreeAbelianGroup HomologicalComplex FreeMat

open scoped BigOperators NNReal ZeroObject

namespace Data

variable (BD : Data)

-- generalize this to something like `functor.map_homotopy`
@[simps]
def homotopyTwoMul {BD₁ BD₂ : Data} {f g : BD₁ ⟶ BD₂} (h : Homotopy f g) :
    Homotopy ((mul 2).map f) ((mul 2).map g)
    where
  hom j i := UniversalMap.mul 2 (h.hom j i)
  -- Porting note: `dsimp only` beta-reduces the field before rewriting
  zero i j hij := by dsimp only; rw [h.zero i j hij, AddMonoidHom.map_zero]
  comm := by
    intro j
    simp only [mul_map_f, h.comm j, AddMonoidHom.map_add]
    congr 2 <;> · erw [UniversalMap.hMul_comp]; rfl

def homotopyPow' (h : Homotopy (BD.proj 2) (BD.sum 2)) :
    ∀ N, Homotopy (homPow' (BD.proj 2) N) (homPow' (BD.sum 2) N)
  | 0 => Homotopy.refl _
  | N + 1 => (homotopyTwoMul (homotopyPow' h N)).comp h

def homotopyMul (h : Homotopy (BD.proj 2) (BD.sum 2)) (N : ℕ) :
    Homotopy (BD.proj (2 ^ N)) (BD.sum (2 ^ N)) :=
  (Homotopy.ofEq (BD.homPow'_proj N).symm).trans <|
    ((BD.homotopyPow' h N).compLeft (BD.pow'IsoMul N).inv).trans <|
      Homotopy.ofEq <| BD.homPow'_sum N

end Data

/-- A Breen--Deligne `package` consists of Breen--Deligne `data`
that forms a complex, together with a `homotopy`
between the two universal maps `σ_add` and `σ_proj`. -/
structure Package where
  data : Data
  homotopy : Homotopy (data.proj 2) (data.sum 2)

namespace Package

class Adept (BD : outParam Package) (κ : outParam <| ℕ → ℝ≥0) (κ' : ℕ → ℝ≥0) : Prop where
  htpy_suitable' :
    ∀ i, (BD.homotopy.hom i (i + 1)).Suitable (rescaleConstants κ 2 i) (κ' (i + 1) * κ (i + 1))

instance Adept.htpy_suitable (BD : Package) (κ κ' : ℕ → ℝ≥0) [Adept BD κ κ'] (j i : ℕ) :
    (BD.homotopy.hom j i).Suitable (rescaleConstants κ 2 j) (κ' i * κ i) :=
  by
  by_cases hij : j + 1 = i
  · rw [← hij]; apply Adept.htpy_suitable'
  · rw [BD.homotopy.zero]
    · infer_instance
    · exact hij

namespace Adept

open CategoryTheory

-- Porting note: `mulCongr` is a Lean 4 specific iso (see `Data.mulCongr`), so we need to
-- know that its components are suitable.
theorem mulCongr_inv_suitable (BD : Data) {a b : ℕ} (h : a = b) (j : ℕ) (c : ℝ≥0) :
    ((BD.mulCongr h).inv.f j).Suitable c c := by
  subst h
  simp only [Data.mulCongr, eqToIso.inv, eqToHom_refl, HomologicalComplex.id_f]
  exact UniversalMap.suitable_id _

variable (BD : Package) (κ κ' : ℕ → ℝ≥0) [Adept BD κ κ']

-- instance mul_adept_suitable (N : ℕ) (f : (data.mul N).obj BD.data ⟶ BD.data) (i : ℕ) (c₁ : ℝ≥0)
--   [hf : universal_map.suitable c₁ (κ i) (f.f i)] :
--   universal_map.suitable c₁ ((κ' * κ) i) (f.f i) :=
-- begin
--   refine hf.le _ _ _ _ le_rfl _,
--   dsimp,
--   apply fact.out
-- end
instance homotopyPow'_suitable (j i : ℕ) :
    ∀ N,
      ((BD.data.homotopyPow' BD.homotopy N).hom j i).Suitable (rescaleConstants κ (2 ^ N) j)
        ((κ' * κ) i)
  | 0 => UniversalMap.suitable_zero _ _
  | N + 1 => by
    dsimp [Data.homotopyPow']
    refine' @UniversalMap.suitable_add _ _ _ _ _ _ (id _) (id _)
    · refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ (κ' i * κ i) _ _ (id _)
      refine' @UniversalMap.hMul_suitable _ _ _ _ _ (id _) _ ⟨two_pos⟩
      -- Porting note: the recursive call takes `j i N` only (BD κ κ' are fixed)
      refine' (homotopyPow'_suitable j i N).le _ _ _ _ _ le_rfl
      calc
        rescaleConstants κ (2 ^ (N + 1)) j = κ j * (2⁻¹ * (2 ^ N)⁻¹) := by
          simp only [rescaleConstants, pow_succ, mul_inv]
        _ ≤ κ j * (1 * (2 ^ N)⁻¹) := (mul_le_mul' le_rfl (mul_le_mul' (by norm_num) le_rfl))
        _ = κ j * (2 ^ N)⁻¹ := by rw [one_mul]
    · refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ (rescaleConstants κ 2 j) _ _ (id _)
      refine' @UniversalMap.hMul_suitable _ _ _ _ _ (id _) 2 ⟨zero_lt_two⟩
      simp only [rescaleConstants, pow_succ, mul_inv]
      rw [← mul_assoc, mul_right_comm]
      exact @UniversalMap.suitable_hMul_right _ _ _ _ _ _ _

instance homotopyMul_suitable (j i N : ℕ) :
    ((BD.data.homotopyMul BD.homotopy N).hom j i).Suitable (rescaleConstants κ (2 ^ N) j)
      ((κ' * κ) i) :=
  by
  dsimp [Data.homotopyMul, Homotopy.trans_hom]
  simp only [add_zero, zero_add]
  -- Porting note: the instance for the homotopy is passed explicitly, since `(κ' * κ) i` and
  -- `κ' i * κ i` are no longer unified during instance synthesis
  refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ (rescaleConstants κ (2 ^ N) j) _
    (homotopyPow'_suitable BD κ κ' j i N) (id _)
  generalize rescaleConstants κ (2 ^ N) j = c
  induction' N with N IH
  · dsimp [Data.pow'IsoMul, Data.mulOneIso, FreeMat.oneMulIso]
    -- jmc: I don't understand why TC doesn't find the following instance...
    exact @UniversalMap.suitable_of _ _ _ _ _ (BasicUniversalMap.oneMulHom_suitable _)
  · dsimp [Data.pow'IsoMul]; haveI : Fact (0 < 2) := ⟨two_pos⟩
    skip
    refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ c _ (id _) (id _)
    · erw [Data.mul_map_f]
      infer_instance
    · dsimp [Data.mulMulIso, FreeMat.mulMulIso]
      erw [HomologicalComplex.comp_f]
      refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ c _ (id _) (id _)
      · -- Porting note: unfold the component of the iso by hand
        show UniversalMap.Suitable c c (FreeAbelianGroup.of (BasicUniversalMap.mulMulInv 2 (2 ^ N) _))
        infer_instance
      · exact mulCongr_inv_suitable _ _ _ _

end Adept

end Package

end BreenDeligne

