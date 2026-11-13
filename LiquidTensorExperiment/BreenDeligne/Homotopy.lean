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
  Hom j i := UniversalMap.mul 2 (h.hom j i)
  zero' i j hij := by rw [h.zero i j hij, AddMonoidHom.map_zero]
  comm := by
    intro j
    simp only [mul_map_f, h.comm j, AddMonoidHom.map_add]
    congr 2 <;> · erw [UniversalMap.hMul_comp]; rfl

def homotopyPow' (h : Homotopy (BD.proj 2) (BD.Sum 2)) :
    ∀ N, Homotopy (homPow' (BD.proj 2) N) (homPow' (BD.Sum 2) N)
  | 0 => Homotopy.refl _
  | N + 1 => (homotopyTwoMul (BreenDeligne.Data.homotopyPow' N)).comp h

def homotopyMul (h : Homotopy (BD.proj 2) (BD.Sum 2)) (N : ℕ) :
    Homotopy (BD.proj (2 ^ N)) (BD.Sum (2 ^ N)) :=
  (Homotopy.ofEq (BD.homPow'_proj N).symm).trans <|
    ((BD.homotopyPow' h N).compLeft (BD.pow'IsoMul N).inv).trans <|
      Homotopy.ofEq <| BD.homPow'_sum N

end Data

/-- A Breen--Deligne `package` consists of Breen--Deligne `data`
that forms a complex, together with a `homotopy`
between the two universal maps `σ_add` and `σ_proj`. -/
structure Package where
  data : Data
  Homotopy : Homotopy (Data.proj 2) (Data.sum 2)

namespace Package

class Adept (BD : outParam Package) (κ : outParam <| ℕ → ℝ≥0) (κ' : ℕ → ℝ≥0) : Prop where
  htpy_suitable' :
    ∀ i, (BD.Homotopy.Hom i (i + 1)).Suitable (rescaleConstants κ 2 i) (κ' (i + 1) * κ (i + 1))

instance Adept.htpy_suitable (BD : Package) (κ κ' : ℕ → ℝ≥0) [Adept BD κ κ'] (j i : ℕ) :
    (BD.Homotopy.Hom j i).Suitable (rescaleConstants κ 2 j) (κ' i * κ i) :=
  by
  by_cases hij : j + 1 = i
  · rw [← hij]; apply Adept.htpy_suitable'
  · rw [BD.homotopy.zero]
    · infer_instance
    · exact hij

namespace Adept

open CategoryTheory

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
      ((BD.data.homotopyPow' BD.Homotopy N).hom j i).Suitable (rescaleConstants κ (2 ^ N) j)
        ((κ' * κ) i)
  | 0 => UniversalMap.suitable_zero _ _
  | N + 1 => by
    dsimp [Data.homotopyPow']
    refine' @UniversalMap.suitable_add _ _ _ _ _ _ (id _) (id _)
    · refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ (κ' i * κ i) _ _ (id _)
      refine' @UniversalMap.hMul_suitable _ _ _ _ _ (id _) _ ⟨two_pos⟩
      refine' (BreenDeligne.Package.Adept.homotopyPow'_suitable N).le _ _ _ _ _ le_rfl
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
    ((BD.data.homotopyMul BD.Homotopy N).hom j i).Suitable (rescaleConstants κ (2 ^ N) j)
      ((κ' * κ) i) :=
  by
  dsimp [Data.homotopyMul, Homotopy.trans_hom]
  simp only [add_zero, zero_add]
  refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ (rescaleConstants κ (2 ^ N) j) _ _ (id _)
  generalize rescaleConstants κ (2 ^ N) j = c
  induction' N with N IH
  · dsimp [Data.pow'IsoMul, Data.mulOneIso, FreeMat.oneMulIso]
    -- jmc: I don't understand why TC doesn't find the following instance...
    exact @UniversalMap.suitable_of _ _ _ _ _ (BasicUniversalMap.oneMulHom_suitable _)
  · dsimp [Data.pow'IsoMul]; haveI : Fact (0 < 2) := ⟨two_pos⟩
    skip
    refine' @UniversalMap.Suitable.comp _ _ _ _ _ _ c _ (id _) (id _)
    · infer_instance
    · dsimp [Data.mulMulIso, FreeMat.mulMulIso]
      infer_instance

end Adept

end Package

end BreenDeligne

