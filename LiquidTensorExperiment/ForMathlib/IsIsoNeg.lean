import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.Int
import LiquidTensorExperiment.ForMathlib.NegOnePow

#align_import for_mathlib.is_iso_neg

universe v u

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.Preadditive

variable {A : Type u} [Category.{v} A] [Preadditive A] {X Y : A} (f : X ⟶ Y)

-- Move This
@[simp]
theorem isIso_neg_iff : IsIso (-f) ↔ IsIso f := by
  constructor <;> rintro ⟨g, hg⟩ <;> refine' ⟨⟨-g, _⟩⟩ <;>
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp, neg_neg] using hg

-- move me
instance isIso_neg [IsIso f] : IsIso (-f) := by rwa [isIso_neg_iff]

-- Move This
@[simp]
theorem isIso_negOnePow_iff (i : ℤ) : IsIso (i.neg_one_pow • f) ↔ IsIso f :=
  by
  induction' i using Int.induction_on_iff with i
  · simp only [Int.negOnePow_neg_zero, one_zsmul]
  dsimp
  simp only [Int.negOnePow_add, Int.negOnePow_one, mul_neg, mul_one, neg_smul, isIso_neg_iff]

