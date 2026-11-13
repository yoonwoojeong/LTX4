import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import LiquidTensorExperiment.ForMathlib.PreservesFiniteLimits
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Tensor
import LiquidTensorExperiment.ForMathlib.AddCommGroup
import LiquidTensorExperiment.ForMathlib.PreservesExact

#align_import for_mathlib.AddCommGroup.tensor_short_exact

noncomputable section

universe u

open scoped TensorProduct

open CategoryTheory

namespace AddCommGroupCat

variable (A : AddCommGroupCat)

variable [NoZeroSMulDivisors ℤ A]

instance tensorFunctorPreservesFiniteLimits : Limits.PreservesFiniteLimits (tensorFunctor.obj A) :=
  preservesFiniteLimitsOfPreservesMonoPreservesFiniteColimits _ fun X Y f hf => by skip;
    infer_instance

theorem tensor_shortExact {X Y Z : AddCommGroupCat} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : ShortExact f g) :
    ShortExact (mapTensor (𝟙 A) f) (mapTensor (𝟙 A) g) :=
  (tensorFunctor.obj A).map_shortExact f g hfg

end AddCommGroupCat

