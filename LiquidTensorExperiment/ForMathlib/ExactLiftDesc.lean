import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.ExactSeq3

#align_import for_mathlib.exact_lift_desc

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Exact

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {A B C T : 𝓐} {f : A ⟶ B} {g : B ⟶ C}

section lift

variable (h : Exact f g) [Mono f] (φ : T ⟶ B) (w : φ ≫ g = 0)

def monoLift : T ⟶ A :=
  (Abelian.isLimitOfExactOfMono f g h).lift (KernelFork.ofι _ w)

@[simp, reassoc]
theorem monoLift_comp : h.monoLift φ w ≫ f = φ :=
  (Abelian.isLimitOfExactOfMono f g h).fac (KernelFork.ofι _ w) WalkingParallelPair.zero

theorem monoLift_unique (e : T ⟶ A) (he : e ≫ f = φ) : e = h.monoLift φ w := by
  rw [← cancel_mono f, he, h.monoLift_comp]

end lift

section Desc

variable (h : Exact f g) [CategoryTheory.Epi g] (φ : B ⟶ T) (w : f ≫ φ = 0)

def epiDesc : C ⟶ T :=
  (Abelian.isColimitOfExactOfEpi f g h).desc (CokernelCofork.ofπ _ w)

@[simp, reassoc]
theorem comp_epiDesc : g ≫ h.epiDesc φ w = φ :=
  (Abelian.isColimitOfExactOfEpi f g h).fac (CokernelCofork.ofπ _ w) WalkingParallelPair.one

theorem epiDesc_unique (e : C ⟶ T) (he : g ≫ e = φ) : e = h.epiDesc φ w := by
  rw [← cancel_epi g, he, h.comp_epiDesc]

end Desc

end Exact

end CategoryTheory

