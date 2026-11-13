import LiquidTensorExperiment.ForMathlib.ExactSeq2
import LiquidTensorExperiment.ForMathlib.AbelianCategory

#align_import for_mathlib.exact_seq3

namespace CategoryTheory

open CategoryTheory.Limits

variable {A : Type _} [Category A] [Abelian A]

noncomputable section

def ExactSeq.w {X₁ X₂ X₃ : A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (e : ExactSeq A [f, g]) : f ≫ g = 0 := by
  rw [← CategoryTheory.exact_iff_exactSeq] at e ; exact e.w

def ExactSeq.π {X₁ X₂ X₃ : A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (e : ExactSeq A [f, g]) :
    cokernel f ⟶ X₃ :=
  cokernel.desc _ g e.w

def ExactSeq.ι {X₁ X₂ X₃ : A} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (e : ExactSeq A [f, g]) : X₁ ⟶ kernel g :=
  kernel.lift _ f e.w

attribute [local instance] Abelian.Pseudoelement.homToFun

theorem ExactSeq.replace {X₁ X₂ X₃ X₄ X₅ : A} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    {f₄ : X₄ ⟶ X₅} (e : ExactSeq A [f₁, f₂, f₃, f₄]) : Exact (e.extract 0 2).π (e.extract 2 3).ι :=
  by
  apply Abelian.Pseudoelement.exact_of_pseudo_exact
  constructor
  · intro a
    simp only [← Abelian.Pseudoelement.comp_apply]
    suffices (e.extract 0 2).π ≫ (e.extract 2 3).ι = 0 by rw [this]; simp
    ext
    dsimp [exact_seq.π, exact_seq.ι]
    simpa using (e.extract 1 2).w
  · intro t ht
    dsimp [exact_seq.π, exact_seq.ι] at *
    apply_fun fun i => kernel.ι f₄ i at ht 
    simp only [← Abelian.Pseudoelement.comp_apply, kernel.lift_ι] at ht 
    simp at ht 
    have := e.extract 1 2
    erw [← CategoryTheory.exact_iff_exactSeq] at this 
    have := (@Abelian.Pseudoelement.pseudo_exact_of_exact _ _ _ _ _ _ _ _ this).2 _ ht
    obtain ⟨a, ha⟩ := this
    use cokernel.π f₁ a
    rwa [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc]

theorem isZero_of_exactSeq_of_is_iso_of_is_iso {X₁ X₂ X₃ X₄ X₅ : A} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅) [Epi f₁] [Mono f₄] (e : ExactSeq A [f₁, f₂, f₃, f₄]) :
    IsZero X₃ := by
  have h1 : is_zero (cokernel f₁) := CategoryTheory.Limits.isZero_cokernel_of_epi f₁
  have h2 : is_zero (kernel f₄) := CategoryTheory.Limits.isZero_kernel_of_mono f₄
  apply CategoryTheory.Limits.isZero_of_exact_isZero_isZero _ _ _ h1 h2
  exact (e.extract 0 2).π; exact (e.extract 2 3).ι
  apply ExactSeq.replace

theorem isIso_of_exact_of_isZero_of_isZero {X₁ X₂ X₃ X₄ : A} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (f₃ : X₃ ⟶ X₄) (h₁ : IsZero X₁) (h₄ : IsZero X₄) (e : ExactSeq A [f₁, f₂, f₃]) : IsIso f₂ :=
  by
  apply (config := { instances := false }) is_iso_of_mono_of_epi; infer_instance
  apply Exact.mono_of_isZero e.pair; assumption
  apply Exact.epi_of_isZero (e.extract 1 2).pair; assumption

end CategoryTheory

