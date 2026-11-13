import LiquidTensorExperiment.ForMathlib.ShortExact
import LiquidTensorExperiment.ForMathlib.Derived.Defs

#align_import for_mathlib.random_homological_lemmas

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {A : Type _} [Category A] [Abelian A] [EnoughProjectives A]

variable {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

-- this files exists to save these lemmas from a file that will probably get nuked
-- move me
theorem Biprod.lift_desc_comm {X₁ X₂ Y₁ Y₂ : A} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁)
    (f₂₂ : X₂ ⟶ Y₂) :
    biprod.lift (biprod.desc f₁₁ f₂₁) (biprod.desc f₁₂ f₂₂) =
      biprod.desc (biprod.lift f₁₁ f₁₂) (biprod.lift f₂₁ f₂₂) :=
  by
  ext <;>
    simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.inl_desc, biprod.inr_desc]

-- move me
theorem Biprod.comp_lift {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) (h : X ⟶ Z) :
    f ≫ biprod.lift g h = biprod.lift (f ≫ g) (f ≫ h) := by
  ext <;> simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]

-- move me
@[reassoc]
theorem comp_factorThruImage_eq_zero {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    f ≫ factorThruImage g = 0 := by
  rw [← cancel_mono (Limits.image.ι g), Category.assoc, Limits.image.fac, w, zero_comp]

