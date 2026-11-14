import LiquidTensorExperiment.ForMathlib.Derived.DerivedCat
import LiquidTensorExperiment.ForMathlib.Derived.Example
import LiquidTensorExperiment.ForMathlib.ShortExact

#align_import for_mathlib.derived.les

open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Limits

namespace HomologicalComplex

variable {A : Type _} [Category A] [Abelian A]

variable {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simps]
noncomputable def cone.π (w : ∀ i, f.f i ≫ g.f i = 0) : cone f ⟶ Z
    where
  f i := biprod.snd ≫ g.f i
  comm' i j hij := by
    dsimp at hij ; subst j; dsimp [Cone.d]; rw [if_pos rfl, biprod.lift_snd_assoc]
    ext
    ·
      simp only [Exact.w_assoc, zero_comp, Category.assoc, biprod.inl_desc_assoc, Category.id_comp,
        w, exact_inl_snd]
    · simp only [Category.assoc, biprod.inr_snd_assoc, biprod.inr_desc_assoc, g.comm]

--generalize
@[simps]
noncomputable def kernel : CochainComplex A ℤ
    where
  pt i := kernel (f.f i)
  d i j := kernel.map (f.f i) (f.f j) (X.d i j) (Y.d i j) (f.comm i j)
  shape' i j hij := by ext; simp only [kernel.lift_ι, zero_comp, X.shape i j hij, comp_zero]
  d_comp_d' i j k hij hjk := by
    ext
    simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, zero_comp, comp_zero, d_comp_d]

@[simps]
noncomputable def kernel.ι : kernel f ⟶ X
    where
  f i := kernel.ι _
  comm' i j hij := by simp only [kernel_d, kernel.lift_ι]

instance kernel.ι_mono (n : ℕ) : Mono ((kernel.ι f).f n) :=
  show Mono (Limits.kernel.ι (f.f n)) by infer_instance

end HomologicalComplex

