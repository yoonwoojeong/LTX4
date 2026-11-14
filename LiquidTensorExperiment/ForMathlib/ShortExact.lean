import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import for_mathlib.shortExact

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

-- move me
theorem exact_of_exact_image {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f (factorThruImage g)) :
    Exact f g := by rw [← Limits.image.fac g]; exact exact_comp_mono h

open scoped Pseudoelement

theorem exact_factorThruImage_iff {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f (factorThruImage g) ↔ Exact f g :=
  by
  refine'
    ⟨exact_of_exact_image f g, fun h =>
      Abelian.Pseudoelement.exact_of_pseudo_exact _ _
        ⟨fun x =>
          Abelian.Pseudoelement.zero_of_map_zero (Limits.image.ι g)
            (Abelian.Pseudoelement.pseudo_injective_of_mono _) _ _,
          fun y hy => _⟩⟩
  · rw [← Abelian.Pseudoelement.comp_apply, Limits.image.fac]
    exact (Abelian.Pseudoelement.pseudo_exact_of_exact h).1 x
  · replace hy := congr_arg (Limits.image.ι g) hy
    rw [Abelian.Pseudoelement.apply_zero, ← Abelian.Pseudoelement.comp_apply, Limits.image.fac] at
      hy 
    obtain ⟨a, ha⟩ := (Abelian.Pseudoelement.pseudo_exact_of_exact h).2 _ hy
    exact ⟨a, ha⟩

theorem shortExact_kernel_factorThruImage {A B : 𝓐} (f : A ⟶ B) :
    ShortExact (kernel.ι f) (factorThruImage f) :=
  by
  refine' ⟨_⟩
  rw [exact_factorThruImage_iff]
  apply exact_kernel_ι

theorem iso_of_shortExact_comp_right {X Y Z W : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (H1 : ShortExact f g) (H2 : ShortExact f (g ≫ h)) : IsIso h :=
  by
  refine'
    (CategoryTheory.isIso_iff_mono_and_epi _).2
      ⟨Abelian.Pseudoelement.mono_of_zero_of_map_zero _ fun z hz => _,
        Abelian.Pseudoelement.epi_of_pseudo_surjective _ fun w => _⟩
  · haveI := H1.epi
    obtain ⟨y, rfl⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi g z
    rw [← Abelian.Pseudoelement.comp_apply] at hz 
    obtain ⟨x, rfl⟩ := (Abelian.Pseudoelement.pseudo_exact_of_exact H2.exact).2 _ hz
    exact (Abelian.Pseudoelement.pseudo_exact_of_exact H1.exact).1 x
  · haveI := H2.epi
    obtain ⟨y, rfl⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi (g ≫ h) w
    refine' ⟨g y, _⟩
    rw [← Abelian.Pseudoelement.comp_apply]

