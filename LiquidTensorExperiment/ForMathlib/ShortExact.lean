import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import for_mathlib.short_exact

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

-- move me
theorem exact_of_exact_image {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f (factorThruImage g)) :
    Exact f g := by rw [← limits.image.fac g]; exact exact_comp_mono h

open scoped Pseudoelement

theorem exact_factorThruImage_iff {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f (factorThruImage g) ↔ Exact f g :=
  by
  refine'
    ⟨exact_of_exact_image f g, fun h =>
      abelian.pseudoelement.exact_of_pseudo_exact _ _
        ⟨fun x =>
          abelian.pseudoelement.zero_of_map_zero (limits.image.ι g)
            (abelian.pseudoelement.pseudo_injective_of_mono _) _ _,
          fun y hy => _⟩⟩
  · rw [← abelian.pseudoelement.comp_apply, limits.image.fac]
    exact (abelian.pseudoelement.pseudo_exact_of_exact h).1 x
  · replace hy := congr_arg (limits.image.ι g) hy
    rw [abelian.pseudoelement.apply_zero, ← abelian.pseudoelement.comp_apply, limits.image.fac] at
      hy 
    obtain ⟨a, ha⟩ := (abelian.pseudoelement.pseudo_exact_of_exact h).2 _ hy
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
    (is_iso_iff_mono_and_epi _).2
      ⟨abelian.pseudoelement.mono_of_zero_of_map_zero _ fun z hz => _,
        abelian.pseudoelement.epi_of_pseudo_surjective _ fun w => _⟩
  · haveI := H1.epi
    obtain ⟨y, rfl⟩ := abelian.pseudoelement.pseudo_surjective_of_epi g z
    rw [← abelian.pseudoelement.comp_apply] at hz 
    obtain ⟨x, rfl⟩ := (abelian.pseudoelement.pseudo_exact_of_exact H2.exact).2 _ hz
    exact (abelian.pseudoelement.pseudo_exact_of_exact H1.exact).1 x
  · haveI := H2.epi
    obtain ⟨y, rfl⟩ := abelian.pseudoelement.pseudo_surjective_of_epi (g ≫ h) w
    refine' ⟨g y, _⟩
    rw [← abelian.pseudoelement.comp_apply]

