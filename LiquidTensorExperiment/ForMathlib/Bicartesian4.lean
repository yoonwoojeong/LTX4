import LiquidTensorExperiment.ForMathlib.Bicartesian3

#align_import for_mathlib.bicartesian4

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

section Part1

-- jmc: feel free to generalize to arbitrary abelian cats
variable {A B C D : Ab.{u}} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}

variable {α : A ⟶ A} {β : B ⟶ B} {γ : C ⟶ C} {δ : D ⟶ D}

open scoped ZeroObject

theorem bicartesian_of_id_of_end_of_end_of_id (H : ExactSeq Ab.{u} [f, g, h]) (sq1 : Commsq f α β f)
    (sq2 : Commsq g β γ g) (sq3 : Commsq h γ δ h) (hα : α = -𝟙 _) (hδ : δ = -𝟙 _) :
    sq2.Bicartesian := by
  have aux : _ := _
  rw [Commsq.bicartesian_iff_isos _ _ aux aux sq2.kernel sq2 sq2.cokernel]
  swap
  · apply exact.cons; · exact exact_kernel_ι
    apply exact.exact_seq; · apply abelian.exact_cokernel
  constructor
  · let t : A ⟶ kernel g := kernel.lift g f ((exact_iff_exact_seq _ _).2 (H.extract 0 2)).w
    have : is_iso α := by
      rw [hα]
      infer_instance
    refine'
      @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ (kernel t) A (kernel g) 0
        (kernel t) A (kernel g) 0 (kernel.ι t) t 0 (kernel.ι t) t 0 (-𝟙 _) α _ 0 _ _ _ 0 0 0 0 0 _ _
        _ _ _ _ _ _ _ _ _
    · simp only [preadditive.neg_comp, category.id_comp, preadditive.comp_neg, category.comp_id, hα]
    ·
      simp only [← cancel_mono (kernel.ι g), sq1.w, category.assoc, kernel.lift_ι,
        kernel.lift_ι_assoc]
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
    · exact exact_kernel_ι
    · exact exact_epi_zero t
    · exact exact_of_zero 0 0
    · exact exact_kernel_ι
    · exact exact_epi_zero t
    · exact exact_of_zero 0 0
  · let t : cokernel g ⟶ D := cokernel.desc g h ((exact_iff_exact_seq _ _).2 (H.extract 1 2)).w
    have : is_iso δ := by
      rw [hδ]
      infer_instance
    refine'
      @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ 0 0 (cokernel g) D 0 0
        (cokernel g) D 0 0 t 0 0 t 0 0 _ δ _ _ _ (cokernel t) (cokernel t) (cokernel.π t)
        (cokernel.π t) (-𝟙 _) _ _ _ _ _ _ _ _ _ _ _
    · exact Subsingleton.elim _ _
    · exact Subsingleton.elim _ _
    ·
      simp only [← cancel_epi (cokernel.π g), sq3.w, cokernel.π_desc_assoc, category.assoc,
        cokernel.π_desc]
    · simp only [hδ, preadditive.neg_comp, category.id_comp, preadditive.comp_neg, category.comp_id]
    · exact exact_of_zero 0 0
    · exact exact_zero_mono t
    · exact abelian.exact_cokernel t
    · exact exact_of_zero 0 0
    · exact exact_zero_mono t
    · exact abelian.exact_cokernel t

end Part1

section Part2

open scoped ZeroObject

-- jmc: this part does not depend on the first section,
-- it's the same file because two lemmas have the same theme
-- jmc: feel free to generalize to arbitrary abelian cats
variable {A₁₁ A₁₂ A₁₃ A₁₄ A₁₅ : Ab.{u}}

variable {A₂₁ A₂₂ A₂₃ A₂₄ A₂₅ : Ab.{u}}

-- horizontal maps are `f`s and vertical maps are `g`s
variable {f₁₁ : A₁₁ ⟶ A₁₂} {f₁₂ : A₁₂ ⟶ A₁₃} {f₁₃ : A₁₃ ⟶ A₁₄} {f₁₄ : A₁₄ ⟶ A₁₅}

variable {g₁₁ : A₁₁ ⟶ A₂₁} {g₁₂ : A₁₂ ⟶ A₂₂} {g₁₃ : A₁₃ ⟶ A₂₃} {g₁₄ : A₁₄ ⟶ A₂₄} {g₁₅ : A₁₅ ⟶ A₂₅}

variable {f₂₁ : A₂₁ ⟶ A₂₂} {f₂₂ : A₂₂ ⟶ A₂₃} {f₂₃ : A₂₃ ⟶ A₂₄} {f₂₄ : A₂₄ ⟶ A₂₅}

theorem exact_kernel_cokernel : ExactSeq Ab.{u} [kernel.ι f₁₁, f₁₁, cokernel.π f₁₁] :=
  by
  apply exact.cons; · exact exact_kernel_ι
  apply exact.exact_seq; · apply abelian.exact_cokernel

theorem isIso_kernel_map_of_bicartesian {sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁} (H : sq.Bicartesian) :
    IsIso (kernel.map f₁₁ f₂₁ _ _ sq.w) :=
  by
  rw [Commsq.bicartesian_iff_isos _ _ _ _ sq.kernel sq sq.cokernel] at H 
  · exact H.1
  · exact exact_kernel_cokernel
  · exact exact_kernel_cokernel

theorem isIso_cokernel_map_of_bicartesian {sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁} (H : sq.Bicartesian) :
    IsIso (cokernel.map f₁₁ f₂₁ _ _ sq.w) :=
  by
  rw [Commsq.bicartesian_iff_isos _ _ _ _ sq.kernel sq sq.cokernel] at H 
  · exact H.2
  · exact exact_kernel_cokernel
  · exact exact_kernel_cokernel

section

variable (f₁₁)

theorem exact_epi_comp_iff [Epi f₁₁] : Exact (f₁₁ ≫ f₁₂) f₁₃ ↔ Exact f₁₂ f₁₃ :=
  by
  refine' ⟨fun h => _, fun h => exact_epi_comp h⟩
  rw [abelian.exact_iff] at h 
  let hc :=
    isColimitOfIsColimitComp (colimit.is_colimit (parallel_pair (f₁₁ ≫ f₁₂) 0))
      (by rw [← cancel_epi f₁₁, ← category.assoc, cokernel_cofork.condition, comp_zero])
  refine' (abelian.exact_iff' _ _ (limit.is_limit _) hc).2 ⟨_, h.2⟩
  exact zero_of_epi_comp f₁₁ (by rw [← h.1, category.assoc])

end

section

variable (f₁₃)

theorem exact_comp_mono_iff [Mono f₁₃] : Exact f₁₁ (f₁₂ ≫ f₁₃) ↔ Exact f₁₁ f₁₂ :=
  by
  refine' ⟨fun h => _, fun h => exact_comp_mono h⟩
  rw [abelian.exact_iff] at h 
  let hc :=
    isLimitOfIsLimitComp (limit.is_limit (parallel_pair (f₁₂ ≫ f₁₃) 0))
      (by rw [← cancel_mono f₁₃, category.assoc, kernel_fork.condition, zero_comp])
  refine' (abelian.exact_iff' _ _ hc (colimit.is_colimit _)).2 ⟨_, h.2⟩
  exact zero_of_comp_mono f₁₃ (by rw [← h.1, category.assoc])

end

theorem iso_of_bicartesian_of_bicartesian (h_ex₁ : ExactSeq Ab.{u} [f₁₁, f₁₂, f₁₃, f₁₄])
    (h_ex₂ : ExactSeq Ab.{u} [f₂₁, f₂₂, f₂₃, f₂₄]) (sq1 : Commsq f₁₁ g₁₁ g₁₂ f₂₁)
    (sq2 : Commsq f₁₂ g₁₂ g₁₃ f₂₂) (sq3 : Commsq f₁₃ g₁₃ g₁₄ f₂₃) (sq4 : Commsq f₁₄ g₁₄ g₁₅ f₂₄)
    (H1 : sq1.Bicartesian) (H4 : sq4.Bicartesian) : IsIso g₁₃ :=
  by
  haveI := isIso_cokernel_map_of_bicartesian H1
  haveI := isIso_kernel_map_of_bicartesian H4
  let f₁₂' := cokernel.desc f₁₁ f₁₂ ((exact_iff_exact_seq _ _).2 (h_ex₁.extract 0 2)).w
  let f₁₃' := kernel.lift f₁₄ f₁₃ ((exact_iff_exact_seq _ _).2 (h_ex₁.extract 2 2)).w
  let f₂₂' := cokernel.desc f₂₁ f₂₂ ((exact_iff_exact_seq _ _).2 (h_ex₂.extract 0 2)).w
  let f₂₃' := kernel.lift f₂₄ f₂₃ ((exact_iff_exact_seq _ _).2 (h_ex₂.extract 2 2)).w
  refine'
    @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ 0 (cokernel f₁₁) A₁₃ (kernel f₁₄)
      0 (cokernel f₂₁) A₂₃ (kernel f₂₄) 0 f₁₂' f₁₃' 0 f₂₂' f₂₃' 0 (cokernel.map f₁₁ f₂₁ _ _ sq1.w)
      g₁₃ (kernel.map f₁₄ f₂₄ _ _ sq4.w) _ _ _ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _
  · exact Subsingleton.elim _ _
  ·
    simp only [← cancel_epi (cokernel.π f₁₁), sq2.w, cokernel.π_desc_assoc, category.assoc,
      cokernel.π_desc]
  ·
    simp only [← cancel_mono (kernel.ι f₂₄), sq3.w, category.assoc, kernel.lift_ι,
      kernel.lift_ι_assoc]
  · exact Subsingleton.elim _ _
  · exact exact_zero_mono f₁₂'
  · rw [← exact_epi_comp_iff (cokernel.π f₁₁), cokernel.π_desc, ←
      exact_comp_mono_iff (kernel.ι f₁₄), kernel.lift_ι]
    exact (exact_iff_exact_seq _ _).2 (h_ex₁.extract 1 2)
  · exact exact_epi_zero f₁₃'
  · exact exact_zero_mono f₂₂'
  · rw [← exact_epi_comp_iff (cokernel.π f₂₁), cokernel.π_desc, ←
      exact_comp_mono_iff (kernel.ι f₂₄), kernel.lift_ι]
    exact (exact_iff_exact_seq _ _).2 (h_ex₂.extract 1 2)
  · exact exact_epi_zero f₂₃'

theorem iso_of_zero_of_bicartesian (h_ex₁ : ExactSeq Ab.{u} [f₁₂, f₁₃, f₁₄])
    (h_ex₂ : ExactSeq Ab.{u} [f₂₂, f₂₃, f₂₄]) (hz₁ : IsZero A₁₂) (hz₂ : IsZero A₂₂)
    (sq2 : Commsq f₁₂ g₁₂ g₁₃ f₂₂) (sq3 : Commsq f₁₃ g₁₃ g₁₄ f₂₃) (sq4 : Commsq f₁₄ g₁₄ g₁₅ f₂₄)
    (H4 : sq4.Bicartesian) : IsIso g₁₃ :=
  by
  have aux₁ : exact (0 : A₁₂ ⟶ A₁₂) f₁₂ := by have : mono f₁₂ := ⟨fun _ x y h => hz₁.eq_of_tgt _ _⟩;
    rwa [(abelian.tfae_mono A₁₂ f₁₂).out 2 0]
  have aux₂ : exact (0 : A₂₂ ⟶ A₂₂) f₂₂ := by have : mono f₂₂ := ⟨fun _ x y h => hz₂.eq_of_tgt _ _⟩;
    rwa [(abelian.tfae_mono A₂₂ f₂₂).out 2 0]
  refine' iso_of_bicartesian_of_bicartesian (aux₁.cons h_ex₁) (aux₂.cons h_ex₂) _ sq2 sq3 sq4 _ H4
  · exact g₁₂
  · exact Commsq.ofEq (zero_comp.trans comp_zero.symm)
  · apply Commsq.Bicartesian.of_isLimit_of_is_colimt
    · refine'
        pullback_cone.is_limit.mk _ (fun s => 0) (fun s => hz₁.eq_of_tgt _ _)
          (fun s => hz₂.eq_of_tgt _ _) _
      intros; apply hz₁.eq_of_tgt
    · refine'
        pushout_cocone.is_colimit.mk _ (fun s => 0) (fun s => hz₁.eq_of_src _ _)
          (fun s => hz₂.eq_of_src _ _) _
      intros; apply hz₂.eq_of_src

end Part2

