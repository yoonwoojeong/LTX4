import LiquidTensorExperiment.ForMathlib.ExactSeq3
import LiquidTensorExperiment.ForMathlib.Bicartesian2

#align_import for_mathlib.bicartesian3

open CategoryTheory CategoryTheory.Limits

universe u

local notation "𝓐" => Ab.{u}

-- Consider the following diagram
variable {Kv₁ Kv₂ : 𝓐}

variable {Kh₁ A₁₁ A₁₂ Qh₁ : 𝓐}

variable {Kh₂ A₂₁ A₂₂ Qh₂ : 𝓐}

variable {Qv₁ Qv₂ : 𝓐}

-- with morphisms
variable (fKv : Kv₁ ⟶ Kv₂)

variable {ιv₁ : Kv₁ ⟶ A₁₁} {ιv₂ : Kv₂ ⟶ A₁₂}

variable {ιh₁ : Kh₁ ⟶ A₁₁} {f₁ : A₁₁ ⟶ A₁₂} {πh₁ : A₁₂ ⟶ Qh₁}

variable (gKh : Kh₁ ⟶ Kh₂) {g₁ : A₁₁ ⟶ A₂₁} {g₂ : A₁₂ ⟶ A₂₂} (gQh : Qh₁ ⟶ Qh₂)

variable {ιh₂ : Kh₂ ⟶ A₂₁} {f₂ : A₂₁ ⟶ A₂₂} {πh₂ : A₂₂ ⟶ Qh₂}

variable {πv₁ : A₂₁ ⟶ Qv₁} {πv₂ : A₂₂ ⟶ Qv₂}

variable (fQv : Qv₁ ⟶ Qv₂)

-- with exact rows and columns
variable (H₁ : ExactSeq 𝓐 [ιh₁, f₁, πh₁])

variable (H₂ : ExactSeq 𝓐 [ιh₂, f₂, πh₂])

variable (V₁ : ExactSeq 𝓐 [ιv₁, g₁, πv₁])

variable (V₂ : ExactSeq 𝓐 [ιv₂, g₂, πv₂])

-- and such that all the extremal maps are appropriately monos or epis
variable [Mono ιv₁] [Mono ιv₂] [Mono ιh₁] [Mono ιh₂]

variable [Epi πv₁] [Epi πv₂] [Epi πh₁] [Epi πh₂]

-- of course the diagram should commute
variable (sqᵤ : Commsq fKv ιv₁ ιv₂ f₁)

variable (sqₗ : Commsq ιh₁ gKh g₁ ιh₂) (sqm : Commsq f₁ g₁ g₂ f₂)

variable (sqᵣ : Commsq πh₁ g₂ gQh πh₂)

variable (sqₛ : Commsq f₂ πv₁ πv₂ fQv)

open scoped ZeroObject

open CategoryTheory.Abelian

def isLimitOfIsLimitComp {X Y Z : 𝓐} {f : X ⟶ Y} {g : Y ⟶ Z} {c : KernelFork (f ≫ g)}
    (hc : IsLimit c) (h : c.ι ≫ f = 0) : IsLimit (KernelFork.ofι c.ι h) :=
  KernelFork.IsLimit.ofι _ _
    (fun T l hl => hc.lift (KernelFork.ofι l (by rw [reassoc_of hl, zero_comp])))
    (fun T l hl => hc.fac _ _) fun T l hl m hm => Fork.IsLimit.hom_ext hc (by erw [hm, hc.fac]; rfl)

def isColimitOfIsColimitComp {X Y Z : 𝓐} {f : X ⟶ Y} {g : Y ⟶ Z} {c : CokernelCofork (f ≫ g)}
    (hc : IsColimit c) (h : g ≫ c.π = 0) : IsColimit (CokernelCofork.ofπ c.π h) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun T l hl => hc.desc (CokernelCofork.ofπ l (by rw [category.assoc, hl, comp_zero])))
    (fun T l hl => hc.fac _ _) fun T l hl m hm =>
    Cofork.IsColimit.hom_ext hc (by erw [hm, hc.fac]; rfl)

section

theorem isIso_of_isLimit (H₁ : Exact ιh₁ f₁) (H₂ : Exact ιh₂ f₂)
    (h : IsLimit (PullbackCone.mk f₁ g₁ sqm.w)) : IsIso gKh :=
  by
  have : mono gKh := by
    refine' preadditive.mono_of_cancel_zero _ fun P g hg => _
    apply zero_of_comp_mono ιh₁
    apply pullback_cone.is_limit.hom_ext h
    · rw [pullback_cone.mk_fst, category.assoc, zero_comp, H₁.w, comp_zero]
    · rw [pullback_cone.mk_snd, category.assoc, sqₗ.w, ← category.assoc, hg, zero_comp, zero_comp]
  obtain ⟨l, hl₁, hl₂ : l ≫ g₁ = _⟩ := pullback_cone.is_limit.lift' h 0 ιh₂ (by simp [H₂.w])
  let ker := is_limit_of_exact_of_mono _ _ H₁
  obtain ⟨inv, hinv : inv ≫ ιh₁ = l⟩ := kernel_fork.is_limit.lift' ker l hl₁
  have hinv' : inv ≫ gKh = 𝟙 _ := by
    rw [← cancel_mono ιh₂, category.assoc, ← sqₗ.w, reassoc_of hinv, hl₂, category.id_comp]
  refine' ⟨⟨inv, _, hinv'⟩⟩
  rw [← cancel_mono gKh, category.assoc, hinv', category.comp_id, category.id_comp]

end

section

theorem isIso_of_isColimit (H₁ : Exact f₁ πh₁) (H₂ : Exact f₂ πh₂)
    (h : IsColimit (PushoutCocone.mk _ _ sqm.w)) : IsIso gQh :=
  by
  have : epi gQh := by
    refine' preadditive.epi_of_cancel_zero _ fun P g hg => _
    apply zero_of_epi_comp πh₂
    apply pushout_cocone.is_colimit.hom_ext h
    ·
      rw [pushout_cocone.mk_inl, ← category.assoc, ← sqᵣ.w, category.assoc, hg, comp_zero,
        comp_zero]
    · rw [pushout_cocone.mk_inr, ← category.assoc, H₂.w, comp_zero, zero_comp]
  obtain ⟨l, hl₁ : g₂ ≫ l = _, hl₂⟩ := pushout_cocone.is_colimit.desc' h πh₁ 0 (by simp [H₁.w])
  let coker := is_colimit_of_exact_of_epi _ _ H₂
  obtain ⟨inv, hinv : πh₂ ≫ inv = l⟩ := cokernel_cofork.is_colimit.desc' coker l hl₂
  have hinv' : gQh ≫ inv = 𝟙 _ := by
    rw [← cancel_epi πh₁, ← category.assoc, sqᵣ.w, category.assoc, hinv, hl₁, category.comp_id]
  refine' ⟨⟨inv, hinv', _⟩⟩
  rw [← cancel_epi gQh, reassoc_of hinv', category.comp_id]

end

theorem Commsq.bicartesian_iff_isos : sqm.Bicartesian ↔ IsIso gKh ∧ IsIso gQh :=
  by
  constructor
  · intro h; constructor
    ·
      exact
        isIso_of_isLimit gKh sqₗ sqm ((exact_iff_exact_seq _ _).2 (H₁.extract 0 2))
          ((exact_iff_exact_seq _ _).2 (H₂.extract 0 2)) h.is_limit
    ·
      exact
        isIso_of_isColimit gQh sqm sqᵣ ((exact_iff_exact_seq _ _).2 (H₁.extract 1 2))
          ((exact_iff_exact_seq _ _).2 (H₂.extract 1 2)) h.is_colimit
  · rintro ⟨gKh_iso, gQh_iso⟩
    skip
    apply Commsq.Bicartesian.of_isLimit_of_is_colimt
    · apply is_limit.of_point_iso (limit.is_limit _)
      · infer_instance
      · let r := pullback.lift _ _ sqm.w
        let x : Kh₁ ⟶ kernel (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) :=
          by
          refine' kernel.lift _ (ιh₁ ≫ r) _
          simp only [(H₁.extract 0 2).w, category.assoc, pullback.lift_fst]
        have : is_iso x :=
          by
          let psq := Commsq.ofEq (@pullback.condition _ _ _ _ _ g₂ f₂ _)
          let hker :=
            abelian.is_limit_of_exact_of_mono _ _ ((exact_iff_exact_seq _ _).2 (H₂.extract 0 2))
          obtain ⟨u : _ ⟶ Kh₂, hu⟩ :=
            kernel_fork.is_limit.lift' hker
              (kernel.ι (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) ≫ pullback.snd) _
          · rw [fork.ι_of_ι] at hu 
            let lsq := Commsq.ofEq hu.symm
            haveI : is_iso u := isIso_of_isLimit u lsq psq _ _ _
            · have hxu : x ≫ u = gKh := by
                simp only [← cancel_mono ιh₂, category.assoc, hu, x, kernel.lift_ι_assoc, r,
                  pullback.lift_snd, sqₗ.w]
              have hx : x = gKh ≫ inv u := by rw [← is_iso.comp_inv_eq, is_iso.inv_inv, hxu]
              rw [hx]
              infer_instance
            · exact exact_kernel_ι
            · exact (exact_iff_exact_seq _ _).2 (H₂.extract 0 2)
            · exact pullback_is_pullback _ _
          · rw [category.assoc, ← pullback.condition, kernel.condition_assoc, zero_comp]
        refine'
          @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ 0 _ _ _ 0 _ _ _ 0 ιh₁ f₁ 0
            (kernel.ι (pullback.fst : pullback g₂ f₂ ⟶ A₁₂)) pullback.fst 0 x r (𝟙 _) _ _ _ _ _ πh₁
            πh₁ (𝟙 _) _ _ _ _ _ _ _ _ _ _ _
        · simp only [eq_iff_true_of_subsingleton]
        · simp only [kernel.lift_ι]
        · simp only [pullback.lift_fst, category.comp_id]
        · simp only [category.id_comp, category.comp_id]
        · exact exact_zero_mono ιh₁
        · exact (exact_iff_exact_seq _ _).2 (H₁.extract 0 2)
        · exact (exact_iff_exact_seq _ _).2 (H₁.extract 1 2)
        · exact exact_zero_mono (kernel.ι pullback.fst)
        · exact exact_kernel_ι
        · have : (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) ≫ πh₁ = 0 :=
            by
            apply zero_of_comp_mono gQh
            rw [category.assoc, sqᵣ.w, pullback.condition_assoc, (H₂.extract 1 2).w, comp_zero]
          apply abelian.exact_of_is_cokernel _ _ this
          have hex := (exact_iff_exact_seq _ _).2 (H₁.extract 1 2)
          rw [← pullback.lift_fst _ _ sqm.w] at hex 
          exact isColimitOfIsColimitComp (abelian.is_colimit_of_exact_of_epi _ _ hex) _
    · apply is_colimit.of_point_iso (colimit.is_colimit _)
      · infer_instance
      · let r := pushout.desc _ _ sqm.w
        let x : cokernel (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) ⟶ Qh₂ :=
          by
          refine' cokernel.desc _ (r ≫ πh₂) _
          simp only [(H₂.extract 1 2).w, ← category.assoc, pushout.inr_desc]
        have : is_iso x :=
          by
          let psq := Commsq.ofEq (@pushout.condition _ _ _ _ _ f₁ g₁ _)
          let hcoker :=
            abelian.is_colimit_of_exact_of_epi _ _ ((exact_iff_exact_seq _ _).2 (H₁.extract 1 2))
          obtain ⟨u : Qh₁ ⟶ _, hu⟩ :=
            cokernel_cofork.is_colimit.desc' hcoker
              (pushout.inl ≫ cokernel.π (pushout.inr : A₂₁ ⟶ pushout f₁ g₁)) _
          · rw [cofork.π_of_π] at hu 
            let lsq := Commsq.ofEq hu
            haveI : is_iso u := isIso_of_isColimit u psq lsq _ _ _
            · have hxu : u ≫ x = gQh := by
                simp only [← cancel_epi πh₁, hu, x, cokernel.π_desc, reassoc_of hu, r,
                  pushout.inl_desc_assoc, sqᵣ.w]
              have hx : x = inv u ≫ gQh := by rw [← is_iso.inv_comp_eq, is_iso.inv_inv, hxu]
              rw [hx]
              infer_instance
            · exact (exact_iff_exact_seq _ _).2 (H₁.extract 1 2)
            · exact exact_cokernel pushout.inr
            · exact pushout_is_pushout _ _
          · rw [← category.assoc, pushout.condition, category.assoc, cokernel.condition, comp_zero]
        refine'
          @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ _ _ _ _ _ _ _ _ ιh₂
            (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) (cokernel.π (pushout.inr : A₂₁ ⟶ pushout f₁ g₁)) ιh₂
            f₂ πh₂ (𝟙 _) (𝟙 _) r x _ _ _ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _
        · simp only [category.id_comp, category.comp_id]
        · simp only [category.id_comp, pushout.inr_desc]
        · simp only [cokernel.π_desc]
        · simp only [eq_iff_true_of_subsingleton]
        · have : ιh₂ ≫ (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) = 0 :=
            by
            apply zero_of_epi_comp gKh
            rw [← sqₗ.w_assoc, ← pushout.condition, reassoc_of (H₁.extract 0 2).w, zero_comp]
          apply abelian.exact_of_is_kernel _ _ this
          have hex := (exact_iff_exact_seq _ _).2 (H₂.extract 0 2)
          rw [← pushout.inr_desc _ _ sqm.w] at hex 
          exact isLimitOfIsLimitComp (abelian.is_limit_of_exact_of_mono _ _ hex) _
        · exact exact_cokernel pushout.inr
        · exact exact_epi_zero (cokernel.π pushout.inr)
        · exact (exact_iff_exact_seq _ _).2 (H₂.extract 0 2)
        · exact (exact_iff_exact_seq _ _).2 (H₂.extract 1 2)
        · exact exact_epi_zero πh₂

