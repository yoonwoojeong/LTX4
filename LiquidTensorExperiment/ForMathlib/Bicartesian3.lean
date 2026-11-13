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
    (fun T l hl => hc.desc (CokernelCofork.ofπ l (by rw [Category.assoc, hl, comp_zero])))
    (fun T l hl => hc.fac _ _) fun T l hl m hm =>
    Cofork.IsColimit.hom_ext hc (by erw [hm, hc.fac]; rfl)

section

theorem isIso_of_isLimit (H₁ : Exact ιh₁ f₁) (H₂ : Exact ιh₂ f₂)
    (h : IsLimit (PullbackCone.mk f₁ g₁ sqm.w)) : IsIso gKh :=
  by
  have : mono gKh := by
    refine' Preadditive.mono_of_cancel_zero _ fun P g hg => _
    apply zero_of_comp_mono ιh₁
    apply PullbackCone.IsLimit.hom_ext h
    · rw [PullbackCone.mk_fst, Category.assoc, zero_comp, H₁.w, comp_zero]
    · rw [PullbackCone.mk_snd, Category.assoc, sqₗ.w, ← Category.assoc, hg, zero_comp, zero_comp]
  obtain ⟨l, hl₁, hl₂ : l ≫ g₁ = _⟩ := PullbackCone.IsLimit.lift' h 0 ιh₂ (by simp [H₂.w])
  let ker := CategoryTheory.Abelian.isLimitOfExactOfMono _ _ H₁
  obtain ⟨inv, hinv : inv ≫ ιh₁ = l⟩ := KernelFork.IsLimit.lift' ker l hl₁
  have hinv' : inv ≫ gKh = 𝟙 _ := by
    rw [← cancel_mono ιh₂, Category.assoc, ← sqₗ.w, reassoc_of hinv, hl₂, Category.id_comp]
  refine' ⟨⟨inv, _, hinv'⟩⟩
  rw [← cancel_mono gKh, Category.assoc, hinv', Category.comp_id, Category.id_comp]

end

section

theorem isIso_of_isColimit (H₁ : Exact f₁ πh₁) (H₂ : Exact f₂ πh₂)
    (h : IsColimit (PushoutCocone.mk _ _ sqm.w)) : IsIso gQh :=
  by
  have : epi gQh := by
    refine' Preadditive.epi_of_cancel_zero _ fun P g hg => _
    apply zero_of_epi_comp πh₂
    apply PushoutCocone.IsColimit.hom_ext h
    ·
      rw [PushoutCocone.mk_inl, ← Category.assoc, ← sqᵣ.w, Category.assoc, hg, comp_zero,
        comp_zero]
    · rw [PushoutCocone.mk_inr, ← Category.assoc, H₂.w, comp_zero, zero_comp]
  obtain ⟨l, hl₁ : g₂ ≫ l = _, hl₂⟩ := PushoutCocone.IsColimit.desc' h πh₁ 0 (by simp [H₁.w])
  let coker := CategoryTheory.Abelian.isColimitOfExactOfEpi _ _ H₂
  obtain ⟨inv, hinv : πh₂ ≫ inv = l⟩ := CokernelCofork.IsColimit.desc' coker l hl₂
  have hinv' : gQh ≫ inv = 𝟙 _ := by
    rw [← cancel_epi πh₁, ← Category.assoc, sqᵣ.w, Category.assoc, hinv, hl₁, Category.comp_id]
  refine' ⟨⟨inv, hinv', _⟩⟩
  rw [← cancel_epi gQh, reassoc_of hinv', Category.comp_id]

end

theorem Commsq.bicartesian_iff_isos : sqm.Bicartesian ↔ IsIso gKh ∧ IsIso gQh :=
  by
  constructor
  · intro h; constructor
    ·
      exact
        isIso_of_isLimit gKh sqₗ sqm ((CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 0 2))
          ((CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 0 2)) h.isLimit
    ·
      exact
        isIso_of_isColimit gQh sqm sqᵣ ((CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 1 2))
          ((CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 1 2)) h.isColimit
  · rintro ⟨gKh_iso, gQh_iso⟩
    skip
    apply Commsq.Bicartesian.of_isLimit_of_is_colimt
    · apply IsLimit.ofPointIso (limit.isLimit _)
      · infer_instance
      · let r := pullback.lift _ _ sqm.w
        let x : Kh₁ ⟶ kernel (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) :=
          by
          refine' kernel.lift _ (ιh₁ ≫ r) _
          simp only [(H₁.extract 0 2).w, Category.assoc, pullback.lift_fst]
        have : is_iso x :=
          by
          let psq := Commsq.ofEq (@pullback.condition _ _ _ _ _ g₂ f₂ _)
          let hker :=
            Abelian.isLimitOfExactOfMono _ _ ((CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 0 2))
          obtain ⟨u : _ ⟶ Kh₂, hu⟩ :=
            KernelFork.IsLimit.lift' hker
              (kernel.ι (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) ≫ pullback.snd) _
          · rw [fork.ι_of_ι] at hu 
            let lsq := Commsq.ofEq hu.symm
            haveI : is_iso u := isIso_of_isLimit u lsq psq _ _ _
            · have hxu : x ≫ u = gKh := by
                simp only [← cancel_mono ιh₂, Category.assoc, hu, x, kernel.lift_ι_assoc, r,
                  pullback.lift_snd, sqₗ.w]
              have hx : x = gKh ≫ inv u := by rw [← IsIso.comp_inv_eq, IsIso.inv_inv, hxu]
              rw [hx]
              infer_instance
            · exact exact_kernel_ι
            · exact (CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 0 2)
            · exact CategoryTheory.Limits.pullbackIsPullback _ _
          · rw [Category.assoc, ← pullback.condition, kernel.condition_assoc, zero_comp]
        refine'
          @Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono _ _ _ 0 _ _ _ 0 _ _ _ 0 ιh₁ f₁ 0
            (kernel.ι (pullback.fst : pullback g₂ f₂ ⟶ A₁₂)) pullback.fst 0 x r (𝟙 _) _ _ _ _ _ πh₁
            πh₁ (𝟙 _) _ _ _ _ _ _ _ _ _ _ _
        · simp only [eq_iff_true_of_subsingleton]
        · simp only [kernel.lift_ι]
        · simp only [pullback.lift_fst, Category.comp_id]
        · simp only [Category.id_comp, Category.comp_id]
        · exact exact_zero_mono ιh₁
        · exact (CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 0 2)
        · exact (CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 1 2)
        · exact exact_zero_mono (kernel.ι pullback.fst)
        · exact exact_kernel_ι
        · have : (pullback.fst : pullback g₂ f₂ ⟶ A₁₂) ≫ πh₁ = 0 :=
            by
            apply zero_of_comp_mono gQh
            rw [Category.assoc, sqᵣ.w, pullback.condition_assoc, (H₂.extract 1 2).w, comp_zero]
          apply Abelian.exact_of_is_cokernel _ _ this
          have hex := (CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 1 2)
          rw [← pullback.lift_fst _ _ sqm.w] at hex 
          exact isColimitOfIsColimitComp (Abelian.isColimitOfExactOfEpi _ _ hex) _
    · apply IsColimit.ofPointIso (colimit.isColimit _)
      · infer_instance
      · let r := pushout.desc _ _ sqm.w
        let x : cokernel (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) ⟶ Qh₂ :=
          by
          refine' cokernel.desc _ (r ≫ πh₂) _
          simp only [(H₂.extract 1 2).w, ← Category.assoc, pushout.inr_desc]
        have : is_iso x :=
          by
          let psq := Commsq.ofEq (@pushout.condition _ _ _ _ _ f₁ g₁ _)
          let hcoker :=
            Abelian.isColimitOfExactOfEpi _ _ ((CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 1 2))
          obtain ⟨u : Qh₁ ⟶ _, hu⟩ :=
            CokernelCofork.IsColimit.desc' hcoker
              (pushout.inl ≫ cokernel.π (pushout.inr : A₂₁ ⟶ pushout f₁ g₁)) _
          · rw [cofork.π_of_π] at hu 
            let lsq := Commsq.ofEq hu
            haveI : is_iso u := isIso_of_isColimit u psq lsq _ _ _
            · have hxu : u ≫ x = gQh := by
                simp only [← cancel_epi πh₁, hu, x, cokernel.π_desc, reassoc_of hu, r,
                  pushout.inl_desc_assoc, sqᵣ.w]
              have hx : x = inv u ≫ gQh := by rw [← IsIso.inv_comp_eq, IsIso.inv_inv, hxu]
              rw [hx]
              infer_instance
            · exact (CategoryTheory.exact_iff_exactSeq _ _).2 (H₁.extract 1 2)
            · exact exact_cokernel pushout.inr
            · exact CategoryTheory.Limits.pushoutIsPushout _ _
          · rw [← Category.assoc, pushout.condition, Category.assoc, cokernel.condition, comp_zero]
        refine'
          @Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono _ _ _ _ _ _ _ _ _ _ _ ιh₂
            (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) (cokernel.π (pushout.inr : A₂₁ ⟶ pushout f₁ g₁)) ιh₂
            f₂ πh₂ (𝟙 _) (𝟙 _) r x _ _ _ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _
        · simp only [Category.id_comp, Category.comp_id]
        · simp only [Category.id_comp, pushout.inr_desc]
        · simp only [cokernel.π_desc]
        · simp only [eq_iff_true_of_subsingleton]
        · have : ιh₂ ≫ (pushout.inr : A₂₁ ⟶ pushout f₁ g₁) = 0 :=
            by
            apply zero_of_epi_comp gKh
            rw [← sqₗ.w_assoc, ← pushout.condition, reassoc_of (H₁.extract 0 2).w, zero_comp]
          apply Abelian.exact_of_is_kernel _ _ this
          have hex := (CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 0 2)
          rw [← pushout.inr_desc _ _ sqm.w] at hex 
          exact isLimitOfIsLimitComp (Abelian.isLimitOfExactOfMono _ _ hex) _
        · exact exact_cokernel pushout.inr
        · exact exact_epi_zero (cokernel.π pushout.inr)
        · exact (CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 0 2)
        · exact (CategoryTheory.exact_iff_exactSeq _ _).2 (H₂.extract 1 2)
        · exact exact_epi_zero πh₂

