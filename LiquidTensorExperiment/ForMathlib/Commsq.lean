import LiquidTensorExperiment.ForMathlib.HomologyExact
import LiquidTensorExperiment.ForMathlib.SplitExact
import LiquidTensorExperiment.ForMathlib.SumStr

#align_import for_mathlib.commsq

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable {A₁₁ A₁₂ A₁₃ A₁₄ A₁₅ : 𝓐}

variable {A₂₁ A₂₂ A₂₃ A₂₄ A₂₅ : 𝓐}

variable {A₃₁ A₃₂ A₃₃ A₃₄ A₃₅ : 𝓐}

variable {A₄₁ A₄₂ A₄₃ A₄₄ A₄₅ : 𝓐}

variable {A₅₁ A₅₂ A₅₃ A₅₄ A₅₅ : 𝓐}

variable {f₁₁ : A₁₁ ⟶ A₁₂} {f₁₂ : A₁₂ ⟶ A₁₃} {f₁₃ : A₁₃ ⟶ A₁₄} {f₁₄ : A₁₄ ⟶ A₁₅}

variable {g₁₁ : A₁₁ ⟶ A₂₁} {g₁₂ : A₁₂ ⟶ A₂₂} {g₁₃ : A₁₃ ⟶ A₂₃} {g₁₄ : A₁₄ ⟶ A₂₄} {g₁₅ : A₁₅ ⟶ A₂₅}

variable {f₂₁ : A₂₁ ⟶ A₂₂} {f₂₂ : A₂₂ ⟶ A₂₃} {f₂₃ : A₂₃ ⟶ A₂₄} {f₂₄ : A₂₄ ⟶ A₂₅}

variable {g₂₁ : A₂₁ ⟶ A₃₁} {g₂₂ : A₂₂ ⟶ A₃₂} {g₂₃ : A₂₃ ⟶ A₃₃} {g₂₄ : A₂₄ ⟶ A₃₄} {g₂₅ : A₂₅ ⟶ A₃₅}

variable {f₃₁ : A₃₁ ⟶ A₃₂} {f₃₂ : A₃₂ ⟶ A₃₃} {f₃₃ : A₃₃ ⟶ A₃₄} {f₃₄ : A₃₄ ⟶ A₃₅}

variable {g₃₁ : A₃₁ ⟶ A₄₁} {g₃₂ : A₃₂ ⟶ A₄₂} {g₃₃ : A₃₃ ⟶ A₄₃} {g₃₄ : A₃₄ ⟶ A₄₄} {g₃₅ : A₃₅ ⟶ A₄₅}

variable {f₄₁ : A₄₁ ⟶ A₄₂} {f₄₂ : A₄₂ ⟶ A₄₃} {f₄₃ : A₄₃ ⟶ A₄₄} {f₄₄ : A₄₄ ⟶ A₄₅}

variable {g₄₁ : A₄₁ ⟶ A₅₁} {g₄₂ : A₄₂ ⟶ A₅₂} {g₄₃ : A₄₃ ⟶ A₅₃} {g₄₄ : A₄₄ ⟶ A₅₄} {g₄₅ : A₄₅ ⟶ A₅₅}

variable {f₅₁ : A₅₁ ⟶ A₅₂} {f₅₂ : A₅₂ ⟶ A₅₃} {f₅₃ : A₅₃ ⟶ A₅₄} {f₅₄ : A₅₄ ⟶ A₅₅}

section

variable (f₁₁ g₁₁ g₁₂ f₂₁)

/-- A *commutative square* is a commutative diagram of the following shape:
```
A₁₁ --- f₁₁ --> A₁₂
 |               |
g₁₁             g₁₂
 |               |
 v               v
A₂₁ --- f₂₁ --> A₂₂
```
The order of (explicit) variables is: top-to-bottom, left-to-right,
alternating between rows of horizontal maps and rows of vertical maps. -/
@[ext]
structure Commsq where
  s : 𝓐
  ι : A₁₁ ⟶ S
  π : S ⟶ A₂₂
  diag : A₁₁ ⟶ A₂₂
  Sum : SumStr A₁₂ A₂₁ S
  ι_fst : ι ≫ Sum.fst = f₁₁
  ι_snd : ι ≫ Sum.snd = g₁₁
  inl_π : Sum.inl ≫ π = g₁₂
  inr_π : Sum.inr ≫ π = f₂₁
  tr₁ : g₁₁ ≫ f₂₁ = diag
  tr₂ : f₁₁ ≫ g₁₂ = diag

end

namespace Commsq

attribute [simp, reassoc] ι_fst ι_snd inl_π inr_π

@[reassoc]
theorem w (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁ := by rw [sq.tr₁, sq.tr₂]

@[reassoc]
theorem w_inv [IsIso g₁₁] [IsIso g₁₂] (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) :
    inv g₁₁ ≫ f₁₁ = f₂₁ ≫ inv g₁₂ := by
  rw [IsIso.eq_comp_inv, Category.assoc, sq.w, IsIso.inv_hom_id_assoc]

def ofEq (w : f₁₁ ≫ g₁₂ = g₁₁ ≫ f₂₁) : Commsq f₁₁ g₁₁ g₁₂ f₂₁
    where
  s := A₁₂ ⊞ A₂₁
  ι := biprod.lift f₁₁ g₁₁
  π := biprod.desc g₁₂ f₂₁
  diag := g₁₁ ≫ f₂₁
  Sum := SumStr.biprod _ _
  ι_fst := biprod.lift_fst _ _
  ι_snd := biprod.lift_snd _ _
  inl_π := biprod.inl_desc _ _
  inr_π := biprod.inr_desc _ _
  tr₁ := rfl
  tr₂ := w

def symm (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : Commsq g₁₁ f₁₁ f₂₁ g₁₂ :=
  { sq with
    Sum := sq.Sum.symm
    ι_fst := sq.ι_snd
    ι_snd := sq.ι_fst
    inl_π := sq.inr_π
    inr_π := sq.inl_π
    tr₁ := sq.tr₂
    tr₂ := sq.tr₁ }

theorem ι_eq (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq.ι = f₁₁ ≫ sq.Sum.inl + g₁₁ ≫ sq.Sum.inr :=
  by
  rw [← cancel_mono (𝟙 sq.S), ← sq.sum.total]
  simp only [Preadditive.add_comp, Category.assoc, ι_fst_assoc, ι_snd_assoc, Preadditive.comp_add,
    Preadditive.add_comp_assoc, SumStr.inl_fst, Category.comp_id, SumStr.inr_fst, comp_zero,
    add_zero, SumStr.inl_snd, SumStr.inr_snd, zero_add]

theorem π_eq (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq.π = sq.Sum.fst ≫ g₁₂ + sq.Sum.snd ≫ f₂₁ :=
  by
  rw [← cancel_epi (𝟙 sq.S), ← sq.sum.total]
  simp only [Preadditive.add_comp, Category.assoc, inl_π, inr_π, Preadditive.comp_add,
    Preadditive.add_comp_assoc, SumStr.inl_fst, Category.comp_id, SumStr.inr_fst, comp_zero,
    add_zero, SumStr.inl_snd, SumStr.inr_snd, zero_add]

section Iso

open CategoryTheory.Preadditive

theorem ι_iso_hom (sq₁ sq₂ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq₁.ι ≫ (sq₁.Sum.Iso sq₂.Sum).hom = sq₂.ι :=
  by
  simp only [SumStr.iso_hom, comp_add, ι_fst_assoc, ι_snd_assoc]
  simp only [← sq₂.ι_fst_assoc, ← sq₂.ι_snd_assoc, ← comp_add, SumStr.total, Category.comp_id]

theorem iso_hom_π (sq₁ sq₂ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : (sq₁.Sum.Iso sq₂.Sum).hom ≫ sq₂.π = sq₁.π :=
  by
  simp only [SumStr.iso_hom, add_comp, Category.assoc, inl_π, inr_π]
  simp only [← sq₁.inl_π, ← sq₁.inr_π]
  simp only [← Category.assoc, ← add_comp, SumStr.total, Category.id_comp]

theorem ι_iso_inv (sq₁ sq₂ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq₂.ι ≫ (sq₁.Sum.Iso sq₂.Sum).inv = sq₁.ι :=
  ι_iso_hom _ _

theorem iso_inv_π (sq₁ sq₂ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : (sq₁.Sum.Iso sq₂.Sum).inv ≫ sq₁.π = sq₂.π :=
  iso_hom_π _ _

end Iso

theorem ofIso (e₁₁ : A₁₁ ≅ A₃₃) (e₁₂ : A₁₂ ≅ A₃₄) (e₂₁ : A₂₁ ≅ A₄₃) (e₂₂ : A₂₂ ≅ A₄₄)
    (sqa : Commsq f₁₁ e₁₁.hom e₁₂.hom f₃₃) (sqb : Commsq g₁₁ e₁₁.hom e₂₁.hom g₃₃)
    (sqc : Commsq g₁₂ e₁₂.hom e₂₂.hom g₃₄) (sqd : Commsq f₂₁ e₂₁.hom e₂₂.hom f₄₃)
    (sq1 : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : Commsq f₃₃ g₃₃ g₃₄ f₄₃ :=
  ofEq <| by rw [← cancel_epi e₁₁.hom, ← sqa.w_assoc, ← sqc.w, ← sqb.w_assoc, ← sqd.w, sq1.w_assoc]

def kernel (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) :
    Commsq (kernel.ι f₁₁) (kernel.map _ _ _ _ sq.w) g₁₁ (kernel.ι f₂₁) :=
  Commsq.ofEq <| by simp only [kernel.lift_ι]

def cokernel (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) :
    Commsq (cokernel.π f₁₁) g₁₂ (cokernel.map _ _ _ _ sq.w) (cokernel.π f₂₁) :=
  Commsq.ofEq <| by simp only [cokernel.π_desc]

def Bicartesian (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : Prop :=
  ShortExact (-f₁₁ ≫ sq.Sum.inl + g₁₁ ≫ sq.Sum.inr) sq.π

def Bicartesian.isLimit {sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq.Bicartesian) :
    IsLimit (PullbackCone.mk f₁₁ g₁₁ sq.w) :=
  PullbackCone.IsLimit.mk sq.w
    (fun s =>
      (@Abelian.isLimitOfExactOfMono _ _ _ _ _ _ _ _ h.Mono h.exact).lift
        (Fork.ofι (-s.fst ≫ sq.Sum.inl + s.snd ≫ sq.Sum.inr)
          (by
            simp only [s.condition, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
              inl_π, inr_π, add_left_neg, comp_zero])))
    (fun s =>
      by
      have : f₁₁ = -(-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) ≫ sq.sum.fst := by
        simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, SumStr.inl_fst,
          Category.comp_id, SumStr.inr_fst, comp_zero, add_zero, neg_neg]
      conv_lhs =>
        congr
        skip
        rw [this]
      rw [Preadditive.comp_neg, ← Category.assoc]
      erw [(@Abelian.isLimitOfExactOfMono _ _ _ _ _ _ _ _ h.mono h.exact).fac _
          WalkingParallelPair.zero]
      simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, comp_zero,
        Fork.ofι_π_app, SumStr.inl_fst, Category.comp_id, SumStr.inr_fst, add_zero, neg_neg])
    (fun s =>
      by
      have : g₁₁ = (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) ≫ sq.sum.snd := by
        simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, SumStr.inl_snd,
          comp_zero, neg_zero, SumStr.inr_snd, Category.comp_id, zero_add]
      conv_lhs =>
        congr
        skip
        rw [this]
      rw [← Category.assoc]
      erw [(@Abelian.isLimitOfExactOfMono _ _ _ _ _ _ _ _ h.mono h.exact).fac _
          WalkingParallelPair.zero]
      simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, comp_zero,
        Fork.ofι_π_app, SumStr.inl_snd, neg_zero, SumStr.inr_snd, Category.comp_id, zero_add])
    fun s m h₁ h₂ =>
    by
    apply Fork.IsLimit.hom_ext (@Abelian.isLimitOfExactOfMono _ _ _ _ _ _ _ _ h.mono h.exact)
    erw [IsLimit.fac]
    simp only [reassoc_of h₁, reassoc_of h₂, kernel_fork.ι_of_ι, Preadditive.comp_add,
      Preadditive.comp_neg, Fork.ofι_π_app]

def Bicartesian.isColimit {sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq.Bicartesian) :
    IsColimit (PushoutCocone.mk g₁₂ f₂₁ sq.w) :=
  PushoutCocone.IsColimit.mk sq.w
    (fun s =>
      (@Abelian.isColimitOfExactOfEpi _ _ _ _ _ _ _ _ h.Epi h.exact).desc
        (Cofork.ofπ (sq.Sum.fst ≫ s.inl + sq.Sum.snd ≫ s.inr)
          (by
            simp only [s.condition, Preadditive.comp_add, Preadditive.add_comp_assoc,
              Preadditive.neg_comp, Category.assoc, SumStr.inl_fst, Category.comp_id,
              SumStr.inr_fst, comp_zero, add_zero, SumStr.inl_snd, neg_zero, SumStr.inr_snd,
              zero_add, add_left_neg, zero_comp])))
    (fun s =>
      by
      conv_lhs =>
        congr
        rw [← sq.inl_π]
      rw [Category.assoc]
      erw [(@Abelian.isColimitOfExactOfEpi _ _ _ _ _ _ _ _ h.epi h.exact).fac _
          WalkingParallelPair.one]
      simp only [Preadditive.comp_add, add_zero, zero_comp, Cofork.ofπ_ι_app, SumStr.inl_fst_assoc,
        SumStr.inl_snd_assoc])
    (fun s =>
      by
      conv_lhs =>
        congr
        rw [← sq.inr_π]
      rw [Category.assoc]
      erw [(@Abelian.isColimitOfExactOfEpi _ _ _ _ _ _ _ _ h.epi h.exact).fac _
          WalkingParallelPair.one]
      simp only [Preadditive.comp_add, zero_add, zero_comp, Cofork.ofπ_ι_app, SumStr.inr_fst_assoc,
        SumStr.inr_snd_assoc])
    fun s m h₁ h₂ =>
    by
    apply
      Cofork.IsColimit.hom_ext (@Abelian.isColimitOfExactOfEpi _ _ _ _ _ _ _ _ h.epi h.exact)
    erw [IsColimit.fac]
    simp only [cokernel_cofork.π_of_π, Cofork.ofπ_ι_app]
    conv_lhs =>
      congr
      rw [← Category.id_comp sq.π]
    rw [← sq.sum.total]
    simp only [h₁, h₂, Preadditive.add_comp, Category.assoc, inl_π, inr_π]

theorem Bicartesian.of_isLimit_of_is_colimt {sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁}
    (hl : IsLimit (PullbackCone.mk f₁₁ g₁₁ sq.w)) (hc : IsColimit (PushoutCocone.mk g₁₂ f₂₁ sq.w)) :
    sq.Bicartesian :=
  by
  have h : (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) ≫ sq.π = 0 := by
    simp only [sq.w, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, inl_π, inr_π,
      add_left_neg]
  let hker : is_limit (KernelFork.ofι _ h) :=
    by
    fapply KernelFork.IsLimit.ofι
    · refine' fun T g hg => hl.lift (PullbackCone.mk (-g ≫ sq.sum.fst) (g ≫ sq.sum.snd) _)
      rw [sq.π_eq, Preadditive.comp_add] at hg 
      simp only [add_eq_zero_iff_eq_neg.1 hg, Preadditive.neg_comp, Category.assoc, neg_neg]
    · intro T g hg
      simp only [Preadditive.comp_add, Preadditive.comp_neg, ← Category.assoc]
      erw [hl.fac _ WalkingSpan.left, hl.fac _ WalkingSpan.right]
      simp only [Preadditive.neg_comp, Category.assoc, neg_neg, PullbackCone.mk_π_app_left,
        PullbackCone.mk_π_app_right, ← Preadditive.comp_add, sq.sum.total, Category.comp_id]
    · intro T g hg m hm
      apply PullbackCone.IsLimit.hom_ext hl
      · erw [PullbackCone.mk_fst, hl.fac _ WalkingSpan.left]
        simp only [← hm, Preadditive.neg_comp, Category.assoc, neg_neg, PullbackCone.mk_π_app_left,
          Preadditive.comp_neg, Preadditive.add_comp, SumStr.inl_fst, Category.comp_id,
          SumStr.inr_fst, comp_zero, add_zero]
      · erw [PullbackCone.mk_snd, hl.fac _ WalkingSpan.right]
        simp only [← hm, Preadditive.neg_comp, Category.assoc, PullbackCone.mk_π_app_right,
          Preadditive.add_comp, SumStr.inl_snd, comp_zero, neg_zero, SumStr.inr_snd,
          Category.comp_id, zero_add]
  let hcoker : is_colimit (CokernelCofork.ofπ _ h) :=
    by
    fapply CokernelCofork.IsColimit.ofπ
    · refine' fun T g hg => hc.desc (PushoutCocone.mk (sq.sum.inl ≫ g) (sq.sum.inr ≫ g) _)
      rwa [Preadditive.add_comp, Preadditive.neg_comp, add_eq_zero_iff_neg_eq, neg_neg,
        Category.assoc, Category.assoc] at hg 
    · intro T g hg
      simp only [sq.π_eq, Preadditive.add_comp, Category.assoc]
      erw [hc.fac _ WalkingCospan.left, hc.fac _ WalkingCospan.right]
      simp only [PushoutCocone.mk_ι_app_left, PushoutCocone.mk_ι_app_right, ← Category.assoc, ←
        Preadditive.add_comp, sq.sum.total, Category.id_comp]
    · intro T g hg m hm
      apply PushoutCocone.IsColimit.hom_ext hc
      · erw [PushoutCocone.mk_inl, hc.fac _ WalkingCospan.left]
        simp only [← hm, PushoutCocone.mk_ι_app_left, inl_π_assoc]
      · erw [PushoutCocone.mk_inr, hc.fac _ WalkingCospan.right]
        simp only [← hm, PushoutCocone.mk_ι_app_right, inr_π_assoc]
  haveI : mono (-f₁₁ ≫ sq.sum.inl + g₁₁ ≫ sq.sum.inr) := CategoryTheory.Limits.mono_of_isLimit_fork hker
  haveI : epi sq.π := CategoryTheory.Limits.epi_of_isColimit_cofork hcoker
  exact ⟨Abelian.exact_of_is_kernel _ _ h hker⟩

open CategoryTheory.Preadditive

theorem Bicartesian.congr {sq₁ : Commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq₁.Bicartesian)
    (sq₂ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq₂.Bicartesian :=
  by
  have := h.mono; have := h.epi; skip
  have hm : mono (-f₁₁ ≫ sq₂.sum.inl + g₁₁ ≫ sq₂.sum.inr) :=
    by
    suffices
      -f₁₁ ≫ sq₂.sum.inl + g₁₁ ≫ sq₂.sum.inr =
        (-f₁₁ ≫ sq₁.sum.inl + g₁₁ ≫ sq₁.sum.inr) ≫ (sq₁.sum.iso sq₂.sum).hom
      by rw [this]; apply mono_comp
    simp only [SumStr.iso_hom, comp_add, add_comp_assoc, neg_comp, Category.assoc, SumStr.inl_fst,
      Category.comp_id, SumStr.inr_fst, comp_zero, add_zero, SumStr.inl_snd, neg_zero,
      SumStr.inr_snd, zero_add]
  have he : epi sq₂.π := by rw [← sq₁.iso_inv_π sq₂]; apply epi_comp
  have H : exact (-f₁₁ ≫ sq₂.sum.inl + g₁₁ ≫ sq₂.sum.inr) sq₂.π :=
    by
    apply exact_of_iso_of_exact' _ _ _ _ (iso.refl _) (sq₁.sum.iso sq₂.sum) (iso.refl _) _ _ h.exact
    ·
      simp only [Iso.refl_hom, comp_add, Category.id_comp, SumStr.iso_hom, add_comp_assoc, neg_comp,
        Category.assoc, SumStr.inl_fst, SumStr.inr_fst, comp_zero, add_zero, SumStr.inl_snd,
        neg_zero, SumStr.inr_snd, zero_add]
    · simp only [Iso.refl_hom, Category.comp_id, iso_hom_π]
  exact ⟨H⟩

theorem bicartesian_iff (sq₁ sq₂ : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq₁.Bicartesian ↔ sq₂.Bicartesian :=
  ⟨fun h => h.congr _, fun h => h.congr _⟩

--move this (do we want this?)
instance {C : Type _} [Category C] [Preadditive C] {X Y : C} : Neg (X ≅ Y) :=
  ⟨fun e => ⟨-e.hom, -e.inv, by simp, by simp⟩⟩

@[simp]
theorem neg_iso_hom {C : Type _} [Category C] [Preadditive C] {X Y : C} {e : X ≅ Y} :
    (-e).hom = -e.hom :=
  rfl

@[simp]
theorem neg_iso_inv {C : Type _} [Category C] [Preadditive C] {X Y : C} {e : X ≅ Y} :
    (-e).inv = -e.inv :=
  rfl

-- move me
@[simp]
theorem CategoryTheory.ShortExact.neg_left (h : ShortExact f₁₁ f₁₂) : ShortExact (-f₁₁) f₁₂ :=
  by
  haveI := h.mono; haveI := h.epi
  refine' ⟨_⟩
  have : -f₁₁ = (-iso.refl _).hom ≫ f₁₁ := by
    simp only [neg_iso_hom, Iso.refl_hom, Category.id_comp, neg_comp]
  rw [this, exact_iso_comp]
  exact h.exact

-- move me
@[simp]
theorem CategoryTheory.ShortExact.neg_left_iff : ShortExact (-f₁₁) f₁₂ ↔ ShortExact f₁₁ f₁₂ :=
  by
  refine' ⟨_, fun h => h.neg_left⟩
  intro h; simpa only [neg_neg] using h.neg_left

theorem Bicartesian.symm {sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁} (h : sq.Bicartesian) : sq.symm.Bicartesian :=
  by
  rw [bicartesian] at h ⊢
  rw [← CategoryTheory.ShortExact.neg_left_iff]
  simp only [neg_add_rev, neg_neg]
  exact h

theorem Bicartesian.symm_iff (sq : Commsq f₁₁ g₁₁ g₁₂ f₂₁) : sq.symm.Bicartesian ↔ sq.Bicartesian :=
  ⟨fun h => h.symm, fun h => h.symm⟩

section

variable (g₁₁ g₁₂ g₁₃)

-- move me
theorem ShortExact.of_iso (h : ShortExact f₁₁ f₁₂) (sq1 : Commsq f₁₁ g₁₁ g₁₂ f₂₁)
    (sq2 : Commsq f₁₂ g₁₂ g₁₃ f₂₂) [IsIso g₁₁] [IsIso g₁₂] [IsIso g₁₃] : ShortExact f₂₁ f₂₂ :=
  by
  have := h.mono; have := h.epi; skip
  have : mono f₂₁ :=
    by
    suffices mono (f₂₁ ≫ inv g₁₂) by skip; apply mono_of_mono f₂₁ (inv g₁₂)
    rw [← sq1.w_inv]; infer_instance
  have : epi f₂₂ := by
    suffices epi (g₁₂ ≫ f₂₂) by skip; apply epi_of_epi g₁₂ f₂₂
    · rw [← sq2.w]; apply epi_comp
  skip; refine' ⟨_⟩
  apply
    exact_of_iso_of_exact' _ _ _ _ (CategoryTheory.asIso g₁₁) (CategoryTheory.asIso g₁₂) (CategoryTheory.asIso g₁₃) sq1.symm.w sq2.symm.w
      h.exact

end

theorem Bicartesian.of_iso (e₁₁ : A₁₁ ≅ A₃₃) (e₁₂ : A₁₂ ≅ A₃₄) (e₂₁ : A₂₁ ≅ A₄₃) (e₂₂ : A₂₂ ≅ A₄₄)
    {sq1 : Commsq f₁₁ g₁₁ g₁₂ f₂₁} {sq2 : Commsq f₃₃ g₃₃ g₃₄ f₄₃}
    (sqa : Commsq f₁₁ e₁₁.hom e₁₂.hom f₃₃) (sqb : Commsq g₁₁ e₁₁.hom e₂₁.hom g₃₃)
    (sqc : Commsq g₁₂ e₁₂.hom e₂₂.hom g₃₄) (sqd : Commsq f₂₁ e₂₁.hom e₂₂.hom f₄₃)
    (h : sq1.Bicartesian) : sq2.Bicartesian :=
  by
  let e : sq1.S ≅ sq2.S := _
  apply ShortExact.of_iso e₁₁.hom e.hom e₂₂.hom h
  pick_goal 3
  ·
    refine'
        ⟨sq1.sum.fst ≫ e₁₂.hom ≫ sq2.sum.inl + sq1.sum.snd ≫ e₂₁.hom ≫ sq2.sum.inr,
          sq2.sum.fst ≫ e₁₂.inv ≫ sq1.sum.inl + sq2.sum.snd ≫ e₂₁.inv ≫ sq1.sum.inr, _, _⟩ <;>
      · dsimp;
        simp only [comp_add, add_comp_assoc, Category.assoc, SumStr.inl_fst, Category.comp_id,
          SumStr.inr_fst, comp_zero, add_zero, Iso.hom_inv_id_assoc, SumStr.inl_snd, SumStr.inr_snd,
          zero_add, sq1.sum.total, sq2.sum.total, Iso.inv_hom_id_assoc]
  · apply Commsq.ofEq; dsimp
    simp only [comp_add, add_comp_assoc, neg_comp, Category.assoc, SumStr.inl_fst, Category.comp_id,
      SumStr.inr_fst, comp_zero, add_zero, SumStr.inl_snd, neg_zero, SumStr.inr_snd, zero_add,
      comp_neg, sqa.w_assoc, sqb.w_assoc]
  · apply Commsq.ofEq; dsimp
    simp only [add_comp, Category.assoc, inl_π, inr_π, ← sqc.w, ← sqd.w, sq1.π_eq]

end Commsq

