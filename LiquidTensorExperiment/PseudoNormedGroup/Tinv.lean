import LiquidTensorExperiment.PseudoNormedGroup.CLC

#align_import pseudo_normed_group.Tinv

/-!

# V-hat((M_c)^n)^{T⁻¹}

This file defines a fundamental construction defined just above Definition 9.3
in `analytic.pdf`: the subspac of V-hat(M_c^n) where the two actions of T⁻¹ coincide.

## Main definition

Here `M` is a profinitely filtered pseudo-normed group with `T⁻¹` scaling things by `r'`,
`V` is a seminormed group with `T⁻¹` scaling norms by `r`, `c` is a real (a filtration coefficient)
and `n` is a natural.

- `CLCFPTinv r V r' c n M`: the seminormed group defined as the subgroup of `V-hat(M_c^n)` where
  the two actions of `T⁻¹` (one coming from the action on M, the other coming from the
  action on V) coincide.

-/


open scoped Classical NNReal

noncomputable section

attribute [local instance] typePow

namespace CategoryTheory

theorem comm_sq₂ {C} [Category C] {A₁ A₂ A₃ B₁ B₂ B₃ : C} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
    {f₃ : A₃ ⟶ B₃} {a : A₁ ⟶ A₂} {a' : A₂ ⟶ A₃} {b : B₁ ⟶ B₂} {b' : B₂ ⟶ B₃} (h₁ : a ≫ f₂ = f₁ ≫ b)
    (h₂ : a' ≫ f₃ = f₂ ≫ b') : (a ≫ a') ≫ f₃ = f₁ ≫ b ≫ b' := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, ← Category.assoc]

end CategoryTheory

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup CategoryTheory.Limits

open NormedAddGroupHom

namespace SemiNormedGroupCat

def equalizer {V W : SemiNormedGroupCat} (f g : V ⟶ W) :=
  of (f.equalizer g)

namespace equalizer

def ι {V W : SemiNormedGroupCat} (f g : V ⟶ W) : equalizer f g ⟶ V :=
  NormedAddGroupHom.Equalizer.ι _ _

@[reassoc]
theorem condition {V W : SemiNormedGroupCat} (f g : V ⟶ W) : ι f g ≫ f = ι f g ≫ g :=
  NormedAddGroupHom.Equalizer.comp_ι_eq _ _

theorem ι_range {V W : SemiNormedGroupCat} (f g : V ⟶ W) :
    NormedAddGroupHom.range (ι f g) = NormedAddGroupHom.ker (f - g) :=
  by
  ext x; rw [NormedAddGroupHom.mem_range, NormedAddGroupHom.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩; rw [NormedAddGroupHom.sub_apply]; exact x.2
  · intro h; refine' ⟨⟨x, h⟩, rfl⟩

theorem ι_range' {V W : SemiNormedGroupCat} (f g : V ⟶ W) :
    NormedAddGroupHom.range (ι f g) = NormedAddGroupHom.ker (g - f) :=
  by
  rw [ι_range]; ext x
  rw [NormedAddGroupHom.mem_ker, NormedAddGroupHom.mem_ker, NormedAddGroupHom.sub_apply, NormedAddGroupHom.sub_apply, sub_eq_zero, sub_eq_zero]
  exact eq_comm

def map {V₁ V₂ W₁ W₂ : SemiNormedGroupCat} {f₁ f₂ g₁ g₂} (φ : V₁ ⟶ V₂) (ψ : W₁ ⟶ W₂)
    (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) : equalizer f₁ g₁ ⟶ equalizer f₂ g₂ :=
  NormedAddGroupHom.Equalizer.map _ _ hf.symm hg.symm

theorem map_comp_ι {V₁ V₂ W₁ W₂ : SemiNormedGroupCat} {f₁ f₂ g₁ g₂} (φ : V₁ ⟶ V₂) (ψ : W₁ ⟶ W₂)
    (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) : map φ ψ hf hg ≫ ι f₂ g₂ = ι f₁ g₁ ≫ φ :=
  rfl

theorem map_congr {V₁ V₂ W₁ W₂ : SemiNormedGroupCat} {f₁ f₂ g₁ g₂} {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂}
    {V₁' V₂' W₁' W₂' : SemiNormedGroupCat} {f₁' f₂' g₁' g₂'} {φ' : V₁' ⟶ V₂'} {ψ' : W₁' ⟶ W₂'}
    {hf : φ ≫ f₂ = f₁ ≫ ψ} {hg : φ ≫ g₂ = g₁ ≫ ψ} {hf' : φ' ≫ f₂' = f₁' ≫ ψ'}
    {hg' : φ' ≫ g₂' = g₁' ≫ ψ'} (Hφ : Arrow.mk φ = Arrow.mk φ') (Hψ : Arrow.mk ψ = Arrow.mk ψ')
    (Hf₁ : Arrow.mk f₁ = Arrow.mk f₁') (Hf₂ : Arrow.mk f₂ = Arrow.mk f₂')
    (Hg₁ : Arrow.mk g₁ = Arrow.mk g₁') (Hg₂ : Arrow.mk g₂ = Arrow.mk g₂') :
    Arrow.mk (map φ ψ hf hg) = Arrow.mk (map φ' ψ' hf' hg') := by
  cases Hφ
  cases Hψ
  cases Hf₁
  cases Hf₂
  cases Hg₁
  cases Hg₂
  rfl

theorem map_comp_map {V₁ V₂ V₃ W₁ W₂ W₃ : SemiNormedGroupCat} {f₁ f₂ f₃ g₁ g₂ g₃} {φ : V₁ ⟶ V₂}
    {ψ : W₁ ⟶ W₂} {φ' : V₂ ⟶ V₃} {ψ' : W₂ ⟶ W₃} (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ)
    (hf' : φ' ≫ f₃ = f₂ ≫ ψ') (hg' : φ' ≫ g₃ = g₂ ≫ ψ') :
    map φ ψ hf hg ≫ map φ' ψ' hf' hg' = map (φ ≫ φ') (ψ ≫ ψ') (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
  by ext; rfl

theorem map_id {J} [Category J] {V W : SemiNormedGroupCat} (f g : V ⟶ W) :
    map (𝟙 V) (𝟙 W) (show 𝟙 V ≫ f = f ≫ 𝟙 W by simp) (show 𝟙 V ≫ g = g ≫ 𝟙 W by simp) = 𝟙 _ := by
  ext; rfl

theorem norm_map_le {V₁ V₂ W₁ W₂ : SemiNormedGroupCat} {f₁ f₂ g₁ g₂} {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂}
    (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) (C : ℝ) (hφ : ‖ι f₁ g₁ ≫ φ‖ ≤ C) :
    ‖map φ ψ hf hg‖ ≤ C :=
  NormedAddGroupHom.Equalizer.norm_map_le _ _ C hφ

@[simps obj map]
protected def f {J} [Category J] {V W : J ⥤ SemiNormedGroupCat} (f g : V ⟶ W) :
    J ⥤ SemiNormedGroupCat
    where
  obj X := of (NormedAddGroupHom.equalizer (f.app X) (g.app X))
  map φ := equalizer.map (V.map φ) (W.map φ) (f.naturality _) (g.naturality _)
  map_id X := by
    simp only [CategoryTheory.Functor.map_id] <;> exact NormedAddGroupHom.Equalizer.map_id
  map_comp φ ψ := by
    simp only [Functor.map_comp]
    exact (map_comp_map _ _ _ _).symm

@[simps]
def mapNat {J} [Category J] {V₁ V₂ W₁ W₂ : J ⥤ SemiNormedGroupCat} {f₁ f₂ g₁ g₂} (φ : V₁ ⟶ V₂)
    (ψ : W₁ ⟶ W₂) (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) :
    equalizer.f f₁ g₁ ⟶ equalizer.f f₂ g₂
    where
  app X :=
    equalizer.map (φ.app X) (ψ.app X) (by rw [← NatTrans.comp_app, ← NatTrans.comp_app, hf])
      (by rw [← NatTrans.comp_app, ← NatTrans.comp_app, hg])
  naturality X Y α := by simp only [equalizer.f_map, map_comp_map, NatTrans.naturality]

theorem mapNat_comp_mapNat {J} [Category J] {V₁ V₂ V₃ W₁ W₂ W₃ : J ⥤ SemiNormedGroupCat}
    {f₁ f₂ f₃ g₁ g₂ g₃} {φ : V₁ ⟶ V₂} {ψ : W₁ ⟶ W₂} {φ' : V₂ ⟶ V₃} {ψ' : W₂ ⟶ W₃}
    (hf : φ ≫ f₂ = f₁ ≫ ψ) (hg : φ ≫ g₂ = g₁ ≫ ψ) (hf' : φ' ≫ f₃ = f₂ ≫ ψ')
    (hg' : φ' ≫ g₃ = g₂ ≫ ψ') :
    mapNat φ ψ hf hg ≫ mapNat φ' ψ' hf' hg' =
      mapNat (φ ≫ φ') (ψ ≫ ψ') (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
  by
  -- Porting note: Lean 3 `ext` was recursive
  apply NatTrans.ext
  funext X
  exact map_comp_map (NatTrans.congr_app hf X) (NatTrans.congr_app hg X)
    (NatTrans.congr_app hf' X) (NatTrans.congr_app hg' X)

theorem mapNat_id {J} [Category J] {V W : J ⥤ SemiNormedGroupCat} (f g : V ⟶ W) :
    mapNat (𝟙 V) (𝟙 W) (show 𝟙 V ≫ f = f ≫ 𝟙 W by simp) (show 𝟙 V ≫ g = g ≫ 𝟙 W by simp) = 𝟙 _ := by
  -- Porting note: Lean 3 `ext` was recursive
  apply NatTrans.ext
  funext X
  exact NormedAddGroupHom.Equalizer.map_id

end equalizer

end SemiNormedGroupCat

universe u

variable (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

variable (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)]

variable (M M₁ M₂ M₃ : ProFiltPseuNormGrpWithTinv.{u} r')

variable (c c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ : ℝ≥0) (l m n : ℕ)

variable (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)

def cLCTinv (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    {A B : Profiniteᵒᵖ} (f g : A ⟶ B) : SemiNormedGroupCat :=
  SemiNormedGroupCat.of <|
    NormedAddGroupHom.equalizer ((cLC V).map f) ((cLC V).map g ≫ (cLC.tInv r V).app B)

namespace cLCTinv

def ι (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)] {A B : Profiniteᵒᵖ}
    (f g : A ⟶ B) : cLCTinv r V f g ⟶ (cLC V).obj A :=
  SemiNormedGroupCat.equalizer.ι _ _

theorem ι_range (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
    NormedAddGroupHom.range (ι r V f g) =
      NormedAddGroupHom.ker ((cLC V).map f - (cLC V).map g ≫ (cLC.tInv r V).app B) :=
  SemiNormedGroupCat.equalizer.ι_range _ _

theorem ι_range' (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    {A B : Profiniteᵒᵖ} (f g : A ⟶ B) :
    NormedAddGroupHom.range (ι r V f g) =
      NormedAddGroupHom.ker ((cLC V).map g ≫ (cLC.tInv r V).app B - (cLC V).map f) :=
  SemiNormedGroupCat.equalizer.ι_range' _ _

def map {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂) (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂)
    (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) : cLCTinv r V f₁ g₁ ⟶ cLCTinv r V f₂ g₂ :=
  SemiNormedGroupCat.equalizer.map ((cLC V).map ϕ) ((cLC V).map ψ)
      (by rw [← Functor.map_comp, ← Functor.map_comp, h₁]) <|
    by
    rw [← Category.assoc, ← Functor.map_comp, h₂, Functor.map_comp, Category.assoc,
      (cLC.tInv _ _).naturality, Category.assoc]

theorem map_comp_ι {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂) (ϕ : A₁ ⟶ A₂)
    (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
    map r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂ ≫ ι r V f₂ g₂ = ι r V f₁ g₁ ≫ (cLC V).map ϕ :=
  SemiNormedGroupCat.equalizer.map_comp_ι _ _ _ _

theorem map_normNoninc {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂) (ϕ : A₁ ⟶ A₂)
    (ψ : B₁ ⟶ B₂) (h₁ h₂) :
    NormedAddGroupHom.NormNoninc (cLCTinv.map r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂) :=
  by
  dsimp only [map, SemiNormedGroupCat.equalizer.map]
  exact NormedAddGroupHom.Equalizer.map_normNoninc _ _ (cLC.map_normNoninc _ _)

theorem norm_map_le {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂) (ϕ : A₁ ⟶ A₂)
    (ψ : B₁ ⟶ B₂) (h₁ h₂) (C : ℝ≥0)
    (H :
      ‖(SemiNormedGroupCat.equalizer.ι ((cLC V).map f₁)
              ((cLC V).map g₁ ≫ (cLC.tInv r V).app B₁) ≫
            (cLC V).map ϕ)‖ ≤
        C) :
    ‖cLCTinv.map r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂‖ ≤ C :=
  SemiNormedGroupCat.equalizer.norm_map_le _ _ C H

@[simp]
theorem map_id {A B : Profiniteᵒᵖ} (f g : A ⟶ B) : map r V f g f g (𝟙 A) (𝟙 B) rfl rfl = 𝟙 _ :=
  by
  simp only [map, SemiNormedGroupCat.equalizer.map, CategoryTheory.Functor.map_id]
  exact NormedAddGroupHom.Equalizer.map_id

theorem map_comp {A₁ A₂ A₃ B₁ B₂ B₃ : Profiniteᵒᵖ} {f₁ g₁ : A₁ ⟶ B₁} {f₂ g₂ : A₂ ⟶ B₂}
    {f₃ g₃ : A₃ ⟶ B₃} (ϕ₁ : A₁ ⟶ A₂) (ϕ₂ : A₂ ⟶ A₃) (ψ₁ : B₁ ⟶ B₂) (ψ₂ : B₂ ⟶ B₃)
    (h1 h2 h3 h4 h5 h6) :
    cLCTinv.map r V f₁ g₁ f₃ g₃ (ϕ₁ ≫ ϕ₂) (ψ₁ ≫ ψ₂) h1 h2 =
      cLCTinv.map r V f₁ g₁ f₂ g₂ ϕ₁ ψ₁ h3 h4 ≫ cLCTinv.map r V f₂ g₂ f₃ g₃ ϕ₂ ψ₂ h5 h6 :=
  by
  simp only [map, CategoryTheory.Functor.map_comp]
  exact (SemiNormedGroupCat.equalizer.map_comp_map _ _ _ _).symm

theorem map_comp_map {A₁ A₂ A₃ B₁ B₂ B₃ : Profiniteᵒᵖ} {f₁ g₁ : A₁ ⟶ B₁} {f₂ g₂ : A₂ ⟶ B₂}
    {f₃ g₃ : A₃ ⟶ B₃} (ϕ₁ : A₁ ⟶ A₂) (ϕ₂ : A₂ ⟶ A₃) (ψ₁ : B₁ ⟶ B₂) (ψ₂ : B₂ ⟶ B₃) (h₁ h₂ h₃ h₄) :
    cLCTinv.map r V f₁ g₁ f₂ g₂ ϕ₁ ψ₁ h₁ h₂ ≫ cLCTinv.map r V f₂ g₂ f₃ g₃ ϕ₂ ψ₂ h₃ h₄ =
      cLCTinv.map r V f₁ g₁ f₃ g₃ (ϕ₁ ≫ ϕ₂) (ψ₁ ≫ ψ₂) (comm_sq₂ h₁ h₃) (comm_sq₂ h₂ h₄) :=
  (map_comp _ _ _ _ _ _ _ _ _ _ _ _).symm

@[simps]
def mapIso {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂) (ϕ : A₁ ≅ A₂)
    (ψ : B₁ ≅ B₂) (h₁ : ϕ.hom ≫ f₂ = f₁ ≫ ψ.hom) (h₂ : ϕ.hom ≫ g₂ = g₁ ≫ ψ.hom) :
    cLCTinv r V f₁ g₁ ≅ cLCTinv r V f₂ g₂
    where
  hom := map r V f₁ g₁ f₂ g₂ ϕ.hom ψ.hom h₁ h₂
  inv :=
    map r V f₂ g₂ f₁ g₁ ϕ.inv ψ.inv (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₁])
      (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₂])
  hom_inv_id := by simp only [map_comp_map, Iso.hom_inv_id]; apply map_id
  inv_hom_id := by simp only [map_comp_map, Iso.inv_hom_id]; apply map_id

-- Porting note: the types `α` and `β` of `Isometry` are given explicitly, since otherwise
-- instance search fails on `(forget SemiNormedGroupCat).obj (cLCTinv r V f₁ g₁)`.
theorem mapIso_isometry {A₁ B₁ A₂ B₂ : Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
    (ϕ : A₁ ≅ A₂) (ψ : B₁ ≅ B₂) (h₁ : ϕ.hom ≫ f₂ = f₁ ≫ ψ.hom) (h₂ : ϕ.hom ≫ g₂ = g₁ ≫ ψ.hom) :
    Isometry (α := ↥(cLCTinv r V f₁ g₁)) (β := ↥(cLCTinv r V f₂ g₂))
      (mapIso r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂).hom := by
  refine' SemiNormedGroupCat.iso_isometry_of_normNoninc (mapIso r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂) _ _
  · exact map_normNoninc r V f₁ g₁ f₂ g₂ ϕ.hom ψ.hom h₁ h₂
  · exact map_normNoninc r V f₂ g₂ f₁ g₁ ϕ.inv ψ.inv
      (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₁])
      (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₂])

@[simps]
protected def f {J} [Category J] (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V]
    [Fact (0 < r)] {A B : J ⥤ Profiniteᵒᵖ} (f g : A ⟶ B) : J ⥤ SemiNormedGroupCat
    where
  obj X := cLCTinv r V (f.app X) (g.app X)
  map φ := map _ _ _ _ _ _ (A.map φ) (B.map φ) (f.naturality _) (g.naturality _)
  map_id X := by simp only [CategoryTheory.Functor.map_id] <;> apply map_id
  map_comp φ ψ := by simp only [Functor.map_comp] <;> apply map_comp

theorem f_def {J} [Category J] (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    {A B : J ⥤ Profiniteᵒᵖ} (f g : A ⟶ B) :
    cLCTinv.f r V f g =
      SemiNormedGroupCat.equalizer.f (whiskerRight f (cLC V))
        (whiskerRight g (cLC V) ≫ whiskerLeft B (cLC.tInv r V)) :=
  rfl

@[simps]
def mapNat {J} [Category J] {A₁ B₁ A₂ B₂ : J ⥤ Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
    (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
    cLCTinv.f r V f₁ g₁ ⟶ cLCTinv.f r V f₂ g₂
    where
  app X :=
    map r V (f₁.app X) (g₁.app X) (f₂.app X) (g₂.app X) (ϕ.app X) (ψ.app X)
      (by rw [← NatTrans.comp_app, h₁, NatTrans.comp_app])
      (by rw [← NatTrans.comp_app, h₂, NatTrans.comp_app])
  naturality X Y α := by simp only [cLCTinv.f_map, map_comp_map, ϕ.naturality, ψ.naturality]

-- Porting note: in Lean 3 the right hand side was given by a tactic block ending in `ext; simp`;
-- we write down the resulting term explicitly (the cast along `f_def` is a definitional unfolding),
-- and give the implicit arguments of `equalizer.mapNat` explicitly to avoid a timeout.
theorem mapNat_def {J} [Category J] {A₁ B₁ A₂ B₂ : J ⥤ Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁)
    (f₂ g₂ : A₂ ⟶ B₂) (ϕ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂) (h₁ : ϕ ≫ f₂ = f₁ ≫ ψ) (h₂ : ϕ ≫ g₂ = g₁ ≫ ψ) :
    mapNat r V f₁ g₁ f₂ g₂ ϕ ψ h₁ h₂ =
      (SemiNormedGroupCat.equalizer.mapNat
        (f₁ := whiskerRight f₁ (cLC V)) (f₂ := whiskerRight f₂ (cLC V))
        (g₁ := whiskerRight g₁ (cLC V) ≫ whiskerLeft B₁ (cLC.tInv r V))
        (g₂ := whiskerRight g₂ (cLC V) ≫ whiskerLeft B₂ (cLC.tInv r V))
        (whiskerRight ϕ (cLC V)) (whiskerRight ψ (cLC V))
        (by rw [← CategoryTheory.whiskerRight_comp, ← CategoryTheory.whiskerRight_comp, h₁])
        (by
          apply NatTrans.ext
          funext x
          simp only [NatTrans.comp_app, CategoryTheory.whiskerLeft_app,
            CategoryTheory.whiskerRight_app]
          rw [Category.assoc, ← (cLC.tInv r V).naturality, ← Category.assoc, ← Category.assoc,
            ← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app, h₂]) :
        cLCTinv.f r V f₁ g₁ ⟶ cLCTinv.f r V f₂ g₂) :=
  rfl

-- @[simps]
def mapNatIso {J} [Category J] {A₁ B₁ A₂ B₂ : J ⥤ Profiniteᵒᵖ} (f₁ g₁ : A₁ ⟶ B₁) (f₂ g₂ : A₂ ⟶ B₂)
    (ϕ : A₁ ≅ A₂) (ψ : B₁ ≅ B₂) (h₁ : ϕ.hom ≫ f₂ = f₁ ≫ ψ.hom) (h₂ : ϕ.hom ≫ g₂ = g₁ ≫ ψ.hom) :
    cLCTinv.f r V f₁ g₁ ≅ cLCTinv.f r V f₂ g₂
    where
  hom := mapNat r V f₁ g₁ f₂ g₂ ϕ.hom ψ.hom h₁ h₂
  inv :=
    mapNat r V f₂ g₂ f₁ g₁ ϕ.inv ψ.inv
      (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₁])
      (by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, h₂])
  hom_inv_id :=
    by
    simp only [cLCTinv.mapNat_def, _root_.id, SemiNormedGroupCat.equalizer.mapNat_comp_mapNat, ←
      CategoryTheory.whiskerRight_comp, Iso.hom_inv_id, CategoryTheory.whiskerRight_id', SemiNormedGroupCat.equalizer.mapNat_id]
    rfl
  inv_hom_id :=
    by
    simp only [cLCTinv.mapNat_def, _root_.id, SemiNormedGroupCat.equalizer.mapNat_comp_mapNat, ←
      CategoryTheory.whiskerRight_comp, Iso.inv_hom_id, CategoryTheory.whiskerRight_id', SemiNormedGroupCat.equalizer.mapNat_id]
    rfl

end cLCTinv

theorem aux (r' c c₂ : ℝ≥0) [r1 : Fact (r' ≤ 1)] [h : Fact (c₂ ≤ r' * c)] : Fact (c₂ ≤ c) :=
  ⟨h.1.trans <| (mul_le_mul' r1.1 le_rfl).trans (by simp)⟩

@[simps obj]
def cLCFPTinv₂ (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')]
    [r1 : Fact (r' ≤ 1)] [NormedWithAut r V] (c c₂ : ℝ≥0) [Fact (c₂ ≤ r' * c)] (n : ℕ) :
    (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroupCat :=
  haveI : Fact (c₂ ≤ c) := aux r' c c₂
  cLCTinv.f r V (NatTrans.op (filtrationPow.tinv r' c₂ c n))
    (NatTrans.op (filtrationPow.castLe r' c₂ c n))

theorem cLCFPTinv₂_def (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')]
    [r1 : Fact (r' ≤ 1)] [NormedWithAut r V] (c c₂ : ℝ≥0) [Fact (c₂ ≤ r' * c)] (n : ℕ) :
    cLCFPTinv₂ r V r' c c₂ n =
      SemiNormedGroupCat.equalizer.f (cLCFP.tinv V r' c c₂ n)
        (@cLCFP.res V r' c c₂ n (aux r' c c₂) ≫ cLCFP.tInv r V r' c₂ n) :=
  rfl

instance cLCFPTinv₂.separatedSpace [Fact (c₂ ≤ r' * c₁)] (M) :
    SeparatedSpace ((cLCFPTinv₂ r V r' c₁ c₂ n).obj M) :=
  by
  -- Porting note: Lean 3 went through `separated_iff_t2` and `subtype.t2_space`; here the
  -- instance for subtypes of separated uniform spaces applies directly.
  exact Subtype.separatedSpace _

instance cLCFPTinv₂.completeSpace [Fact (c₂ ≤ r' * c₁)] (M) :
    CompleteSpace ((cLCFPTinv₂ r V r' c₁ c₂ n).obj M) :=
  by
  refine' @IsClosed.completeSpace_coe _ (id _) (id _) _ _
  · apply UniformSpace.Completion.completeSpace
  · refine' isClosed_eq _ continuous_const
    -- Porting note: the function is displayed through `toAddMonoidHom`
    simp only [NormedAddGroupHom.coe_toAddMonoidHom]
    apply NormedAddGroupHom.continuous

/-- The functor that sends `M` and `c` to `V-hat((filtration M c)^n)^{T⁻¹}`,
defined by taking `T⁻¹`-invariants for two different actions by `T⁻¹`:

* The first comes from the action of `T⁻¹` on `M`.
* The second comes from the action of `T⁻¹` on `V`.

We take the equalizer of those two actions.

See the lines just above Definition 9.3 of [Analytic]. -/
def cLCFPTinv (r : ℝ≥0) (V : SemiNormedGroupCat) (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) [NormedWithAut r V]
    [Fact (0 < r)] [Fact (0 < r')] [Fact (r' ≤ 1)] :
    (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroupCat :=
  cLCFPTinv₂ r V r' c (r' * c) n

namespace cLCFPTinv₂

theorem map_normNoninc [Fact (c₂ ≤ r' * c)] [Fact (c₂ ≤ c)] {M₁ M₂} (f : M₁ ⟶ M₂) :
    ((cLCFPTinv₂ r V r' c c₂ n).map f).NormNoninc :=
  -- Porting note: the arguments are given explicitly since unification does not find them
  cLCTinv.map_normNoninc r V ((NatTrans.op (filtrationPow.tinv r' c₂ c n)).app M₁)
    ((NatTrans.op (filtrationPow.castLe r' c₂ c n)).app M₁)
    ((NatTrans.op (filtrationPow.tinv r' c₂ c n)).app M₂)
    ((NatTrans.op (filtrationPow.castLe r' c₂ c n)).app M₂)
    ((filtrationPow r' c n).op.map f) ((filtrationPow r' c₂ n).op.map f)
    (NatTrans.naturality _ _) (NatTrans.naturality _ _)

def res [Fact (c₂ ≤ r' * c₁)] [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ r' * c₃)] [Fact (c₄ ≤ c₃)]
    [Fact (c₃ ≤ c₁)] [Fact (c₄ ≤ c₂)] : cLCFPTinv₂ r V r' c₁ c₂ n ⟶ cLCFPTinv₂ r V r' c₃ c₄ n :=
  cLCTinv.mapNat r V _ _ _ _ (NatTrans.op (filtrationPow.castLe _ c₃ c₁ n))
    (NatTrans.op (filtrationPow.castLe _ c₄ c₂ n)) rfl rfl

@[simp]
theorem res_refl [Fact (c₂ ≤ r' * c₁)] [Fact (c₂ ≤ c₁)] : res r V r' c₁ c₂ c₁ c₂ n = 𝟙 _ := by
  simp only [res, filtrationPow.castLe_refl, NatTrans.op_id]; ext x : 2; apply cLCTinv.map_id

theorem res_comp_res [Fact (c₂ ≤ r' * c₁)] [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ r' * c₃)] [Fact (c₄ ≤ c₃)]
    [Fact (c₆ ≤ r' * c₅)] [Fact (c₆ ≤ c₅)] [Fact (c₃ ≤ c₁)] [Fact (c₄ ≤ c₂)] [Fact (c₅ ≤ c₃)]
    [Fact (c₆ ≤ c₄)] [Fact (c₅ ≤ c₁)] [Fact (c₆ ≤ c₂)] :
    res r V r' c₁ c₂ c₃ c₄ n ≫ res r V r' c₃ c₄ c₅ c₆ n = res r V r' c₁ c₂ c₅ c₆ n :=
  by
  ext x : 2; simp only [res, NatTrans.comp_app]
  -- Porting note: the morphisms are given explicitly since unification does not find them
  exact (cLCTinv.map_comp r V ((NatTrans.op (filtrationPow.castLe r' c₃ c₁ n)).app x)
    ((NatTrans.op (filtrationPow.castLe r' c₅ c₃ n)).app x)
    ((NatTrans.op (filtrationPow.castLe r' c₄ c₂ n)).app x)
    ((NatTrans.op (filtrationPow.castLe r' c₆ c₄ n)).app x) rfl rfl rfl rfl rfl rfl).symm

theorem res_normNoninc {_ : Fact (c₂ ≤ r' * c₁)} {_ : Fact (c₂ ≤ c₁)} {_ : Fact (c₄ ≤ r' * c₃)}
    {_ : Fact (c₄ ≤ c₃)} {_ : Fact (c₃ ≤ c₁)} {_ : Fact (c₄ ≤ c₂)} (M) :
    ((res r V r' c₁ c₂ c₃ c₄ n).app M).NormNoninc :=
  -- Porting note: the arguments are given explicitly since unification does not find them
  cLCTinv.map_normNoninc r V ((NatTrans.op (filtrationPow.tinv r' c₂ c₁ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₂ c₁ n)).app M)
    ((NatTrans.op (filtrationPow.tinv r' c₄ c₃ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₄ c₃ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₃ c₁ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₄ c₂ n)).app M) rfl rfl

theorem norm_res_le [Fact (c₂ ≤ r' * c₁)] [Fact (c₂ ≤ c₁)] [Fact (c₄ ≤ r' * c₃)] [Fact (c₄ ≤ c₃)]
    [Fact (c₃ ≤ c₁)] [Fact (c₄ ≤ c₂)] (h₂₃ : c₂ = c₃) (M) :
    ‖((res r V r' c₁ c₂ c₃ c₄ n).app M)‖ ≤ r := by
  -- Porting note: the arguments are given explicitly since unification does not find them
  refine' cLCTinv.norm_map_le r V ((NatTrans.op (filtrationPow.tinv r' c₂ c₁ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₂ c₁ n)).app M)
    ((NatTrans.op (filtrationPow.tinv r' c₄ c₃ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₄ c₃ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₃ c₁ n)).app M)
    ((NatTrans.op (filtrationPow.castLe r' c₄ c₂ n)).app M) rfl rfl r _
  rw [← Category.comp_id ((cLC V).map ((NatTrans.op (filtrationPow.castLe r' c₃ c₁ n)).app M))]
  have := NatTrans.congr_app (cLC.t r V).inv_hom_id ((filtrationPow r' c₃ n).op.obj M)
  dsimp only [NatTrans.id_app] at this
  rw [← this, cLC.tInv_eq, NatTrans.comp_app, ← Category.assoc ((cLC V).map _)]
  subst c₃
  rw [← SemiNormedGroupCat.equalizer.condition_assoc, ← Category.assoc]
  refine' NormedAddGroupHom.norm_comp_le_of_le' 1 r r (mul_one ↑r).symm _ _
  · apply cLC.norm_t_le
  · apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
    exact (cLC.map_normNoninc V _).comp NormedAddGroupHom.Equalizer.ι_normNoninc

end cLCFPTinv₂

namespace cLCFPTinv

theorem map_normNoninc {M₁ M₂} (f : M₁ ⟶ M₂) : ((cLCFPTinv r V r' c n).map f).NormNoninc :=
  cLCFPTinv₂.map_normNoninc _ _ _ _ _ _ _

def res [Fact (c₂ ≤ c₁)] : cLCFPTinv r V r' c₁ n ⟶ cLCFPTinv r V r' c₂ n :=
  cLCFPTinv₂.res r V r' c₁ _ c₂ _ n

@[simp]
theorem res_refl : res r V r' c₁ c₁ n = 𝟙 _ :=
  cLCFPTinv₂.res_refl _ _ _ _ _ _

theorem res_comp_res [Fact (c₃ ≤ c₁)] [Fact (c₅ ≤ c₃)] [Fact (c₅ ≤ c₁)] :
    res r V r' c₁ c₃ n ≫ res r V r' c₃ c₅ n = res r V r' c₁ c₅ n :=
  cLCFPTinv₂.res_comp_res _ _ _ _ _ _ _ _ _ _

theorem res_normNoninc {_ : Fact (c₂ ≤ c₁)} (M) : ((res r V r' c₁ c₂ n).app M).NormNoninc :=
  cLCFPTinv₂.res_normNoninc r V r' _ _ _ _ _ _

theorem norm_res_le [Fact (c₂ ≤ c₁)] [Fact (c₂ ≤ r' * c₁)] (M) :
    ‖((res r V r' c₁ c₂ n).app M)‖ ≤ r :=
  by
  rw [← res_comp_res r V r' c₁ (r' * c₁) c₂]
  refine'
    norm_comp_le_of_le' _ _ _ (one_mul ↑r).symm _ (cLCFPTinv₂.norm_res_le r V r' _ _ _ _ n rfl M)
  apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
  exact res_normNoninc r V r' (r' * c₁) c₂ n M

theorem norm_res_le_pow (N : ℕ) [Fact (c₂ ≤ c₁)] [h : Fact (c₂ ≤ r' ^ N * c₁)] (M) :
    ‖((res r V r' c₁ c₂ n).app M)‖ ≤ r ^ N :=
  by
  induction' N with N ih generalizing c₁ c₂
  · rw [pow_zero]
    apply NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1
    exact res_normNoninc r V r' c₁ c₂ n M
  haveI : Fact (c₂ ≤ r' ^ N * c₁) := NNReal.fact_le_pow_hMul_of_le_pow_succ_hMul _ _ _
  rw [pow_succ, mul_assoc] at h ; skip
  rw [← res_comp_res r V r' c₁ (r' ^ N * c₁) c₂]
  exact norm_comp_le_of_le' _ _ _ (pow_succ _ _) (norm_res_le r V r' _ _ n M) (ih _ _)

end cLCFPTinv

namespace BreenDeligne

open cLCFPTinv

variable (M) {l m n}

namespace UniversalMap

variable (ϕ ψ : UniversalMap m n)

def evalCLCFPTinv₂ [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] [ϕ.Suitable c₃ c₁]
    [ϕ.Suitable c₄ c₂] : cLCFPTinv₂ r V r' c₁ c₂ n ⟶ cLCFPTinv₂ r V r' c₃ c₄ m :=
  by
  dsimp only [cLCFPTinv₂_def]
  refine'
    SemiNormedGroupCat.equalizer.mapNat (ϕ.evalCLCFP _ _ _ _) (ϕ.evalCLCFP _ _ _ _)
      (Tinv_comp_eval_CLCFP V r' c₁ c₂ c₃ c₄ ϕ).symm _
  haveI : Fact (c₂ ≤ c₁) := aux r' _ _; haveI : Fact (c₄ ≤ c₃) := aux r' _ _
  have h₁ := res_comp_eval_CLCFP V r' c₁ c₂ c₃ c₄ ϕ
  have h₂ := T_inv_comp_eval_CLCFP r V r' c₂ c₄ ϕ
  have := comm_sq₂ h₁ h₂
  exact this.symm

@[simp]
theorem evalCLCFPTinv₂_zero [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] :
    (0 : UniversalMap m n).evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ = 0 := by
  simp only [eval_CLCFPTinv₂, eval_CLCFP_zero]; ext; rfl

@[simp]
theorem evalCLCFPTinv₂_add [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] [ϕ.Suitable c₃ c₁]
    [ϕ.Suitable c₄ c₂] [ψ.Suitable c₃ c₁] [ψ.Suitable c₄ c₂] :
    (ϕ + ψ : UniversalMap m n).evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ =
      ϕ.evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ + ψ.evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ :=
  by simp only [eval_CLCFPTinv₂, eval_CLCFP_add]; ext; rfl

@[simp]
theorem evalCLCFPTinv₂_sub [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] [ϕ.Suitable c₃ c₁]
    [ϕ.Suitable c₄ c₂] [ψ.Suitable c₃ c₁] [ψ.Suitable c₄ c₂] :
    (ϕ - ψ : UniversalMap m n).evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ =
      ϕ.evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ - ψ.evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ :=
  by simp only [eval_CLCFPTinv₂, eval_CLCFP_sub]; ext; rfl

theorem evalCLCFPTinv₂_comp {l m n : FreeMat} (f : l ⟶ m) (g : m ⟶ n) [Fact (c₂ ≤ r' * c₁)]
    [Fact (c₄ ≤ r' * c₃)] [Fact (c₆ ≤ r' * c₅)] [f.Suitable c₅ c₃] [f.Suitable c₆ c₄]
    [g.Suitable c₃ c₁] [g.Suitable c₄ c₂] :
    @evalCLCFPTinv₂ r V _ _ r' _ _ c₁ c₂ c₅ c₆ _ _ (f ≫ g) _ _ (Suitable.comp c₃)
        (Suitable.comp c₄) =
      g.evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄ ≫ f.evalCLCFPTinv₂ r V r' c₃ c₄ c₅ c₆ :=
  by
  dsimp only [eval_CLCFPTinv₂, cLCFPTinv₂_def]; delta id
  simp only [SemiNormedGroupCat.equalizer.mapNat_comp_mapNat]
  generalize_proofs h1 h2 h3 h4 h5 h6 h7 h8
  revert h5 h6 h7 h8; skip
  have H1 : eval_CLCFP V r' c₁ c₅ (f ≫ g) = eval_CLCFP V r' c₁ c₃ g ≫ eval_CLCFP V r' c₃ c₅ f :=
    eval_CLCFP_comp V r' c₁ c₃ c₅ g f
  have H2 : eval_CLCFP V r' c₂ c₆ (f ≫ g) = eval_CLCFP V r' c₂ c₄ g ≫ eval_CLCFP V r' c₄ c₆ f :=
    eval_CLCFP_comp V r' c₂ c₄ c₆ g f
  rw [H1, H2]
  intros; rfl

theorem res_comp_evalCLCFPTinv₂ [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] [Fact (c₆ ≤ r' * c₅)]
    [Fact (c₈ ≤ r' * c₇)] [Fact (c₂ ≤ c₁)] [Fact (c₃ ≤ c₁)] [Fact (c₄ ≤ c₂)] [Fact (c₄ ≤ c₃)]
    [Fact (c₆ ≤ c₅)] [Fact (c₇ ≤ c₅)] [Fact (c₈ ≤ c₆)] [Fact (c₈ ≤ c₇)] [ϕ.Suitable c₅ c₁]
    [ϕ.Suitable c₆ c₂] [ϕ.Suitable c₇ c₃] [ϕ.Suitable c₈ c₄] :
    cLCFPTinv₂.res r V r' c₁ c₂ c₃ c₄ n ≫ ϕ.evalCLCFPTinv₂ r V r' c₃ c₄ c₇ c₈ =
      ϕ.evalCLCFPTinv₂ r V r' c₁ c₂ c₅ c₆ ≫ cLCFPTinv₂.res r V r' c₅ c₆ c₇ c₈ m :=
  by
  dsimp only [cLCFPTinv₂.res, eval_CLCFPTinv₂, cLCFPTinv₂_def, cLCTinv.mapNat_def]; delta id
  simp only [SemiNormedGroupCat.equalizer.mapNat_comp_mapNat]
  congr 1 <;> · simp only [← cLCFP.res_def]; apply res_comp_eval_CLCFP

theorem norm_evalCLCFPTinv₂_le [Fact (c₂ ≤ r' * c₁)] [Fact (c₄ ≤ r' * c₃)] [ϕ.Suitable c₃ c₁]
    [ϕ.Suitable c₄ c₂] (N : ℕ) (h : ϕ.BoundBy N) (M) :
    ‖((ϕ.evalCLCFPTinv₂ r V r' c₁ c₂ c₃ c₄).app M)‖ ≤ N :=
  by
  apply SemiNormedGroupCat.equalizer.norm_map_le
  refine' NormedAddGroupHom.norm_comp_le_of_le' _ _ _ (mul_one _).symm _ _
  · apply norm_eval_CLCFP_le; exact h
  · apply NormNoninc.normNoninc_iff_norm_le_one.1
    exact equalizer.ι_norm_noninc

def evalCLCFPTinv [ϕ.Suitable c₂ c₁] : cLCFPTinv r V r' c₁ n ⟶ cLCFPTinv r V r' c₂ m :=
  ϕ.evalCLCFPTinv₂ r V r' c₁ _ c₂ _

theorem evalCLCFPTinv_def [ϕ.Suitable c₂ c₁] :
    ϕ.evalCLCFPTinv r V r' c₁ c₂ = ϕ.evalCLCFPTinv₂ r V r' c₁ _ c₂ _ :=
  rfl

@[simp]
theorem evalCLCFPTinv_zero : (0 : UniversalMap m n).evalCLCFPTinv r V r' c₁ c₂ = 0 := by
  apply eval_CLCFPTinv₂_zero

@[simp]
theorem evalCLCFPTinv_add [ϕ.Suitable c₂ c₁] [ψ.Suitable c₂ c₁] :
    (ϕ + ψ : UniversalMap m n).evalCLCFPTinv r V r' c₁ c₂ =
      ϕ.evalCLCFPTinv r V r' c₁ c₂ + ψ.evalCLCFPTinv r V r' c₁ c₂ :=
  evalCLCFPTinv₂_add _ _ _ _ _ _ _ _ _

@[simp]
theorem evalCLCFPTinv_sub [ϕ.Suitable c₂ c₁] [ψ.Suitable c₂ c₁] :
    (ϕ - ψ : UniversalMap m n).evalCLCFPTinv r V r' c₁ c₂ =
      ϕ.evalCLCFPTinv r V r' c₁ c₂ - ψ.evalCLCFPTinv r V r' c₁ c₂ :=
  evalCLCFPTinv₂_sub _ _ _ _ _ _ _ _ _

theorem evalCLCFPTinv_comp {l m n : FreeMat} (f : l ⟶ m) (g : m ⟶ n) [hg : g.Suitable c₂ c₁]
    [hf : f.Suitable c₃ c₂] :
    @evalCLCFPTinv r V _ _ r' _ _ c₁ c₃ _ _ (f ≫ g) (Suitable.comp c₂) =
      g.evalCLCFPTinv r V r' c₁ c₂ ≫ f.evalCLCFPTinv r V r' c₂ c₃ :=
  by apply eval_CLCFPTinv₂_comp

theorem res_comp_evalCLCFPTinv [Fact (c₂ ≤ c₁)] [ϕ.Suitable c₄ c₂] [ϕ.Suitable c₃ c₁]
    [Fact (c₄ ≤ c₃)] :
    res r V r' c₁ c₂ n ≫ ϕ.evalCLCFPTinv r V r' c₂ c₄ =
      ϕ.evalCLCFPTinv r V r' c₁ c₃ ≫ res r V r' c₃ c₄ m :=
  by apply res_comp_eval_CLCFPTinv₂

theorem res_comp_evalCLCFPTinv_absorb [Fact (c₂ ≤ c₁)] [hϕ : ϕ.Suitable c₃ c₂] :
    res r V r' c₁ c₂ n ≫ ϕ.evalCLCFPTinv r V r' c₂ c₃ =
      @evalCLCFPTinv r V _ _ r' _ _ c₁ c₃ _ _ ϕ (hϕ.le _ _ _ _ le_rfl (Fact.out _)) :=
  by
  rw [@res_comp_eval_CLCFPTinv r V _ _ r' _ _ c₁ c₂ c₃ c₃ _ _ ϕ (_root_.id _) (_root_.id _)
      (_root_.id _) (_root_.id _),
    res_refl, Category.comp_id]

theorem evalCLCFPTinv_comp_res_absorb {_ : Fact (c₃ ≤ c₂)} [hϕ : ϕ.Suitable c₂ c₁] :
    ϕ.evalCLCFPTinv r V r' c₁ c₂ ≫ res r V r' c₂ c₃ m =
      @evalCLCFPTinv r V _ _ r' _ _ c₁ c₃ _ _ ϕ (hϕ.le _ _ _ _ (Fact.out _) le_rfl) :=
  by
  rw [←
    @res_comp_eval_CLCFPTinv r V _ _ r' _ _ c₁ c₁ c₂ c₃ _ _ ϕ (_root_.id _) (_root_.id _)
      (_root_.id _) (_root_.id _),
    res_refl, Category.id_comp]

theorem norm_evalCLCFPTinv_le [NormedWithAut r V] [Fact (0 < r)] [ϕ.Suitable c₂ c₁] (N : ℕ)
    (h : ϕ.BoundBy N) (M) : ‖((ϕ.evalCLCFPTinv r V r' c₁ c₂).app M)‖ ≤ N :=
  norm_evalCLCFPTinv₂_le r V r' _ _ _ _ _ N h M

theorem evalCLCFPTinv_normNoninc [NormedWithAut r V] [Fact (0 < r)] [h : ϕ.VerySuitable r r' c₂ c₁]
    (M) : ((ϕ.evalCLCFPTinv r V r' c₁ c₂).app M).NormNoninc :=
  by
  apply NormNoninc.normNoninc_iff_norm_le_one.2
  have h' := h
  rcases h with ⟨N, k, c', hN, hϕ, hr, H⟩
  haveI : Fact (c' ≤ c₁) := ⟨H.trans <| Fact.out _⟩
  have aux := res_comp_eval_CLCFPTinv r V r' c₁ c' c₂ c₂ ϕ
  rw [res_refl, Category.comp_id] at aux 
  rw [← aux]
  refine' le_trans _ hr
  rw [mul_comm]
  apply NormedAddGroupHom.norm_comp_le_of_le
  · apply_mod_cast norm_eval_CLCFPTinv_le; exact hN
  · haveI : Fact (c' ≤ r' ^ k * c₁) := ⟨H⟩
    rw [NNReal.coe_pow]
    apply norm_res_le_pow

end UniversalMap

end BreenDeligne

