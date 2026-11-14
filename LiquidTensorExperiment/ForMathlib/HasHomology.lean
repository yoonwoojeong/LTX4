import Mathlib.Algebra.Homology.Homology
import Mathlib.CategoryTheory.Abelian.Homology
import LiquidTensorExperiment.ForMathlib.Commsq
import LiquidTensorExperiment.ForMathlib.ExactLiftDesc

#align_import for_mathlib.hasHomology

/-!

# `has_homology f g H`

If `A B C H` are objects of an abelian category, if `f : A ⟶ B` and if `g : B ⟶ C`, then
a term of type `has_homology f g H` can be thought of as the claim that `H` "is" the
homology of the complex `A ⟶ B ⟶ C`, or, more precisely, as an isomorphism between `H`
and the homology of this complex.

-/


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐]

variable {A B C : 𝓐} {f : A ⟶ B} {g : B ⟶ C} {H : 𝓐}

/-- If `f : A ⟶ B` and `g : B ⟶ C` are morphisms in an abelian category, then `has_homology f g H`
is the claim that `f ≫ g = 0` and furthermore an identification of `H` with the middle homology of
the corresponding three term exact sequence formed by `f` and `g`. -/
structure HasHomology (f : A ⟶ B) (g : B ⟶ C) (H : 𝓐) where
  w : f ≫ g = 0
  π : kernel g ⟶ H
  ι : H ⟶ cokernel f
  π_ι : π ≫ ι = kernel.ι _ ≫ cokernel.π _
  ex_π : Exact (kernel.lift g f w) π
  ι_ex : Exact ι (cokernel.desc f g w)
  [epi_π : Epi π]
  [mono_ι : Mono ι]

-- move me
instance (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) : Epi (homology'.π' f g w) :=
  epi_comp _ _

-- move me
instance (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) : Mono (homology'.ι f g w) :=
  mono_comp _ _

/-- If `f ≫ g = 0` then `homology f g w` can be identified with the homology of the three
term exact sequence coming from `f` and `g`. -/
def homology'.has (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) : HasHomology f g (homology' f g w) :=
  { w
    π := homology'.π' f g w
    ι := homology'.ι f g w
    π_ι := homology'.π'_ι _ _ _
    ex_π := by
      delta homology'.π'
      rw [exact_comp_iso]
      exact Abelian.exact_cokernel _
    ι_ex := by
      delta homology'.ι
      rw [exact_iso_comp]
      exact exact_kernel_ι
    epi_π := by infer_instance
    mono_ι := by infer_instance }

theorem homology'.has_π {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) :
    (homology'.has f g w).π = homology'.π' f g w :=
  rfl

theorem homology'.has_ι {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) :
    (homology'.has f g w).ι = homology'.ι f g w :=
  rfl

namespace HasHomology

attribute [instance] epi_π mono_ι

attribute [reassoc] π_ι

section Misc

@[reassoc (attr := simp)]
theorem ι_desc (hH : HasHomology f g H) : hH.ι ≫ cokernel.desc f g hH.w = 0 :=
  hH.ι_ex.w

@[reassoc (attr := simp)]
theorem lift_π (hH : HasHomology f g H) : kernel.lift g f hH.w ≫ hH.π = 0 :=
  hH.ex_π.w

def ofIso {H₁ H₂ : 𝓐} (hH : HasHomology f g H₁) (i : H₁ ≅ H₂) : HasHomology f g H₂
    where
  w := hH.w
  π := hH.π ≫ i.hom
  ι := i.inv ≫ hH.ι
  π_ι := by simp [hH.π_ι]
  ex_π := exact_comp_iso.2 hH.ex_π
  ι_ex := exact_iso_comp.2 hH.ι_ex
  epi_π := epi_comp _ _
  mono_ι := mono_comp _ _

end Misc

section Degenerate

-- move this; I couldn't find it
theorem exact_iso_comp_snd_iff_exact_comp_iso_fst_iff {D : 𝓐} (f : A ⟶ B) {e : B ⟶ C} (g : C ⟶ D)
    [IsIso e] : Exact f (e ≫ g) ↔ Exact (f ≫ e) g :=
  ⟨Preadditive.exact_of_iso_of_exact' f (e ≫ g) (f ≫ e) g (Iso.refl A) (asIso e) (Iso.refl D)
      (by simp) (by simp),
    Preadditive.exact_of_iso_of_exact' (f ≫ e) g f (e ≫ g) (Iso.refl A) (asIso e).symm (Iso.refl D)
      (by simp) (by simp)⟩

-- move this; I couldn't find it
theorem exact_zero_right_of_epi [Epi f] : Exact f (0 : B ⟶ C) :=
  ⟨comp_zero, imageToKernel_epi_of_epi_of_zero f⟩

attribute [local instance] epi_comp

--`mono_comp` is a global instance!
def fstEqZero : HasHomology (0 : A ⟶ B) g (kernel g)
    where
  w := zero_comp
  π := 𝟙 _
  ι := kernel.ι g ≫ cokernel.π 0
  π_ι := by simp
  ex_π := by
    rw [kernel.lift_zero]
    exact exact_zero_left_of_mono A
  ι_ex := by
    rw [← exact_iso_comp_snd_iff_exact_comp_iso_fst_iff, cokernel.π_desc]
    exact exact_kernel_ι
  epi_π := inferInstance
  mono_ι := inferInstance

def sndEqZero : HasHomology f (0 : B ⟶ C) (cokernel f)
    where
  w := comp_zero
  π := kernel.ι 0 ≫ cokernel.π f
  ι := 𝟙 _
  π_ι := by simp
  ex_π := by
    rw [exact_iso_comp_snd_iff_exact_comp_iso_fst_iff, kernel.lift_ι]
    exact Abelian.exact_cokernel f
  ι_ex := by
    rw [cokernel.desc_zero]
    exact exact_zero_right_of_epi
  epi_π := inferInstance
  mono_ι := inferInstance

def sndEqZero' (hg : g = 0) : HasHomology f g (cokernel f)
    where
  w := hg.symm ▸ comp_zero
  π := kernel.ι g ≫ cokernel.π f
  ι := 𝟙 _
  π_ι := by simp
  ex_π := by
    subst hg
    simp [exact_iso_comp_snd_iff_exact_comp_iso_fst_iff, kernel.lift_ι]
    exact Abelian.exact_cokernel f
  ι_ex := by
    subst hg
    rw [cokernel.desc_zero]
    exact exact_zero_right_of_epi
  epi_π := by subst hg <;> infer_instance
  mono_ι := inferInstance

def fstSndEqZero : HasHomology (0 : A ⟶ B) (0 : B ⟶ C) B
    where
  w := comp_zero
  π := kernel.ι 0
  ι := cokernel.π 0
  π_ι := rfl
  ex_π := by
    rw [kernel.lift_zero]
    exact exact_zero_left_of_mono A
  ι_ex := by
    rw [cokernel.desc_zero]
    exact exact_zero_right_of_epi
  epi_π := inferInstance
  mono_ι := inferInstance

def fstSndEqZero' (hf : f = 0) (hg : g = 0) : HasHomology f g B
    where
  w := hf.symm ▸ zero_comp
  π := kernel.ι g
  ι := cokernel.π f
  π_ι := rfl
  ex_π := by
    subst hf
    rw [kernel.lift_zero]
    exact exact_zero_left_of_mono A
  ι_ex := by
    subst hg
    rw [cokernel.desc_zero]
    exact exact_zero_right_of_epi
  epi_π := by subst hg <;> infer_instance
  mono_ι := by subst hf <;> infer_instance

end Degenerate

section Ext

theorem ext_π (hH : HasHomology f g H) {X : 𝓐} (φ ψ : H ⟶ X) (h : hH.π ≫ φ = hH.π ≫ ψ) : φ = ψ := by
  rwa [cancel_epi] at h 

theorem ext_ι (hH : HasHomology f g H) {X : 𝓐} (φ ψ : X ⟶ H) (h : φ ≫ hH.ι = ψ ≫ hH.ι) : φ = ψ := by
  rwa [cancel_mono] at h 

end Ext

section lift

variable (hH : HasHomology f g H)

variable {X : 𝓐} (φ : X ⟶ cokernel f) (hφ : φ ≫ cokernel.desc f g hH.w = 0)

/-- If ``has_homology f g H` and `φ : X ⟶ cokernel f` composes to zero with the canonical
map `cokernel f ⟶ C` then `has_homology.lift φ` is the morphism `X ⟶ H` which recovers `φ` after
composing with the canonical map `H ⟶ cokernel f` (the statement that the triangle commutes
is `lift_comp_ι`). -/
def lift : X ⟶ H :=
  hH.ι_ex.monoLift φ hφ

@[reassoc (attr := simp)]
theorem lift_comp_ι : hH.lift φ hφ ≫ hH.ι = φ :=
  hH.ι_ex.monoLift_comp φ hφ

theorem lift_unique (e : X ⟶ H) (he : e ≫ hH.ι = φ) : e = hH.lift φ hφ :=
  hH.ι_ex.monoLift_unique _ _ e he

@[simp]
theorem lift_ι : hH.lift hH.ι hH.ι_desc = 𝟙 H :=
  (hH.lift_unique _ _ _ <| Category.id_comp _).symm

theorem π_eq_lift :
    hH.π =
      hH.lift (kernel.ι _ ≫ cokernel.π _)
        (by simp only [Category.assoc, cokernel.π_desc, kernel.condition]) :=
  lift_unique _ _ _ _ hH.π_ι

@[reassoc]
theorem comp_lift {X Y : 𝓐} (φ : X ⟶ Y) (ψ : Y ⟶ cokernel f) (hψ : ψ ≫ cokernel.desc f g hH.w = 0) :
    φ ≫ hH.lift ψ hψ = hH.lift (φ ≫ ψ) (by rw [Category.assoc, hψ, comp_zero]) := by
  apply lift_unique; rw [Category.assoc, lift_comp_ι]

theorem homology'_lift_eq {X Y Z W : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) (φ : W ⟶ cokernel f)
    (hφ) : homology'.lift f g w φ hφ = (homology'.has f g w).lift φ hφ :=
  by
  ext
  simp only [homology'.lift_ι]
  dsimp [HasHomology.lift]
  erw [Exact.monoLift_comp]

end lift

section Desc

variable (hH : HasHomology f g H)

variable {X : 𝓐} (φ : kernel g ⟶ X) (hφ : kernel.lift g f hH.w ≫ φ = 0)

/-- If `has_homology f g H` and `φ : kernel g ⟶ X` becomes zero when precomposed with
the canonical map from `A` to `kernel g`, then `has_homology.desc φ` is the morphism `H ⟶ X` which
recovers `φ` after composing with the canonical map `kernel g ⟶ H`. The proof that this
triangle commutes is `π_comp_desc`. -/
def desc : H ⟶ X :=
  hH.ex_π.epiDesc φ hφ

@[reassoc (attr := simp)]
theorem π_comp_desc : hH.π ≫ hH.desc φ hφ = φ :=
  hH.ex_π.comp_epiDesc φ hφ

theorem desc_unique (e : H ⟶ X) (he : hH.π ≫ e = φ) : e = hH.desc φ hφ :=
  hH.ex_π.epiDesc_unique _ _ e he

@[simp]
theorem desc_π : hH.desc hH.π hH.lift_π = 𝟙 H :=
  (hH.desc_unique _ _ _ <| Category.comp_id _).symm

theorem ι_eq_desc :
    hH.ι =
      hH.desc (kernel.ι _ ≫ cokernel.π _)
        (by simp only [kernel.lift_ι_assoc, cokernel.condition]) :=
  desc_unique _ _ _ _ hH.π_ι

@[reassoc]
theorem desc_comp {X Y : 𝓐} (φ : kernel g ⟶ X) (ψ : X ⟶ Y) (hφ : kernel.lift g f hH.w ≫ φ = 0) :
    hH.desc φ hφ ≫ ψ = hH.desc (φ ≫ ψ) (by rw [reassoc_of hφ, zero_comp]) := by apply desc_unique;
  rw [π_comp_desc_assoc]

theorem homology'_desc_eq {X Y Z W : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (w) (φ : kernel g ⟶ W) (hφ) :
    homology'.desc' f g w φ hφ = (homology'.has f g w).desc φ hφ :=
  by
  ext
  simp only [homology'.π'_desc']
  dsimp [HasHomology.desc]
  simp only [Exact.comp_epiDesc]

end Desc

section Map

variable {A₁ B₁ C₁ H₁ A₂ B₂ C₂ H₂ A₃ B₃ C₃ H₃ : 𝓐}

variable {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (h₁ : HasHomology f₁ g₁ H₁)

variable {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (h₂ : HasHomology f₂ g₂ H₂)

variable {f₃ : A₃ ⟶ B₃} {g₃ : B₃ ⟶ C₃} (h₃ : HasHomology f₃ g₃ H₃)

variable {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂} {γ : C₁ ⟶ C₂}

variable {α' : A₂ ⟶ A₃} {β' : B₂ ⟶ B₃} {γ' : C₂ ⟶ C₃}

variable (sq1 : Commsq f₁ α β f₂) (sq2 : Commsq g₁ β γ g₂)

variable (sq1' : Commsq f₂ α' β' f₃) (sq2' : Commsq g₂ β' γ' g₃)

/-- If `h₁ : has_homology f₁ g₁ H₁` and `h₂ : has_homology f₂ g₂ H₂` then given compatible morphisms
`f₁ ⟶ g₁` and `f₂ ⟶ g₂`, `has_homology.map h₁ h₂` is the induced morphism `H₁ ⟶ H₂`. -/
def map : H₁ ⟶ H₂ :=
  h₁.desc
      (h₂.lift (kernel.ι _ ≫ β ≫ cokernel.π _) <| by
        simp only [Category.assoc, cokernel.π_desc, ← sq2.w, kernel.condition_assoc, zero_comp]) <|
    by
    apply h₂.ext_ι
    simp only [Category.assoc, zero_comp, h₂.lift_comp_ι, kernel.lift_ι_assoc, sq1.w_assoc,
      cokernel.condition, comp_zero]

@[reassoc (attr := simp)]
theorem π_map :
    h₁.π ≫ h₁.map h₂ sq1 sq2 =
      (h₂.lift (kernel.ι _ ≫ β ≫ cokernel.π _) <| by
        simp only [Category.assoc, cokernel.π_desc, ← sq2.w, kernel.condition_assoc, zero_comp]) :=
  h₁.π_comp_desc _ _

@[reassoc (attr := simp)]
theorem map_ι :
    h₁.map h₂ sq1 sq2 ≫ h₂.ι =
      (h₁.desc (kernel.ι _ ≫ β ≫ cokernel.π _) <| by
        simp only [kernel.lift_ι_assoc, sq1.w_assoc, cokernel.condition, comp_zero]) :=
  by apply h₁.desc_unique; rw [h₁.π_map_assoc, h₂.lift_comp_ι]

theorem π_map_ι : h₁.π ≫ h₁.map h₂ sq1 sq2 ≫ h₂.ι = kernel.ι _ ≫ β ≫ cokernel.π _ := by simp

theorem homology'_map_eq (w₁ : f₁ ≫ g₁ = 0) (w₂ : f₂ ≫ g₂ = 0)
    (e₁ : α ≫ (Arrow.mk f₂).hom = (Arrow.mk f₁).hom ≫ β)
    (e₂ : β ≫ (Arrow.mk g₂).hom = (Arrow.mk g₁).hom ≫ γ) :
    homology'.map w₁ w₂ (Arrow.homMk e₁) (Arrow.homMk e₂) rfl =
      (homology'.has f₁ g₁ w₁).map (homology'.has f₂ g₂ w₂) (Commsq.ofEq e₁.symm)
        (Commsq.ofEq e₂.symm) :=
  by
  --- I don't think using `exact.epi_desc` and `exact.mono_desc` is a good choice...
  rw [homology'.map_eq_desc'_lift_left]
  apply (homology'.has _ _ w₁).ext_π
  apply (homology'.has _ _ w₂).ext_ι
  simp [HasHomology.homology'_lift_eq, HasHomology.homology'_desc_eq]

theorem homology'_map_eq' (w₁ : f₁ ≫ g₁ = 0) (w₂ : f₂ ≫ g₂ = 0) :
    homology'.map w₁ w₂ ⟨α, β, sq1.w.symm⟩ ⟨β, γ, sq2.w.symm⟩ rfl =
      (homology'.has f₁ g₁ w₁).map (homology'.has f₂ g₂ w₂) sq1 sq2 :=
  homology'_map_eq _ _ _ _

theorem eq_map_of_π_map_ι (φ : H₁ ⟶ H₂) (hφ : h₁.π ≫ φ ≫ h₂.ι = kernel.ι g₁ ≫ β ≫ cokernel.π f₂) :
    φ = h₁.map h₂ sq1 sq2 := by rwa [← π_map_ι h₁ h₂ sq1 sq2, cancel_epi, cancel_mono] at hφ 

@[reassoc (attr := simp)]
theorem lift_map {X : 𝓐} (φ : X ⟶ cokernel f₁) (hφ : φ ≫ cokernel.desc f₁ g₁ h₁.w = 0) :
    h₁.lift φ hφ ≫ h₁.map h₂ sq1 sq2 =
      h₂.lift (φ ≫ cokernel.map f₁ f₂ α β sq1.w)
        (by rw [Category.assoc, cokernel.map_desc, reassoc_of hφ, zero_comp]; exact sq2.w) :=
  by
  apply lift_unique; rw [Category.assoc, map_ι]
  conv_rhs => rw [← lift_comp_ι h₁ φ hφ, Category.assoc]
  congr 1
  apply h₁.ext_π
  rw [π_comp_desc, π_ι_assoc, cokernel.π_desc]

-- move this
attribute [reassoc] Limits.kernel.lift_map

@[reassoc (attr := simp)]
theorem map_desc {X : 𝓐} (φ : kernel g₂ ⟶ X) (hφ : kernel.lift g₂ f₂ h₂.w ≫ φ = 0) :
    h₁.map h₂ sq1 sq2 ≫ h₂.desc φ hφ =
      h₁.desc (kernel.map g₁ g₂ β γ sq2.w ≫ φ)
        (by rw [CategoryTheory.Limits.kernel.lift_map_assoc, hφ, comp_zero]; exact sq1.w) :=
  by
  apply desc_unique; rw [π_map_assoc]
  conv_rhs => rw [← π_comp_desc h₂ φ hφ, ← Category.assoc]
  congr 1
  apply h₂.ext_ι
  rw [lift_comp_ι, Category.assoc, π_ι, kernel.lift_ι_assoc, Category.assoc]

/-- Gluing two commutative squares "vertically" (the convention is that `f`s and `g`s are
horizontal morphisms, and `α`s and `β`s are vertical morphisms). -/
def Commsq.vcomp : Commsq f₁ (α ≫ α') (β ≫ β') f₃ :=
  Commsq.ofEq <|
    calc
      f₁ ≫ β ≫ β' = α ≫ f₂ ≫ β' := sq1.w_assoc β'
      _ = α ≫ α' ≫ f₃ := (congr_arg _ <| sq1'.w)
      _ = (α ≫ α') ≫ f₃ := (Category.assoc _ _ _).symm

/-- A commutative square with identity isomorphisms for the two vertical maps. -/
def Commsq.vrefl (f : A ⟶ B) : Commsq f (Iso.refl _).hom (Iso.refl _).hom f :=
  Commsq.ofEq <| by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The reflection of a vertical square with isomorphisms for the vertical maps. -/
def Commsq.vinv {α : A₁ ≅ A₂} {β : B₁ ≅ B₂} (sq1 : Commsq f₁ α.hom β.hom f₂) :
    Commsq f₂ α.inv β.inv f₁ :=
  Commsq.ofEq <| by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, sq1.w]

theorem map_comp_map :
    h₁.map h₂ sq1 sq2 ≫ h₂.map h₃ sq1' sq2' = h₁.map h₃ (sq1.vcomp sq1') (sq2.vcomp sq2') :=
  by
  apply h₁.ext_π; apply h₃.ext_ι
  simp only [Category.assoc, map_ι, map_desc, π_comp_desc, kernel.lift_ι_assoc]

theorem map_id (h : HasHomology f g H) {α : A ⟶ A} {β : B ⟶ B} {γ : C ⟶ C} (sq1 : Commsq f α β f)
    (sq2 : Commsq g β γ g) (hβ : β = 𝟙 _) : h.map h sq1 sq2 = 𝟙 H :=
  by
  apply h.ext_π; apply h.ext_ι
  rw [π_map, lift_comp_ι, Category.comp_id, π_ι, hβ, Category.id_comp]

-- The isomorphism on `has_homology` induced by isomorphisms `f₁ ≅ f₂` and `g₁ ≅ g₂`.
@[simps]
def mapIso {α : A₁ ≅ A₂} {β : B₁ ≅ B₂} {γ : C₁ ≅ C₂} (sq1 : Commsq f₁ α.hom β.hom f₂)
    (sq2 : Commsq g₁ β.hom γ.hom g₂) : H₁ ≅ H₂
    where
  hom := h₁.map h₂ sq1 sq2
  inv := h₂.map h₁ sq1.vinv sq2.vinv
  hom_inv_id := by rw [map_comp_map, map_id]; exact β.hom_inv_id
  inv_hom_id := by rw [map_comp_map, map_id]; exact β.inv_hom_id

-- The canonical isomorphism between H₁ and H₂ if both satisfy `has_homology f g Hᵢ`.
abbrev iso (h₁ : HasHomology f g H₁) (h₂ : HasHomology f g H₂) : H₁ ≅ H₂ :=
  mapIso h₁ h₂ (Commsq.vrefl f) (Commsq.vrefl g)

theorem iso_inv (h₁ : HasHomology f g H₁) (h₂ : HasHomology f g H₂) :
    (iso h₁ h₂).inv = (iso h₂ h₁).hom :=
  rfl

theorem π_iso (h₁ : HasHomology f g H₁) (h₂ : HasHomology f g H₂) : h₁.π ≫ (h₁.Iso h₂).hom = h₂.π :=
  by
  simp only [Iso.refl_hom, Category.id_comp, map_iso_hom, π_map]
  exact (π_eq_lift h₂).symm

theorem iso_ι (h₁ : HasHomology f g H₁) (h₂ : HasHomology f g H₂) : (h₁.Iso h₂).hom ≫ h₂.ι = h₁.ι :=
  by
  simp only [Iso.refl_hom, Category.id_comp, map_iso_hom, map_ι]
  exact (ι_eq_desc h₁).symm

theorem map_iso_homology'_map :
    HasHomology.map h₁ h₂ sq1 sq2 =
      (HasHomology.iso h₁ (homology'.has f₁ g₁ h₁.w)).hom ≫
        homology'.map h₁.w h₂.w ⟨α, β, sq1.w.symm⟩ ⟨β, γ, sq2.w.symm⟩ rfl ≫
          (HasHomology.iso h₂ (homology'.has f₂ g₂ h₂.w)).inv :=
  by
  apply h₁.ext_π
  apply h₂.ext_ι
  simp [HasHomology.homology'_map_eq']

end Map

section Op

open Opposite

def op (h : HasHomology f g H) : HasHomology g.op f.op (op H)
    where
  w := by rw [← op_comp, h.w, op_zero]
  π := (kernelOpOp f).hom ≫ h.ι.op
  ι := h.π.op ≫ (cokernelOpOp g).inv
  π_ι :=
    by
    simp only [CategoryTheory.kernelOpOp_hom, CategoryTheory.cokernelOpOp_inv, ← op_comp, Category.assoc, h.π_ι_assoc,
      kernel.lift_ι_assoc, cokernel.π_desc]
    rfl
  ex_π :=
    by
    rw [← exact_comp_hom_inv_comp_iff (CategoryTheory.kernelOpOp f), Iso.inv_hom_id_assoc, CategoryTheory.kernelOpOp_hom]
    convert h.ι_ex.op using 1
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.Limits.coequalizer.hom_ext
    erw [unop_comp, coequalizer.π_desc_assoc, coequalizer.π_desc]
    rw [← unop_comp, kernel.lift_ι, g.unop_op]
  ι_ex :=
    by
    rw [← exact_comp_hom_inv_comp_iff (CategoryTheory.cokernelOpOp g), Category.assoc, Iso.inv_hom_id,
      Category.comp_id, CategoryTheory.cokernelOpOp_inv]
    convert h.ex_π.op using 1
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.Limits.equalizer.hom_ext
    erw [unop_comp, equalizer.lift_ι, Category.assoc, equalizer.lift_ι]
    rw [← unop_comp, cokernel.π_desc, f.unop_op]
  epi_π := epi_comp _ _
  mono_ι := mono_comp _ _

-- @[simps]
def homologyUnopIso {A B C : 𝓐ᵒᵖ} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
    homology' f g w ≅ Opposite.op (homology' g.unop f.unop (by rw [← unop_comp, w, unop_zero])) :=
  (homology'.has f g w).Iso (homology'.has g.unop f.unop _).op

def homologyOpIso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
    homology' g.op f.op (by rw [← op_comp, w, op_zero]) ≅ Opposite.op (homology' f g w) :=
  homologyUnopIso _ _ _

end Op

end HasHomology

