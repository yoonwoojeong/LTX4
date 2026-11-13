import LiquidTensorExperiment.ForMathlib.HomologyIsoDatum
import LiquidTensorExperiment.ForMathlib.ShortComplex

#align_import for_mathlib.homology_map_datum

noncomputable section

universe v

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C D : Type _} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  {S₁ S₂ : ShortComplex C} {H₁ H₂ : C}

/-- Each S₁, S₂ is a sequence of two composable arrows, φ is a map (i.e. two
commutative squares) between S₁ and S₂. The datum given here allows to
compute the map in homology induced by φ: up to the identifications of the
homologies with H₁ and H₂ respectively, it is η. -/
structure HomologyMapDatum (φ : S₁ ⟶ S₂) (h₁ : HomologyIsoDatum S₁.1.f S₁.1.g H₁)
    (h₂ : HomologyIsoDatum S₂.1.f S₂.1.g H₂) (η : H₁ ⟶ H₂) where
  κ : h₁.k ⟶ h₂.k
  fac₁' : h₁.f' ≫ κ = φ.τ₁ ≫ h₂.f'
  fac₂' : κ ≫ h₂.ι = h₁.ι ≫ φ.τ₂
  fac₃' : h₁.π ≫ η = κ ≫ h₂.π

namespace HomologyMapDatum

attribute [reassoc] fac₁ fac₂ fac₃

attribute [local simp] fac₁ fac₂

variable (φ : S₁ ⟶ S₂) {h₁ : HomologyIsoDatum S₁.1.f S₁.1.g H₁}
  {h₂ : HomologyIsoDatum S₂.1.f S₂.1.g H₂} {η : H₁ ⟶ H₂}

variable (μ : HomologyMapDatum φ h₁ h₂ η)

@[simps]
def tautological' :
    HomologyMapDatum φ (HomologyIsoDatum.tautological' _ _ _) (HomologyIsoDatum.tautological' _ _ _)
      (ShortComplex.homologyFunctor.map φ)
    where
  κ := kernel.map _ _ _ _ φ.comm₂₃
  fac₁' := by
    ext
    dsimp
    simp only [assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    exact φ.comm₁₂
  fac₂' := by apply kernel.lift_ι
  fac₃' := by apply homology'.π'_map

variable {φ}

@[simps]
def mapExactFunctor (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    HomologyMapDatum (F.mapShortComplex.map φ) (h₁.applyExactFunctor F) (h₂.applyExactFunctor F)
      (F.map η)
    where
  κ := F.map μ.κ
  fac₁' := by dsimp; simp only [← F.map_comp, μ.fac₁]
  fac₂' := by dsimp; simp only [← F.map_comp, μ.fac₂]
  fac₃' := by dsimp; simp only [← F.map_comp, μ.fac₃]

theorem homology'_map_eq : ShortComplex.homologyFunctor.map φ = h₁.Iso.inv ≫ η ≫ h₂.Iso.Hom :=
  by
  simp only [ShortComplex.homologyFunctor_map, HomologyIsoDatum.iso_inv, HomologyIsoDatum.iso_hom, ←
    cancel_epi h₁.iso₁.hom, ← cancel_mono (homology'.ι _ _ S₂.2), ←
    cancel_epi (homology'.π' _ _ S₁.2), assoc, homology'.map_ι, homology'.π'_ι_assoc,
    cokernel.π_desc, assoc]
  erw [homology'.lift_ι, homology'.π'_desc'_assoc, assoc, μ.fac₃_assoc, h₁.iso₁_hom_kernel_ι_assoc,
    ← μ.fac₂_assoc, h₁.iso₁.hom_inv_id_assoc, ← h₂.cokernel_π_iso₂_inv_assoc,
    h₂.iso₂.inv_hom_id_assoc, h₂.cokernel_f'_eq_π_iso₂_hom]
  congr 1
  simp only [← cancel_epi h₂.iso₁.inv, ← h₂.iso₁_hom_kernel_ι, assoc, h₂.iso₁.inv_hom_id_assoc, ←
    h₂.hasHomology.π_ι, h₂.hasHomology_π, h₂.hasHomology_ι]

end HomologyMapDatum

namespace HomologyIsoDatum

/-- If we understand the homology of `S`, then we should understand what is the
homology map of the morphism `F.map_short_complex S ⟶ G.map_short_complex S`
given by a natural transformation `φ : F ⟶ G` between exact functors -/
def mapNatTrans {S : ShortComplex C} {H : C} (h : HomologyIsoDatum S.1.f S.1.g H) {F G : C ⥤ D}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (φ : F ⟶ G) :
    HomologyMapDatum (φ.mapShortComplex.app S) (h.applyExactFunctor F) (h.applyExactFunctor G)
      (φ.app H)
    where
  κ := φ.app _
  fac₁' := NatTrans.naturality _ _
  fac₂' := (NatTrans.naturality _ _).symm
  fac₃' := NatTrans.naturality _ _

end HomologyIsoDatum

namespace HomologyMapDatum

def ofGAreZeros (φ : S₁ ⟶ S₂) (hg₁ : S₁.1.g = 0) (hg₂ : S₂.1.g = 0) :
    HomologyMapDatum φ (HomologyIsoDatum.ofGIsZero S₁.1.f S₁.1.g hg₁)
      (HomologyIsoDatum.ofGIsZero S₂.1.f S₂.1.g hg₂) (cokernel.map _ _ φ.τ₁ φ.τ₂ φ.comm₁₂)
    where
  κ := φ.τ₂
  fac₁' := φ.comm₁₂
  fac₂' := by dsimp; simp only [comp_id, id_comp]
  fac₃' := by dsimp; simp only [cokernel.π_desc]

def ofBothAreZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.1.f = 0) (hg₁ : S₁.1.g = 0) (hf₂ : S₂.1.f = 0)
    (hg₂ : S₂.1.g = 0) :
    HomologyMapDatum φ (HomologyIsoDatum.ofBothZeros S₁.1.f S₁.1.g hf₁ hg₁)
      (HomologyIsoDatum.ofBothZeros S₂.1.f S₂.1.g hf₂ hg₂) φ.τ₂
    where
  κ := φ.τ₂
  fac₁' := by tidy
  fac₂' := by tidy
  fac₃' := by tidy

end HomologyMapDatum

namespace ShortComplex

theorem homologyFunctor_map_eq_id {K : ShortComplex C} (φ : K ⟶ K) (hφ : φ.τ₂ = 𝟙 K.obj.y) :
    homologyFunctor.map φ = 𝟙 _ :=
  by
  let μ :
    HomologyMapDatum φ (HomologyIsoDatum.tautological' _ _ K.2)
      (HomologyIsoDatum.tautological' _ _ K.2) (𝟙 _) :=
    { κ := 𝟙 _
      fac₁' := by ext; dsimp; simp only [comp_id, kernel.lift_ι, assoc, ← φ.comm₁₂, hφ]
      fac₂' := by dsimp; simp only [hφ, id_comp, comp_id]
      fac₃' := by simp only [comp_id, id_comp] }
  simpa only [μ.homology'_map_eq, HomologyIsoDatum.tautological'_iso, Iso.refl_hom, comp_id]

end ShortComplex

