import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.Algebra.Homology.Homology
import LiquidTensorExperiment.ForMathlib.HasHomology

#align_import for_mathlib.homology_iso_datum

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type _} [Category.{v} C] [Abelian C]

variable {D : Type _} [Category.{v} D] [Abelian D]

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (H : C) (w : f ≫ g = 0)

-- Eventually, all of this should be refactored using `short_complex`.
/-- This structure expresses that there is a candidate `H` for the
homology of composable maps `f : X ⟶ Y` and `g : Y ⟶ Z`.
When `0 ⟶ K ⟶ Y ⟶ Z` and `X ⟶ K ⟶ Q ⟶ 0` are exact, this
will give a `h : homology_iso_datum f g H` and there shall
be an isomorphism `h.iso : H ≅ homology f g h.w`. The differences with
`has_homology f g H` are :
* this definition is not self dual: the homology is thought as the
quotient of cycles by boundaries;
* the object `K` can be any choice for the kernel of `Y ⟶ Z` and
`H` can be any choice of cokernel for `X ⟶ K`. -/
@[nolint has_inhabited_instance]
structure HomologyIsoPredatum where
  w : f ≫ g = 0
  k : C
  ι : K ⟶ Y
  f' : X ⟶ K
  fac : f' ≫ ι = f
  zero₁' : ι ≫ g = 0
  π : K ⟶ H
  zero₂' : f' ≫ π = 0

namespace HomologyIsoPredatum

attribute [simp, reassoc] fac zero₁ zero₂

@[simps]
def tautological : HomologyIsoPredatum f g (cokernel (kernel.lift g f w)) :=
  { w
    k := kernel g
    ι := kernel.ι _
    f' := kernel.lift g f w
    fac := kernel.lift_ι _ _ _
    zero₁' := kernel.condition _
    π := cokernel.π _
    zero₂' := cokernel.condition _ }

@[simps]
def tautological' : HomologyIsoPredatum f g (homology' f g w) :=
  { w
    k := kernel g
    ι := kernel.ι _
    f' := kernel.lift g f w
    fac := kernel.lift_ι _ _ _
    zero₁' := kernel.condition _
    π := homology'.π' f g w
    zero₂' := homology'.condition_π' _ _ _ }

variable {f g}

variable {H} (h : HomologyIsoPredatum f g H)

@[simps]
def fork : KernelFork g :=
  KernelFork.ofι h.ι h.zero₁

@[simps]
def cofork : CokernelCofork h.f' :=
  CokernelCofork.ofπ h.π h.zero₂

@[simps]
def applyFunctor {D : Type _} [Category D] [Abelian D] (F : C ⥤ D) [F.Additive] :
    HomologyIsoPredatum (F.map f) (F.map g) (F.obj H)
    where
  w := by rw [← F.map_comp, h.w, F.map_zero]
  k := F.obj h.k
  ι := F.map h.ι
  f' := F.map h.f'
  fac := by rw [← F.map_comp, h.fac]
  zero₁' := by simp only [← F.map_comp, zero₁, F.map_zero]
  π := F.map h.π
  zero₂' := by simp only [← F.map_comp, zero₂, F.map_zero]

@[simps]
def mapIso {X' Y' Z' : C} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (e₁ : Arrow.mk f ≅ Arrow.mk f')
    (e₂ : Arrow.mk g ≅ Arrow.mk g') (eq : e₁.hom.right = e₂.hom.left) :
    HomologyIsoPredatum f' g' H :=
  by
  have comm₁ : e₁.hom.left ≫ f' = f ≫ e₁.hom.right := Arrow.w e₁.hom
  have comm₂ : e₂.hom.left ≫ g' = g ≫ e₂.hom.right := Arrow.w e₂.hom
  have h₁ : e₁.inv.left ≫ e₁.hom.left = 𝟙 X' := by
    rw [← Comma.comp_left, e₁.inv_hom_id, Arrow.id_left]; rfl
  exact
    { w := by
        rw [← cancel_epi e₁.hom.left, ← Category.assoc, comm₁, Eq, Category.assoc, comm₂, ←
          Category.assoc, h.w, zero_comp, comp_zero]
      k := h.K
      ι := h.ι ≫ e₁.hom.right
      f' := e₁.inv.left ≫ h.f'
      fac := by
        slice_lhs 2 3 => rw [h.fac']
        rw [← comm₁, ← Category.assoc, h₁, Category.id_comp]
      zero₁' := by rw [Eq, Category.assoc, comm₂, ← Category.assoc, h.zero₁', zero_comp]
      π := h.π
      zero₂' := by rw [Category.assoc, h.zero₂', comp_zero] }

end HomologyIsoPredatum

@[nolint has_inhabited_instance]
structure HomologyIsoDatum (H : C) extends HomologyIsoPredatum f g H where
  forkIsLimit : IsLimit to_homology_iso_predatum.Fork
  coforkIsColimit : IsColimit to_homology_iso_predatum.Cofork

namespace HomologyIsoDatum

variable {H f g}

@[protected]
def h (h : HomologyIsoDatum f g H) : C :=
  H

variable (f g)

@[simps]
def tautological : HomologyIsoDatum f g (cokernel (kernel.lift g f w))
    where
  toHomologyIsoPredatum := HomologyIsoPredatum.tautological f g w
  forkIsLimit := by apply CategoryTheory.Limits.kernelIsKernel
  coforkIsColimit := by apply CategoryTheory.Limits.cokernelIsCokernel

@[simps]
def tautological' : HomologyIsoDatum f g (homology' f g w)
    where
  toHomologyIsoPredatum := HomologyIsoPredatum.tautological' f g w
  forkIsLimit := by apply CategoryTheory.Limits.kernelIsKernel
  coforkIsColimit := by
    dsimp [HomologyIsoPredatum.cofork]
    refine' IsColimit.ofIsoColimit (CategoryTheory.Limits.cokernelIsCokernel (kernel.lift g f w)) _
    refine' Cocones.ext (homology'IsoCokernelLift f g w).symm _
    rintro (_ | _)
    tidy

variable {f g} (h : HomologyIsoDatum f g H)

def mapIso {X' Y' Z' : C} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (e₁ : Arrow.mk f ≅ Arrow.mk f')
    (e₂ : Arrow.mk g ≅ Arrow.mk g') (eq : e₁.hom.right = e₂.hom.left) : HomologyIsoDatum f' g' H
    where
  toHomologyIsoPredatum := h.toHomologyIsoPredatum.mapIso f' g' e₁ e₂ Eq
  forkIsLimit :=
    by
    refine' (IsLimit.equivOfNatIsoOfIso _ _ _ _).toFun h.forkIsLimit
    · refine'
        parallelPair.ext (arrow.rightFunc.map_iso e₁) (arrow.rightFunc.map_iso e₂) _ (by simp)
      have h₂ := Arrow.w e₂.hom
      dsimp at h₂ ⊢
      rw [Eq, h₂]
    · refine' Cones.ext (iso.refl _) _
      rintro (_ | _)
      tidy
  coforkIsColimit :=
    by
    refine' (IsColimit.equivOfNatIsoOfIso _ _ _ _).toFun h.coforkIsColimit
    · refine' parallelPair.ext (arrow.leftFunc.map_iso e₁) (iso.refl _) _ (by tidy)
      · dsimp
        have h₁ : e₁.hom.left ≫ e₁.inv.left = 𝟙 X := by
          rw [← Comma.comp_left, e₁.hom_inv_id, Arrow.id_left]; rfl
        rw [Category.comp_id, ← Category.assoc, h₁, Category.id_comp]
    · refine' Cocones.ext (iso.refl _) _
      rintro (_ | _)
      tidy

def iso₁ : h.k ≅ kernel g :=
  IsLimit.conePointUniqueUpToIso h.forkIsLimit (LimitCone.isLimit _)

@[simp, reassoc]
theorem iso₁_hom_kernel_ι : h.iso₁.hom ≫ kernel.ι g = h.ι :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

instance : Mono h.ι := by rw [← h.iso₁_hom_kernel_ι]; infer_instance

@[simp, reassoc]
theorem f'_iso₁_hom : h.f' ≫ h.iso₁.hom = kernel.lift g f h.w :=
  by
  ext
  simp only [Category.assoc, iso₁_hom_kernel_ι, HomologyIsoPredatum.fac, kernel.lift_ι]

def iso₂ : H ≅ cokernel h.f' :=
  IsColimit.coconePointUniqueUpToIso h.coforkIsColimit (ColimitCocone.isColimit _)

@[simp, reassoc]
theorem cokernel_π_iso₂_inv : cokernel.π h.f' ≫ h.iso₂.inv = h.π :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

@[reassoc]
theorem cokernel_f'_eq_π_iso₂_hom : cokernel.π h.f' = h.π ≫ h.iso₂.hom := by
  rw [← cokernel_π_iso₂_inv, Category.assoc, h.iso₂.inv_hom_id, Category.comp_id]

instance : Epi h.π := by rw [← h.cokernel_π_iso₂_inv]; apply epi_comp

def iso₃ : cokernel h.f' ≅ cokernel (kernel.lift g f h.w) :=
  cokernel.mapIso _ _ (Iso.refl _) h.iso₁
    (by simp only [f'_iso₁_hom, Iso.refl_hom, Category.id_comp])

@[simp, reassoc]
theorem cokernel_π_iso₃_hom :
    cokernel.π h.f' ≫ h.iso₃.hom = h.iso₁.hom ≫ cokernel.π (kernel.lift g f h.w) :=
  by
  dsimp only [iso₃]
  simp only [cokernel.mapIso_hom, cokernel.π_desc]

variable (f g)

@[simp]
theorem tautological_iso₁ : (tautological f g w).iso₁ = Iso.refl _ :=
  by
  ext
  dsimp only [iso₁]
  simp only [equalizer_as_kernel, Iso.refl_hom, Category.id_comp]
  change kernel.lift _ _ _ ≫ _ = _
  simpa only [equalizer_as_kernel, kernel.lift_ι]

@[simp]
theorem tautological'_iso₁ : (tautological' f g w).iso₁ = Iso.refl _ :=
  by
  ext
  dsimp only [iso₁]
  simp only [equalizer_as_kernel, Iso.refl_hom, Category.id_comp]
  change kernel.lift _ _ _ ≫ _ = _
  simpa only [equalizer_as_kernel, kernel.lift_ι]

@[simp]
theorem tautological_iso₂ : (tautological f g w).iso₂ = Iso.refl _ :=
  by
  suffices (tautological f g w).iso₂.symm = iso.refl _
    by
    change (tautological f g w).iso₂.symm.symm = _
    simpa only [this]
  ext
  simpa only [Iso.symm_hom, cokernel_π_iso₂_inv, Iso.refl_hom, Category.comp_id]

@[simp]
theorem tautological_iso₃ : (tautological f g w).iso₃ = Iso.refl _ :=
  by
  ext
  simpa only [cokernel_π_iso₃_hom, tautological_iso₁, Iso.refl_hom, Category.id_comp,
    Category.comp_id]

variable {f g}

def iso : H ≅ homology' f g h.w :=
  h.iso₂ ≪≫ h.iso₃ ≪≫ (homology'IsoCokernelLift f g h.w).symm

variable (f g)

@[simp]
theorem tautological_iso : (tautological f g w).Iso = (homology'IsoCokernelLift f g w).symm := by
  dsimp only [iso]; simp only [tautological_iso₂, tautological_iso₃, Iso.refl_trans]

theorem tautological_iso_hom :
    (tautological f g w).Iso.Hom = (homology'IsoCokernelLift f g w).inv := by
  simp only [tautological_iso, Iso.symm_hom]

variable {f g}

@[nolint has_inhabited_instance]
structure Change {H₁ H₂ : C} (h₁ : HomologyIsoDatum f g H₁) (h₂ : HomologyIsoDatum f g H₂) where
  κ : h₁.k ⟶ h₂.k
  fac₁' : h₁.f' ≫ κ = h₂.f'
  fac₂' : κ ≫ h₂.ι = h₁.ι
  η : H₁ ⟶ H₂
  fac₃' : h₁.π ≫ η = κ ≫ h₂.π

namespace Change

attribute [simp, reassoc] fac₁ fac₂

attribute [reassoc] fac₃

variable {H₁ H₂ : C} {h₁ : HomologyIsoDatum f g H₁} {h₂ : HomologyIsoDatum f g H₂}
  (c : Change h₁ h₂)

@[simp, reassoc]
theorem fac_iso₁ : c.κ ≫ h₂.iso₁.hom = h₁.iso₁.hom := by ext;
  simp only [Category.assoc, iso₁_hom_kernel_ι, fac₂]

instance : IsIso c.κ :=
  IsIso.of_isIso_fac_right c.fac_iso₁

def cokerIso : cokernel h₁.f' ≅ cokernel h₂.f' :=
  cokernel.mapIso _ _ (Iso.refl _) (asIso c.κ)
    (by simp only [CategoryTheory.asIso_hom, fac₁, Iso.refl_hom, Category.id_comp])

@[simp, reassoc]
theorem cokerIso_comm : cokernel.π h₁.f' ≫ c.cokerIso.hom = c.κ ≫ cokernel.π h₂.f' :=
  by
  dsimp only [HomologyIsoDatum.Change.cokerIso]
  simp only [CategoryTheory.asIso_hom, cokernel.mapIso_hom, cokernel.π_desc]

@[reassoc]
theorem fac_iso₂ : c.cokerIso.hom ≫ h₂.iso₂.inv = h₁.iso₂.inv ≫ c.η :=
  by
  ext
  simp only [HomologyIsoDatum.Change.cokerIso_comm_assoc, cokernel_π_iso₂_inv, cokernel_π_iso₂_inv_assoc, fac₃]

instance : IsIso c.η :=
  by
  haveI : is_iso (h₁.iso₂.inv ≫ c.η) := by rw [← fac_iso₂]; infer_instance
  apply IsIso.of_isIso_comp_left h₁.iso₂.inv

@[simp, reassoc]
theorem cokerIso_iso₃_hom : c.cokerIso.hom ≫ h₂.iso₃.hom = h₁.iso₃.hom :=
  by
  ext
  simp only [HomologyIsoDatum.Change.cokerIso_comm_assoc, cokernel_π_iso₃_hom, fac_iso₁_assoc]

@[simp, reassoc]
theorem η_iso₂_hom_iso₃_hom : c.η ≫ h₂.iso₂.hom ≫ h₂.iso₃.hom = h₁.iso₂.hom ≫ h₁.iso₃.hom := by
  rw [← cancel_epi h₁.iso₂.inv, Iso.inv_hom_id_assoc, ← c.cokerIso_iso₃_hom, ← fac_iso₂_assoc,
    Iso.inv_hom_id_assoc]

@[simp, reassoc]
theorem η_iso_hom : c.η ≫ h₂.Iso.Hom = h₁.Iso.Hom :=
  by
  dsimp only [iso]
  simp only [Iso.trans_hom, η_iso₂_hom_iso₃_hom_assoc]

theorem η_iso : asIso c.η ≪≫ h₂.Iso = h₁.Iso := by ext;
  simp only [Iso.trans_hom, CategoryTheory.asIso_hom, η_iso_hom]

variable (f g)

@[simps]
def tautological :
    Change (HomologyIsoDatum.tautological' f g w) (HomologyIsoDatum.tautological f g w)
    where
  κ := 𝟙 _
  η := (homology'IsoCokernelLift f g w).hom
  fac₁' := Category.comp_id _
  fac₂' := Category.id_comp _
  fac₃' :=
    by
    dsimp [homology'.π', homology'IsoCokernelLift, homology'IsoCokernelImageToKernel']
    simp only [CategoryTheory.Limits.cokernelIsoOfEq_inv_comp_desc, cokernel.π_desc_assoc, Category.assoc,
      π_comp_cokernel_iso_of_eq_hom, Iso.inv_hom_id_assoc, Category.id_comp]

end Change

variable (f g)

@[simp]
theorem tautological'_iso : (tautological' f g w).Iso = Iso.refl _ :=
  by
  ext1
  rw [← (Change.tautological f g w).η_iso_hom]
  simp only [← (Change.tautological f g w).η_iso_hom, Change.tautological_η, Iso.refl_hom,
    tautological_iso, Iso.symm_hom, Iso.hom_inv_id]

variable {f g}

section ApplyExactFunctor

variable (F : C ⥤ D) [Functor.Additive F]

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

@[simps]
def applyExactFunctor : HomologyIsoDatum (F.map f) (F.map g) (F.obj H)
    where
  toHomologyIsoPredatum := h.toHomologyIsoPredatum.applyFunctor F
  forkIsLimit :=
    by
    let e : CategoryTheory.Limits.parallelPair g 0 ⋙ F ≅ CategoryTheory.Limits.parallelPair (F.map g) 0 :=
      parallelPair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
    have hF :=
      (IsLimit.postcomposeInvEquiv e.symm _).invFun (CategoryTheory.Limits.isLimitOfPreserves F h.forkIsLimit)
    refine' IsLimit.ofIsoLimit hF (Cones.ext (iso.refl _) _)
    rintro (_ | _)
    tidy
  coforkIsColimit :=
    by
    let e : CategoryTheory.Limits.parallelPair h.f' 0 ⋙ F ≅ CategoryTheory.Limits.parallelPair (F.map h.f') 0 :=
      parallelPair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
    have hF :=
      (IsColimit.precomposeInvEquiv e _).invFun (CategoryTheory.Limits.isColimitOfPreserves F h.coforkIsColimit)
    refine' IsColimit.ofIsoColimit hF (Cocones.ext (iso.refl _) _)
    rintro (_ | _)
    tidy

end ApplyExactFunctor

section HomologicalComplex

variable {A : Type _} [Category A] [Abelian A]

variable {M : Type _} {c : ComplexShape M}

def ofHomologicalComplex (X : HomologicalComplex A c) (i j k : M) (hij : c.Rel i j)
    (hjk : c.Rel j k) : HomologyIsoDatum (X.d i j) (X.d j k) (X.homology' j) :=
  by
  refine'
    (HomologyIsoDatum.tautological' (X.d_to j) (X.d_from j) (X.d_to_comp_d_from j)).mapIso _ _ _ _ _
  · refine' Arrow.isoMk (X.X_prev_iso hij) (iso.refl _) _
    dsimp
    simp only [X.d_to_eq hij, Category.comp_id]
  · refine' Arrow.isoMk (iso.refl _) (X.X_next_iso hjk) _
    dsimp
    simp only [X.d_from_eq hjk, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rfl

open scoped ZeroObject

end HomologicalComplex

section HasHomology

variable (f g)

theorem homology'IsoCokernelLift_comp_ι :
    (homology'IsoCokernelLift f g w).inv ≫ homology'.ι f g w =
      cokernel.map _ _ (𝟙 X) (kernel.ι g) (by simp only [kernel.lift_ι, Category.id_comp]) :=
  by
  ext
  dsimp [homology'IsoCokernelLift, homology'.ι, homology'IsoCokernelImageToKernel',
    homology'IsoKernelDesc]
  simp only [CategoryTheory.Limits.cokernelIsoOfEq_inv_comp_desc, Category.assoc, cokernel.π_desc_assoc,
    cokernel.π_desc, CategoryTheory.Limits.cokernelIsoOfEq_hom_comp_desc_assoc, kernel.lift_ι,
    CategoryTheory.Limits.kernelSubobject_arrow_assoc, CategoryTheory.Limits.kernelSubobject_arrow'_assoc]

theorem homology'_ι_eq :
    homology'.ι f g w =
      (homology'IsoCokernelLift f g w).hom ≫
        cokernel.map _ _ (𝟙 X) (kernel.ι g) (by simp only [kernel.lift_ι, Category.id_comp]) :=
  by simp only [← homology_iso_cokernel_lift_comp_ι, Iso.hom_inv_id_assoc]

variable {f g}

theorem iso_hom_homology'_ι_eq_iso₂_hom_cokernel_map :
    h.Iso.Hom ≫ homology'.ι f g h.w = h.iso₂.hom ≫ cokernel.map h.f' f (𝟙 X) h.ι (by simp) :=
  by
  dsimp only [iso, iso₂, iso₃]
  simp only [homology_ι_eq f g h.w, Iso.refl_hom, Iso.trans_hom, cokernel.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  ext
  simp only [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, iso₁_hom_kernel_ι_assoc]

theorem homology'_π'_eq : homology'.π' f g h.w = h.iso₁.inv ≫ h.π ≫ h.Iso.Hom :=
  by
  rw [← cancel_mono (homology'.ι f g h.w)]
  dsimp only [iso]
  simp only [homology'.π'_ι, Category.assoc, Iso.trans_hom, Iso.symm_hom,
    homology_iso_cokernel_lift_comp_ι, ← cokernel_π_iso₂_inv, Iso.inv_hom_id_assoc,
    cokernel_π_iso₃_hom_assoc, cokernel.π_desc]

theorem iso_inv :
    h.Iso.inv =
      homology'.desc' f g h.w (h.iso₁.inv ≫ h.π)
        (by
          simp only [← h.f'_iso₁_hom, Category.assoc, h.iso₁.hom_inv_id_assoc,
            HomologyIsoPredatum.zero₂]) :=
  by
  rw [← cancel_epi (homology'.π' f g h.w), homology'.π'_desc', homology_π'_eq, Category.assoc,
    Category.assoc, h.iso.hom_inv_id, Category.comp_id]

theorem iso_hom :
    h.Iso.Hom =
      homology'.lift f g h.w (h.iso₂.hom ≫ cokernel.map h.f' f (𝟙 X) h.ι (by simp))
        (by
          rw [← cancel_epi h.iso₂.inv]
          ext
          simp only [Category.assoc, Iso.inv_hom_id_assoc, cokernel.π_desc_assoc, cokernel.π_desc,
            HomologyIsoPredatum.zero₁, comp_zero]) :=
  by
  rw [← cancel_epi h.iso.inv, h.iso.inv_hom_id, h.iso_inv, ← cancel_mono (homology'.ι f g h.w), ←
    cancel_epi (homology'.π' f g h.w), ← cancel_epi h.iso₁.hom]
  simp only [Category.assoc, Category.id_comp, homology'.π'_ι, homology'.lift_ι,
    homology'.π'_desc'_assoc, h.iso₁.hom_inv_id_assoc, h.iso₁_hom_kernel_ι_assoc, ←
    cokernel_π_iso₂_inv, h.iso₂.inv_hom_id_assoc, cokernel.π_desc]

@[simps]
def hasHomology : HasHomology f g H where
  w := h.w
  π := h.iso₁.inv ≫ h.π
  ι := h.iso₂.hom ≫ cokernel.map h.f' f (𝟙 X) h.ι (by simp)
  π_ι := by
    simp only [Category.assoc, ← cokernel_π_iso₂_inv_assoc, Iso.inv_hom_id_assoc, cokernel.π_desc, ←
      h.iso₁_hom_kernel_ι]
  ex_π :=
    by
    refine'
      Preadditive.exact_of_iso_of_exact (kernel.lift g f h.w) (cokernel.π (kernel.lift g f h.w)) _ _
        (iso.refl _) _ _ (Abelian.exact_cokernel _)
    · refine' Arrow.isoMk (iso.refl _) (h.iso₃.symm ≪≫ h.iso₂.symm) _
      dsimp
      simp only [← cancel_mono h.iso₂.hom, ← cancel_mono h.iso₃.hom, Category.id_comp,
        Category.assoc, ← cokernel_π_iso₂_inv, Iso.inv_hom_id_assoc, cokernel_π_iso₃_hom,
        Iso.inv_hom_id, Category.comp_id]
    · rfl
  ι_ex :=
    by
    refine'
      Preadditive.exact_of_iso_of_exact (homology'.ι f g h.w) (cokernel.desc f g h.w) _ _ _
        (iso.refl _) _ (homology'.has f g h.w).ι_ex
    · refine' Arrow.isoMk h.iso.symm (iso.refl _) _
      dsimp
      simp only [← h.iso_hom_homology'_ι_eq_iso₂_hom_cokernel_map, Iso.inv_hom_id_assoc,
        Category.comp_id]
    · rfl
  epi_π := epi_comp _ _
  mono_ι := by
    rw [← iso_hom_homology_ι_eq_iso₂_hom_cokernel_map]
    infer_instance

end HasHomology

variable (f g)

@[simps]
def ofFIsZero (hf : f = 0) : HomologyIsoDatum f g (kernel g)
    where
  w := by rw [hf, zero_comp]
  k := kernel g
  ι := kernel.ι g
  f' := 0
  fac := by rw [hf, zero_comp]
  zero₁' := kernel.condition g
  π := 𝟙 _
  zero₂' := by rw [zero_comp]
  forkIsLimit := kernelIsKernel g
  coforkIsColimit :=
    isColimitAux _ (fun s => s.π) (fun s => by apply Category.id_comp) fun s m hm => by rw [← hm];
      symm; apply Category.id_comp

@[simps]
def ofGIsZero (hg : g = 0) : HomologyIsoDatum f g (cokernel f)
    where
  w := by rw [hg, comp_zero]
  k := Y
  ι := 𝟙 Y
  f' := f
  fac := Category.comp_id _
  zero₁' := by rw [hg, comp_zero]
  π := cokernel.π f
  zero₂' := cokernel.condition f
  forkIsLimit :=
    isLimitAux _ (fun s => s.ι) (fun s => by apply Category.comp_id) fun s m hm => by rw [← hm];
      symm; apply Category.comp_id
  coforkIsColimit := by apply CategoryTheory.Limits.cokernelIsCokernel

@[simps]
def ofBothZeros (hf : f = 0) (hg : g = 0) : HomologyIsoDatum f g Y
    where
  w := by rw [hg, comp_zero]
  k := Y
  ι := 𝟙 Y
  f' := 0
  fac := by rw [hf, zero_comp]
  zero₁' := by rw [hg, comp_zero]
  π := 𝟙 Y
  zero₂' := zero_comp
  forkIsLimit :=
    isLimitAux _ (fun s => s.ι) (fun s => by apply Category.comp_id) fun s m hm => by rw [← hm];
      symm; apply Category.comp_id
  coforkIsColimit :=
    isColimitAux _ (fun s => s.π) (fun s => by apply Category.id_comp) fun s m hm => by rw [← hm];
      symm; dsimp; apply Category.id_comp

end HomologyIsoDatum

