import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Abelian.Basic
import LiquidTensorExperiment.ForMathlib.SplitExact
import LiquidTensorExperiment.ForMathlib.Derived.Defs
import LiquidTensorExperiment.ForMathlib.HasHomology

#align_import for_mathlib.imker

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable (C : CochainComplex 𝓐 ℤ)

open scoped ZeroObject

/-- Given a cochain complex
```
C^{n-2} → C^{n-1} → C^n → C^{n+1}
```
`imker C n` should be the cochain complex
```
   0  → Im(d^{n-1}) → Ker(d^n) → 0
```
supported in degrees n-1 and n (note that both terms are naturally subobjects
of C^n). As a result, `H_i(imker C n) = 0` for all `i≠n`, and `= H_i(C)` for `i=n`.
-/
def imker (C : CochainComplex 𝓐 ℤ) (n : ℤ) : CochainComplex 𝓐 ℤ
    where
  pt i := if i = n - 1 then image (C.dTo n) else if i = n then kernel (C.dFrom n) else 0
  d i j :=
    if hi : i = n - 1 then
      if hj : j = n then
        -- modulo eq_to_iso this is just the `image_to_kernel` map.
            (eqToIso (by rw [hi, if_pos rfl]) : (_ : 𝓐) ≅ image (C.dTo n)).Hom ≫
          imageToKernel' _ _ (HomologicalComplex.dTo_comp_dFrom _ n) ≫
            (eqToIso (by rw [if_neg, if_pos hj]; linarith)).Hom
      else 0
    else 0
  shape' := by
    rintro i j (h : _ ≠ _)
    split_ifs with hi
    · rw [dif_neg]
      rintro rfl
      exact (h (add_eq_of_eq_sub hi)).elim
    · rfl
  d_comp_d' := by
    rintro i j k (rfl : _ = _) (rfl : _ = _)
    split_ifs with hi hn
    · subst hi
      simp only [add_right_eq_self, one_ne_zero, not_false_iff, dif_neg, comp_zero]
    · apply zero_comp

namespace Imker

open HomologicalComplex (single)

theorem x_def {n i : ℤ} :
    (imker C n).pt i =
      if i = n - 1 then image (C.dTo n) else if i = n then kernel (C.dFrom n) else 0 :=
  rfl

@[simps]
def xIsoImage (n : ℤ) : (imker C n).pt (n - 1) ≅ image (C.dTo n) :=
  eqToIso (by rw [X_def, if_pos rfl])

@[simps]
def xIsoImageOfEq {n i : ℤ} (h : i = n - 1) : (imker C n).pt i ≅ image (C.dTo n) :=
  eqToIso (by rw [X_def, if_pos h])

@[simps]
def xIsoImage' (n : ℤ) : (C.imker (n + 1)).pt n ≅ image (C.d n (n + 1)) :=
  eqToIso (by simp) ≪≫ xIsoImage C (n + 1) ≪≫ imageIsoOfEq (C.dTo_eq rfl) ≪≫ image.isIsoComp _

@[simps]
def xIsoKernel (n : ℤ) : (imker C n).pt n ≅ kernel (C.dFrom n) :=
  eqToIso (by rw [X_def, if_neg, if_pos rfl]; linarith)

@[simps]
def xIsoKernelOfEq {n i : ℤ} (h : i = n) : (imker C n).pt i ≅ kernel (C.dFrom n) :=
  eqToIso (by rw [X_def, if_neg, if_pos h]; linarith)

@[simps]
def kernelIsoXOfEq {n i : ℤ} (h : i = n) : (kernel (C.dFrom n) : 𝓐) ≅ (imker C n).pt i :=
  eqToIso (by rw [X_def, if_neg, if_pos h]; linarith)

theorem x_isZero_of_ne {i j : ℤ} (h1 : j ≠ i - 1) (h2 : j ≠ i) : IsZero ((C.imker i).pt j) :=
  by
  rw [X_def, if_neg h1, if_neg h2]
  exact is_zero_zero 𝓐

@[simp]
theorem d_def {n i j : ℤ} :
    (imker C n).d i j =
      if hi : i = n - 1 then
        if hj : j = n then
          (eqToIso (by rw [hi, if_pos rfl]) :
                (if i = n - 1 then image (C.dTo n) else if i = n then kernel (C.dFrom n) else 0 :
                    𝓐) ≅
                  image (C.dTo n)).Hom ≫
            imageToKernel' _ _ (HomologicalComplex.dTo_comp_dFrom _ n) ≫
              (eqToIso (by dsimp only [imker]; rw [if_neg, if_pos hj]; linarith) :
                  (kernel (C.dFrom n) : 𝓐) ≅ _).Hom
        else 0
      else 0 :=
  rfl

theorem d_eq_im_to_ker {n i j : ℤ} (h : i = n - 1) (hj : j = n) :
    (imker C n).d i j =
      (xIsoImageOfEq C h).Hom ≫
        imageToKernel' _ _ (HomologicalComplex.dTo_comp_dFrom _ n) ≫ (xIsoKernelOfEq _ hj).inv :=
  by
  simp only [h, hj, eq_self_iff_true, d_def, eq_to_iso.hom, dif_pos, X_iso_image_of_eq_hom,
    X_iso_kernel_of_eq_inv]
  rfl

theorem dFrom_eq_zero {n i : ℤ} (h : i ≠ n - 1) : (C.imker n).dFrom i = 0 := by
  rw [HomologicalComplex.dFrom_eq (C.imker n) rfl, d_def, dif_neg h, zero_comp]

theorem boundedBy (i : ℤ) : ((HomotopyCategory.quotient _ _).obj (C.imker i)).BoundedBy (i + 1) :=
  by
  intro j hj
  simp only [HomotopyCategory.quotient_obj_as]
  apply X_is_zero_of_ne <;> linarith

instance isBoundedAbove (i : ℤ) :
    ((HomotopyCategory.quotient _ _).obj (C.imker i)).IsBoundedAbove :=
  ⟨⟨i + 1, boundedBy C i⟩⟩

/-- The natural map from `imker C n` to `H_n(C)[n]`, the complex consisting of the n'th
homology of C supported in degree n. -/
def toSingle (n : ℤ) : C.imker n ⟶ (single _ _ n).obj (C.homology' n)
    where
  f i :=
    if h : i = n then
      (xIsoKernelOfEq C h).Hom ≫
        cokernel.π (imageToKernel' _ _ (HomologicalComplex.dTo_comp_dFrom _ n)) ≫
          (homology'IsoCokernelImageToKernel' _ _ _).inv ≫
            (HomologicalComplex.singleObjXSelf 𝓐 (ComplexShape.up ℤ) n _).inv ≫ eqToHom (by rw [h])
    else 0
  comm' := by
    rintro i j (rfl : _ = _)
    simp only [HomologicalComplex.singleObjXSelf_inv, eq_to_iso.hom, eq_to_hom_trans,
      HomologicalComplex.single_obj_d, comp_zero]
    split_ifs with hi hn
    · subst hi; clear hn
      rw [d_eq_im_to_ker C (show i = i + 1 - 1 by ring) rfl]
      simp only [category.assoc, iso.inv_hom_id_assoc, cokernel.condition_assoc, zero_comp,
        comp_zero]
    · exact (hn rfl).elim
    · rw [comp_zero]

-- move
theorem HomologicalComplex.single_obj_isZero (V : Type _) [_inst_1 : Category V]
    [_inst_2 : HasZeroMorphisms V] [_inst_3 : HasZeroObject V] {ι : Type _}
    [_inst_4 : DecidableEq ι] (c : ComplexShape ι) {i j : ι} (h : i ≠ j) (A : V) :
    IsZero (((single V c j).obj A).pt i) :=
  by
  change is_zero (ite (i = j) A 0)
  rw [if_neg h]
  exact is_zero_zero V

-- move
def HomologicalComplex.singleObjIsoZero (V : Type _) [_inst_1 : Category V]
    [_inst_2 : HasZeroMorphisms V] [_inst_3 : HasZeroObject V] {ι : Type _}
    [_inst_4 : DecidableEq ι] (c : ComplexShape ι) {i j : ι} (h : i ≠ j) (A : V) :
    ((single V c j).obj A).pt i ≅ 0 :=
  IsZero.isoZero (HomologicalComplex.single_obj_isZero _ _ h _)

-- why does `homology_zero_zero` need a zero object?
-- move
theorem homology'_isZero_of_isZero {V : Type _} [Category V] [HasZeroMorphisms V] {A B C : V}
    (hB : IsZero B) {f : A ⟶ B} {g : B ⟶ C} [HasKernels V] [HasImages V] [HasCokernels V]
    [HasZeroObject V]
    -- ??
    (w : f ≫ g = 0) :
    IsZero (homology' f g w) :=
  by
  simp_rw [is_zero.eq_zero_of_tgt hB f]
  simp_rw [is_zero.eq_zero_of_src hB g]
  exact is_zero_of_iso_of_zero hB homology_zero_zero.symm

-- variant of homology_zero_zero
-- move
def homologyZeroZero' {V : Type _} [Category V] [Abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C}
    (hf : f = 0) (hg : g = 0) : homology' f g (by simp [hf]) ≅ B :=
  eqToIso (show homology' f g _ = homology' (0 : A ⟶ B) (0 : B ⟶ C) (by simp) by simp [hf, hg]) ≪≫
    homology'ZeroZero

-- move
theorem isIso_cokernel_pi_imageToKernel_of_zero_of_zero {V : Type _} [Category V] [Abelian V]
    {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (hf : f = 0) (hg : g = 0) :
    IsIso (cokernel.π (imageToKernel f g (by simp [hf]))) :=
  by
  subst hf
  subst hg
  rw [imageToKernel_zero_left]
  apply cokernel.π_of_zero

-- move
theorem Cokernel.desc_spec {V : Type _} [Category V] [Abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C}
    (w : f ≫ g = 0) (c : cokernel f ⟶ C) : cokernel.π f ≫ c = g ↔ c = cokernel.desc f g w :=
  by
  have h2 := cokernel.π_desc f g w
  constructor
  · rintro rfl
    symm
    rwa [cancel_epi] at h2 
  · rintro rfl
    assumption

-- move
theorem Cokernel.desc_comp_left {V : Type _} [Category V] [Abelian V] {A B C D : V} {f : A ⟶ B}
    {g : B ⟶ C} {e : C ⟶ D} (w : f ≫ g = 0) :
    cokernel.desc f g w ≫ e = cokernel.desc f (g ≫ e) (by rw [← category.assoc, w, zero_comp]) :=
  by
  rw [← cokernel.desc_spec]
  simp [cokernel.π_desc]

-- move
theorem IsIsoCokernel.desc {V : Type _} [Category V] [Abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C}
    (h : Exact f g) (h2 : Epi g) : IsIso (cokernel.desc f g h.1) :=
  isIso_of_op (cokernel.desc f g h.w)

-- move
theorem sqFrom_epi_of_epi {ι : Type _} {V : Type _} [_inst_1 : Category V] [_inst_2 : Abelian V]
    {c : ComplexShape ι} {C₁ C₂ : HomologicalComplex V c} (φ : C₁.Hom C₂) (i : ι)
    (h2 : IsZero (C₂.xNext i)) [Epi (φ.f i)] : Epi (HomologicalComplex.Hom.sqFrom φ i) :=
  ⟨by
    rintro ψ ⟨fL, fR, fw⟩ ⟨gL, gR, gw⟩
    intro h
    congr
    · apply_fun CategoryTheory.CommaMorphism.left at h 
      simp at h 
      rwa [cancel_epi] at h 
    · dsimp at fR gR 
      have fR0 : fR = 0 := is_zero.eq_zero_of_src h2 _
      subst fR0
      have gR0 : gR = 0 := is_zero.eq_zero_of_src h2 _
      subst gR0⟩

-- move
theorem kernelSubobjectMap_epi_of_epi {C : Type _} [_inst_1 : Category C] [Abelian C] {X Y : C}
    {f : X ⟶ Y} (hY : IsZero Y) {X' Y' : C} {f' : X' ⟶ Y'} (hY' : IsZero Y')
    (φ : Arrow.mk f ⟶ Arrow.mk f') [Epi φ.left] : Epi (kernelSubobjectMap φ) :=
  by
  have hf : f = 0 := is_zero.eq_zero_of_tgt hY _
  have hf' : f' = 0 := is_zero.eq_zero_of_tgt hY' _
  have hfiso : is_iso (kernel_subobject f).arrow :=
    by
    rw [← kernel_subobject_arrow, hf]
    simp
    infer_instance
  have hf'iso : is_iso (kernel_subobject f').arrow :=
    by
    rw [← kernel_subobject_arrow, hf']
    simp
    infer_instance
  suffices epi (kernel_subobject_map φ ≫ (kernel_subobject f').arrow) by
    rwa [epi_is_iso_comp_iff_epi] at this 
  rw [kernel_subobject_map_arrow]
  simp
  infer_instance

-- move
theorem imageToKernel_epi_of_epi {V : Type _} [Category V] [Abelian V] {A B C : V} (f : A ⟶ B)
    (g : B ⟶ C) [Epi f] (w : f ≫ g = 0) : Epi (imageToKernel f g w) :=
  by
  have claim0 := image_subobject_arrow_comp f
  have claim : (image_subobject f).arrow = imageToKernel f g w ≫ (kernel_subobject g).arrow :=
    (imageToKernel_arrow f g w).symm
  have claim2 := factorThruImageSubobject_comp_imageToKernel _ _ w
  suffices epi (factor_thru_kernel_subobject g f w)
    by
    rw [← claim2] at this 
    skip
    apply epi_of_epi (factor_thru_image_subobject f) (imageToKernel f g w)
  apply epi_of_epi_of_comp_epi_of_mono _ (kernel_subobject g).arrow
  rw [factor_thru_kernel_subobject_comp_arrow g f w]
  infer_instance

-- move
theorem imageToKernel_zero_left' {V : Type _} [Category V] [HasZeroMorphisms V] {A B C : V}
    {f : A ⟶ B} (hf : f = 0) (g : B ⟶ C) [HasKernels V] [HasZeroObject V] [HasImage f] :
    imageToKernel f g (by rw [hf, zero_comp]) = 0 :=
  by
  convert imageToKernel_zero_left g
  rw [zero_comp]

-- move
theorem Cokernel.desc_isIso {A B C D : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (e : C ⟶ D) [IsIso e]
    (w : f ≫ g = 0) :
    cokernel.desc f g w ≫ e = cokernel.desc f (g ≫ e) (by rw [← category.assoc, w, zero_comp]) :=
  by
  rw [← cancel_epi (cokernel.π f)]
  simp

-- move
theorem imageToKernel_eq_imageToKernel_of_eq_snd {A B C : 𝓐} (f : A ⟶ B) {g h : B ⟶ C} (hgh : g = h)
    (w : f ≫ g = 0) :
    imageToKernel f g w = imageToKernel f h (by rw [← hgh, w]) ≫ eqToHom (by rw [hgh]) :=
  by
  subst hgh
  simp only [eq_to_hom_refl, category.comp_id]

-- move
theorem imageToKernel_eq_imageToKernel_of_eq_fst {A B C : 𝓐} (f g : A ⟶ B) {h : B ⟶ C} (hfg : f = g)
    (w : f ≫ h = 0) :
    imageToKernel f h w = eqToHom (by rw [hfg]) ≫ imageToKernel g h (by rw [← hfg, w]) :=
  by
  subst hfg
  simp only [eq_to_hom_refl, category.id_comp]

-- lemma cokernel.desc_with_isomorphisms {A B C D : 𝓐} (f : A ⟶ B) (e : B ⟶ C) (g : C ⟶ D)
--   [is_iso e] (w : f ≫ e ≫ g = 0) :
--   (cokernel_comp_is_iso f e).hom ≫ cokernel.desc f (e ≫ g) w =
--   cokernel.desc (f ≫ e) g (by simp [w]) :=
-- begin
--   simp,
--   admit, -- presumably this is true!
-- end
-- move to `single`
theorem Single.d_eq_zero (V : Type _) [Category V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι : Type _} [DecidableEq ι] (c : ComplexShape ι) (i j k : ι) (v : V) :
    ((single V c i).obj v).d j k = 0 :=
  rfl

-- move to `single`
theorem Single.dFrom_eq_zero (V : Type _) [Category V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι : Type _} [DecidableEq ι] (c : ComplexShape ι) (i j : ι) (v : V) :
    ((single V c i).obj v).dFrom j = 0 :=
  Single.d_eq_zero _ _ _ _ _ _

-- move to `single`
theorem Single.dTo_eq_zero (V : Type _) [Category V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι : Type _} [DecidableEq ι] (c : ComplexShape ι) (i j : ι) (v : V) :
    ((single V c i).obj v).dTo j = 0 :=
  Single.d_eq_zero _ _ _ _ _ _

-- this is preparation for `imker.map_is_iso` which follows.
theorem HomologyFunctor.isIso_of_is_zero_of_is_zero_of_is_zero {ι : Type _} {c : ComplexShape ι}
    {i j : ι} (hij : c.Rel i j) {C₁ C₂ : HomologicalComplex 𝓐 c} (h1from : C₁.dFrom j = 0)
    (h2to : C₂.dTo j = 0) (h2from : C₂.dFrom j = 0) (isomap : cokernel (C₁.dTo j) ≅ C₂.pt j)
    {f : C₁ ⟶ C₂} (hf : f.f j = cokernel.π (C₁.dTo j) ≫ isomap.Hom) :
    IsIso ((homology'Functor 𝓐 c j).map f) :=
  by
  rw [homology'Functor_map]
  let h₁ : HasHomology (C₁.d_to j) (C₁.d_from j) (cokernel (C₁.d_to j)) :=
    HasHomology.sndEqZero' h1from
  let h₂ : HasHomology (C₂.d_to j) (C₂.d_from j) (C₂.X j) := HasHomology.fstSndEqZero' h2to h2from
  have :=
    HasHomology.map_iso_homology'_map h₁ h₂ (Commsq.ofEq (HomologicalComplex.Hom.comm_to f j)).symm
      (Commsq.ofEq (HomologicalComplex.Hom.comm_from f j)).symm
  rw [← is_iso_iff_is_iso_comp_left (h₁.iso (homology'.has (C₁.d_to j) (C₁.d_from j) _)).Hom]
  swap; infer_instance
  rw [← is_iso_iff_is_iso_comp_right (h₂.iso (homology'.has (C₂.d_to j) (C₂.d_from j) _)).inv]
  swap; infer_instance
  suffices h2 : is_iso (h₁.map h₂ (Commsq.ofEq _).symm (Commsq.ofEq _).symm)
  · rw [this] at h2 ; convert h2 using 1; simp; congr
  convert_to is_iso isomap.hom; swap; infer_instance
  simp only [h₁, h₂, HasHomology.map, HasHomology.sndEqZero', HasHomology.fstSndEqZero',
    HasHomology.desc, HasHomology.lift, hf, category.assoc]
  symm
  apply exact.epi_desc_unique
  apply exact.mono_lift_unique
  simp only [category.assoc]

/-- `to_single C n` induces an isomorphism of cohomology in degree `n`. -/
theorem map_isIso (n : ℤ) :
    IsIso
      (homology'.map (HomologicalComplex.dTo_comp_dFrom _ _) (HomologicalComplex.dTo_comp_dFrom _ _)
        (HomologicalComplex.Hom.sqTo (toSingle C n) n)
        (HomologicalComplex.Hom.sqFrom (toSingle C n) n) rfl) :=
  by
  /-
  image_subobject (C.d_to) -> kernel_subobject (C.d_from) -> 0
   |
   \⧸
   0                       -> C.homology n                -> 0
  
  -/
  change is_iso ((homology'Functor 𝓐 (ComplexShape.up ℤ) n).map (to_single C n))
  refine' homology_functor.is_iso_of_is_zero_of_is_zero_of_is_zero _ _ _ _ _ _
  · exact n - 1
  · show _ = _; · ring
  · rw [d_from_eq_zero]; linarith
  · rw [single.d_to_eq_zero]
  · rw [single.d_from_eq_zero]
  · refine' _ ≪≫ (HomologicalComplex.singleObjXSelf _ _ _ _).symm
    refine'
      cokernel_iso_of_eq (HomologicalComplex.dTo_eq (C.imker n) (show n - 1 + 1 = n by ring)) ≪≫ _
    refine' cokernel_epi_comp _ _ ≪≫ _
    refine' cokernel_iso_of_eq (d_eq_im_to_ker _ rfl rfl) ≪≫ _
    refine' cokernel_epi_comp _ _ ≪≫ _
    refine' cokernel_comp_is_iso _ _ ≪≫ _
    exact (homology'IsoCokernelImageToKernel' _ _ _).symm
  · delta to_single
    dsimp; simp

instance toSingleQuasiIso (n : ℤ) :
    HomotopyCategory.IsQuasiIso <| (HomotopyCategory.quotient _ _).map (toSingle C n) :=
  ⟨by
    intro i
    -- split into cases : the n'th map, and all the other maps,
    rcases eq_or_ne i n with (rfl | hin)
    · -- The n'th map is the nontrivial case.
      -- First there's this quotient map to the homotopy category which we replace by `homology_functor`.
      rw [← functor.comp_map]
      apply
        map_is_iso_of_iso_of_map_is_iso
          (HomotopyCategory.homology'Factors 𝓐 (ComplexShape.up ℤ) i).symm
      /- The goal now states that the middle arrow induces an isomorphism
               on homology of the below complexes:
      
               im d -> ker d -> 0
                |       |       |
                \/      \⧸      \/
                 0  -> ker/im-> 0
      
            But we just proved this in `map_is_iso`.
            -/
      apply map_is_iso
    -- For the "boring" cases (where we're asserting 0 ≅ 0) we deal with degree n-1 separately.
    · rcases eq_or_ne i (n - 1) with (rfl | hin')
      -- degree n-1
      · rw [← functor.comp_map]
        apply
          map_is_iso_of_iso_of_map_is_iso
            (HomotopyCategory.homology'Factors 𝓐 (ComplexShape.up ℤ) (n - 1)).symm
        apply is_iso_of_is_zero_of_is_zero
        · apply @is_zero_cokernel_of_epi _ _ _ _ _ _ _
          have foo : HomologicalComplex.dTo (C.imker n) (n - 1) = 0 :=
            by
            apply is_zero.eq_zero_of_src
            have := HomologicalComplex.xPrevIso (C.imker n) (show n - 2 + 1 = n - 1 by ring)
            apply is_zero_of_iso_of_zero _ this.symm
            apply X_is_zero_of_ne <;> linarith
          have : mono (HomologicalComplex.dFrom (C.imker n) (n - 1)) :=
            by
            rw [HomologicalComplex.dFrom_eq (C.imker n) (show n - 1 + 1 = n by ring)]
            rw [d_eq_im_to_ker _ rfl rfl]
            delta imageToKernel'
            -- should register the instance that image_to_kernel' is mono!
            infer_instance
          convert imageToKernel_epi_of_zero_of_mono (HomologicalComplex.dFrom (C.imker n) (n - 1))
        · rw [← functor.comp_obj]
          apply
            obj_is_zero_of_iso
              (HomotopyCategory.homology'Factors 𝓐 (ComplexShape.up ℤ) (n - 1)).symm
          rw [homology'Functor_obj]
          apply homology_is_zero_of_is_zero
          dsimp only
          rw [if_neg hin]
          apply is_zero_zero
      -- other degrees
      · apply is_iso_of_is_zero_of_is_zero
        · rw [← functor.comp_obj]
          apply obj_is_zero_of_iso (HomotopyCategory.homology'Factors 𝓐 (ComplexShape.up ℤ) i).symm
          rw [homology'Functor_obj]
          have hC := X_is_zero_of_ne C hin' hin
          refine' is_zero_of_iso_of_zero hC _
          delta HomologicalComplex.homology'
          symm
          convert homology'ZeroZero
          apply is_zero.eq_zero_of_tgt hC
          apply is_zero.eq_zero_of_src hC
          all_goals infer_instance
        · rw [← functor.comp_obj]
          apply obj_is_zero_of_iso (HomotopyCategory.homology'Factors 𝓐 (ComplexShape.up ℤ) i).symm
          rw [homology'Functor_obj]
          apply homology_is_zero_of_is_zero
          apply HomologicalComplex.single_obj_isZero _ _ hin⟩

end Imker

end CochainComplex

