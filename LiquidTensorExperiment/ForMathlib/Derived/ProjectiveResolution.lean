import LiquidTensorExperiment.ForMathlib.Derived.KProjective
import LiquidTensorExperiment.ForMathlib.Derived.Example

#align_import for_mathlib.derived.ProjectiveResolution

open CategoryTheory

namespace homology'

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
  (w : f ≫ g = 0)

theorem desc_zero (w) :
    homology'.desc' (0 : X ⟶ Y) g w (Limits.kernel.ι _) (by simp) =
      homology'.ι _ _ _ ≫ Limits.cokernel.desc _ (𝟙 _) (by simp) :=
  by
  apply homology'.hom_from_ext
  simp

theorem lift_desc'_of_eq_zero (hf : f = 0) :
    homology'.lift f g w (Limits.kernel.ι g ≫ Limits.cokernel.π f) (by simp) ≫
        homology'.desc' _ _ _ (Limits.kernel.ι g) (by simp [hf]) =
      Limits.kernel.ι _ :=
  by
  subst hf
  rw [desc_zero]
  simp

end homology'

namespace CategoryTheory.ProjectiveResolution

open CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

variable {X : A} (P : ProjectiveResolution X)

noncomputable section

def bhc : BoundedHomotopyCategory A :=
  ChainComplex.toBoundedHomotopyCategory.obj P.complex

def bhcπ : P.bhc ⟶ (BoundedHomotopyCategory.single _ 0).obj X :=
  ChainComplex.toBoundedHomotopyCategory.map P.π ≫
    ((HomotopyCategory.quotient _ _).mapIso (ChainComplex.single₀CompEmbedIsoSingle.app X)).hom

instance [EnoughProjectives A] : HomotopyCategory.IsQuasiIso P.bhcπ :=
  by
  dsimp only [bhc_π]
  suffices HomotopyCategory.IsQuasiIso (chain_complex.toBoundedHomotopyCategory.map P.π) by skip;
    infer_instance
  exact P.is_projective_resolution.isQuasiIsoEmbed

instance [EnoughProjectives A] : HomotopyCategory.IsKProjective P.bhc.val :=
  ChainComplex.toBoundedHomotopyCategory.isKProjective _ X P.π P.IsProjectiveResolution

def extIso [EnoughProjectives A] (Y : BoundedHomotopyCategory A) (i : ℤ) :
    ((BoundedHomotopyCategory.ext i).obj
            (Opposite.op ((BoundedHomotopyCategory.single _ 0).obj X))).obj
        Y ≅
      (preadditiveYoneda.obj (Y⟦i⟧)).obj (Opposite.op P.bhc) :=
  by apply BoundedHomotopyCategory.extIso _ _ _ _ P.bhc_π

def extIsoZero [EnoughProjectives A] (Y : BoundedHomotopyCategory A) :
    ((BoundedHomotopyCategory.ext 0).obj
            (Opposite.op ((BoundedHomotopyCategory.single _ 0).obj X))).obj
        Y ≅
      (preadditiveYoneda.obj Y).obj (Opposite.op P.bhc) :=
  P.extIso Y 0 ≪≫ (preadditiveYoneda.mapIso (shiftZero _ _)).app _

def extSingleIso [EnoughProjectives A] (Y : A) :
    ((BoundedHomotopyCategory.ext 0).obj
            (Opposite.op ((BoundedHomotopyCategory.single _ 0).obj X))).obj
        ((BoundedHomotopyCategory.single _ 0).obj Y) ≅
      (((preadditiveYoneda.obj Y).mapHomologicalComplex _).obj P.bhc.val.as.op).homology' 0 :=
  P.extIsoZero _ ≪≫ P.bhc.homSingleIso Y 0

theorem isZero_hom_of_isZero {X Y : A} (hX : IsZero X) : IsZero (AddCommGroupCat.of (X ⟶ Y)) :=
  { unique_to := fun Z =>
      by
      refine'
        ⟨{  toInhabited := inferInstance
            uniq := fun f => _ }⟩
      ext x
      rw [hX.eq_to x, ← hX.eq_to (0 : X ⟶ Y), map_zero, map_zero]
    unique_from := fun Z =>
      by
      refine'
        ⟨{  toInhabited := inferInstance
            uniq := fun f => _ }⟩
      ext z
      rw [hX.eq_to (f z), ← hX.eq_to _] }

def homologyZeroIso [EnoughProjectives A] (Y : A) :
    (((preadditiveYoneda.obj Y).mapHomologicalComplex _).obj P.bhc.val.as.op).homology' 0 ≅
      kernel ((preadditiveYoneda.obj Y).map (P.complex.d 1 0).op) :=
  homologyIso _ (1 : ℤ) 0 (-1) (by simp) (by simp) ≪≫
    { hom :=
        kernel.lift _
          (homology'.desc' _ _ _ (kernel.ι _)
            (by
              rw [kernel.lift_ι]
              apply IsZero.eq_of_src
              apply CategoryTheory.ProjectiveResolution.isZero_hom_of_isZero
              exact is_zero_zero _))
          (by
            apply homology'.hom_from_ext
            simp only [homology'.π'_desc'_assoc, comp_zero]
            erw [kernel.condition])
      inv :=
        homology'.lift _ _ _ (kernel.ι _ ≫ cokernel.π _)
          (by
            simp only [Functor.mapHomologicalComplex_obj_d, HomologicalComplex.op_d,
              Category.assoc, cokernel.π_desc]
            erw [kernel.condition])
      hom_inv_id := by
        apply homology'.hom_to_ext
        apply homology'.hom_from_ext
        simp
      inv_hom_id := by
        apply equalizer.hom_ext
        simp only [Category.assoc, kernel.lift_ι, equalizer_as_kernel, Category.id_comp]
        apply homology'.lift_desc'_of_eq_zero
        apply IsZero.eq_of_src
        apply CategoryTheory.ProjectiveResolution.isZero_hom_of_isZero
        exact is_zero_zero _ }

def extSingleIsoKernel [EnoughProjectives A] (Y : A) :
    ((BoundedHomotopyCategory.ext 0).obj
            (Opposite.op ((BoundedHomotopyCategory.single _ 0).obj X))).obj
        ((BoundedHomotopyCategory.single _ 0).obj Y) ≅
      kernel ((preadditiveYoneda.obj Y).map (P.complex.d 1 0).op) :=
  P.extSingleIso Y ≪≫ P.homology'ZeroIso _

def homToKernel [EnoughProjectives A] (Y : A) :
    (preadditiveYoneda.obj Y).obj (Opposite.op X) ⟶
      kernel ((preadditiveYoneda.obj Y).map (P.complex.d 1 0).op) :=
  kernel.lift _ (CategoryTheory.Functor.map _ <| Quiver.Hom.op <| P.π.f _)
    (by
      rw [← Functor.map_comp, ← op_comp, ← P.π.comm, op_comp, Functor.map_comp]
      convert zero_comp
      apply IsZero.eq_of_tgt
      dsimp
      apply CategoryTheory.ProjectiveResolution.isZero_hom_of_isZero
      exact is_zero_zero _)

instance mono_homToKernel [EnoughProjectives A] (Y : A) : CategoryTheory.Mono (homToKernel P Y) :=
  by
  dsimp only [CategoryTheory.ProjectiveResolution.homToKernel]
  let e := (preadditive_yoneda.obj Y).map (P.π.f 0).op
  suffices mono e by
    skip
    have he :
      e =
        kernel.lift ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op)
            ((preadditive_yoneda.obj Y).map (P.π.f 0).op) _ ≫
          kernel.ι _ :=
      by simp
    exact mono_of_mono_fac he.symm
  rw [AddCommGroupCat.mono_iff_injective]
  rw [injective_iff_map_eq_zero]
  rintro (f : X ⟶ Y) (hf : _ ≫ f = 0)
  have : (0 : P.complex.X 0 ⟶ Y) = P.π.f 0 ≫ 0 := by simp
  erw [this] at hf 
  haveI : CategoryTheory.Epi (P.π.f 0) := P.epi
  erw [cancel_epi] at hf 
  exact hf

def cokernelTo : cokernel (P.complex.d 1 0) ⟶ X :=
  cokernel.desc _ (P.π.f _)
    (by
      rw [← P.π.comm]
      convert zero_comp
      apply IsZero.eq_of_tgt
      exact is_zero_zero _)

instance epi_cokernelTo : CategoryTheory.Epi P.cokernelTo :=
  by
  dsimp [cokernel_to]
  apply epi_of_epi_fac (cokernel.π_desc _ _ _)
  exact P.epi

instance mono_cokernelTo : Mono P.cokernelTo :=
  by
  dsimp [cokernel_to]
  apply Abelian.Pseudoelement.mono_of_zero_of_map_zero
  intro a ha
  obtain ⟨a, rfl⟩ := Abelian.Pseudoelement.pseudo_surjective_of_epi (cokernel.π _) a
  rw [← Abelian.Pseudoelement.comp_apply, cokernel.π_desc] at ha 
  have e := Abelian.Pseudoelement.pseudo_exact_of_exact P.exact₀
  obtain ⟨b, rfl⟩ := e.2 _ ha
  rw [← Abelian.Pseudoelement.comp_apply, cokernel.condition, Abelian.Pseudoelement.zero_apply]

instance isIso_cokernelTo : IsIso P.cokernelTo :=
  isIso_of_mono_of_epi _

instance epi_homToKernel [EnoughProjectives A] (Y : A) : CategoryTheory.Epi (homToKernel P Y) :=
  by
  dsimp only [CategoryTheory.ProjectiveResolution.homToKernel]
  rw [AddCommGroupCat.epi_iff_surjective]
  intro f
  let g : P.complex.X 0 ⟶ Y := kernel.ι ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op) f
  have hg : P.complex.d 1 0 ≫ g = 0 := by
    dsimp only [g]
    change
      (kernel.ι ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op) ≫
            (preadditive_yoneda.obj Y).map (P.complex.d 1 0).op)
          f =
        0
    rw [kernel.condition]; rfl
  change ∃ q : X ⟶ _, _ = _
  let q' : cokernel (P.complex.d 1 0) ⟶ Y := cokernel.desc _ g hg
  use inv P.cokernel_to ≫ q'
  apply_fun kernel.ι ((preadditive_yoneda.obj Y).map (P.complex.d 1 0).op)
  swap
  · rw [← AddCommGroupCat.mono_iff_injective]; infer_instance
  rw [← comp_apply, kernel.lift_ι]
  dsimp only [q']
  change _ ≫ _ = _
  rw [← Category.assoc]
  let t := _; change t ≫ _ = _
  have ht : t = cokernel.π _ := by dsimp only [t]; rw [IsIso.comp_inv_eq]; dsimp [cokernel_to];
    simp
  rw [ht]; simp

instance isIso_homToKernel [EnoughProjectives A] (Y : A) : IsIso (homToKernel P Y) :=
  isIso_of_mono_of_epi _

def homTo [EnoughProjectives A] (Y : A) :
    (preadditiveYoneda.obj Y).obj (Opposite.op X) ⟶
      (preadditiveYoneda.obj ((BoundedHomotopyCategory.single _ 0).obj Y)).obj (Opposite.op P.bhc)
    where
  toFun := fun f : X ⟶ Y => P.bhcπ ≫ (BoundedHomotopyCategory.single _ _).map f
  map_zero' := by
    convert comp_zero
    dsimp [BoundedHomotopyCategory.single]
    simp
  map_add' :=
    by
    -- Missing additive isntance for bounded_homotopy_category.single
    dsimp [BoundedHomotopyCategory.single]
    intro a b
    rw [← Preadditive.comp_add]; congr 1
    rw [← Functor.map_add]
    congr 1
    -- Missing additive instance....
    ext i
    dsimp
    split_ifs <;> simp

instance isIso_homTo [EnoughProjectives A] (Y : A) : IsIso (P.homTo Y) :=
  by
  -- rw AddCommGroup.is_iso_iff_bijective, <-- missing :(
  apply (config := { instances := false }) is_iso_of_mono_of_epi;
  infer_instance
  · rw [AddCommGroupCat.mono_iff_injective]
    intro a b h
    dsimp [hom_to] at h 
    erw [← (HomotopyCategory.quotient _ _).map_comp] at h 
    erw [← (HomotopyCategory.quotient _ _).map_comp] at h 
    replace h := HomotopyCategory.homotopyOfEq _ _ h
    have hh := h.comm 0; dsimp at hh 
    simp only [eq_self_iff_true, Category.comp_id, Category.id_comp, if_true, Category.assoc,
      HomologicalComplex.cochainComplex_dNext, HomologicalComplex.cochainComplex_prevD,
      HomologicalComplex.single_obj_d, comp_zero, add_zero] at hh 
    dsimp [ChainComplex.single₀CompEmbedIsoSingle,
      ChainComplex.single₀CompEmbedIsoSingleComponent] at hh 
    simp only [Category.id_comp] at hh 
    rw [← dNext_eq_dFrom_fromNext, ← prevD_eq_toPrev_dTo] at hh 
    dsimp [dNext, prevD] at hh 
    have : h.hom ((ComplexShape.up ℤ).next 0) 0 = 0 := by apply IsZero.eq_of_src;
      rw [CochainComplex.next]; apply is_zero_zero
    simp only [comp_zero, add_zero, zero_add, this, cancel_epi (P.π.f 0)] at hh 
    exact hh
  · rw [AddCommGroupCat.epi_iff_surjective]
    rintro (a : P.bhc ⟶ _)
    change ∃ b : X ⟶ Y, _ ≫ _ = _
    let q := a.out
    let q' : P.complex.X 0 ⟶ Y := q.f 0
    let b : X ⟶ Y := inv P.cokernel_to ≫ cokernel.desc _ q' _
    swap
    · dsimp [q']; change P.bhc.val.as.d (-1) 0 ≫ _ = _; rw [← q.comm]
      convert zero_comp
      apply IsZero.eq_of_tgt
      exact is_zero_zero _
    use b
    rw [← HomotopyCategory.quotient_map_out a]
    erw [← (HomotopyCategory.quotient _ _).map_comp]
    congr 1; change _ = q; ext ((_ | i) | i)
    · change _ = q'
      simp only [Iso.app_hom, Functor.map_comp, Functor.map_inv, Category.assoc,
        HomologicalComplex.comp_f, HomologicalComplex.single_map_f, Int.ofNat_eq_coe,
        Int.ofNat_zero, eq_self_iff_true, CategoryTheory.eqToHom_refl, Category.comp_id, Category.id_comp,
        dite_eq_ite, if_true]
      change P.π.f 0 ≫ _ = _
      simp_rw [← Category.assoc]
      let t := _; change t ≫ _ = _
      have ht : t = cokernel.π _ := by
        dsimp [t]
        rw [← Functor.map_inv, ← CategoryTheory.asIso_inv, ← Functor.mapIso_inv]
        let w := (HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapIso (CategoryTheory.asIso P.cokernel_to)
        change (P.π.f 0 ≫ _) ≫ ((HomologicalComplex.eval _ _ 0).mapIso w).inv = _
        rw [Iso.comp_inv_eq]
        dsimp [ChainComplex.single₀CompEmbedIsoSingle,
          ChainComplex.single₀CompEmbedIsoSingleComponent]
        simp only [eq_self_iff_true, Category.comp_id, Category.id_comp, if_true]
        dsimp [cokernel_to]
        simp only [cokernel.π_desc]
        change _ ≫ (iso.refl _).hom = _
        simp only [Iso.refl_hom, Category.comp_id]
      rw [ht]; clear ht; clear t
      rw [cokernel.π_desc]
    · apply IsZero.eq_of_src; exact is_zero_zero _
    · apply IsZero.eq_of_tgt; exact is_zero_zero _

def extSingleIsoHom [EnoughProjectives A] (Y : A) :
    (preadditiveYoneda.obj Y).obj (Opposite.op X) ≅
      ((BoundedHomotopyCategory.ext 0).obj
            (Opposite.op ((BoundedHomotopyCategory.single _ 0).obj X))).obj
        ((BoundedHomotopyCategory.single _ 0).obj Y) :=
  (asIso <| P.homTo _) ≪≫
    (preadditiveYoneda.mapIso <| (shiftZero _ _).symm).app _ ≪≫
      (P.extIso ((BoundedHomotopyCategory.single _ 0).obj Y) 0).symm

end CategoryTheory.ProjectiveResolution

