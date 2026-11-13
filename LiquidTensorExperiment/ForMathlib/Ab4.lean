import Mathlib.CategoryTheory.Abelian.Homology
import LiquidTensorExperiment.ForMathlib.HomotopyCategoryPretriangulated
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.HomotopyCategoryCoproducts

#align_import for_mathlib.ab4

namespace CategoryTheory

open CategoryTheory.Limits

universe v u

class AB4 (A : Type u) [Category.{v} A] [HasCoproducts.{v} A] : Prop where
  cond :
    ∀ {α : Type v} (X Y : α → A) (f : ∀ a, X a ⟶ Y a) (hf : ∀ a, Mono (f a)),
      Mono (Sigma.desc fun a => f a ≫ Sigma.ι Y a)

variable {A : Type u} [Category.{v} A]

instance aB4_mono [HasCoproducts.{v} A] [AB4 A] {α : Type v} (X Y : α → A) (f : ∀ a, X a ⟶ Y a)
    [∀ a, Mono (f a)] : Mono (Sigma.desc fun a => f a ≫ Sigma.ι Y a) := by apply AB4.cond;
  assumption

variable (A)

noncomputable def sigmaFunctor [HasCoproducts.{v} A] (α : Type v) : (α → A) ⥤ A
    where
  obj X := sigmaObj X
  map X Y f := Sigma.desc fun a => f a ≫ Sigma.ι _ a
  map_id' X := by ext ⟨j⟩; simp
  map_comp' X Y Z f j := by ext ⟨j⟩; simp

variable {A}

instance sigmaFunctor_preserves_mono [HasCoproducts.{v} A] [AB4 A] (α : Type v) {X Y : α → A}
    (f : X ⟶ Y) [∀ a, Mono (f a)] : Mono ((sigmaFunctor A α).map f) :=
  CategoryTheory.aB4_mono X Y f

instance sigmaFunctor_preserves_epi [HasCoproducts.{v} A] (α : Type v) {X Y : α → A} (f : X ⟶ Y)
    [∀ a, Epi (f a)] : Epi ((sigmaFunctor A α).map f) :=
  by
  constructor; intro Z s t h
  apply colimit.hom_ext
  rintro ⟨a⟩
  dsimp [sigma_functor] at h 
  apply_fun fun e => colimit.ι _ (discrete.mk a) ≫ e at h 
  simp at h 
  rwa [cancel_epi] at h 

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem aB4_of_preservesColimits_of_reflects_limits_of_aB4 {A B : Type u} [Category.{v} A]
    [Category.{v} B] [HasCoproducts.{v} A] [HasCoproducts.{v} B] (F : A ⥤ B) [PreservesColimits F]
    [CreatesLimits F] [HasLimits B] [AB4 B] : AB4 A :=
  by
  constructor; intro a X Y f hf
  let t := _; change mono t
  suffices mono (F.map t)
    by
    haveI := reflectsLimitsOfSizeShrink.{0, v, 0, v} F
    apply F.mono_of_mono_map this
  let eX : F.obj (∐ fun a : a => X a) ≅ ∐ fun a => F.obj (X a) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (nat_iso.of_components (fun _ => iso.refl _) _)
  swap; · rintro ⟨⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩; dsimp; simp; dsimp; simp
  let eY : F.obj (∐ fun a : a => Y a) ≅ ∐ fun a => F.obj (Y a) :=
    (is_colimit_of_preserves F (colimit.is_colimit _)).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (nat_iso.of_components (fun _ => iso.refl _) _)
  swap; · rintro ⟨⟩ ⟨⟩ ⟨⟨⟨⟩⟩⟩; dsimp; simp; dsimp; simp
  let tt : (∐ fun a => F.obj (X a)) ⟶ ∐ fun a => F.obj (Y a) :=
    sigma.desc fun a => F.map (f a) ≫ sigma.ι _ a
  have : mono tt := by apply AB4.cond; intro a; infer_instance
  suffices F.map t = eX.hom ≫ tt ≫ eY.inv by rw [this]; apply mono_comp
  apply (is_colimit_of_preserves F (colimit.is_colimit _)).hom_ext
  swap; infer_instance
  rintro ⟨i⟩
  erw [← F.map_comp, colimit.ι_desc, F.map_comp]
  dsimp [eX, tt, t, eY, limits.is_colimit.cocone_point_unique_up_to_iso, is_colimit_of_preserves,
    has_colimit.iso_of_nat_iso, is_colimit.map]
  slice_rhs 0 1 => erw [(is_colimit_of_preserves F (colimit.is_colimit _)).fac]
  slice_rhs 0 1 => erw [colimit.ι_desc]
  dsimp [iso.refl]
  simp only [category.id_comp, colimit.ι_desc, cofan.mk_ι_app, category.assoc,
    cocones.precompose_obj_ι, nat_trans.comp_app, nat_iso.of_components_inv_app, colimit.cocone_ι,
    functor.map_cocone_ι_app]
  dsimp
  simp

noncomputable example {X Y Z : A} [Abelian A] (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    cokernel (imageToKernel' f g w) ≅ homology' f g w :=
  (homology'IsoCokernelImageToKernel' f g w).symm

noncomputable def coproductKernelComparison (M : Type _) (S : ComplexShape M) (α : Type v)
    [Abelian A] [HasCoproducts.{v} A] (i : M) (X : α → HomologicalComplex A S) :
    (∐ fun a : α => kernel ((X a).dFrom i)) ⟶ kernel ((∐ X).dFrom i) :=
  Sigma.desc fun a =>
    kernel.lift _ (kernel.ι _ ≫ (Sigma.ι _ a : X a ⟶ ∐ X).f i)
      (by
        rw [category.assoc, (sigma.ι X a : X a ⟶ _).comm_from, ← category.assoc, kernel.condition,
          zero_comp])

-- This should follow from the AB4 assumption
instance mono_coproductKernelComparison (M : Type _) (S : ComplexShape M) (α : Type v) [Abelian A]
    [HasCoproducts.{v} A] [AB4 A] (i : M) (X : α → HomologicalComplex A S) :
    Mono (coproductKernelComparison M S α i X) :=
  by
  let ι : kernel ((∐ X).dFrom i) ⟶ _ := kernel.ι _
  let t := _; change mono t
  suffices mono (t ≫ ι) by skip; apply mono_of_mono t ι
  let F : HomologicalComplex A S ⥤ A := HomologicalComplex.eval _ _ i
  let E : (∐ X).pt i ≅ ∐ fun b => (X b).pt i :=
    (is_colimit_of_preserves F (colimit.is_colimit (discrete.functor X))).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun b => iso.refl _)
  suffices t ≫ ι = (sigma.desc fun a => kernel.ι _ ≫ sigma.ι (fun b => (X b).pt i) a) ≫ E.inv by
    rw [this]; infer_instance
  dsimp [t, ι, coproduct_kernel_comparison]
  apply colimit.hom_ext; intro a
  simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, kernel.lift_ι, category.assoc,
    has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
    colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app, colimit.cocone_ι,
    HomologicalComplex.eval_map]
  dsimp; simp only [category.id_comp]

noncomputable def evalNext (A : Type u) [Category.{v} A] [Abelian A] {M : Type _}
    (S : ComplexShape M) (i : M) : HomologicalComplex A S ⥤ A
    where
  obj X := X.xNext i
  map X Y f := f.next i
  map_id' X := rfl
  map_comp' X Y Z f g := rfl

open scoped ZeroObject

noncomputable def preservesColimitsOfShapeConstZeroAux (α : Type v) (M : Type _)
    (S : ComplexShape M) [Abelian A] [HasCoproducts.{v} A]
    (K : Discrete α ⥤ HomologicalComplex A S) :
    IsColimit (((Functor.const _).obj (0 : A)).mapCocone (colimit.cocone K))
    where
  desc S := 0
  fac S j := (isZero_zero _).eq_of_src _ _
  uniq S m hm := (isZero_zero _).eq_of_src _ _

noncomputable instance preservesColimitsOfShapeConstZero (α : Type v) (M : Type _)
    (S : ComplexShape M) [Abelian A] [HasCoproducts.{v} A] :
    PreservesColimitsOfShape (Discrete α) ((Functor.const _).obj 0 : HomologicalComplex A S ⥤ A) :=
  by
  constructor; intro K
  apply preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit K)
  apply preserves_colimits_of_shape_const_zero_aux

noncomputable def evalNextIso (M : Type _) (S : ComplexShape M) [Abelian A] (i : M) :
    evalNext A S i ≅ HomologicalComplex.eval _ _ (S.next i) :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      intro X Y f
      simp only [iso.refl_hom, category.comp_id, HomologicalComplex.eval_map, category.id_comp]
      rfl)

noncomputable instance evalNextPreservesCoproducts (α : Type v) (M : Type _) (S : ComplexShape M)
    [Abelian A] [HasCoproducts.{v} A] (i : M) :
    PreservesColimitsOfShape (Discrete α) (evalNext A S i) :=
  by
  apply preserves_colimits_of_shape_of_nat_iso (eval_next_iso M S i).symm
  infer_instance

noncomputable def evalPrev (A : Type u) [Category.{v} A] [Abelian A] {M : Type _}
    (S : ComplexShape M) (i : M) : HomologicalComplex A S ⥤ A
    where
  obj X := X.xPrev i
  map X Y f := f.prev i
  map_id' X := rfl
  map_comp' X Y Z f g := rfl

noncomputable def evalPrevIso (M : Type _) (S : ComplexShape M) [Abelian A] (i : M) :
    evalPrev A S i ≅ HomologicalComplex.eval _ _ (S.prev i) :=
  NatIso.ofComponents (fun X => Iso.refl _)
    (by
      intro X Y f
      simp only [iso.refl_hom, category.comp_id, HomologicalComplex.eval_map, category.id_comp]
      rfl)

noncomputable instance evalPrevPreservesCoproducts (α : Type v) (M : Type _) (S : ComplexShape M)
    [Abelian A] [HasCoproducts.{v} A] (i : M) :
    PreservesColimitsOfShape (Discrete α) (evalPrev A S i) :=
  by
  apply preserves_colimits_of_shape_of_nat_iso (eval_prev_iso M S i).symm
  infer_instance

theorem exact_iff_exact_cokernel_desc [Abelian A] (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f g ↔ ∃ w, Mono (cokernel.desc f g w) :=
  by
  constructor
  · intro h; refine' ⟨h.w, _⟩
    apply abelian.pseudoelement.mono_of_zero_of_map_zero
    intro a ha
    have h' : exact f (cokernel.π f) := abelian.exact_cokernel f
    replace h' := abelian.pseudoelement.pseudo_exact_of_exact h'
    have hπ := abelian.pseudoelement.pseudo_surjective_of_epi (cokernel.π f)
    obtain ⟨b, rfl⟩ := hπ a
    rw [← abelian.pseudoelement.comp_apply, cokernel.π_desc] at ha 
    replace h := abelian.pseudoelement.pseudo_exact_of_exact h
    obtain ⟨b, rfl⟩ := h.2 _ ha
    rw [← abelian.pseudoelement.comp_apply, cokernel.condition]
    simp only [abelian.pseudoelement.zero_apply]
  · rintro ⟨w, h⟩; rw [abelian.exact_iff]; refine' ⟨w, _⟩; skip
    rw [← cancel_mono (cokernel.desc f g w)]
    simp only [category.assoc, cokernel.π_desc, kernel.condition, zero_comp]

theorem exact_iff_exact_of_cofork [Abelian A] (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : CokernelCofork f) (hT : IsColimit T) :
    Exact f g ↔ ∃ w : f ≫ g = 0, Mono (hT.desc (CokernelCofork.ofπ g w)) :=
  by
  let e : T.X ≅ cokernel f := hT.cocone_point_unique_up_to_iso (colimit.is_colimit _)
  rw [exact_iff_exact_cokernel_desc]
  apply exists_congr fun w => _
  have : hT.desc (cokernel_cofork.of_π g w) = e.hom ≫ cokernel.desc f g w :=
    by
    dsimp [e, limits.is_colimit.cocone_point_unique_up_to_iso]
    apply hT.hom_ext; intro i
    simp only [is_colimit.fac, is_colimit.fac_assoc, colimit.cocone_ι, colimit.ι_desc]
  rw [this]
  constructor
  · intro; infer_instance
  · intro; constructor
    intro Z a b h
    rw [← cancel_mono e.inv, ← cancel_mono (e.hom ≫ cokernel.desc f g w)]
    simpa

noncomputable def sigmaCokernelCofork [Abelian A] [HasCoproducts.{v} A] [AB4 A] {α : Type v}
    (X Y : α → A) (f : X ⟶ Y) : CokernelCofork ((sigmaFunctor A α).map f) :=
  CokernelCofork.ofπ
    (Sigma.desc fun a : α => cokernel.π (f a) ≫ Sigma.ι (fun b => cokernel (f b)) a)
    (by
      apply colimit.hom_ext
      intro a
      dsimp [sigma_functor]
      simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc,
        cokernel.condition_assoc, zero_comp, comp_zero])

noncomputable def isColimitSigmaCokernelCofork [Abelian A] [HasCoproducts.{v} A] [AB4 A]
    {α : Type v} (X Y : α → A) (f : X ⟶ Y) : IsColimit (sigmaCokernelCofork X Y f) :=
  isColimitAux _
    (fun S =>
      Sigma.desc fun b =>
        cokernel.desc _ (Sigma.ι _ _ ≫ S.π)
          (by
            rw [← category.assoc]
            let t := _; change t ≫ _ = _
            have ht : t = sigma.ι X b ≫ (sigma_functor A α).map f := by dsimp [sigma_functor]; simp
            rw [ht]; clear ht; clear t
            rw [category.assoc, S.condition, comp_zero]))
    (by
      intro S
      dsimp [sigma_cokernel_cofork]
      apply colimit.hom_ext
      simp only [category.assoc, colimit.ι_desc, cofan.mk_ι_app, eq_self_iff_true,
        cokernel_cofork.condition, comp_zero, colimit.ι_desc_assoc, cokernel.π_desc, imp_true_iff]
      rintro ⟨j⟩
      simp)
    (by
      intro S m hm
      apply colimit.hom_ext; rintro ⟨a⟩
      simp only [colimit.ι_desc, cofan.mk_ι_app]
      apply coequalizer.hom_ext; simp only [coequalizer_as_cokernel, cokernel.π_desc]
      simp_rw [← hm, ← category.assoc]; congr 1
      dsimp [sigma_cokernel_cofork]
      simp only [colimit.ι_desc, cofan.mk_ι_app])

theorem exact_coproduct [Abelian A] [HasCoproducts.{v} A] [AB4 A] {α : Type v} (X Y Z : α → A)
    (f : X ⟶ Y) (g : Y ⟶ Z) (w : ∀ i, Exact (f i) (g i)) :
    Exact ((sigmaFunctor A α).map f) ((sigmaFunctor A α).map g) :=
  by
  let ι : (fun a : α => cokernel (f a)) ⟶ Z := fun a => cokernel.desc _ (g a) (w a).w
  let π : Y ⟶ fun a : α => cokernel (f a) := fun a => cokernel.π _
  have : ∀ a, mono (ι a) := by
    intro a
    suffices ∃ w, mono (cokernel.desc (f a) (g a) w) by obtain ⟨q, h⟩ := this; exact h
    rw [← exact_iff_exact_cokernel_desc]; apply w
  have : mono ((sigma_functor A α).map ι) := by apply AB4.cond; assumption
  -- Now need to show that sigma functor commutes with cokernels
  -- Use the fact that this commutes with cokernels to identify the source
  -- with the cokernel of `f`.
  -- Then use exact_iff_exact_cokernel_desc
  rw [exact_iff_exact_of_cofork ((sigma_functor A α).obj X) ((sigma_functor A α).obj Y)
      ((sigma_functor A α).obj Z) ((sigma_functor A α).map f) ((sigma_functor A α).map g)
      (sigma_cokernel_cofork _ _ f) (is_colimit_sigma_cokernel_cofork _ _ f)]
  refine' ⟨_, _⟩
  · apply colimit.hom_ext; intro a
    dsimp [sigma_functor]
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc, comp_zero]
    rw [← category.assoc, (w a.1).w, zero_comp]
  simp only [exact_iff_exact_cokernel_desc] at w 
  choose w₁ w₂ using w
  convert AB4.cond _ Z ι w₂ using 1
  apply colimit.hom_ext; intro a
  dsimp [is_colimit_sigma_cokernel_cofork, is_colimit_aux]
  simp only [colimit.ι_desc, cofan.mk_ι_app]
  apply coequalizer.hom_ext
  simp only [cokernel.π_desc, cokernel.π_desc_assoc]
  dsimp [sigma_functor]
  simp only [colimit.ι_desc, cofan.mk_ι_app]

section

open scoped Pseudoelement

instance epi_coproductKernelComparison [HasCoproducts.{v} A] [AB4 A] (M : Type _)
    (S : ComplexShape M) (α : Type v) [Abelian A] [HasCoproducts.{v} A] (i : M)
    (X : α → HomologicalComplex A S) : Epi (coproductKernelComparison M S α i X) :=
  by
  /-
       _ -ι₁-> _ -π₁-> _
       |       |       |
       t     E.inv   Q.inv
       |       |       |
       v       v       v
       _ -ι₂-> _ -π₂-> _
  
    -/
  let t := _;
  change epi t
  let F : HomologicalComplex A S ⥤ A := HomologicalComplex.eval _ _ i
  let N : HomologicalComplex A S ⥤ A := eval_next _ _ i
  let E : (∐ X).pt i ≅ ∐ fun b => (X b).pt i :=
    (is_colimit_of_preserves F (colimit.is_colimit (discrete.functor X))).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun b => iso.refl _)
  let Q : (∐ X).xNext i ≅ ∐ fun b => (X b).xNext i :=
    (is_colimit_of_preserves N (colimit.is_colimit (discrete.functor X))).coconePointUniqueUpToIso
        (colimit.is_colimit _) ≪≫
      has_colimit.iso_of_nat_iso (discrete.nat_iso fun b => iso.refl _)
  let ι₁ : (∐ fun a : α => kernel ((X a).dFrom i)) ⟶ ∐ fun b => (X b).pt i :=
    sigma.desc fun a => kernel.ι _ ≫ sigma.ι _ a
  let π₁ : (∐ fun b => (X b).pt i) ⟶ ∐ fun b => (X b).xNext i :=
    sigma.desc fun a => (X a).dFrom i ≫ sigma.ι _ a
  let ι₂ : kernel ((∐ X).dFrom i) ⟶ (∐ X).pt i := kernel.ι _
  let π₂ : (∐ X).pt i ⟶ (∐ X).xNext i := (∐ X).dFrom i
  have sqι : ι₁ ≫ E.inv = t ≫ ι₂ := by
    apply colimit.hom_ext; intro a; dsimp [ι₁, E, t, ι₂]
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc,
      has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
      colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app, colimit.cocone_ι,
      HomologicalComplex.eval_map]
    dsimp [coproduct_kernel_comparison]
    simp only [category.id_comp, colimit.ι_desc_assoc, cofan.mk_ι_app, kernel.lift_ι]
  have sqπ : π₁ ≫ Q.inv = E.inv ≫ π₂ :=
    by
    dsimp [π₁, Q, E, π₂, coproduct_kernel_comparison]; apply colimit.hom_ext; rintro ⟨a⟩
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc,
      has_colimit.iso_of_nat_iso_ι_inv_assoc, discrete.nat_iso_inv_app,
      colimit.comp_cocone_point_unique_up_to_iso_inv, functor.map_cocone_ι_app, colimit.cocone_ι,
      colimit.comp_cocone_point_unique_up_to_iso_inv_assoc, HomologicalComplex.eval_map]
    dsimp
    simp only [HomologicalComplex.Hom.comm_from, category.id_comp]
    erw [category.id_comp]
    rfl
  have e1 : exact ι₁ π₁ := by apply exact_coproduct; intro b; exact exact_kernel_ι
  have e2 : exact ι₂ π₂ := exact_kernel_ι
  have hι₂ := abelian.pseudoelement.pseudo_injective_of_mono ι₂
  replace e1 := abelian.pseudoelement.pseudo_exact_of_exact e1
  replace e2 := abelian.pseudoelement.pseudo_exact_of_exact e2
  have hEinv := abelian.pseudoelement.pseudo_surjective_of_epi E.inv
  have hQinv := abelian.pseudoelement.pseudo_injective_of_mono Q.inv
  apply abelian.pseudoelement.epi_of_pseudo_surjective
  -- Now we start the diagram chase.
  intro x
  let x' := ι₂ x
  obtain ⟨y, hy⟩ := hEinv x'
  have hy' : π₁ y = 0 := by
    apply hQinv
    simp only [abelian.pseudoelement.apply_zero, ← abelian.pseudoelement.comp_apply, sqπ]
    rw [abelian.pseudoelement.comp_apply, hy]
    dsimp only [x']; rw [e2.1]
  obtain ⟨z, hz⟩ := e1.2 _ hy'
  use z
  apply hι₂
  rw [← abelian.pseudoelement.comp_apply, ← sqι, abelian.pseudoelement.comp_apply, hz, hy]

end

instance isIso_coproductKernelComparison (M : Type _) (S : ComplexShape M) (α : Type v) [Abelian A]
    [HasCoproducts.{v} A] [AB4 A] (i : M) (X : α → HomologicalComplex A S) :
    IsIso (coproductKernelComparison M S α i X) :=
  isIso_of_mono_of_epi _

noncomputable def coproductHomologyComparison (M : Type _) (S : ComplexShape M) (α : Type v)
    [Abelian A] [HasCoproducts.{v} A] (i : M) (X : α → HomologicalComplex A S) :
    (∐ fun a : α => (X a).homology' i) ⟶ (∐ X).homology' i :=
  Sigma.desc fun b => (homology'Functor _ _ _).map <| Sigma.ι _ _

noncomputable def coproductHomologyComparisonInv (M : Type _) (S : ComplexShape M) (α : Type v)
    [Abelian A] [HasCoproducts.{v} A] [AB4 A] (i : M) (X : α → HomologicalComplex A S) :
    (∐ X).homology' i ⟶ ∐ fun a : α => (X a).homology' i :=
  homology'.desc' _ _ _
    (inv (coproductKernelComparison M S α i X) ≫
      Sigma.desc fun b =>
        homology'.π' ((X b).dTo _) ((X b).dFrom i) (HomologicalComplex.dTo_comp_dFrom _ _) ≫
          Sigma.ι _ b)
    (by
      rw [← category.assoc]; let t := _; change t ≫ _ = _
      let e : (∐ X).xPrev i ≅ ∐ fun a => (X a).xPrev i :=
        (is_colimit_of_preserves (eval_prev A S i) (colimit.is_colimit _)).coconePointUniqueUpToIso
            (colimit.is_colimit _) ≪≫
          has_colimit.iso_of_nat_iso (discrete.nat_iso fun b => iso.refl _)
      have ht : t = e.hom ≫ sigma.desc fun b => _ ≫ sigma.ι _ b
      rotate_left 2
      · refine' kernel.lift _ _ _; exact (X b).dTo i
        exact (X b).dTo_comp_dFrom i
      · dsimp [t, e, limits.is_colimit.cocone_point_unique_up_to_iso, has_colimit.iso_of_nat_iso,
          is_colimit.map, coproduct_kernel_comparison]
        rw [is_iso.comp_inv_eq]
        apply
          (is_colimit_of_preserves (eval_prev A S i)
              (colimit.is_colimit (discrete.functor X))).hom_ext
        rintro ⟨j⟩
        apply equalizer.hom_ext
        simp only [functor.map_cocone_ι_app, colimit.cocone_ι, equalizer_as_kernel, category.assoc,
          kernel.lift_ι]
        slice_rhs 1 2 =>
          erw [(is_colimit_of_preserves (eval_prev A S i)
                (colimit.is_colimit (discrete.functor X))).fac]
        dsimp [eval_prev]
        simp only [HomologicalComplex.Hom.comm_to, colimit.ι_desc, cocones.precompose_obj_ι,
          nat_trans.comp_app, discrete.nat_iso_hom_app, colimit.cocone_ι, category.assoc,
          cofan.mk_ι_app, kernel.lift_ι, kernel.lift_ι_assoc]
        dsimp; simp only [category.id_comp]
      · rw [ht]
        dsimp [e, limits.is_colimit.cocone_point_unique_up_to_iso]
        apply
          (is_colimit_of_preserves (eval_prev A S i)
              (colimit.is_colimit (discrete.functor X))).hom_ext
        intro j
        simp only [functor.map_cocone_ι_app, colimit.cocone_ι, category.assoc,
          has_colimit.iso_of_nat_iso_hom_desc, comp_zero]
        slice_lhs 1 2 =>
          erw [(is_colimit_of_preserves (eval_prev A S i)
                (colimit.is_colimit (discrete.functor X))).fac]
        simp only [colimit.cocone_ι, colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app,
          cofan.mk_ι_app, category.assoc, homology'.condition_π'_assoc, zero_comp, comp_zero])

noncomputable def coproductHomologyIso (M : Type _) (S : ComplexShape M) (α : Type v) [Abelian A]
    [HasCoproducts.{v} A] [AB4 A] (i : M) (X : α → HomologicalComplex A S) :
    (∐ fun a : α => (X a).homology' i) ≅ (∐ X).homology' i
    where
  Hom := coproductHomologyComparison _ _ _ _ _
  inv := coproductHomologyComparisonInv _ _ _ _ _
  hom_inv_id' :=
    by
    dsimp [coproduct_homology_comparison, coproduct_homology_comparison_inv]
    apply colimit.hom_ext; rintro ⟨a⟩
    dsimp
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, category.comp_id]
    apply homology'.hom_from_ext
    rw [homology'.map_eq_desc'_lift_left]
    simp only [HomologicalComplex.Hom.sqFrom_left, homology'.π'_desc'_assoc]
    let t := _; change t ≫ _ = _
    have ht : t = kernel.lift _ (kernel.ι _ ≫ _) _ ≫ homology'.π' _ _ _
    rotate_left 2
    · let e : X a ⟶ ∐ X := sigma.ι _ a; exact e.f i
    · dsimp
      rw [category.assoc, (sigma.ι X a : X a ⟶ ∐ X).comm_from, ← category.assoc, kernel.condition,
        zero_comp]
    · dsimp [t]; apply homology'.hom_to_ext
      simp only [category.assoc, homology'.lift_ι, HomologicalComplex.homology'.π'_ι,
        kernel.lift_ι_assoc]
    · rw [ht]; clear ht; clear t
      rw [category.assoc, homology'.π'_desc', ← category.assoc]
      let t := _; change t ≫ _ = _
      have ht : t = sigma.ι _ a := by
        dsimp [t]; rw [is_iso.comp_inv_eq]
        apply equalizer.hom_ext
        dsimp [coproduct_kernel_comparison]
        simp only [category.assoc, kernel.lift_ι]
        erw [colimit.ι_desc_assoc]
        dsimp
        simp only [kernel.lift_ι]
      rw [ht]; clear ht; clear t
      erw [colimit.ι_desc]
      rfl
  inv_hom_id' :=
    by
    dsimp [coproduct_homology_comparison, coproduct_homology_comparison_inv]
    apply homology'.hom_from_ext
    simp only [homology'.π'_desc'_assoc, category.assoc, category.comp_id, is_iso.inv_comp_eq]
    apply colimit.hom_ext; rintro ⟨a⟩
    dsimp
    simp only [HomologicalComplex.Hom.sqFrom_right, HomologicalComplex.Hom.sqTo_right,
      colimit.ι_desc_assoc, cofan.mk_ι_app, category.assoc, colimit.ι_desc, homology'.π'_map]
    erw [colimit.ι_desc_assoc]; rfl

noncomputable def isColimitHomologyMapCocone (M : Type _) (S : ComplexShape M) (α : Type v)
    [Abelian A] [HasCoproducts.{v} A] [AB4 A] (i : M) (X : α → HomologicalComplex A S) :
    IsColimit ((homology'Functor A S i).mapCocone (colimit.cocone (Discrete.functor X)))
    where
  desc E := (coproductHomologyIso _ _ _ _ _).inv ≫ Sigma.desc fun a => E.ι.app ⟨_⟩
  fac := by
    rintro E ⟨j⟩
    dsimp [coproduct_homology_comparison_inv, coproduct_homology_iso]
    apply homology'.hom_from_ext
    rw [homology'.map_eq_desc'_lift_left]
    simp only [HomologicalComplex.Hom.sqFrom_left, homology'.π'_desc'_assoc]
    let t := _; change t ≫ _ = _
    have ht : t = kernel.lift _ (kernel.ι _ ≫ _) _ ≫ homology'.π' _ _ _
    rotate_left 2
    · let e := sigma.ι X j; exact e.f i
    · dsimp; rw [category.assoc]
      erw [(sigma.ι X j : X j ⟶ ∐ X).comm_from]
      rw [← category.assoc, kernel.condition, zero_comp]
    · dsimp [t]
      apply homology'.hom_to_ext
      simp only [category.assoc, homology'.lift_ι, HomologicalComplex.homology'.π'_ι,
        kernel.lift_ι_assoc]
    rw [ht]; clear ht; clear t
    simp only [category.assoc, homology'.π'_desc'_assoc]
    simp only [← category.assoc]
    let t := _; change (t ≫ _) ≫ _ = _
    have ht : t = sigma.ι _ j := by
      dsimp [t]; rw [is_iso.comp_inv_eq]
      dsimp [coproduct_kernel_comparison]
      erw [colimit.ι_desc]; rfl
    rw [ht]; clear ht; clear t
    simp only [category.assoc]; erw [colimit.ι_desc_assoc]; dsimp
    rw [category.assoc, colimit.ι_desc]; rfl
  uniq := by
    intro E m hm
    rw [iso.eq_inv_comp]; dsimp [coproduct_homology_comparison, coproduct_homology_iso]
    apply colimit.hom_ext; rintro ⟨j⟩; specialize hm ⟨j⟩
    simpa only [← hm, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc,
      functor.map_cocone_ι_app, colimit.cocone_ι, homology'Functor_map]

noncomputable instance homologyFunctorPreservesCoproducts (M : Type _) (S : ComplexShape M)
    (α : Type v) [Abelian A] [HasCoproducts.{v} A] [AB4 A] (i) :
    PreservesColimitsOfShape (Discrete α) (homology'Functor A S i) :=
  by
  constructor; intro K
  let E : K ≅ discrete.functor fun n => K.obj ⟨n⟩ := discrete.nat_iso fun ⟨i⟩ => iso.refl _
  suffices preserves_colimit (discrete.functor fun n => K.obj ⟨n⟩) (homology'Functor A _ i) by
    apply preserves_colimit_of_iso_diagram _ E.symm; assumption
  apply
    preserves_colimit_of_preserves_colimit_cocone
      (colimit.is_colimit (discrete.functor fun n => K.obj ⟨n⟩))
  apply is_colimit_homology_map_cocone

noncomputable def isColimitHomotopyCategoryHomologyFunctorMapCocone {α : Type v} [Abelian A]
    [HasCoproducts.{v} A] [AB4 A] (i) (K : α → HomotopyCategory A (ComplexShape.up ℤ)) :
    IsColimit
      ((HomotopyCategory.homology'Functor A (ComplexShape.up ℤ) i).mapCocone
        (HomotopyCategory.colimitCofan K))
    where
  desc S :=
    (isColimitOfPreserves (homology'Functor A (ComplexShape.up ℤ) i)
          (colimit.isColimit <| Discrete.functor fun i => (K i).as)).desc
      ⟨S.pt, Discrete.natTrans fun i => S.ι.app i⟩
  fac := by
    rintro S ⟨j⟩; dsimp
    erw [(is_colimit_of_preserves (homology'Functor A (ComplexShape.up ℤ) i)
          (colimit.is_colimit (discrete.functor fun i : α => (K i).as))).fac]
    rfl
  uniq := by
    intro S m hm
    apply
      (is_colimit_of_preserves (homology'Functor A (ComplexShape.up ℤ) i)
          (colimit.is_colimit (discrete.functor fun i : α => (K i).as))).hom_ext
    rintro ⟨j⟩
    erw [(is_colimit_of_preserves (homology'Functor A (ComplexShape.up ℤ) i)
          (colimit.is_colimit (discrete.functor fun i : α => (K i).as))).fac]
    dsimp; rw [← hm]; rfl

noncomputable instance homotopyCategoryHomologyFunctorPreservesCoproducts (α : Type v) [Abelian A]
    [HasCoproducts.{v} A] [AB4 A] (i) :
    PreservesColimitsOfShape (Discrete α)
      (HomotopyCategory.homology'Functor A (ComplexShape.up ℤ) i) :=
  by
  constructor; intro K
  let E : K ≅ discrete.functor fun n => K.obj ⟨n⟩ := discrete.nat_iso fun ⟨i⟩ => iso.refl _
  suffices
    preserves_colimit (discrete.functor fun n => K.obj ⟨n⟩)
      (HomotopyCategory.homology'Functor A _ i)
    by apply preserves_colimit_of_iso_diagram _ E.symm; assumption
  apply
    preserves_colimit_of_preserves_colimit_cocone
      (HomotopyCategory.isColimitCofan fun n => K.obj ⟨n⟩)
  apply is_colimit_homotopy_category_homology_functor_map_cocone

end CategoryTheory

