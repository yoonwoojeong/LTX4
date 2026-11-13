import Mathlib.CategoryTheory.Sites.Limits
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.FunctorCategory
import LiquidTensorExperiment.ForMathlib.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact

#align_import for_mathlib.abelian_sheaves.main

namespace CategoryTheory

namespace Sheaf

noncomputable section

universe w v u

variable {C : Type max v u} [Category.{v} C] {J : GrothendieckTopology C}

variable {A : Type w} [Category.{max v u} A]

section HasZeroMorphisms

variable [Limits.HasZeroMorphisms A]

instance : Limits.HasZeroMorphisms (Sheaf J A)
    where
  Zero X Y := ⟨⟨0⟩⟩
  comp_zero X Y f Z := Sheaf.Hom.ext _ _ <| Limits.comp_zero
  zero_comp X Y Z f := Sheaf.Hom.ext _ _ <| Limits.zero_comp

end HasZeroMorphisms

section ParallelPair

def parallelPairIso {F G : Sheaf J A} (η γ : F ⟶ G) :
    Limits.parallelPair η γ ⋙ sheafToPresheaf J A ≅ Limits.parallelPair η.val γ.val :=
  NatIso.ofComponents
    (fun x =>
      match x with
      | limits.walking_parallel_pair.zero => eqToIso rfl
      | limits.walking_parallel_pair.one => eqToIso rfl)
    (by
      rintro (x | x) (y | y) (f | f | f)
      any_goals rfl
      any_goals ext; dsimp [parallel_pair_iso._match_1]; simp)

end ParallelPair

section Kernels

--variables [limits.has_zero_morphisms A]
-- TODO: Add some instances that derive the following from `[has_kernels A]`.
--variables [limits.has_limits_of_shape limits.walking_parallel_pair A]
variable [Limits.HasFiniteLimits A]

instance hasFiniteLimits : Limits.HasFiniteLimits (Sheaf J A) :=
  by
  apply Limits.hasFiniteLimits_of_hasFiniteLimits_of_size.{max v u}
  intro K _ _
  infer_instance

instance preservesFiniteLimits : Limits.PreservesFiniteLimits (sheafToPresheaf J A) :=
  by
  apply Limits.preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  intro K _ _
  infer_instance

variable [Limits.HasZeroMorphisms A]

def kernelIso {F G : Sheaf J A} (η : F ⟶ G) :
    (sheafToPresheaf J A).obj (Limits.kernel η) ≅ Limits.kernel ((sheafToPresheaf J A).map η) :=
  Limits.PreservesKernel.iso (sheafToPresheaf J A) η

def kernelSheaf {F G : Sheaf J A} (η : F ⟶ G) : Sheaf J A
    where
  val := Limits.kernel.{max v u} ((sheafToPresheaf J A).map η)
  cond := by
    apply presheaf.is_sheaf_of_iso J (kernel_iso η).symm
    exact Sheaf.cond _

def kernelι {F G : Sheaf J A} (η : F ⟶ G) : kernelSheaf η ⟶ F :=
  ⟨Limits.kernel.ι _⟩

def kernelFork {F G : Sheaf J A} (η : F ⟶ G) : Limits.Fork η 0 :=
  Limits.Fork.ofι (kernelι η) <| by simp only [limits.comp_zero]; ext1;
    apply limits.kernel.condition

def isLimitKernelFork {F G : Sheaf J A} (η : F ⟶ G) : Limits.IsLimit (kernelFork η) :=
  Limits.isLimitAux _
    (fun S => ⟨Limits.kernel.lift _ S.ι.val <| congr_arg Sheaf.Hom.val S.condition⟩)
    (by intro S; ext1; apply limits.kernel.lift_ι)
    (by
      intro S m hm
      ext : 2
      simp only [limits.kernel.lift_ι]
      exact congr_arg Sheaf.hom.val hm)

-- Sanity check
example : Limits.HasKernels (Sheaf J A) := by infer_instance

def kernelIsoKernelSheaf {F G : Sheaf J A} (η : F ⟶ G) : Limits.kernel η ≅ kernelSheaf η :=
  (Limits.limit.isLimit _).conePointUniqueUpToIso (isLimitKernelFork _)

@[simp, reassoc]
theorem kernelIsoKernelSheaf_hom_ι {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).Hom ≫ kernelι η = Limits.kernel.ι _ :=
  ((Limits.limit.isLimit _).uniqueUpToIso (isLimitKernelFork η)).Hom.w
    Limits.WalkingParallelPair.zero

@[simp, reassoc]
theorem kernelIsoKernelSheaf_hom_ι_val {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).Hom.val ≫ (kernelι η).val = (Limits.kernel.ι η).val :=
  by
  change ((kernel_iso_kernel_sheaf η).Hom ≫ kernel_ι η).val = (limits.kernel.ι η).val
  simp

@[simp, reassoc]
theorem kernelIsoKernelSheaf_inv_ι {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).inv ≫ Limits.kernel.ι _ = kernelι η := by
  simp only [← kernel_iso_kernel_sheaf_hom_ι, iso.inv_hom_id_assoc]

@[simp, reassoc]
theorem kernelIsoKernelSheaf_inv_ι_val {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).inv.val ≫ (Limits.kernel.ι η).val = (kernelι η).val :=
  by
  change ((kernel_iso_kernel_sheaf η).inv ≫ limits.kernel.ι η).val = (kernel_ι η).val
  simp

end Kernels

section Cokernels

--variables [limits.has_zero_morphisms A]
-- TODO: Add some instances that derive the following from `[has_cokernels A]`.
--variables [limits.has_colimits_of_shape.{_ (max v u)} limits.walking_parallel_pair A]
variable [Limits.HasFiniteColimits A]

-- We will need to sheafify....
variable [ConcreteCategory.{max v u} A]

variable [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), Limits.HasMultiequalizer (S.index P)]

variable [Limits.PreservesLimits (forget A)]

variable [∀ X : C, Limits.HasColimitsOfShape (J.cover X)ᵒᵖ A]

variable [∀ X : C, Limits.PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget A)]

variable [ReflectsIsomorphisms (forget A)]

instance hasFiniteColimits : Limits.HasFiniteColimits (Sheaf J A) :=
  by
  apply Limits.hasFiniteColimits_of_hasFiniteColimits_of_size.{max v u}
  intro K _ _
  infer_instance

variable [Limits.HasZeroMorphisms A]

def cokernelSheaf {F G : Sheaf J A} (η : F ⟶ G) : Sheaf J A
    where
  val := J.sheafify (Limits.cokernel ((sheafToPresheaf J A).map η))
  -- ;-)
  cond := GrothendieckTopology.Plus.isSheaf_plus_plus _ _

def cokernelπ {F G : Sheaf J A} (η : F ⟶ G) : G ⟶ cokernelSheaf η :=
  ⟨show (sheafToPresheaf J A).obj G ⟶ J.sheafify (Limits.cokernel ((sheafToPresheaf J A).map η))
      from
      Limits.cokernel.π ((sheafToPresheaf J A).map η) ≫
        J.toSheafify (Limits.cokernel ((sheafToPresheaf J A).map η))⟩

def cokernelCofork {F G : Sheaf J A} (η : F ⟶ G) : Limits.Cofork η 0 :=
  Limits.Cofork.ofπ (cokernelπ η)
    (by
      ext1
      rw [limits.zero_comp]
      dsimp only [cokernel_π]
      show η.val ≫ _ = 0
      erw [← category.assoc, limits.cokernel.condition, limits.zero_comp])

def isColimitCokernelCofork {F G : Sheaf J A} (η : F ⟶ G) : Limits.IsColimit (cokernelCofork η) :=
  Limits.isColimitAux _
    (fun S =>
      ⟨J.sheafifyLift
          (Limits.cokernel.desc ((sheafToPresheaf J A).map η) S.π.val <|
            congr_arg Sheaf.Hom.val S.condition)
          S.pt.2⟩)
    (by
      intro S; ext1
      change (_ ≫ _) ≫ _ = _
      rw [category.assoc, J.to_sheafify_sheafify_lift, limits.cokernel.π_desc])
    (by
      intro S m hm; ext1
      apply J.sheafify_lift_unique
      rw [Sheaf.hom.ext_iff] at hm 
      change (_ ≫ _) ≫ _ = _ at hm 
      rw [category.assoc] at hm 
      ext1
      rw [hm, limits.cokernel.π_desc])

-- Sanity check
example : Limits.HasCokernels (Sheaf J A) := by infer_instance

def cokernelIsoCokernelSheaf {F G : Sheaf J A} (η : F ⟶ G) : Limits.cokernel η ≅ cokernelSheaf η :=
  (Limits.colimit.isColimit _).coconePointUniqueUpToIso (isColimitCokernelCofork _)

@[simp]
theorem cokernelIsoCokernelSheaf_hom_π {F G : Sheaf J A} (η : F ⟶ G) :
    Limits.cokernel.π η ≫ (cokernelIsoCokernelSheaf η).Hom = cokernelπ _ :=
  ((Limits.colimit.isColimit _).uniqueUpToIso (isColimitCokernelCofork η)).Hom.w
    Limits.WalkingParallelPair.one

@[simp]
theorem cokernelIsoCokernelSheaf_inv_π {F G : Sheaf J A} (η : F ⟶ G) :
    cokernelπ η ≫ (cokernelIsoCokernelSheaf η).inv = Limits.cokernel.π η := by
  simp only [← cokernel_iso_cokernel_sheaf_hom_π, category.assoc, iso.hom_inv_id, category.comp_id]

end Cokernels

section KernelsAndCokernels

-- TODO: use has kernels and cokernels, when possible... see above
--variables [limits.has_colimits_of_shape.{_ (max v u)} limits.walking_parallel_pair A]
--variables [limits.has_limits_of_shape.{_ (max v u)} limits.walking_parallel_pair A]
variable [Limits.HasZeroMorphisms A] [Limits.HasFiniteLimits A] [Limits.HasFiniteColimits A]

-- We will need to sheafify....
variable [ConcreteCategory.{max v u} A]

variable [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), Limits.HasMultiequalizer (S.index P)]

variable [Limits.PreservesLimits (forget A)]

variable [∀ X : C, Limits.HasColimitsOfShape (J.cover X)ᵒᵖ A]

variable [∀ X : C, Limits.PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget A)]

variable [ReflectsIsomorphisms (forget A)]

def coimToIm'Aux {F G : Sheaf J A} (η : F ⟶ G) :
    Abelian.coimage ((sheafToPresheaf J A).map η) ⟶
      (sheafToPresheaf J A).obj (kernelSheaf (cokernelπ η)) :=
  Abelian.coimageImageComparison _ ≫
    Limits.kernel.lift _ (Limits.kernel.ι _)
      (by
        dsimp [cokernel_π]
        rw [← category.assoc, limits.kernel.condition]
        simp only [limits.zero_comp])

def coimToIm' {F G : Sheaf J A} (η : F ⟶ G) :
    cokernelSheaf (kernelι η) ⟶ kernelSheaf (cokernelπ η) :=
  ⟨J.sheafifyLift (coimToIm'Aux η) (kernelSheaf _).2⟩

def kernelSheafCokernelπIso {F G : Sheaf J A} (η : F ⟶ G) :
    kernelSheaf (Limits.cokernel.π η) ≅ kernelSheaf (cokernelπ η)
    where
  Hom :=
    ⟨Limits.kernel.map _ _ (𝟙 _) ((sheafToPresheaf J A).map (cokernelIsoCokernelSheaf η).Hom)
        (by
          rw [← functor.map_comp]
          dsimp [cokernel_iso_cokernel_sheaf, limits.is_colimit.cocone_point_unique_up_to_iso,
            cokernel_cofork]
          show Sheaf.hom.val (limits.cokernel.π η ≫ _) = _
          simp only [limits.coequalizer.π_desc, category.id_comp])⟩
  inv :=
    ⟨Limits.kernel.map _ _ (𝟙 _) ((sheafToPresheaf J A).map (cokernelIsoCokernelSheaf η).inv)
        (by
          rw [← functor.map_comp]
          dsimp [cokernel_iso_cokernel_sheaf, limits.is_colimit.cocone_point_unique_up_to_iso,
            cokernel_π, is_colimit_cokernel_cofork, limits.is_colimit_aux]
          erw [category.id_comp, category.assoc, J.to_sheafify_sheafify_lift,
            limits.cokernel.π_desc])⟩
  hom_inv_id' := by
    ext : 2
    delta limits.kernel.map
    dsimp
    erw [category.assoc, limits.kernel.lift_ι, ← category.assoc, limits.kernel.lift_ι,
      category.comp_id, category.comp_id, category.id_comp]
  inv_hom_id' := by
    ext : 2
    delta limits.kernel.map
    dsimp
    erw [category.assoc, limits.kernel.lift_ι, ← category.assoc, limits.kernel.lift_ι,
      category.comp_id, category.comp_id, category.id_comp]

def cokernelSheafKernelιIso {F G : Sheaf J A} (η : F ⟶ G) :
    cokernelSheaf (Limits.kernel.ι η) ≅ cokernelSheaf (kernelι η)
    where
  Hom :=
    ⟨J.sheafifyLift
        (Limits.cokernel.map _ _ ((sheafToPresheaf J A).map (kernelIsoKernelSheaf η).Hom) (𝟙 _)
            (by rw [category.comp_id, ← functor.map_comp, kernel_iso_kernel_sheaf_hom_ι]) ≫
          J.toSheafify _)
        (cokernelSheaf _).2⟩
  inv :=
    ⟨J.sheafifyLift
        (Limits.cokernel.map _ _ ((sheafToPresheaf J A).map (kernelIsoKernelSheaf η).inv) (𝟙 _)
            (by rw [category.comp_id, ← functor.map_comp, kernel_iso_kernel_sheaf_inv_ι]) ≫
          J.toSheafify _)
        (cokernelSheaf _).2⟩
  hom_inv_id' := by
    ext1
    apply J.sheafify_hom_ext _ _ (cokernel_sheaf _).2
    erw [← category.assoc, J.to_sheafify_sheafify_lift, category.assoc, J.to_sheafify_sheafify_lift,
      ← category.assoc]
    conv_rhs => erw [category.comp_id]
    convert category.id_comp _
    ext1
    delta limits.cokernel.map
    erw [← category.assoc, limits.coequalizer.π_desc, category.id_comp, limits.coequalizer.π_desc,
      category.id_comp, category.comp_id]
  inv_hom_id' := by
    ext1
    apply J.sheafify_hom_ext _ _ (cokernel_sheaf _).2
    erw [← category.assoc, J.to_sheafify_sheafify_lift, category.assoc, J.to_sheafify_sheafify_lift,
      ← category.assoc]
    conv_rhs => erw [category.comp_id]
    convert category.id_comp _
    ext1
    delta limits.cokernel.map
    erw [← category.assoc, limits.coequalizer.π_desc, category.id_comp, limits.coequalizer.π_desc,
      category.id_comp, category.comp_id]

theorem eq_coimToIm' {F G : Sheaf J A} (η : F ⟶ G) :
    (cokernelSheafKernelιIso η).inv ≫
        (cokernelIsoCokernelSheaf _).inv ≫
          Abelian.coimageImageComparison η ≫
            (kernelIsoKernelSheaf _).Hom ≫ (kernelSheafCokernelπIso η).Hom =
      coimToIm' η :=
  by
  dsimp [abelian.coimage_image_comparison, cokernel_sheaf_kernel_ι_iso, coim_to_im',
    coim_to_im'_aux, kernel_sheaf_cokernel_π_iso, limits.is_colimit.cocone_point_unique_up_to_iso,
    limits.is_limit.cone_point_unique_up_to_iso]
  delta limits.kernel.map limits.cokernel.map
  ext1
  apply J.sheafify_lift_unique
  ext : 2
  conv_rhs =>
    erw [← category.assoc, limits.cokernel.π_desc, category.assoc, limits.kernel.lift_ι,
      limits.kernel.lift_ι]
  dsimp
  simp only [category.assoc, category.comp_id, category.id_comp, J.to_sheafify_sheafify_lift_assoc,
    kernel_iso_kernel_sheaf_hom_ι_val, limits.kernel.lift_ι, limits.cokernel.π_desc_assoc]
  dsimp [cokernel_iso_cokernel_sheaf, limits.is_colimit.cocone_point_unique_up_to_iso,
    is_colimit_cokernel_cofork, limits.is_colimit_aux]
  rw [J.to_sheafify_sheafify_lift_assoc]
  simp only [limits.cokernel.π_desc_assoc, ← category.assoc, ← Sheaf.hom.comp_val,
    limits.cokernel.π_desc]
  simp only [category_theory.category_comp_val, category.assoc]
  erw [kernel_iso_kernel_sheaf_hom_ι_val]
  rw [← Sheaf.hom.comp_val, limits.kernel.lift_ι]

theorem coim_to_im_eq {F G : Sheaf J A} (η : F ⟶ G) :
    Abelian.coimageImageComparison η =
      (cokernelIsoCokernelSheaf _).Hom ≫
        (cokernelSheafKernelιIso η).Hom ≫
          coimToIm' η ≫ (kernelSheafCokernelπIso η).inv ≫ (kernelIsoKernelSheaf _).inv :=
  by
  rw [← eq_coim_to_im']
  simp only [category.assoc, iso.hom_inv_id, iso.inv_hom_id, iso.hom_inv_id_assoc,
    iso.inv_hom_id_assoc, category.comp_id]

end KernelsAndCokernels

section Preadditive

variable [Preadditive A]

/-
instance : preadditive (Sheaf J A) :=
{ hom_group := λ P Q,
  { add := λ f g, ⟨f.val + g.val⟩,
    add_assoc := by { intros, ext1, apply add_assoc },
    zero := ⟨0⟩,
    zero_add := by { intros, ext1, apply zero_add },
    add_zero := by { intros, ext1, apply add_zero },
    nsmul := λ n f, ⟨n • f.val⟩,
    nsmul_zero' := by { intros, ext1, simpa },
    nsmul_succ' := by { intros, ext1, simpa },
    neg := λ f, ⟨-f.val⟩,
    sub := λ f g, ⟨f.val - g.val⟩,
    sub_eq_add_neg := by { intros, ext1, apply sub_eq_add_neg },
    zsmul := λ n f, ⟨n • f.val⟩,
    zsmul_zero' := by { intros, ext1, simpa },
    zsmul_succ' := by { intros, ext1, simpa },
    zsmul_neg' := by { intros, ext1, simpa },
    add_left_neg := by { intros, ext1, apply add_left_neg },
    add_comm := by { intros, ext1, apply add_comm } },
  add_comp' := λ P Q R f g h, by { ext1, apply preadditive.add_comp },
  comp_add' := λ P Q R f g h, by { ext1, apply preadditive.comp_add } }
-/
end Preadditive

section Additive

variable [AdditiveCategory A]

--[limits.has_finite_limits A]
instance : AdditiveCategory (Sheaf J A) :=
  { (by infer_instance : Preadditive (Sheaf J A)) with
    HasBiproductsOfShape := by
      intro K _
      constructor
      intro F
      apply limits.has_biproduct.of_has_product F }

end Additive

section Abelian

variable [Abelian A]

-- We need sheafification
variable [ConcreteCategory.{max v u} A]

variable [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.cover X), Limits.HasMultiequalizer (S.index P)]

variable [Limits.PreservesLimits (forget A)]

--variables [limits.has_finite_limits A]
variable [∀ X : C, Limits.HasColimitsOfShape (J.cover X)ᵒᵖ A]

variable [∀ X : C, Limits.PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget A)]

variable [ReflectsIsomorphisms (forget A)]

open GrothendieckTopology

def parallelPairSheafification {F G : Sheaf J A} (η : F ⟶ G) :
    Limits.parallelPair (Limits.cokernel.π η.val) 0 ⋙ J.sheafification A ≅
      Limits.parallelPair (cokernelπ η).val 0 :=
  NatIso.ofComponents
    (fun x =>
      match x with
      | limits.walking_parallel_pair.zero => by dsimp; refine' (J.iso_sheafify G.2).symm
      | limits.walking_parallel_pair.one => by dsimp; exact eq_to_iso rfl)
    (by
      -- This proof is SLOW :-(
      rintro (a | a) (b | b) (f | f | f)
      · dsimp [parallel_pair_sheafification._match_1]
        simp only [iso.eq_inv_comp, Functor.map_id]
        dsimp [grothendieck_topology.iso_sheafify]
        rw [← category.assoc, is_iso.comp_inv_eq, category.id_comp]
        change J.to_sheafify _ ≫ (sheafification J A).map _ = _
        erw [Functor.map_id, category.comp_id]
      · dsimp [parallel_pair_sheafification._match_1]
        rw [category.comp_id, iso.eq_inv_comp]
        dsimp [grothendieck_topology.iso_sheafify, cokernel_π]
        change (to_sheafification J A).app _ ≫ (sheafification J A).map _ = _
        rw [← (to_sheafification J A).naturality]
        rfl
      · dsimp [parallel_pair_sheafification._match_1]
        simp only [limits.comp_zero, category.comp_id]
        change (sheafification J A).map _ = _
        apply J.sheafify_hom_ext
        · exact plus.is_sheaf_plus_plus J (limits.cokernel η.val)
        erw [← (to_sheafification J A).naturality]
        simp
      · dsimp [parallel_pair_sheafification._match_1]
        simp only [limits.comp_zero, category.id_comp, category.comp_id]
        change (sheafification J A).map _ = _
        simp only [Functor.map_id]
        erw [(sheafification J A).map_id]; rfl)

def kernelCokernelπIso {F G : Sheaf J A} (η : F ⟶ G) :
    J.sheafify (Limits.kernel (Limits.cokernel.π ((sheafToPresheaf J A).map η))) ≅
      Limits.kernel ((sheafToPresheaf J A).map (cokernelπ η)) :=
  by
  let e :=
    (limits.is_limit_of_preserves (sheafification J A)
          (limits.limit.is_limit
            (limits.parallel_pair (limits.cokernel.π ((Sheaf_to_presheaf J A).map η))
              0))).conePointUniqueUpToIso
      (limits.limit.is_limit _)
  refine' e ≪≫ _
  change limits.limit _ ≅ _
  refine' limits.has_limit.iso_of_nat_iso _
  apply parallel_pair_sheafification

/-
{ hom := J.sheafify_lift (limits.kernel.map _ _ (𝟙 _) (J.to_sheafify _) (by admit)) (by admit),
  inv := begin
    let e : J.sheafify ((Sheaf_to_presheaf J A).obj G) ⟶
      J.sheafify (limits.cokernel ((Sheaf_to_presheaf J A).map η)) :=
        (sheafification J A).map (limits.cokernel.π _),
    let ee : limits.kernel ((Sheaf_to_presheaf J A).map (cokernel_π η)) ⟶ limits.kernel e,
    { refine limits.kernel.map _ _ (J.to_sheafify _) (𝟙 _) _,
      rw category.comp_id,
      dsimp only [e],
      rw ← grothendieck_topology.to_sheafification_app,
      rw ← (to_sheafification J A).naturality,
      refl },
    refine ee ≫ _,
    dsimp only [e],
    change limits.kernel ((Sheaf_to_presheaf J A).map ((presheaf_to_Sheaf J A).map _)) ⟶ _,
    refine (Sheaf_to_presheaf J A).map (kernel_iso_kernel_sheaf _).inv ≫ _,
    change _ ⟶ (Sheaf_to_presheaf J A).obj ((presheaf_to_Sheaf J A).obj _),
    refine (Sheaf_to_presheaf J A).map _,
    haveI : is_left_adjoint (presheaf_to_Sheaf J A) := by admit,
    -- Now we need to use the fact that finite limits commute with sheafification,
    -- i.e. that sheafification is left exact.
    admit
  end,
  hom_inv_id' := by admit,
  inv_hom_id' := by admit }
-/
theorem coimToIm'_eq {F G : Sheaf J A} (η : F ⟶ G) :
    (sheafToPresheaf J A).map (coimToIm' η) =
      (sheafification J A).map (Abelian.coimageImageComparison _) ≫ (kernelCokernelπIso η).Hom :=
  by
  dsimp only [kernel_cokernel_π_iso, limits.is_limit.cone_point_unique_up_to_iso, functor.map_iso,
    iso.trans_hom]
  simp only [category.assoc]
  dsimp only [id, limits.is_limit.unique_up_to_iso, limits.cones.forget,
    limits.is_limit.lift_cone_morphism, functor.map_cone]
  apply limits.equalizer.hom_ext
  simp only [category.assoc]
  --delta limits.equalizer.ι,
  erw [limits.has_limit.iso_of_nat_iso_hom_π]
  dsimp only [parallel_pair_sheafification, nat_iso.of_components, id, iso_sheafify, as_iso,
    iso.symm]
  simp only [← category.assoc]
  rw [is_iso.eq_comp_inv]
  simp only [category.assoc]
  erw [limits.limit.lift_π]
  dsimp [limits.cones.functoriality, sheafify_map]
  simp_rw [← plus_functor_map, ← functor.comp_map, ← functor.map_comp]
  dsimp [coim_to_im', abelian.coimage_image_comparison, coim_to_im'_aux]
  apply J.sheafify_hom_ext
  · exact plus.is_sheaf_plus_plus J G.val
  simp_rw [← category.assoc]
  erw [J.to_sheafify_sheafify_lift]
  change _ = (to_sheafification J A).app _ ≫ (sheafification J A).map _
  erw [← (to_sheafification J A).naturality]
  simp only [category.assoc, limits.kernel.lift_ι]
  dsimp
  erw [category.assoc]

instance isIso_coim_to_im {F G : Sheaf J A} (η : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison η) :=
  by
  rw [coim_to_im_eq]
  suffices is_iso (coim_to_im' η) by skip; apply is_iso.comp_is_iso
  suffices is_iso ((Sheaf_to_presheaf J A).map (coim_to_im' η)) by skip;
    apply is_iso_of_fully_faithful (Sheaf_to_presheaf J A)
  rw [coim_to_im'_eq]
  apply is_iso.comp_is_iso

instance abelian : Abelian (Sheaf J A) :=
  Abelian.ofCoimageImageComparisonIsIso

end Abelian

end Sheaf

end CategoryTheory

