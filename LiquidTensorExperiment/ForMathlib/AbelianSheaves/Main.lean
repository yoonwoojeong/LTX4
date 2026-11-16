import Mathlib.CategoryTheory.Sites.Limits
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.FunctorCategory
import LiquidTensorExperiment.ForMathlib.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact

#align_import for_mathlib.abelian_sheaves.main

-- Porting note: `noncomputable theory` moved before the first namespace so that the
-- `end`s match
noncomputable section

namespace CategoryTheory

namespace Sheaf

universe w v u

variable {C : Type max v u} [Category.{v} C] {J : GrothendieckTopology C}

variable {A : Type w} [Category.{max v u} A]

-- Porting note: as in Lean 3, the zero morphisms variable is not local to a section, so the
-- later (duplicate) `variable` in the kernels section is in scope together with it.
variable [Limits.HasZeroMorphisms A]

-- Porting note: universe levels given explicitly; Lean 4 cannot solve the universe constraints
-- of `Category (Sheaf J A)` (`max u v` for morphisms, `max w u v` for objects) otherwise.
instance : Limits.HasZeroMorphisms.{max v u, max w v u} (Sheaf J A)
    where
  zero X Y := ⟨⟨0⟩⟩
  comp_zero := by intros; exact Sheaf.Hom.ext _ _ Limits.comp_zero
  zero_comp := by intros; exact Sheaf.Hom.ext _ _ Limits.zero_comp


section ParallelPair

-- Porting note: the functor types are stated explicitly; otherwise Lean 4 leaves universe
-- constraints that cannot be solved (and reports them at later declarations).
def parallelPairIso {F G : Sheaf J A} (η γ : F ⟶ G) :
    (Limits.parallelPair η γ : Limits.WalkingParallelPair ⥤ Sheaf J A) ⋙ sheafToPresheaf J A ≅
      (Limits.parallelPair η.val γ.val : Limits.WalkingParallelPair ⥤ Cᵒᵖ ⥤ A) :=
  NatIso.ofComponents
    (fun x => by
      cases x
      · exact eqToIso rfl
      · exact eqToIso rfl)
    (by
      rintro (x | x) (y | y) (f | f | f)
      any_goals rfl
      any_goals ext; dsimp; simp)

end ParallelPair

section Kernels

--variables [limits.has_zero_morphisms A]
-- TODO: Add some instances that derive the following from `[has_kernels A]`.
--variables [limits.has_limits_of_shape limits.WalkingParallelPair A]
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
    apply Presheaf.isSheaf_of_iso J (kernelIso η).symm
    exact Sheaf.cond _

def kernelι {F G : Sheaf J A} (η : F ⟶ G) : kernelSheaf η ⟶ F :=
  ⟨Limits.kernel.ι _⟩

def kernelFork {F G : Sheaf J A} (η : F ⟶ G) : Limits.Fork η 0 :=
  Limits.Fork.ofι (kernelι η) <| by simp only [Limits.comp_zero]; ext1;
    apply Limits.kernel.condition

def isLimitKernelFork {F G : Sheaf J A} (η : F ⟶ G) : Limits.IsLimit (kernelFork η) :=
  Limits.isLimitAux _
    (fun S => ⟨Limits.kernel.lift _ S.ι.val <| congr_arg Sheaf.Hom.val S.condition⟩)
    (by intro S; ext1; apply Limits.kernel.lift_ι)
    (by
      intro S m hm
      ext : 2
      simp only [Limits.kernel.lift_ι]
      exact congr_arg Sheaf.Hom.val hm)

-- Sanity check
example : Limits.HasKernels (Sheaf J A) := by infer_instance

def kernelIsoKernelSheaf {F G : Sheaf J A} (η : F ⟶ G) : Limits.kernel η ≅ kernelSheaf η :=
  (Limits.limit.isLimit _).conePointUniqueUpToIso (isLimitKernelFork _)

@[reassoc (attr := simp)]
theorem kernelIsoKernelSheaf_hom_ι {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).hom ≫ kernelι η = Limits.kernel.ι _ :=
  ((Limits.limit.isLimit _).uniqueUpToIso (isLimitKernelFork η)).hom.w
    Limits.WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem kernelIsoKernelSheaf_hom_ι_val {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).hom.val ≫ (kernelι η).val = (Limits.kernel.ι η).val :=
  by
  change ((CategoryTheory.Sheaf.kernelIsoKernelSheaf η).hom ≫ kernelι η).val = (Limits.kernel.ι η).val
  simp

@[reassoc (attr := simp)]
theorem kernelIsoKernelSheaf_inv_ι {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).inv ≫ Limits.kernel.ι _ = kernelι η := by
  simp only [← kernelIsoKernelSheaf_hom_ι, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem kernelIsoKernelSheaf_inv_ι_val {F G : Sheaf J A} (η : F ⟶ G) :
    (kernelIsoKernelSheaf η).inv.val ≫ (Limits.kernel.ι η).val = (kernelι η).val :=
  by
  change ((CategoryTheory.Sheaf.kernelIsoKernelSheaf η).inv ≫ Limits.kernel.ι η).val = (kernelι η).val
  simp

end Kernels

section Cokernels

--variables [limits.has_zero_morphisms A]
-- TODO: Add some instances that derive the following from `[has_cokernels A]`.
--variables [limits.has_colimits_of_shape.{_ (max v u)} limits.WalkingParallelPair A]
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
      rw [Limits.zero_comp]
      dsimp only [cokernelπ]
      show η.val ≫ _ = 0
      erw [← Category.assoc, Limits.cokernel.condition, Limits.zero_comp])

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
      rw [Category.assoc, J.toSheafify_sheafifyLift, Limits.cokernel.π_desc])
    (by
      intro S m hm; ext1
      apply J.sheafifyLift_unique
      rw [Sheaf.Hom.ext_iff] at hm 
      change (_ ≫ _) ≫ _ = _ at hm 
      rw [Category.assoc] at hm 
      ext1
      rw [hm, Limits.cokernel.π_desc])

-- Sanity check
example : Limits.HasCokernels (Sheaf J A) := by infer_instance

def cokernelIsoCokernelSheaf {F G : Sheaf J A} (η : F ⟶ G) : Limits.cokernel η ≅ cokernelSheaf η :=
  (Limits.colimit.isColimit _).coconePointUniqueUpToIso (isColimitCokernelCofork _)

@[simp]
theorem cokernelIsoCokernelSheaf_hom_π {F G : Sheaf J A} (η : F ⟶ G) :
    Limits.cokernel.π η ≫ (cokernelIsoCokernelSheaf η).hom = cokernelπ _ :=
  ((Limits.colimit.isColimit _).uniqueUpToIso (isColimitCokernelCofork η)).hom.w
    Limits.WalkingParallelPair.one

@[simp]
theorem cokernelIsoCokernelSheaf_inv_π {F G : Sheaf J A} (η : F ⟶ G) :
    cokernelπ η ≫ (cokernelIsoCokernelSheaf η).inv = Limits.cokernel.π η := by
  simp only [← cokernelIsoCokernelSheaf_hom_π, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Cokernels

section KernelsAndCokernels

-- TODO: use has kernels and cokernels, when possible... see above
--variables [limits.has_colimits_of_shape.{_ (max v u)} limits.WalkingParallelPair A]
--variables [limits.has_limits_of_shape.{_ (max v u)} limits.WalkingParallelPair A]
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
        dsimp [cokernelπ]
        rw [← Category.assoc, Limits.kernel.condition]
        simp only [Limits.zero_comp])

def coimToIm' {F G : Sheaf J A} (η : F ⟶ G) :
    cokernelSheaf (kernelι η) ⟶ kernelSheaf (cokernelπ η) :=
  ⟨J.sheafifyLift (coimToIm'Aux η) (kernelSheaf _).2⟩

def kernelSheafCokernelπIso {F G : Sheaf J A} (η : F ⟶ G) :
    kernelSheaf (Limits.cokernel.π η) ≅ kernelSheaf (cokernelπ η)
    where
  hom :=
    ⟨Limits.kernel.map _ _ (𝟙 _) ((sheafToPresheaf J A).map (cokernelIsoCokernelSheaf η).hom)
        (by
          rw [← Functor.map_comp]
          dsimp [cokernelIsoCokernelSheaf, Limits.IsColimit.coconePointUniqueUpToIso,
            cokernel_cofork]
          show Sheaf.Hom.val (Limits.cokernel.π η ≫ _) = _
          simp only [Limits.coequalizer.π_desc, Category.id_comp])⟩
  inv :=
    ⟨Limits.kernel.map _ _ (𝟙 _) ((sheafToPresheaf J A).map (cokernelIsoCokernelSheaf η).inv)
        (by
          rw [← Functor.map_comp]
          dsimp [cokernelIsoCokernelSheaf, Limits.IsColimit.coconePointUniqueUpToIso,
            cokernelπ, isColimitCokernelCofork, Limits.isColimitAux]
          erw [Category.id_comp, Category.assoc, J.toSheafify_sheafifyLift,
            Limits.cokernel.π_desc])⟩
  hom_inv_id := by
    ext : 2
    delta Limits.kernel.map
    dsimp
    erw [Category.assoc, Limits.kernel.lift_ι, ← Category.assoc, Limits.kernel.lift_ι,
      Category.comp_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    ext : 2
    delta Limits.kernel.map
    dsimp
    erw [Category.assoc, Limits.kernel.lift_ι, ← Category.assoc, Limits.kernel.lift_ι,
      Category.comp_id, Category.comp_id, Category.id_comp]

def cokernelSheafKernelιIso {F G : Sheaf J A} (η : F ⟶ G) :
    cokernelSheaf (Limits.kernel.ι η) ≅ cokernelSheaf (kernelι η)
    where
  hom :=
    ⟨J.sheafifyLift
        (Limits.cokernel.map _ _ ((sheafToPresheaf J A).map (kernelIsoKernelSheaf η).hom) (𝟙 _)
            (by rw [Category.comp_id, ← Functor.map_comp, kernelIsoKernelSheaf_hom_ι]) ≫
          J.toSheafify _)
        (cokernelSheaf _).2⟩
  inv :=
    ⟨J.sheafifyLift
        (Limits.cokernel.map _ _ ((sheafToPresheaf J A).map (kernelIsoKernelSheaf η).inv) (𝟙 _)
            (by rw [Category.comp_id, ← Functor.map_comp, kernelIsoKernelSheaf_inv_ι]) ≫
          J.toSheafify _)
        (cokernelSheaf _).2⟩
  hom_inv_id := by
    ext1
    apply J.sheafify_hom_ext _ _ (CategoryTheory.Sheaf.cokernelSheaf _).2
    erw [← Category.assoc, J.toSheafify_sheafifyLift, Category.assoc, J.toSheafify_sheafifyLift,
      ← Category.assoc]
    conv_rhs => erw [Category.comp_id]
    convert Category.id_comp _
    ext1
    delta Limits.cokernel.map
    erw [← Category.assoc, Limits.coequalizer.π_desc, Category.id_comp, Limits.coequalizer.π_desc,
      Category.id_comp, Category.comp_id]
  inv_hom_id := by
    ext1
    apply J.sheafify_hom_ext _ _ (CategoryTheory.Sheaf.cokernelSheaf _).2
    erw [← Category.assoc, J.toSheafify_sheafifyLift, Category.assoc, J.toSheafify_sheafifyLift,
      ← Category.assoc]
    conv_rhs => erw [Category.comp_id]
    convert Category.id_comp _
    ext1
    delta Limits.cokernel.map
    erw [← Category.assoc, Limits.coequalizer.π_desc, Category.id_comp, Limits.coequalizer.π_desc,
      Category.id_comp, Category.comp_id]

theorem eq_coimToIm' {F G : Sheaf J A} (η : F ⟶ G) :
    (cokernelSheafKernelιIso η).inv ≫
        (cokernelIsoCokernelSheaf _).inv ≫
          Abelian.coimageImageComparison η ≫
            (kernelIsoKernelSheaf _).hom ≫ (kernelSheafCokernelπIso η).hom =
      coimToIm' η :=
  by
  dsimp [Abelian.coimageImageComparison, cokernelSheafKernelιIso, CategoryTheory.Sheaf.coimToIm',
    CategoryTheory.Sheaf.coimToIm'Aux, kernelSheafCokernelπIso, Limits.IsColimit.coconePointUniqueUpToIso,
    Limits.IsLimit.conePointUniqueUpToIso]
  delta Limits.kernel.map Limits.cokernel.map
  ext1
  apply J.sheafifyLift_unique
  ext : 2
  conv_rhs =>
    erw [← Category.assoc, Limits.cokernel.π_desc, Category.assoc, Limits.kernel.lift_ι,
      Limits.kernel.lift_ι]
  dsimp
  simp only [Category.assoc, Category.comp_id, Category.id_comp, J.toSheafify_sheafifyLift_assoc,
    kernelIsoKernelSheaf_hom_ι_val, Limits.kernel.lift_ι, Limits.cokernel.π_desc_assoc]
  dsimp [cokernelIsoCokernelSheaf, Limits.IsColimit.coconePointUniqueUpToIso,
    isColimitCokernelCofork, Limits.isColimitAux]
  rw [J.toSheafify_sheafifyLift_assoc]
  simp only [Limits.cokernel.π_desc_assoc, ← Category.assoc, ← Sheaf.Hom.comp_val,
    Limits.cokernel.π_desc]
  simp only [category_theory.category_comp_val, Category.assoc]
  erw [kernelIsoKernelSheaf_hom_ι_val]
  rw [← Sheaf.Hom.comp_val, Limits.kernel.lift_ι]

theorem coimToIm_eq {F G : Sheaf J A} (η : F ⟶ G) :
    Abelian.coimageImageComparison η =
      (cokernelIsoCokernelSheaf _).hom ≫
        (cokernelSheafKernelιIso η).hom ≫
          coimToIm' η ≫ (kernelSheafCokernelπIso η).inv ≫ (kernelIsoKernelSheaf _).inv :=
  by
  rw [← CategoryTheory.Sheaf.eq_coimToIm']
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, Category.comp_id]

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
      apply Limits.HasBiproduct.of_hasProduct F }

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
      | Limits.WalkingParallelPair.zero => by dsimp; refine' (J.iso_sheafify G.2).symm
      | Limits.WalkingParallelPair.one => by dsimp; exact eq_to_iso rfl)
    (by
      -- This proof is SLOW :-(
      rintro (a | a) (b | b) (f | f | f)
      · dsimp [parallelPairSheafification._match_1]
        simp only [Iso.eq_inv_comp, Functor.map_id]
        dsimp [GrothendieckTopology.isoSheafify]
        rw [← Category.assoc, IsIso.comp_inv_eq, Category.id_comp]
        change J.toSheafify _ ≫ (sheafification J A).map _ = _
        erw [Functor.map_id, Category.comp_id]
      · dsimp [parallelPairSheafification._match_1]
        rw [Category.comp_id, Iso.eq_inv_comp]
        dsimp [GrothendieckTopology.isoSheafify, cokernelπ]
        change (CategoryTheory.GrothendieckTopology.toSheafification J A).app _ ≫ (sheafification J A).map _ = _
        rw [← (CategoryTheory.GrothendieckTopology.toSheafification J A).naturality]
        rfl
      · dsimp [parallelPairSheafification._match_1]
        simp only [Limits.comp_zero, Category.comp_id]
        change (sheafification J A).map _ = _
        apply J.sheafify_hom_ext
        · exact Plus.isSheaf_plus_plus J (Limits.cokernel η.val)
        erw [← (CategoryTheory.GrothendieckTopology.toSheafification J A).naturality]
        simp
      · dsimp [parallelPairSheafification._match_1]
        simp only [Limits.comp_zero, Category.id_comp, Category.comp_id]
        change (sheafification J A).map _ = _
        simp only [Functor.map_id]
        erw [(sheafification J A).map_id]; rfl)

def kernelCokernelπIso {F G : Sheaf J A} (η : F ⟶ G) :
    J.sheafify (Limits.kernel (Limits.cokernel.π ((sheafToPresheaf J A).map η))) ≅
      Limits.kernel ((sheafToPresheaf J A).map (cokernelπ η)) :=
  by
  let e :=
    (Limits.isLimitOfPreserves (sheafification J A)
          (Limits.limit.isLimit
            (Limits.parallelPair (Limits.cokernel.π ((Sheaf_to_presheaf J A).map η))
              0))).conePointUniqueUpToIso
      (Limits.limit.isLimit _)
  refine' e ≪≫ _
  change Limits.limit _ ≅ _
  refine' Limits.HasLimit.isoOfNatIso _
  apply CategoryTheory.Sheaf.parallelPairSheafification

/-
{ hom := J.sheafify_lift (limits.kernel.map _ _ (𝟙 _) (J.toSheafify _) (by admit)) (by admit),
  inv := begin
    let e : J.sheafify ((Sheaf_to_presheaf J A).obj G) ⟶
      J.sheafify (limits.cokernel ((Sheaf_to_presheaf J A).map η)) :=
        (sheafification J A).map (limits.cokernel.π _),
    let ee : limits.kernel ((Sheaf_to_presheaf J A).map (cokernelπ η)) ⟶ limits.kernel e,
    { refine limits.kernel.map _ _ (J.toSheafify _) (𝟙 _) _,
      rw category.comp_id,
      dsimp only [e],
      rw ← grothendieck_topology.toSheafification_app,
      rw ← (toSheafification J A).naturality,
      refl },
    refine ee ≫ _,
    dsimp only [e],
    change limits.kernel ((Sheaf_to_presheaf J A).map ((presheaf_to_Sheaf J A).map _)) ⟶ _,
    refine (Sheaf_to_presheaf J A).map (kernelIsoKernelSheaf _).inv ≫ _,
    change _ ⟶ (Sheaf_to_presheaf J A).obj ((presheaf_to_Sheaf J A).obj _),
    refine (Sheaf_to_presheaf J A).map _,
    haveI : IsLeftAdjoint (presheaf_to_Sheaf J A) := by admit,
    -- Now we need to use the fact that finite limits commute with sheafification,
    -- i.e. that sheafification is left exact.
    admit
  end,
  hom_inv_id' := by admit,
  inv_hom_id' := by admit }
-/
theorem coimToIm'_eq {F G : Sheaf J A} (η : F ⟶ G) :
    (sheafToPresheaf J A).map (coimToIm' η) =
      (sheafification J A).map (Abelian.coimageImageComparison _) ≫ (kernelCokernelπIso η).hom :=
  by
  dsimp only [kernelCokernelπIso, Limits.IsLimit.conePointUniqueUpToIso, Functor.mapIso,
    Iso.trans_hom]
  simp only [Category.assoc]
  dsimp only [id, Limits.IsLimit.uniqueUpToIso, Limits.Cones.forget,
    Limits.IsLimit.liftConeMorphism, Functor.mapCone]
  apply Limits.equalizer.hom_ext
  simp only [Category.assoc]
  --delta limits.equalizer.ι,
  erw [Limits.HasLimit.isoOfNatIso_hom_π]
  dsimp only [CategoryTheory.Sheaf.parallelPairSheafification, NatIso.ofComponents, id, CategoryTheory.GrothendieckTopology.isoSheafify, CategoryTheory.asIso,
    iso.symm]
  simp only [← Category.assoc]
  rw [IsIso.eq_comp_inv]
  simp only [Category.assoc]
  erw [Limits.limit.lift_π]
  dsimp [Limits.Cones.functoriality, CategoryTheory.GrothendieckTopology.sheafifyMap]
  simp_rw [← CategoryTheory.GrothendieckTopology.plusFunctor_map, ← Functor.comp_map, ← Functor.map_comp]
  dsimp [CategoryTheory.Sheaf.coimToIm', Abelian.coimageImageComparison, CategoryTheory.Sheaf.coimToIm'Aux]
  apply J.sheafify_hom_ext
  · exact Plus.isSheaf_plus_plus J G.val
  simp_rw [← Category.assoc]
  erw [J.toSheafify_sheafifyLift]
  change _ = (CategoryTheory.GrothendieckTopology.toSheafification J A).app _ ≫ (sheafification J A).map _
  erw [← (CategoryTheory.GrothendieckTopology.toSheafification J A).naturality]
  simp only [Category.assoc, Limits.kernel.lift_ι]
  dsimp
  erw [Category.assoc]

instance isIso_coim_to_im {F G : Sheaf J A} (η : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison η) :=
  by
  rw [coimToIm_eq]
  suffices IsIso (CategoryTheory.Sheaf.coimToIm' η) by skip; apply IsIso.comp_isIso
  suffices IsIso ((Sheaf_to_presheaf J A).map (CategoryTheory.Sheaf.coimToIm' η)) by skip;
    apply CategoryTheory.isIso_of_fully_faithful (Sheaf_to_presheaf J A)
  rw [CategoryTheory.Sheaf.coimToIm'_eq]
  apply IsIso.comp_isIso

instance abelian : Abelian (Sheaf J A) :=
  Abelian.ofCoimageImageComparisonIsIso

end Abelian

end Sheaf

end CategoryTheory

