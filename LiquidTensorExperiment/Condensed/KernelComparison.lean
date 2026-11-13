import LiquidTensorExperiment.Condensed.ProjectiveResolution

#align_import condensed.kernel_comparison

open CategoryTheory.Limits

open CategoryTheory

namespace Condensed

--TODO: generalize (as needed...)
universe u

variable {A B : Condensed.{u} Ab.{u + 1}} (f : A ⟶ B)

noncomputable section

def kernelDiagramIso {A B : Condensed.{u} Ab.{u + 1}} (S : ExtrDisc) (f : A ⟶ B) :
    parallelPair f 0 ⋙ Condensed.evaluation Ab S.val ≅
      parallelPair ((Condensed.evaluation Ab S.val).map f) 0 :=
  (NatIso.ofComponents fun X =>
      match X with
      | walking_parallel_pair.zero => Iso.refl _
      | walking_parallel_pair.one => Iso.refl _) <|
    by rintro (a | a) (b | b) (f | f); tidy

def cokernelDiagramIso {A B : Condensed.{u} Ab.{u + 1}} (S : ExtrDisc) (f : A ⟶ B) :
    Limits.parallelPair ((Condensed.evaluation Ab S.val).map f) 0 ≅
      Limits.parallelPair f 0 ⋙ Condensed.evaluation Ab S.val :=
  (NatIso.ofComponents fun X =>
      match X with
      | walking_parallel_pair.zero => Iso.refl _
      | walking_parallel_pair.one => Iso.refl _) <|
    by rintro (a | a) (b | b) (f | f); tidy

def kernelIso (S : ExtrDisc.{u}) :
    (Condensed.evaluation _ S.val).obj (kernel f) ≅ kernel ((Condensed.evaluation _ S.val).map f) :=
  (isLimitOfPreserves (Condensed.evaluation _ S.val)
          (limit.isLimit (parallelPair f 0))).conePointUniqueUpToIso
      (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (kernelDiagramIso _ _)

@[simp, reassoc]
theorem kernelIso_hom (S : ExtrDisc.{u}) :
    (kernelIso f S).Hom ≫ kernel.ι _ = (Condensed.evaluation _ S.val).map (kernel.ι _) :=
  by
  dsimp [kernel_iso, kernel_diagram_iso]
  simp only [category.assoc, has_limit.iso_of_nat_iso_hom_π, nat_iso.of_components_hom_app,
    limit.cone_point_unique_up_to_iso_hom_comp_assoc, functor.map_cone_π_app,
    equalizer.fork_π_app_zero, equalizer_as_kernel, Condensed.evaluation_map]
  apply category.comp_id

def cokernelIso (S : ExtrDisc.{u}) :
    cokernel ((Condensed.evaluation _ S.val).map f) ≅
      (Condensed.evaluation _ S.val).obj (cokernel f) :=
  HasColimit.isoOfNatIso (cokernelDiagramIso _ _) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitOfPreserves (Condensed.evaluation _ _) (colimit.isColimit (parallelPair f 0)))

@[simp, reassoc]
theorem cokernelIso_hom (S : ExtrDisc.{u}) :
    cokernel.π _ ≫ (cokernelIso f S).Hom = (Condensed.evaluation _ S.val).map (cokernel.π _) :=
  by
  dsimp [cokernel_iso, cokernel_diagram_iso]
  simp only [has_colimit.iso_of_nat_iso_ι_hom_assoc, nat_iso.of_components_hom_app,
    colimit.comp_cocone_point_unique_up_to_iso_hom, functor.map_cocone_ι_app,
    coequalizer.cofork_ι_app_one, coequalizer_as_cokernel, Condensed.evaluation_map]
  apply category.id_comp

end Condensed

