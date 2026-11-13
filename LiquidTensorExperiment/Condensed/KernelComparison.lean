import LiquidTensorExperiment.Condensed.ProjectiveResolution

#align_import condensed.kernelComparison

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
      | WalkingParallelPair.zero => Iso.refl _
      | WalkingParallelPair.one => Iso.refl _) <|
    by rintro (a | a) (b | b) (f | f); tidy

def cokernelDiagramIso {A B : Condensed.{u} Ab.{u + 1}} (S : ExtrDisc) (f : A ⟶ B) :
    Limits.parallelPair ((Condensed.evaluation Ab S.val).map f) 0 ≅
      Limits.parallelPair f 0 ⋙ Condensed.evaluation Ab S.val :=
  (NatIso.ofComponents fun X =>
      match X with
      | WalkingParallelPair.zero => Iso.refl _
      | WalkingParallelPair.one => Iso.refl _) <|
    by rintro (a | a) (b | b) (f | f); tidy

def kernelIso (S : ExtrDisc.{u}) :
    (Condensed.evaluation _ S.val).obj (kernel f) ≅ kernel ((Condensed.evaluation _ S.val).map f) :=
  (isLimitOfPreserves (Condensed.evaluation _ S.val)
          (limit.isLimit (parallelPair f 0))).conePointUniqueUpToIso
      (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (kernelDiagramIso _ _)

@[simp, reassoc]
theorem kernelIso_hom (S : ExtrDisc.{u}) :
    (kernelIso f S).hom ≫ kernel.ι _ = (Condensed.evaluation _ S.val).map (kernel.ι _) :=
  by
  dsimp [kernel_iso, Condensed.kernelDiagramIso]
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π, NatIso.ofComponents_hom_app,
    limit.conePointUniqueUpToIso_hom_comp_assoc, Functor.mapCone_π_app,
    equalizer.fork_π_app_zero, equalizer_as_kernel, Condensed.evaluation_map]
  apply Category.comp_id

def cokernelIso (S : ExtrDisc.{u}) :
    cokernel ((Condensed.evaluation _ S.val).map f) ≅
      (Condensed.evaluation _ S.val).obj (cokernel f) :=
  HasColimit.isoOfNatIso (cokernelDiagramIso _ _) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitOfPreserves (Condensed.evaluation _ _) (colimit.isColimit (parallelPair f 0)))

@[simp, reassoc]
theorem cokernelIso_hom (S : ExtrDisc.{u}) :
    cokernel.π _ ≫ (cokernelIso f S).hom = (Condensed.evaluation _ S.val).map (cokernel.π _) :=
  by
  dsimp [cokernel_iso, Condensed.cokernelDiagramIso]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, NatIso.ofComponents_hom_app,
    colimit.comp_coconePointUniqueUpToIso_hom, Functor.mapCocone_ι_app,
    coequalizer.cofork_ι_app_one, coequalizer_as_cokernel, Condensed.evaluation_map]
  apply Category.id_comp

end Condensed

