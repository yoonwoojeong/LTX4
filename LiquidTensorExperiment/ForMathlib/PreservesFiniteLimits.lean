import LiquidTensorExperiment.ForMathlib.SplitExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

#align_import for_mathlib.preservesFiniteLimits

noncomputable section

universe v u₁ u₂

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits Opposite

section

variable {𝓐 : Type u₁} {𝓑 : Type u₂} [Category.{v} 𝓐] [Category.{v} 𝓑] (F : 𝓐 ⥤ 𝓑)

variable [Abelian 𝓐] [Abelian 𝓑]

def preservesLimitsOfShapePemptyOfPreservesTerminal [PreservesLimit (Functor.empty.{0} 𝓐) F] :
    PreservesLimitsOfShape (Discrete PEmpty) F
    where PreservesLimit K :=
    preservesLimitOfIsoDiagram.{0, 0} F (Functor.emptyExt (Functor.empty 𝓐) _)

def preservesTerminalObjectOfPreservesZeroMorphisms [Functor.PreservesZeroMorphisms F] :
    PreservesLimit (Functor.empty.{0} 𝓐) F :=
  preservesTerminalOfIso F <|
    (F.mapIso HasZeroObject.zeroIsoTerminal.symm).trans <|
      (Functor.mapZeroObject F).trans <| HasZeroObject.zeroIsoTerminal

def isoOfι {X Y : 𝓐} (f g : X ⟶ Y) (c : Cone (parallelPair f g)) :
    c ≅ Fork.ofι (Fork.ι c) (Fork.condition c) :=
  Fork.ext (Iso.refl _) (by tidy)

def preservesEqualizerOfPreservesKernels [F.Additive]
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] {X Y : 𝓐} (f g : X ⟶ Y) :
    PreservesLimit (parallelPair f g) F := by
  constructor; intro c i
  let c' := Preadditive.isLimitKernelForkOfFork (i.ofIsoLimit (isoOfι _ _ c))
  let iFc := CategoryTheory.Limits.isLimitForkMapOfIsLimit' F (by simp) c'
  apply IsLimit.ofIsoLimit _ ((Cones.functoriality _ F).mapIso (isoOfι _ _ c).symm)
  apply (CategoryTheory.Limits.isLimitMapConeForkEquiv F (Fork.condition c)).invFun
  let p : CategoryTheory.Limits.parallelPair (F.map (f - g)) 0 ≅ CategoryTheory.Limits.parallelPair (F.map f - F.map g) 0 :=
    parallelPair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
  refine'
    IsLimit.ofIsoLimit
      (Preadditive.isLimitForkOfKernelFork ((IsLimit.postcomposeHomEquiv p _).symm iFc)) _
  refine' Fork.ext (iso.refl _) _
  dsimp only [p, Preadditive.forkOfKernelFork, Cones.postcompose, ← Fork.app_zero_eq_ι]
  simp [-Fork.app_zero_eq_ι]

def preservesEqualizersOfPreservesKernels [F.Additive]
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F
    where PreservesLimit K :=
    by
    letI :=
      preservesEqualizerOfPreservesKernels F (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)
    apply CategoryTheory.Limits.preservesLimitOfIsoDiagram F (CategoryTheory.Limits.diagramIsoParallelPair K).symm

-- todo: unify with `exact_comp_mono_iff`
theorem exact_comp_mono_iff' {X Y Z A : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ A) [Mono h] :
    Exact f (g ≫ h) ↔ Exact f g :=
  by
  refine'
    ⟨fun hfg => ⟨zero_of_comp_mono h (by rw [Category.assoc, hfg.1]), _⟩, fun h =>
      exact_comp_mono h⟩
  rw [← (Iso.eq_comp_inv _).1 (imageToKernel_comp_mono _ _ h hfg.1)]
  haveI := hfg.2; apply epi_comp

end

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem preservesFiniteLimitsOfPreservesMonoPreservesFiniteColimits {𝓐 : Type u₁} {𝓑 : Type u₂}
    [Category.{v} 𝓐] [Category.{v} 𝓑] [Abelian 𝓐] [Abelian 𝓑] (F : 𝓐 ⥤ 𝓑)
    (h1 : ∀ ⦃X Y : 𝓐⦄ (f : X ⟶ Y), Mono f → Mono (F.map f)) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F :=
  by
  have : CategoryTheory.Limits.PreservesBinaryBiproducts F := by
    apply CategoryTheory.Limits.preservesBinaryBiproductsOfPreservesBinaryCoproducts
  have : preserves_limits_of_shape (discrete CategoryTheory.Limits.WalkingPair) F := by
    apply CategoryTheory.Limits.preservesBinaryProductsOfPreservesBinaryBiproducts
  have : F.additive := by apply Functor.additive_of_preservesBinaryBiproducts
  have : ∀ {X Y} (f : X ⟶ Y), preserves_limit (CategoryTheory.Limits.parallelPair f 0) F :=
    by
    intro X Y f
    constructor
    intro c hc
    suffices hF : exact (F.map (fork.ι c)) (F.map f)
    · have : mono (F.map (fork.ι c)) := by
        apply h1
        exact Limits.mono_of_isLimit_fork hc
      let this.1 := Abelian.isLimitOfExactOfMono _ _ hF
      let α : CategoryTheory.Limits.parallelPair f 0 ⋙ F ≅ CategoryTheory.Limits.parallelPair (F.map f) 0 :=
        by
        refine' CategoryTheory.Limits.diagramIsoParallelPair _ ≪≫ _
        refine' parallelPair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
      refine' IsLimit.postcomposeHomEquiv α _ _
      refine' this.ofIsoLimit (Cones.ext (iso.refl _) _)
      rintro (_ | _)
      · simp; dsimp; simp
      · simp
    let hc' := hc.ofIsoLimit (isoOfι _ _ _)
    have := Abelian.exact_of_is_kernel _ _ (KernelFork.condition c) hc'
    simp_rw [← image.fac f] at this 
    rw [exact_comp_mono_iff'] at this 
    let this.1 := Abelian.isColimitOfExactOfEpi _ _ this
    let q := CategoryTheory.Limits.isColimitCoforkMapOfIsColimit' F _ this
    have : mono (F.map (image.ι f)) := by apply h1; infer_instance
    simp_rw [← image.fac f]
    rw [Functor.map_comp, exact_comp_mono_iff']
    exact Abelian.exact_of_is_cokernel _ _ _ q
  have : preserves_limits_of_shape CategoryTheory.Limits.WalkingParallelPair F := by
    apply preservesEqualizersOfPreservesKernels
  have : preserves_limit (Functor.empty.{0} 𝓐) F := by
    apply preservesTerminalObjectOfPreservesZeroMorphisms
  have : preserves_limits_of_shape (Discrete.{0} PEmpty) F := by
    apply Limits.preservesLimitsOfShapePemptyOfPreservesTerminal
  haveI p := CategoryTheory.preservesFiniteProductsOfPreservesBinaryAndTerminal F
  exact @CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts _ _ _ _ _ _ _ _ p

