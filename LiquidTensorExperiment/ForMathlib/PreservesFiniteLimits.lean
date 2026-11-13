import LiquidTensorExperiment.ForMathlib.SplitExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

#align_import for_mathlib.preserves_finite_limits

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
  let c' := preadditive.is_limit_kernel_fork_of_fork (i.of_iso_limit (isoOfι _ _ c))
  let iFc := is_limit_fork_map_of_is_limit' F (by simp) c'
  apply is_limit.of_iso_limit _ ((cones.functoriality _ F).mapIso (isoOfι _ _ c).symm)
  apply (is_limit_map_cone_fork_equiv F (fork.condition c)).invFun
  let p : parallel_pair (F.map (f - g)) 0 ≅ parallel_pair (F.map f - F.map g) 0 :=
    parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
  refine'
    is_limit.of_iso_limit
      (preadditive.is_limit_fork_of_kernel_fork ((is_limit.postcompose_hom_equiv p _).symm iFc)) _
  refine' fork.ext (iso.refl _) _
  dsimp only [p, preadditive.fork_of_kernel_fork, cones.postcompose, ← fork.app_zero_eq_ι]
  simp [-fork.app_zero_eq_ι]

def preservesEqualizersOfPreservesKernels [F.Additive]
    [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] :
    PreservesLimitsOfShape WalkingParallelPair F
    where PreservesLimit K :=
    by
    letI :=
      preservesEqualizerOfPreservesKernels F (K.map walking_parallel_pair_hom.left)
        (K.map walking_parallel_pair_hom.right)
    apply preserves_limit_of_iso_diagram F (diagram_iso_parallel_pair K).symm

-- todo: unify with `exact_comp_mono_iff`
theorem exact_comp_mono_iff' {X Y Z A : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ A) [Mono h] :
    Exact f (g ≫ h) ↔ Exact f g :=
  by
  refine'
    ⟨fun hfg => ⟨zero_of_comp_mono h (by rw [category.assoc, hfg.1]), _⟩, fun h =>
      exact_comp_mono h⟩
  rw [← (iso.eq_comp_inv _).1 (imageToKernel_comp_mono _ _ h hfg.1)]
  haveI := hfg.2; apply epi_comp

end

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem preservesFiniteLimitsOfPreservesMonoPreservesFiniteColimits {𝓐 : Type u₁} {𝓑 : Type u₂}
    [Category.{v} 𝓐] [Category.{v} 𝓑] [Abelian 𝓐] [Abelian 𝓑] (F : 𝓐 ⥤ 𝓑)
    (h1 : ∀ ⦃X Y : 𝓐⦄ (f : X ⟶ Y), Mono f → Mono (F.map f)) [PreservesFiniteColimits F] :
    PreservesFiniteLimits F :=
  by
  have : preserves_binary_biproducts F := by
    apply preserves_binary_biproducts_of_preserves_binary_coproducts
  have : preserves_limits_of_shape (discrete walking_pair) F := by
    apply preserves_binary_products_of_preserves_binary_biproducts
  have : F.additive := by apply functor.additive_of_preserves_binary_biproducts
  have : ∀ {X Y} (f : X ⟶ Y), preserves_limit (parallel_pair f 0) F :=
    by
    intro X Y f
    constructor
    intro c hc
    suffices hF : exact (F.map (fork.ι c)) (F.map f)
    · have : mono (F.map (fork.ι c)) := by
        apply h1
        exact limits.mono_of_is_limit_fork hc
      let this.1 := abelian.is_limit_of_exact_of_mono _ _ hF
      let α : parallel_pair f 0 ⋙ F ≅ parallel_pair (F.map f) 0 :=
        by
        refine' diagram_iso_parallel_pair _ ≪≫ _
        refine' parallel_pair.ext (iso.refl _) (iso.refl _) (by simp) (by simp)
      refine' is_limit.postcompose_hom_equiv α _ _
      refine' this.of_iso_limit (cones.ext (iso.refl _) _)
      rintro (_ | _)
      · simp; dsimp; simp
      · simp
    let hc' := hc.of_iso_limit (isoOfι _ _ _)
    have := abelian.exact_of_is_kernel _ _ (kernel_fork.condition c) hc'
    simp_rw [← image.fac f] at this 
    rw [exact_comp_mono_iff'] at this 
    let this.1 := abelian.is_colimit_of_exact_of_epi _ _ this
    let q := is_colimit_cofork_map_of_is_colimit' F _ this
    have : mono (F.map (image.ι f)) := by apply h1; infer_instance
    simp_rw [← image.fac f]
    rw [functor.map_comp, exact_comp_mono_iff']
    exact abelian.exact_of_is_cokernel _ _ _ q
  have : preserves_limits_of_shape walking_parallel_pair F := by
    apply preservesEqualizersOfPreservesKernels
  have : preserves_limit (Functor.empty.{0} 𝓐) F := by
    apply preservesTerminalObjectOfPreservesZeroMorphisms
  have : preserves_limits_of_shape (Discrete.{0} PEmpty) F := by
    apply limits.preserves_limits_of_shape_pempty_of_preserves_terminal
  haveI p := preserves_finite_products_of_preserves_binary_and_terminal F
  exact @preserves_finite_limits_of_preserves_equalizers_and_finite_products _ _ _ _ _ _ _ _ p

