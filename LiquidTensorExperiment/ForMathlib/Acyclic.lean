import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import LiquidTensorExperiment.ForMathlib.Derived.Les2
import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.ForMathlib.Derived.ExtLemmas
import LiquidTensorExperiment.ForMathlib.IsQuasiIso
import LiquidTensorExperiment.ForMathlib.ShortExact
import LiquidTensorExperiment.ForMathlib.Homology
import LiquidTensorExperiment.ForMathlib.ExactLiftDesc
import LiquidTensorExperiment.ForMathlib.AdditiveFunctor
import LiquidTensorExperiment.ForMathlib.HomotopyCategoryLemmas
import LiquidTensorExperiment.ForMathlib.HomologyLiftDesc

#align_import for_mathlib.acyclic

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open HomotopyCategory hiding single

open BoundedHomotopyCategory

universe v v' u u'

-- main proof in this file is inspired by https://math.stackexchange.com/a/2118042
section

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {ι : Type _} {c : ComplexShape ι}

def deltaToKernel (C : HomologicalComplex 𝓐 c) (i j k : ι) : C.pt i ⟶ kernel (C.d j k) :=
  factorThruImage _ ≫ imageToKernel' (C.d i j) _ (C.d_comp_d _ _ _)

def deltaToKernel_ι (C : HomologicalComplex 𝓐 c) (i j k : ι) :
    deltaToKernel C i j k ≫ kernel.ι (C.d j k) = C.d i j :=
  by
  delta deltaToKernel imageToKernel'
  rw [Category.assoc, kernel.lift_ι, image.fac]

def d_deltaToKernel (C : HomologicalComplex 𝓐 c) (h i j k : ι) :
    C.d h i ≫ deltaToKernel C i j k = 0 := by
  rw [← cancel_mono (kernel.ι (C.d j k)), Category.assoc, deltaToKernel_ι, C.d_comp_d, zero_comp]

-- move me
theorem shortExact_comp_iso {A B C D : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (hh : IsIso h) :
    ShortExact f (g ≫ h) ↔ ShortExact f g :=
  by
  constructor <;> intro H
  · haveI : mono f := H.mono
    have : epi g := by haveI := H.epi; have := epi_comp (g ≫ h) (inv h);
      simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    refine' ⟨_⟩; have := H.exact; rwa [exact_comp_iso] at this 
  · haveI : mono f := H.mono
    haveI : epi g := H.epi
    haveI : epi (g ≫ h) := epi_comp g h
    refine' ⟨_⟩; have := H.exact; rwa [exact_comp_iso]

theorem isAcyclic_def (C : HomotopyCategory 𝓐 c) : IsAcyclic C ↔ ∀ i, IsZero (C.as.homology' i) :=
  by
  constructor
  · apply IsAcyclic.cond
  · apply IsAcyclic.mk

theorem isAcyclic_iff_shortExact_to_cycles (C : HomotopyCategory 𝓐 (ComplexShape.up ℤ)) :
    IsAcyclic C ↔
      ∀ i, ShortExact (kernel.ι (C.as.d i (i + 1))) (deltaToKernel C.as i (i + 1) (i + 1 + 1)) :=
  by
  rw [isAcyclic_def]
  symm
  apply (Equiv.addRight (1 : ℤ)).forall_congr'
  intro i
  let e := homology_iso C.as i (i + 1) (i + 1 + 1) rfl rfl
  dsimp [deltaToKernel] at e ⊢
  rw [e.isZero_iff, homology'_isZero_iff_imageToKernel'_isIso]
  constructor
  · apply iso_of_shortExact_comp_right _ _ _; apply shortExact_kernel_factorThruImage
  · intro h; rw [shortExact_comp_iso _ _ _ h]; apply shortExact_kernel_factorThruImage

theorem is_acyclic_iff_shortExact_to_cycles' (C : HomologicalComplex 𝓐 (ComplexShape.down ℤ)) :
    (∀ i, IsZero (C.homology' i)) ↔
      ∀ i,
        ShortExact (kernel.ι (C.d (i + 1 + 1) (i + 1))) (deltaToKernel C (i + 1 + 1) (i + 1) i) :=
  by
  symm
  apply (Equiv.addRight (1 : ℤ)).forall_congr'
  intro i
  let e := homology_iso C (i + 1 + 1) (i + 1) i rfl rfl
  dsimp [deltaToKernel] at e ⊢
  rw [e.isZero_iff, homology'_isZero_iff_imageToKernel'_isIso]
  constructor
  · apply iso_of_shortExact_comp_right _ _ _; apply shortExact_kernel_factorThruImage
  · intro h; rw [shortExact_comp_iso _ _ _ h]; apply shortExact_kernel_factorThruImage

end

variable {𝓐 𝓑 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]

variable [Category 𝓑] [Abelian 𝓑] [EnoughProjectives 𝓑]

variable (C : CochainComplex 𝓐 ℤ)
  [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj C)]

def CategoryTheory.Functor.single (F : BoundedHomotopyCategory 𝓐 ⥤ 𝓑) (i : ℤ) : 𝓐 ⥤ 𝓑 :=
  BoundedHomotopyCategory.single _ i ⋙ F

-- move me
theorem CategoryTheory.Limits.IsZero.biprod {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {X Y : 𝓐}
    (hX : IsZero X) (hY : IsZero Y) : IsZero (X ⊞ Y) :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero] at hX hY ⊢
  ext <;> simp [hX, hY]

instance CategoryTheory.Limits.preservesBinaryBiproductOfAdditive {𝓐 𝓑 : Type _} [Category.{v} 𝓐]
    [Category.{v} 𝓑] [Abelian 𝓐] [Abelian 𝓑] (F : 𝓐 ⥤ 𝓑) [Functor.Additive F] (X Y : 𝓐) :
    PreservesBinaryBiproduct X Y F :=
  preservesBinaryBiproductOfPreservesBiproduct _ _ _

theorem acyclic_left_of_shortExact (B : 𝓐) {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : ShortExact f g) (hY : ∀ i > 0, IsZero (((ext' i).obj (op <| Y)).obj B))
    (hZ : ∀ i > 0, IsZero (((ext' i).obj (op <| Z)).obj B)) :
    ∀ i > 0, IsZero (((ext' i).obj (op <| X)).obj B) :=
  by
  intro i hi
  have := hfg.ext'_five_term_exactSeq B i
  refine' (this.drop 1).pair.isZero_of_isZero_isZero (hY _ hi) (hZ _ _)
  trans i; · exact lt_add_one i; · exact hi

theorem map_is_acyclic_of_acyclic_aux {A B C D X Y Z W : 𝓐} (f : A ⟶ B) (g : C ⟶ D)
    (π : B ⟶ kernel g) {α : X ⟶ B} {β : B ⟶ Y} {γ : Y ⟶ C} {δ : C ⟶ Z} {ε : Z ⟶ D} {ζ : D ⟶ W}
    (hαβ : ShortExact α β) (hγδ : ShortExact γ δ) (hεζ : ShortExact ε ζ) (hf : Mono f)
    (hfπ : Exact f π) (hαπ : α ≫ π = 0) (hγg : γ ≫ g = 0) (hδε : δ ≫ ε = g)
    (hπι : π ≫ kernel.ι g = β ≫ γ) : ShortExact f π :=
  by
  suffices epi π by skip; exact ⟨hfπ⟩
  have hβ : epi β := hαβ.epi
  have hγ : mono γ := hγδ.mono
  have hε : mono ε := hεζ.mono
  skip
  have hιδ : kernel.ι g ≫ δ = 0 := by
    rw [← cancel_mono ε, Category.assoc, hδε, kernel.condition, zero_comp]
  let e1 : Y ⟶ kernel g := hαβ.exact.epiDesc π hαπ
  let e2 : Y ⟶ kernel g := kernel.lift g γ hγg
  let e3 : kernel g ⟶ Y := hγδ.exact.monoLift (kernel.ι g) hιδ
  have he12 : e1 = e2 := by
    rw [← cancel_epi β, ← cancel_mono (kernel.ι g)]
    simp only [hπι, Category.assoc, kernel.lift_ι, Exact.comp_epiDesc_assoc]
  have he13 : e1 ≫ e3 = 𝟙 _ := by
    rw [he12, ← cancel_mono γ, Category.assoc, Exact.monoLift_comp, kernel.lift_ι,
      Category.id_comp]
  have he31 : e3 ≫ e1 = 𝟙 _ := by
    rw [he12, ← cancel_mono (kernel.ι g), Category.assoc, kernel.lift_ι, Exact.monoLift_comp,
      Category.id_comp]
  let e : Y ≅ kernel g := ⟨e1, e3, he13, he31⟩
  have hπ : β ≫ e.hom = π := Exact.comp_epiDesc _ _ _
  rw [← hπ]; exact epi_comp _ _

theorem shortExact_Ext_of_shortExact_of_acyclic {A B C : 𝓐} (Z : 𝓐) {f : A ⟶ B} {g : B ⟶ C}
    (hfg : ShortExact f g) (hC : ∀ i > 0, IsZero (((ext' i).obj (op <| C)).obj Z)) :
    ShortExact (((ext' 0).flip.obj Z).map g.op) (((ext' 0).flip.obj Z).map f.op) :=
  by
  have H0 := hfg.ext'_five_term_exactSeq Z 0
  apply (config := { instances := false }) ShortExact.mk
  · have H := ((hfg.ext'_five_term_exactSeq Z (-1)).drop 2).pair
    apply H.mono_of_is_zero
    apply ext'_isZero_of_neg; decide
  · apply (H0.drop 1).pair.epi_of_isZero
    apply hC; decide
  · exact H0.pair

theorem map_isAcyclic_of_acyclic'' [IsAcyclic ((HomotopyCategory.quotient _ _).obj C)] (B : 𝓐)
    (hC : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C.pt k)).obj B)) :
    ∀ i, IsZero (((((ext' 0).flip.obj B).mapHomologicalComplex _).obj C.op).homology' i) :=
  by
  rw [is_acyclic_iff_shortExact_to_cycles']
  obtain ⟨a, ha⟩ := IsBoundedAbove.cond ((Quotient 𝓐 (ComplexShape.up ℤ)).obj C)
  have aux : ((Quotient 𝓐 (ComplexShape.up ℤ)).obj C).IsAcyclic := ‹_›
  rw [isAcyclic_iff_shortExact_to_cycles] at aux 
  intro i
  let K j := kernel (C.d j (j + 1))
  suffices hK : ∀ j, ∀ i > 0, is_zero (((ext' i).obj (op <| K j)).obj B)
  · have SES1 := shortExact_Ext_of_shortExact_of_acyclic B (aux (i + 1 + 1)) (hK _)
    have SES2 := shortExact_Ext_of_shortExact_of_acyclic B (aux (i + 1)) (hK _)
    have SES3 := shortExact_Ext_of_shortExact_of_acyclic B (aux i) (hK _)
    apply map_is_acyclic_of_acyclic_aux _ _ _ SES1 SES2 SES3 inferInstance <;>
      clear SES1 SES2 SES3 aux
    · delta deltaToKernel imageToKernel'
      apply exact_comp_mono; rw [exact_factorThruImage_iff]; exact exact_kernel_ι
    · rw [← cancel_mono (kernel.ι _), zero_comp, Category.assoc, deltaToKernel_ι]
      swap; infer_instance
      erw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp]
      dsimp only [HomologicalComplex.op_d, quotient_obj_as]
      rw [← op_comp, d_deltaToKernel, op_zero, Functor.map_zero]
    · erw [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp]
      dsimp only [HomologicalComplex.op_d, quotient_obj_as]
      rw [← op_comp, d_deltaToKernel, op_zero, Functor.map_zero]
    · rw [← Functor.map_comp, ← op_comp, deltaToKernel_ι]; rfl
    · rw [deltaToKernel_ι, ← Functor.map_comp, ← op_comp, deltaToKernel_ι]; rfl
    · infer_instance
  clear i; intro j
  have : ∀ j ≥ a, ∀ i > 0, is_zero (((ext' i).obj (op <| K j)).obj B) :=
    by
    intro j hj i hi
    apply BoundedDerivedCategory.ext'_zero_left_isZero
    apply IsZero.op
    refine' IsZero.of_mono (kernel.ι _) _
    exact ha j hj
  apply Int.inductionOn' j a
  · exact this _ le_rfl
  · intro j hj aux; apply this; exact Int.le_add_one hj
  · intro j hj IH
    obtain ⟨j, rfl⟩ : ∃ i, i + 1 = j := ⟨j - 1, sub_add_cancel _ _⟩
    rw [add_sub_cancel]
    apply acyclic_left_of_shortExact B (kernel.ι _) (deltaToKernel _ _ _ _) _ (hC _) IH
    exact aux j

theorem mapIsAcyclicOfAcyclic' [IsAcyclic ((HomotopyCategory.quotient _ _).obj C)] (B : 𝓐)
    (hC : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C.pt k)).obj B)) :
    IsAcyclic
      ((((ext' 0).flip.obj B).rightOp.mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ _).obj C)) :=
  by
  rw [isAcyclic_def]
  intro i
  have h1 : (ComplexShape.up ℤ).Rel (i - 1) i := by dsimp; apply sub_add_cancel
  refine' IsZero.of_iso _ (CategoryTheory.homologyIso' _ (i - 1) i (i + 1) h1 rfl)
  dsimp only [Functor.mapHomotopyCategory_obj, quotient_obj_as, Functor.rightOp_map,
    Functor.mapHomologicalComplex_obj_d]
  apply Exact.homology'_isZero
  apply exact.op
  refine' CategoryTheory.exact_of_homology'_isZero _
  ·
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, HomologicalComplex.d_comp_d, op_zero,
      Functor.map_zero]
  have := map_isAcyclic_of_acyclic'' C B hC i
  apply this.of_iso _; clear this
  let C' :=
    (((ext' 0).flip.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
      (HomologicalComplex.op C)
  have h1 : (ComplexShape.down ℤ).Rel i (i - 1) := by dsimp; apply sub_add_cancel
  exact (CategoryTheory.homologyIso' C' (i + 1) i (i - 1) rfl h1).symm

theorem mapIsAcyclicOfAcyclic [IsAcyclic ((HomotopyCategory.quotient _ _).obj C)] (B : 𝓐)
    (hC : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C.pt k)).obj B)) :
    IsAcyclic
      (((preadditiveYoneda.obj B).rightOp.mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ _).obj C)) :=
  by
  have := mapIsAcyclicOfAcyclic' C B hC
  rw [isAcyclic_def] at this ⊢
  intro i; specialize this i
  apply this.of_iso _; clear this
  have h1 : (ComplexShape.up ℤ).Rel (i - 1) i := by dsimp; apply sub_add_cancel
  refine'
    CategoryTheory.homologyIso' _ (i - 1) i (i + 1) h1 rfl ≪≫ _ ≪≫ (CategoryTheory.homologyIso' _ (i - 1) i (i + 1) h1 rfl).symm
  dsimp only [Functor.mapHomotopyCategory_obj, quotient_obj_as, Functor.rightOp_map,
    Functor.mapHomologicalComplex_obj_d]
  let e i := ((BoundedDerivedCategory.ext'ZeroFlipIso _ B).app (op <| C.X i)).op
  refine' homology'.mapIso _ _ (Arrow.isoMk (e _) (e _) _) (Arrow.isoMk (e _) (e _) _) rfl
  ·
    simp only [Iso.op_hom, Iso.app_hom, Arrow.mk_hom, Functor.flip_obj_map, ← op_comp, ←
      NatTrans.naturality]
  ·
    simp only [Iso.op_hom, Iso.app_hom, Arrow.mk_hom, Functor.flip_obj_map, ← op_comp, ←
      NatTrans.naturality]

theorem acyclic_of_projective (P B : 𝓐) [Projective P] (i : ℤ) (hi : 0 < i) :
    IsZero (((ext' i).obj (op P)).obj B) :=
  by
  rw [(ext'Iso (op P) B i _ (𝟙 _) _).isZero_iff]
  · rcases i with ((_ | i) | i)
    · exfalso; revert hi; decide
    swap; · exfalso; revert hi; decide
    refine' IsZero.homology'_isZero _ _ _ _
    apply AddCommGroupCat.isZero_of_eq
    intros
    apply IsZero.eq_of_src
    apply is_zero_zero
  · refine' ⟨_, _, _⟩
    · rintro (_ | n); · assumption; · dsimp; infer_instance
    · exact exact_zero_mono (𝟙 P)
    · rintro (_ | n) <;> exact exact_of_zero 0 0

def extComputeWithAcyclicAux₁ (B : 𝓐) (i : ℤ) :
    ((ext i).obj (op <| of' C)).obj ((single _ 0).obj B) ≅
      (preadditiveYoneda.obj ((single 𝓐 (-i)).obj B)).obj (op (of' C).replace) :=
  (preadditiveYoneda.mapIso <| (shiftSingleIso 0 i).app B ≪≫ eqToIso (by rw [zero_sub])).app _

abbrev of'Hom {C₁ C₂ : CochainComplex 𝓐 ℤ}
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₁).IsBoundedAbove]
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₂).IsBoundedAbove] (f : C₁ ⟶ C₂) : of' C₁ ⟶ of' C₂ :=
  (HomotopyCategory.quotient _ _).map f

theorem extComputeWithAcyclicAux₁_naturality (C₁ C₂ : CochainComplex 𝓐 ℤ)
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₁).IsBoundedAbove]
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₂).IsBoundedAbove] (B : 𝓐) (f : C₁ ⟶ C₂) (i : ℤ) :
    ((ext i).map <| Quiver.Hom.op <| of'Hom f).app _ ≫ (extComputeWithAcyclicAux₁ C₁ B i).hom =
      (extComputeWithAcyclicAux₁ C₂ B i).hom ≫
        (preadditiveYoneda.obj _).map
          (Quiver.Hom.op <| BoundedHomotopyCategory.lift ((of' C₁).π ≫ of'Hom f) (of' C₂).π) :=
  by
  ext F
  dsimp [Ext, extComputeWithAcyclicAux₁]
  simp only [comp_apply]
  dsimp; simp

def extComputeWithAcyclicAux₂ (B : 𝓐) (i : ℤ) :
    (preadditiveYoneda.obj ((single 𝓐 (-i)).obj B)).obj (op (of' C).replace) ≅
      (((preadditiveYoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
            (of' C).replace.val.as.op).homology'
        (-i) :=
  homSingleIso _ _ _

-- TODO: We should prove naturality of `hom_single_iso` independently!
theorem extComputeWithAcyclicAux₂_naturality (C₁ C₂ : CochainComplex 𝓐 ℤ)
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₁).IsBoundedAbove]
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₂).IsBoundedAbove] (B : 𝓐) (f : C₁ ⟶ C₂) (i : ℤ) :
    (preadditiveYoneda.obj _).map
          (Quiver.Hom.op <| BoundedHomotopyCategory.lift ((of' C₁).π ≫ of'Hom f) (of' C₂).π) ≫
        (extComputeWithAcyclicAux₂ C₁ B i).hom =
      (extComputeWithAcyclicAux₂ C₂ B i).hom ≫
        (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                HomologicalComplex.unopFunctor.rightOp ⋙ (homology'Functor _ _ (-i)).op).map
            (BoundedHomotopyCategory.lift ((of' C₁).π ≫ of'Hom f) (of' C₂).π).out).unop :=
  homSingleIso_naturality _ _ _ _ _

def extComputeWithAcyclicHomB (B : 𝓐) :=
  (preadditiveYoneda.obj B).rightOp.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.unopFunctor.rightOp

theorem extComputeWithAcyclicIsQuasiIsoAux (B : 𝓐)
    (hC : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C.pt k)).obj B)) (i : ℤ) :
    IsQuasiIso
      ((HomotopyCategory.quotient _ _).map
        ((extComputeWithAcyclicHomB B).map (of' C).π.out).unop) :=
  by
  let P := (of' C).replace
  let π : P ⟶ of' C := (of' C).π
  let HomB :=
    (preadditive_yoneda.obj B).rightOp.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      homological_complex.unop_functor.rightOp
  let fq := (HomotopyCategory.quotient _ _).map (HomB.map π.out).unop
  apply isQuasiIsoOfOp
  let f := homological_complex.op_functor.map (HomB.map (Quot.out π))
  have := cone_triangleₕ_mem_distinguished_triangles _ _ f
  replace := HomotopyCategory.isQuasiIso_iff_isAcyclic _ this
  dsimp [HomologicalComplex.cone.triangleₕ] at this 
  erw [this]; clear this i
  constructor
  intro i; obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
  refine' IsZero.of_iso _ (homology_iso _ i (i + 1) (i + 1 + 1) _ _)
  rotate_left; · dsimp; rfl; · dsimp; rfl
  apply Exact.homology'_isZero _
  dsimp only [HomotopyCategory.quotient, quotient.functor_obj_as, HomologicalComplex.cone_d]
  have hπ : is_quasi_iso π := by dsimp [π]; infer_instance
  have := cone_triangleₕ_mem_distinguished_triangles _ _ π.out
  replace := HomotopyCategory.isQuasiIso_iff_isAcyclic _ this
  dsimp [HomologicalComplex.cone.triangleₕ] at this 
  simp only [quotient_map_out] at this 
  replace := this.mp _
  swap; · convert hπ using 1; generalize P.val = X; cases X; rfl
  have preaux :
    ((Quotient 𝓐 (ComplexShape.up ℤ)).obj (HomologicalComplex.cone (Quot.out π))).IsBoundedAbove :=
    by
    constructor
    obtain ⟨a, ha⟩ := IsBoundedAbove.cond ((Quotient 𝓐 (ComplexShape.up ℤ)).obj C)
    obtain ⟨b, hb⟩ := IsBoundedAbove.cond P.val
    refine' ⟨max a b, _⟩
    intro k hk
    refine' CategoryTheory.Limits.IsZero.biprod _ _
    · apply hb; refine' (le_max_right _ _).trans (hk.trans (lt_add_one _).le)
    · apply ha; exact (le_max_left _ _).trans hk
  have aux := @mapIsAcyclicOfAcyclic _ _ _ _ _ _ this B _
  · replace :=
      (@IsAcyclic.cond _ _ _ _ _ _ aux (i + 1)).of_iso
        (homology_iso _ i (i + 1) (i + 1 + 1) _ _).symm
    rotate_left; · dsimp; rfl; · dsimp; rfl
    dsimp only [HomotopyCategory.quotient, quotient.functor_obj_as, HomologicalComplex.cone_d,
      Functor.mapHomotopyCategory_obj, Functor.mapHomologicalComplex_obj_d] at this 
    replace := CategoryTheory.exact_of_homology'_isZero this
    let e := Functor.mapBiprod (preadditive_yoneda.obj B).rightOp
    refine' Preadditive.exact_of_iso_of_exact' _ _ _ _ (e _ _) (e _ _) (e _ _) _ _ this <;>
      dsimp only [e, Functor.mapBiprod_hom]
    all_goals
      ext
      · simp only [Category.assoc, Functor.rightOp_map, HomologicalComplex.Cone.d, biprod.lift_fst,
          eq_self_iff_true, Functor.mapHomologicalComplex_obj_d, Functor.rightOp_map,
          HomologicalComplex.xEqToIso_refl, Category.comp_id, dite_eq_ite, if_true, biprod.lift_fst,
          biprod.lift_desc, Preadditive.comp_neg, comp_zero, add_zero]
        simp only [Functor.mapHomologicalComplex_obj_d, Functor.rightOp_map, Functor.comp_map,
          biprod.lift_desc, Preadditive.comp_neg, comp_zero, add_zero, ← op_comp, ←
          CategoryTheory.Functor.map_comp, biprod.lift_fst]
        simp only [biprod.desc_eq, comp_zero, add_zero, Preadditive.comp_neg, CategoryTheory.op_neg,
          Functor.map_neg, op_comp, CategoryTheory.Functor.map_comp]
        rfl
      · simp only [Category.assoc, Functor.rightOp_map, HomologicalComplex.Cone.d, biprod.lift_snd,
          eq_self_iff_true, Functor.mapHomologicalComplex_obj_d, Functor.rightOp_map,
          Functor.mapHomologicalComplex_map_f, HomologicalComplex.xEqToIso_refl, Category.comp_id,
          dite_eq_ite, if_true, biprod.lift_snd, biprod.lift_desc]
        simp only [Functor.mapHomologicalComplex_obj_d, Functor.rightOp_map, Functor.comp_map,
          biprod.lift_desc, Preadditive.comp_neg, comp_zero, add_zero, ← op_comp, ←
          CategoryTheory.Functor.map_comp, biprod.lift_snd]
        simp only [biprod.desc_eq, op_add, Functor.map_neg, Functor.map_add, op_comp,
          CategoryTheory.Functor.map_comp]
        rfl
  · clear i; intro k i hi
    let e :=
      Functor.mapBiprod ((ext' i).flip.obj B).rightOp (P.val.as.X (k + 1)) ((of' C).val.as.pt k)
    refine' IsZero.of_iso (IsZero.unop _) e.symm.unop
    refine' CategoryTheory.Limits.IsZero.biprod _ _
    · simp only [Functor.rightOp_obj, Functor.flip_obj_obj, CategoryTheory.Limits.isZero_op]
      exact acyclic_of_projective (P.val.as.X (k + 1)) B i hi
    · exact (hC k _ hi).op

def extComputeWithAcyclicAux₃ (B : 𝓐) (i : ℤ) :
    (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _).obj C).unop.homology' (-i) ⟶
      (((preadditiveYoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
            (of' C).replace.val.as.op).homology'
        (-i) :=
  by
  apply
    (HomotopyCategory.homology'Functor Ab _ (-i)).map
      ((HomotopyCategory.quotient _ _).map ((extComputeWithAcyclicHomB B).map (of' C).π.out).unop)

-- Are these two lemmas useful? Do we have them?
theorem Functor.map_unop {𝓐 : Type _} [Category 𝓐] {𝓑 : Type _} [Category 𝓑] (F : 𝓐 ⥤ 𝓑)
    {a₁ a₂ : 𝓐ᵒᵖ} (f : a₁ ⟶ a₂) : F.map f.unop = (F.op.map f).unop :=
  rfl

theorem Functor.map_map' {𝓐 : Type _} [Category 𝓐] {𝓑 : Type _} [Category 𝓑] {𝓒 : Type _}
    [Category 𝓒] (F : 𝓐 ⥤ 𝓑) (G : 𝓑 ⥤ 𝓒) {a₁ a₂ : 𝓐} (φ : a₁ ⟶ a₂) :
    G.map (F.map φ) = (F ⋙ G).map φ :=
  rfl

namespace ExtComputeWithAcyclicAux₃NaturalityHelpers

variable (C₁ C₂ : CochainComplex 𝓐 ℤ) [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₁).IsBoundedAbove]
  [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₂).IsBoundedAbove] (B : 𝓐) (f : C₁ ⟶ C₂) (i : ℤ)

theorem helper₁ (h1 h2) :
    homology'.lift
        ((unop
              (HomologicalComplex.unopFunctor.rightOp.obj
                (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  C₁))).dTo
          (-i))
        ((unop
              (HomologicalComplex.unopFunctor.rightOp.obj
                (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  C₁))).dFrom
          (-i))
        h1
        (kernel.ι
            ((unop
                  (HomologicalComplex.unopFunctor.rightOp.obj
                    (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex
                          (ComplexShape.up ℤ)).obj
                      C₂))).dFrom
              (-i)) ≫
          (HomologicalComplex.unopFunctor.rightOp.map
                    (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex
                          (ComplexShape.up ℤ)).map
                      f)).unop.f
              (-i) ≫
            cokernel.π
              ((unop
                    (HomologicalComplex.unopFunctor.rightOp.obj
                      (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex
                            (ComplexShape.up ℤ)).obj
                        C₁))).dTo
                (-i)))
        h2 =
      kernel.lift _ (kernel.ι _ ≫ (preadditiveYoneda.obj B).map (f.f (-i)).op)
          (by
            rw [Category.assoc]
            have aux :=
              (((preadditive_yoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                          homological_complex.unop_functor.rightOp).map
                      f).unop.comm_from
                (-i)
            dsimp at aux 
            erw [aux, kernel.condition_assoc, zero_comp]) ≫
        homology'.π' _ _ _ :=
  by
  apply homology'.hom_to_ext
  rw [Category.assoc, homology'.π'_ι, kernel.lift_ι_assoc, homology'.lift_ι]
  rfl

theorem helper₂ (h1 h2) :
    homology'.lift ((unop ((extComputeWithAcyclicHomB B).obj (of' C₂).replace.val.as)).dTo (-i))
        ((unop ((extComputeWithAcyclicHomB B).obj (of' C₂).replace.val.as)).dFrom (-i)) h1
        (kernel.ι ((unop ((extComputeWithAcyclicHomB B).obj (of' C₂).val.as)).dFrom (-i)) ≫
          ((extComputeWithAcyclicHomB B).map (Quot.out (of' C₂).π)).unop.f (-i) ≫
            cokernel.π
              ((unop ((extComputeWithAcyclicHomB B).obj (of' C₂).replace.val.as)).dTo (-i)))
        h2 =
      kernel.lift _
          (kernel.ι _ ≫ by
            apply HomologicalComplex.Hom.f
            exact
              (((preadditive_yoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                      homological_complex.unop_functor.rightOp).map
                  (of' C₂).π.out).unop)
          (by
            rw [Category.assoc]
            have :=
              (((preadditive_yoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                          homological_complex.unop_functor.rightOp).map
                      (of' C₂).π.out).unop.comm_from
                (-i)
            erw [this, kernel.condition_assoc, zero_comp]) ≫
        homology'.π' _ _ _ :=
  by
  apply homology'.hom_to_ext
  simp only [homology'.lift_ι, Category.assoc, homology'.π'_ι, kernel.lift_ι_assoc]
  rfl

end ExtComputeWithAcyclicAux₃NaturalityHelpers

theorem extComputeWithAcyclicAux₃_naturality (C₁ C₂ : CochainComplex 𝓐 ℤ)
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₁).IsBoundedAbove]
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₂).IsBoundedAbove] (B : 𝓐) (f : C₁ ⟶ C₂) (i : ℤ) :
    (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                HomologicalComplex.unopFunctor.rightOp ⋙ (homology'Functor _ _ (-i)).op).map
            f).unop ≫
        extComputeWithAcyclicAux₃ C₁ B i =
      extComputeWithAcyclicAux₃ C₂ B i ≫
        (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                HomologicalComplex.unopFunctor.rightOp ⋙ (homology'Functor _ _ (-i)).op).map
            (BoundedHomotopyCategory.lift ((of' C₁).π ≫ of'Hom f) (of' C₂).π).out).unop :=
  by
  dsimp only [extComputeWithAcyclicAux₃, Functor.comp_map, _root_.homology_functor, Functor.op,
    HomologicalComplex.Hom.sqFrom, HomologicalComplex.Hom.sqTo, HomotopyCategory.quotient,
    HomotopyCategory.homology'Functor, Quotient.functor, CategoryTheory.Quotient.lift, Quot.liftOn,
    Quiver.Hom.unop_op]
  simp_rw [homology'.map_eq_desc'_lift_left]
  apply homology'.hom_from_ext
  simp only [Category.assoc, homology'.π'_desc'_assoc]
  slice_rhs 1 2 => erw [homology'.π'_desc']
  dsimp only [Arrow.homMk_left]
  rw [ExtComputeWithAcyclicAux₃NaturalityHelpers.helper₁]
  conv_rhs => rw [ExtComputeWithAcyclicAux₃NaturalityHelpers.helper₂]
  simp only [Category.assoc]
  slice_lhs 2 3 => erw [homology'.π'_desc']
  slice_rhs 2 3 => erw [homology'.π'_desc']
  apply homology'.hom_to_ext
  slice_lhs 2 3 => erw [homology'.lift_ι]
  slice_rhs 2 3 => erw [homology'.lift_ι]
  slice_lhs 1 2 => erw [kernel.lift_ι]
  slice_rhs 1 2 => erw [kernel.lift_ι]
  simp only [Category.assoc]
  dsimp only [extComputeWithAcyclicHomB, Functor.comp_map]
  change
    _ ≫
        (((preadditive_yoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                      homological_complex.unop_functor.rightOp).map
                  f).unop.f
            _ ≫
          _ =
      _
  slice_lhs 2 3 =>
    simp only [← HomologicalComplex.comp_f, ← unop_comp]
    simp only [Functor.comp_map, ← Functor.map_comp]
  slice_rhs 2 3 => simp only [← HomologicalComplex.comp_f, ← unop_comp, ← Functor.map_comp]
  apply Homotopy.kernel_ι_comp_comp_cokernel_π_of_homotopy
  apply Homotopy.homotopyUnopFunctorRightOpMapUnopOfHomotopy
  apply Functor.mapHomotopy
  suffices lift ((of' C₁).π ≫ of'Hom f) (of' C₂).π ≫ (of' C₂).π = (of' C₁).π ≫ of'Hom f
    by
    apply HomotopyCategory.homotopyOfEq
    convert this.symm
    · simpa only [Functor.map_comp, quotient_map_out]
    · simpa only [Functor.map_comp, quotient_map_out]
  simp

theorem extComputeWithAcyclicAux₃_isIso (B : 𝓐)
    (hC : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C.pt k)).obj B)) (i : ℤ) :
    IsIso (extComputeWithAcyclicAux₃ C B i) :=
  by
  haveI := extComputeWithAcyclicIsQuasiIsoAux C B hC i
  apply IsQuasiIso.cond

def extComputeWithAcyclic (B : 𝓐) (hC : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C.pt k)).obj B))
    (i : ℤ) :
    ((ext i).obj (op <| of' C)).obj ((single _ 0).obj B) ≅
      (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _).obj C).unop.homology' (-i) :=
  extComputeWithAcyclicAux₁ C B i ≪≫
    extComputeWithAcyclicAux₂ _ _ _ ≪≫
      haveI := extComputeWithAcyclicAux₃_isIso C B hC i
      (CategoryTheory.asIso (extComputeWithAcyclicAux₃ C B i)).symm

/-
def homological_complex.single_iso (B : 𝓐) {i j : ℤ} (h : j = i) :
  ((homological_complex.single _ (complex_shape.up ℤ) i).obj B).X j ≅ B :=
eq_to_iso (if_pos h)

/-- The morphism in `Ab` which eats a morphism of complexes `C ⟶ B[-i]`
  and returns an element of Extⁱ(C,B[0]). -/
def Ext_compute_with_acyclic_inv_eq_aux (B) (i) :
  AddCommGroup.of (C ⟶ (homological_complex.single _ _ (-i)).obj B) ⟶
  ((Ext i).obj (op (of' C))).obj ((single 𝓐 0).obj B) :=
{ toFun := λ f, (of' C).π ≫ begin
    refine (homotopy_category.quotient _ _).map _,
    refine _ ≫ (homological_complex.single_shift _ _).inv.app _,
    refine (f : C ⟶ (homological_complex.single 𝓐 (complex_shape.up ℤ) (-i)).obj B) ≫ _,
    refine eq_to_hom _,
    simp,
  end,
  map_zero' := begin
    simp only [zero_comp, functor.map_zero, comp_zero],
  end,
  map_add' := begin
    intros,
    simp only [preadditive.add_comp, functor.map_add, preadditive.comp_add],
  end }

lemma iso_equiv_inv_apply_eq_zero_cancel
  {A B C : AddCommGroup} {a : A} {f : A ⟶ B} {e : C ≅ B}
  (h : (f ≫ e.inv) a = 0) : f a = 0 :=
begin
  rw comp_apply at h,
  apply_fun e.hom at h,
  simpa using h,
end

-- Note: in the application of the below, j = -i
/-- The construction which given something in the kernel of `(Cⱼ ⟶ B) ⟶ (Cⱼ-₁ ⟶ B)`
  constructs a morphism of complexes from C to the "skyscraper complex" B[j]. -/
def kernel_yoneda_complex_to_morphism_to_single (B : 𝓐) (j : ℤ) :
-- we're going from the kernel of `(C.X j ⟶ B) ⟶ (C.X_prev j ⟶ B)` (it's actually `C.symm.X_next`)
kernel ((((preadditive_yoneda.obj B).map_homological_complex _).obj
  (homological_complex.op C)).d_from j)
  -- to the additive group of homs
  ⟶ AddCommGroup.of (
  -- from C to B j
  C ⟶ (homological_complex.single 𝓐 (complex_shape.up ℤ) j).obj B) :=
{ toFun := λ f, { f := λ k,
  if hk : k = j then
    (eq_to_hom (by rw hk) : C.X k ⟶ C.X j) ≫
    (kernel.ι ((((preadditive_yoneda.obj B).map_homological_complex _).obj
                (homological_complex.op C)).d_from j) f : C.X j ⟶ B) ≫
    (homological_complex.single_obj_X_self 𝓐 (complex_shape.up ℤ) j B).inv ≫
    eq_to_hom (by rw hk)
  else 0,
    comm' := λ i k, begin
      split_ifs with hij hkj hkj,
      { subst hij, subst hkj, simp {contextual := tt}, },
      { simp only [homological_complex.single_obj_d, comp_zero, eq_self_iff_true,
          implies_true_iff] },
      { subst hkj,
        set g := ((kernel.ι ((((preadditive_yoneda.obj B).map_homological_complex
                            (complex_shape.up ℤ).symm).obj
                  (homological_complex.op C)).d_from k)) f) with hg,
        simp only [complex_shape.up_rel, zero_comp, eq_to_hom_refl,
          homological_complex.single_obj_X_self_inv, category.comp_id, category.id_comp],
        rintro hik, clear hij,
        have := kernel.condition ((((preadditive_yoneda.obj B).map_homological_complex _).obj
          (homological_complex.op C)).d_from k),
        replace this := congr_hom this f,
        rw [comp_apply, ← hg, AddCommGroup.zero_apply] at this,
        rw ← category.assoc,
        symmetry,
        convert zero_comp,
        have foo : (complex_shape.up ℤ).symm.rel k i := hik,
        rw homological_complex.d_from_eq _ foo at this,
        exact iso_equiv_inv_apply_eq_zero_cancel this, },
      { simp only [zero_comp, comp_zero, eq_self_iff_true, implies_true_iff]},
    end },
  map_zero' := by {simp only [map_zero, homological_complex.single_obj_X_self_inv,
    eq_to_hom_trans, zero_comp, comp_zero, dite_eq_ite, if_t_t], refl },
  map_add' := by { intros, ext, simp only [map_add, homological_complex.single_obj_X_self_inv,
    eq_to_hom_trans, preadditive.add_comp, preadditive.comp_add, homological_complex.add_f_apply],
    split_ifs,
    { refl },
    { refl },
    { exact (add_zero _).symm, } } }

lemma Ext_compute_with_acylic_inv_eq (B : 𝓐)
  (hC : ∀ k, ∀ i > 0, is_zero (((Ext' i).obj (op $ C.X k)).obj B))
  (i : ℤ) :
  (Ext_compute_with_acyclic _ B hC i).inv =
  homology.desc' _ _ _
  ( kernel_yoneda_complex_to_morphism_to_single C B (-i) ≫
    Ext_compute_with_acyclic_inv_eq_aux C B i)
admit := admit

-- Replacing some `End` with `cend` fixes my bracket pair colorizer!
-- notation `cend` := category_theory.End

-/
theorem extComputeWithAcyclic_naturality (C₁ C₂ : CochainComplex 𝓐 ℤ)
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₁).IsBoundedAbove]
    [((Quotient 𝓐 (ComplexShape.up ℤ)).obj C₂).IsBoundedAbove] (B : 𝓐)
    (hC₁ : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C₁.pt k)).obj B))
    (hC₂ : ∀ k, ∀ i > 0, IsZero (((ext' i).obj (op <| C₂.pt k)).obj B)) (f : C₁ ⟶ C₂) (i : ℤ) :
    ((ext i).flip.obj ((single _ 0).obj B)).map (Quiver.Hom.op <| of'Hom f) ≫
        (extComputeWithAcyclic C₁ B hC₁ i).hom =
      (extComputeWithAcyclic C₂ B hC₂ i).hom ≫
        (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                HomologicalComplex.unopFunctor.rightOp ⋙ (homology'Functor _ _ (-i)).op).map
            f).unop :=
  by
  dsimp only [extComputeWithAcyclic, Iso.trans_hom]
  slice_lhs 1 2 => erw [extComputeWithAcyclicAux₁_naturality]
  slice_lhs 2 3 => rw [extComputeWithAcyclicAux₂_naturality]
  simp only [Category.assoc]
  congr 2
  dsimp only [Iso.symm_hom, CategoryTheory.asIso_inv]
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  symm
  apply extComputeWithAcyclicAux₃_naturality

