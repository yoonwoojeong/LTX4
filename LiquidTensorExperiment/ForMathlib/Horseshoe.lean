import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import LiquidTensorExperiment.ForMathlib.Projectives
import LiquidTensorExperiment.ForMathlib.HomologicalComplex
import LiquidTensorExperiment.ForMathlib.SnakeLemma2

#align_import for_mathlib.horseshoe

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace ShortExactSequence

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]

variable {D : Type _} [Category D] [Abelian D]

-- move this
theorem ExactOfEpiCompKernel.ι_comp_mono {C : Type u} [Category.{v} C] [Abelian C] {X Y Z W : C}
    (g : Y ⟶ Z) (h : Z ⟶ W) (f : X ⟶ kernel g) (i : kernel g ⟶ Y) (hf : Epi f) (hh : Mono h)
    (hi : i = kernel.ι g) : Exact (f ≫ i) (g ≫ h) :=
  by
  suffices exact i g by
    letI := hf; letI := hh
    exact exact_comp_mono (exact_epi_comp this)
  rw [hi]
  exact exact_kernel_ι

-- move this
theorem biprod_factors (A B : C) [Projective A] [Projective B] (E X : C) (f : A ⊞ B ⟶ X) (e : E ⟶ X)
    [Epi e] : ∃ f' : A ⊞ B ⟶ E, f' ≫ e = f :=
  ⟨biprod.desc (Projective.factorThru (biprod.inl ≫ f) e)
      (Projective.factorThru (biprod.inr ≫ f) e),
    by
    ext <;> simp only [Projective.factorThru_comp, biprod.inl_desc_assoc, biprod.inr_desc_assoc]⟩

variable (A B : ShortExactSequence C) (f : A ⟶ B)

def horseshoeBase : ShortExactSequence C :=
  ShortExactSequence.mkSplit (Projective.over A.1) (Projective.over A.3)

def horseshoeBaseπ : horseshoeBase A ⟶ A
    where
  fst := Projective.π _
  snd := biprod.desc (Projective.π _ ≫ A.f) (Projective.factorThru (Projective.π _) A.g)
  trd := Projective.π _
  sq1' := by dsimp [ShortExactSequence.horseshoeBase]; simp only [biprod.inl_desc]
  sq2' := by
    dsimp [ShortExactSequence.horseshoeBase]; apply CategoryTheory.Limits.biprod.hom_ext'
    ·
      simp only [zero_comp, Exact.w_assoc, biprod.inl_desc_assoc, Category.assoc,
        ShortExactSequence.f_comp_g, comp_zero, exact_inl_snd]
    · simp only [Projective.factorThru_comp, biprod.inr_snd_assoc, biprod.inr_desc_assoc]

instance epi_horseshoeBaseπ_1 : Epi (horseshoeBaseπ A).1 :=
  show Epi (Projective.π _) by infer_instance

instance epi_horseshoeBaseπ_3 : Epi (horseshoeBaseπ A).3 :=
  show Epi (Projective.π _) by infer_instance

attribute [local instance] Limits.HasZeroObject.zero'

instance epi_horseshoeBaseπ_2 : Epi (horseshoeBaseπ A).2 :=
  by
  let φ := horseshoe_base_π A
  have h : φ.3 ≫ (0 : A.3 ⟶ 0) = (0 : _ ⟶ 0) ≫ (0 : 0 ⟶ 0) := by simp
  refine' CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono φ.sq1' φ.sq2' h _ _ _ _ _ _ <;>
      try rw [← epi_iff_exact_zero_right] <;>
    try infer_instance
  exact A.exact'

variable {A B}

def horseshoeKer [Epi f.1] : ShortExactSequence C :=
  (SnakeInput.mkOfShortExactSequenceHom _ _ _ f).kernelSequence _
      (by
        dsimp [SnakeInput.mkOfShortExactSequenceHom,
          SnakeDiagram.mkOfShortExactSequenceHom]
        rw [SnakeDiagram.mkFunctor_map_f1]
        exact A.mono') <|
    isZero_of_iso_of_zero (isZero_zero _) (Limits.cokernel.ofEpi _).symm

@[simp]
theorem horseshoeKer_fst [Epi f.1] : (horseshoeKer f).1 = kernel f.1 :=
  rfl

@[simp]
theorem horseshoeKer_snd [Epi f.1] : (horseshoeKer f).2 = kernel f.2 :=
  rfl

@[simp]
theorem horseshoeKer_trd [Epi f.1] : (horseshoeKer f).3 = kernel f.3 :=
  rfl

def horseshoeKerι [Epi f.1] : horseshoeKer f ⟶ A
    where
  fst := kernel.ι _
  snd := kernel.ι _
  trd := kernel.ι _
  sq1' :=
    by
    dsimp [ShortExactSequence.horseshoeKer, SnakeInput.kernelSequence, SnakeInput.mkOfShortExactSequenceHom,
      SnakeDiagram.mkOfShortExactSequenceHom]
    delta kernel.map
    rw [SnakeDiagram.mkFunctor_map_f0, kernel.lift_ι]
  sq2' :=
    by
    dsimp [ShortExactSequence.horseshoeKer, SnakeInput.kernelSequence, SnakeInput.mkOfShortExactSequenceHom,
      SnakeDiagram.mkOfShortExactSequenceHom]
    delta kernel.map
    rw [SnakeDiagram.mkFunctor_map_g0, kernel.lift_ι]

theorem horseshoeKerι_fst [Epi f.1] : (horseshoeKerι f).1 = kernel.ι f.1 :=
  rfl

theorem horseshoeKerι_snd [Epi f.1] : (horseshoeKerι f).2 = kernel.ι f.2 :=
  rfl

theorem horseshoeKerι_trd [Epi f.1] : (horseshoeKerι f).3 = kernel.ι f.3 :=
  rfl

variable (A)

theorem horseshoeKerι_comp_base_π : horseshoeKerι (horseshoeBaseπ A) ≫ horseshoeBaseπ A = 0 :=
  by
  dsimp [horseshoe_ker_ι, horseshoe_base_π]
  ext1 <;> show kernel.ι _ ≫ _ = 0 <;> exact Exact.w exact_kernel_ι

noncomputable def horseshoeStep (A : ShortExactSequence C) :
    ℕ → Σ (X Y Z : ShortExactSequence C) (ι : X ⟶ Y), Y ⟶ Z
  | 0 => ⟨horseshoeKer (horseshoeBaseπ A), _, _, horseshoeKerι _, horseshoeBaseπ _⟩
  | n + 1 =>
    ⟨horseshoeKer (horseshoeBaseπ (horseshoe_step n).1), _, _, horseshoeKerι _, horseshoeBaseπ _⟩

@[reassoc]
theorem horseshoeStep_comp_eq_zero :
    ∀ n, (horseshoeStep A n).2.2.2.1 ≫ (horseshoeStep A n).2.2.2.2 = 0
  | 0 => horseshoeKerι_comp_base_π _
  | n + 1 => horseshoeKerι_comp_base_π _

theorem step_fst_mono (n : ℕ) : Mono (horseshoeStep A n).2.2.2.1.1 :=
  by
  cases n
  · dsimp [horseshoe_step, horseshoe_ker_ι]
    infer_instance
  · dsimp [horseshoe_step]
    cases n
    --Why do I have to do this again?!
    · rw [horseshoe_ker_ι_fst]
      infer_instance
    · rw [horseshoe_ker_ι_fst]
      infer_instance

theorem step_snd_mono (n : ℕ) : Mono (horseshoeStep A n).2.2.2.1.2 :=
  by
  cases n
  · dsimp [horseshoe_step, horseshoe_ker_ι]
    infer_instance
  · dsimp [horseshoe_step]
    cases n
    --Why do I have to do this again?!
    · rw [horseshoe_ker_ι_snd]
      infer_instance
    · rw [horseshoe_ker_ι_snd]
      infer_instance

theorem step_trd_mono (n : ℕ) : Mono (horseshoeStep A n).2.2.2.1.3 :=
  by
  cases n
  · dsimp [horseshoe_step, horseshoe_ker_ι]
    infer_instance
  · dsimp [horseshoe_step]
    cases n
    --Why do I have to do this again?!
    · rw [horseshoe_ker_ι_trd]
      infer_instance
    · rw [horseshoe_ker_ι_trd]
      infer_instance

def horseshoeObj (n : ℕ) :=
  (horseshoeStep A n).2.1

def horseshoeD (n : ℕ) : horseshoeObj A (n + 1) ⟶ horseshoeObj A n :=
  (horseshoeStep A (n + 1)).2.2.2.2 ≫
    eqToHom (by dsimp [horseshoe_step]; rfl) ≫ (horseshoeStep A n).2.2.2.1

theorem horseshoeD_d (n : ℕ) : horseshoeD A (n + 1) ≫ horseshoeD A n = 0 :=
  by
  dsimp [ShortExactSequence.horseshoeD, horseshoe_ker_ι]
  simp only [Category.id_comp, Category.assoc, comp_zero, zero_comp,
    ShortExactSequence.horseshoeStep_comp_eq_zero_assoc]

def horseshoe (A : ShortExactSequence C) : ChainComplex (ShortExactSequence C) ℕ :=
  ChainComplex.of (horseshoeObj A) (horseshoeD A) (horseshoeD_d A)

variable (A)

def horseshoeπ : (horseshoe A).pt 0 ⟶ A :=
  horseshoeBaseπ _

theorem horseshoe_d_π : (horseshoe A).d 1 0 ≫ horseshoeπ A = 0 :=
  by
  dsimp [horseshoe]
  erw [ChainComplex.of_d]
  dsimp [ShortExactSequence.horseshoeD, horseshoe_π, horseshoe_step]
  simp only [Category.id_comp, Category.assoc, comp_zero, zero_comp,
    ShortExactSequence.horseshoeStep_comp_eq_zero_assoc, horseshoe_ker_ι_comp_base_π]

def horseshoeToSingle₁ :=
  (ChainComplex.toSingle₀Equiv ((HomologicalComplex.fst C).obj (horseshoe A)) A.1).symm
    ⟨(ShortExactSequence.fst C).map (horseshoeπ A),
      by
      have := horseshoe_d_π A; apply_fun fun f => (ShortExactSequence.fst C).map f at this 
      rwa [Functor.map_comp, Functor.map_zero] at this ⟩

def horseshoeToSingle₂ :=
  (ChainComplex.toSingle₀Equiv ((HomologicalComplex.snd C).obj (horseshoe A)) A.2).symm
    ⟨(ShortExactSequence.snd C).map (horseshoeπ A),
      by
      have := horseshoe_d_π A; apply_fun fun f => (ShortExactSequence.snd C).map f at this 
      rwa [Functor.map_comp, Functor.map_zero] at this ⟩

def horseshoeToSingle₃ :=
  (ChainComplex.toSingle₀Equiv ((HomologicalComplex.trd C).obj (horseshoe A)) A.3).symm
    ⟨(ShortExactSequence.trd C).map (horseshoeπ A),
      by
      have := horseshoe_d_π A; apply_fun fun f => (ShortExactSequence.trd C).map f at this 
      rwa [Functor.map_comp, Functor.map_zero] at this ⟩

theorem horseshoe_exact₁ (A : ShortExactSequence C) (n : ℕ) :
    Exact (((HomologicalComplex.fst C).obj (horseshoe A)).d (n + 2) (n + 1))
      (((HomologicalComplex.fst C).obj (horseshoe A)).d (n + 1) n) :=
  by
  dsimp [horseshoe_to_single₁]
  erw [ChainComplex.of_d, ChainComplex.of_d]
  dsimp [ShortExactSequence.horseshoeD, horseshoe_step]
  set f := horseshoe_base_π (horseshoe_step A n).1
  set g := (horseshoe_step A n).2.2.2.1
  cases n <;>
    convert
      exact_of_epi_comp_kernel.ι_comp_mono f.1 _ (horseshoe_base_π (ShortExactSequence.horseshoeKer f)).1 _
        inferInstance _ _ using
      1
  · simp [step_fst_mono]
  · simpa
  · simp [step_fst_mono]
  · simpa

theorem horseshoe_exact₂ (A : ShortExactSequence C) (n : ℕ) :
    Exact (((HomologicalComplex.snd C).obj (horseshoe A)).d (n + 2) (n + 1))
      (((HomologicalComplex.snd C).obj (horseshoe A)).d (n + 1) n) :=
  by
  dsimp [horseshoe_to_single₂]
  erw [ChainComplex.of_d, ChainComplex.of_d]
  dsimp [ShortExactSequence.horseshoeD, horseshoe_step]
  set f := horseshoe_base_π (horseshoe_step A n).1
  set g := (horseshoe_step A n).2.2.2.1
  cases n <;>
    convert
      exact_of_epi_comp_kernel.ι_comp_mono f.2 _ (horseshoe_base_π (ShortExactSequence.horseshoeKer f)).2 _
        inferInstance _ _ using
      1
  · simp [step_snd_mono]
  · simpa
  · simp [step_snd_mono]
  · simpa

theorem horseshoe_exact₃ (A : ShortExactSequence C) (n : ℕ) :
    Exact (((HomologicalComplex.trd C).obj (horseshoe A)).d (n + 2) (n + 1))
      (((HomologicalComplex.trd C).obj (horseshoe A)).d (n + 1) n) :=
  by
  dsimp [horseshoe_to_single₃]
  erw [ChainComplex.of_d, ChainComplex.of_d]
  dsimp [ShortExactSequence.horseshoeD, horseshoe_step]
  set f := horseshoe_base_π (horseshoe_step A n).1
  set g := (horseshoe_step A n).2.2.2.1
  cases n <;>
    convert
      exact_of_epi_comp_kernel.ι_comp_mono f.3 _ (horseshoe_base_π (ShortExactSequence.horseshoeKer f)).3 _
        inferInstance _ _ using
      1
  · simp [step_trd_mono]
  · simpa
  · simp [step_trd_mono]
  · simpa

theorem horseshoeIsProjectiveResolution₁ (A : ShortExactSequence C) :
    ChainComplex.IsProjectiveResolution ((HomologicalComplex.fst C).obj (horseshoe A)) A.1
      (horseshoeToSingle₁ A) :=
  { Projective := by rintro (_ | n) <;> · show projective (Projective.over _); infer_instance
    exact₀ := by
      dsimp [horseshoe_to_single₁, ChainComplex.toSingle₀Equiv, horseshoe_π]
      erw [ChainComplex.of_d]
      dsimp [ShortExactSequence.horseshoeD, horseshoe_step]
      rw [Category.id_comp, ← ShortExactSequence.comp_fst]
      refine' Abelian.Pseudoelement.exact_of_pseudo_exact _ _ ⟨fun a => _, fun a ha => _⟩
      ·
        rw [← Abelian.Pseudoelement.comp_apply, ← ShortExactSequence.comp_fst, Category.assoc,
          horseshoe_ker_ι_comp_base_π, comp_zero, ShortExactSequence.hom_zero_fst,
          Abelian.Pseudoelement.zero_apply]
      · obtain ⟨b, hb⟩ := IsSnakeInput.exists_of_exact exact_kernel_ι _ ha
        obtain ⟨c, hc⟩ :=
          Abelian.Pseudoelement.pseudo_surjective_of_epi (horseshoe_base_π (ShortExactSequence.horseshoeKer _)).1 b
        refine' ⟨c, _⟩
        rw [ShortExactSequence.comp_fst, Abelian.Pseudoelement.comp_apply, hc, ← hb]
        rfl
    exact := fun n => horseshoe_exact₁ A n
    Epi := show Epi (Projective.π _) from inferInstance }

theorem horseshoeIsProjectiveResolution₂ (A : ShortExactSequence C) :
    ChainComplex.IsProjectiveResolution ((HomologicalComplex.snd C).obj (horseshoe A)) A.2
      (horseshoeToSingle₂ A) :=
  { Projective := by
      rintro (_ | n) <;>
        · show projective (Projective.over _ ⊞ Projective.over _)
          infer_instance
    exact₀ := by
      dsimp [horseshoe_to_single₂, ChainComplex.toSingle₀Equiv, horseshoe_π]
      erw [ChainComplex.of_d]
      dsimp [ShortExactSequence.horseshoeD, horseshoe_step]
      rw [Category.id_comp, ← ShortExactSequence.comp_snd]
      refine' Abelian.Pseudoelement.exact_of_pseudo_exact _ _ ⟨fun a => _, fun a ha => _⟩
      ·
        rw [← Abelian.Pseudoelement.comp_apply, ← ShortExactSequence.comp_snd, Category.assoc,
          horseshoe_ker_ι_comp_base_π, comp_zero, ShortExactSequence.hom_zero_snd,
          Abelian.Pseudoelement.zero_apply]
      · obtain ⟨b, hb⟩ := IsSnakeInput.exists_of_exact exact_kernel_ι _ ha
        obtain ⟨c, hc⟩ :=
          Abelian.Pseudoelement.pseudo_surjective_of_epi (horseshoe_base_π (ShortExactSequence.horseshoeKer _)).2 b
        refine' ⟨c, _⟩
        rw [ShortExactSequence.comp_snd, Abelian.Pseudoelement.comp_apply, hc, ← hb]
        rfl
    exact := fun n => horseshoe_exact₂ A n
    Epi := show Epi (horseshoeBaseπ _).2 from inferInstance }

theorem horseshoeIsProjectiveResolution₃ (A : ShortExactSequence C) :
    ChainComplex.IsProjectiveResolution ((HomologicalComplex.trd C).obj (horseshoe A)) A.3
      (horseshoeToSingle₃ A) :=
  { Projective := by rintro (_ | n) <;> · show projective (Projective.over _); infer_instance
    exact₀ := by
      dsimp [horseshoe_to_single₃, ChainComplex.toSingle₀Equiv, horseshoe_π]
      erw [ChainComplex.of_d]
      dsimp [ShortExactSequence.horseshoeD, horseshoe_step]
      rw [Category.id_comp, ← ShortExactSequence.comp_trd]
      refine' Abelian.Pseudoelement.exact_of_pseudo_exact _ _ ⟨fun a => _, fun a ha => _⟩
      ·
        rw [← Abelian.Pseudoelement.comp_apply, ← ShortExactSequence.comp_trd, Category.assoc,
          horseshoe_ker_ι_comp_base_π, comp_zero, ShortExactSequence.hom_zero_trd,
          Abelian.Pseudoelement.zero_apply]
      · obtain ⟨b, hb⟩ := IsSnakeInput.exists_of_exact exact_kernel_ι _ ha
        obtain ⟨c, hc⟩ :=
          Abelian.Pseudoelement.pseudo_surjective_of_epi (horseshoe_base_π (ShortExactSequence.horseshoeKer _)).3 b
        refine' ⟨c, _⟩
        rw [ShortExactSequence.comp_trd, Abelian.Pseudoelement.comp_apply, hc, ← hb]
        rfl
    exact := fun n => horseshoe_exact₃ A n
    Epi := show Epi (Projective.π _) from inferInstance }

theorem horseshoe_split (A : ShortExactSequence C) (n : ℕ) : ((horseshoe A).pt n).split := by
  cases n <;>
    exact ⟨biprod.fst, biprod.inr, biprod.inl_fst, biprod.inr_snd, biprod.inr_fst, biprod.total⟩

theorem horseshoe_f_comp_to_single₂_f (A : ShortExactSequence C) (i : ℕ) :
    ((horseshoe A).pt i).f ≫ (horseshoeToSingle₂ A).f i =
      (horseshoeToSingle₁ A).f i ≫ ((ChainComplex.single₀ C).map A.f).f i :=
  by
  cases i
  · dsimp [horseshoe_to_single₂, horseshoe_to_single₁, horseshoe, ShortExactSequence.horseshoeObj, horseshoe_step,
      ShortExactSequence.horseshoeBase, horseshoe_π, horseshoe_base_π, ChainComplex.toSingle₀Equiv]
    simp
  · dsimp [horseshoe_to_single₂, horseshoe_to_single₁, horseshoe, ShortExactSequence.horseshoeObj, horseshoe_step,
      ShortExactSequence.horseshoeBase, horseshoe_π, horseshoe_base_π, ChainComplex.toSingle₀Equiv]
    simp

theorem horseshoe_g_comp_to_single₃_f (A : ShortExactSequence C) (i : ℕ) :
    ((horseshoe A).pt i).g ≫ (horseshoeToSingle₃ A).f i =
      (horseshoeToSingle₂ A).f i ≫ ((ChainComplex.single₀ C).map A.g).f i :=
  by
  cases i
  · dsimp [horseshoe_to_single₂, horseshoe_to_single₃, ChainComplex.toSingle₀Equiv, horseshoe,
      ShortExactSequence.horseshoeObj, horseshoe_π, horseshoe_step, ShortExactSequence.horseshoeBase, horseshoe_base_π]
    ext
    · simp
    · simp
  · dsimp [horseshoe_to_single₂, horseshoe_to_single₃, horseshoe, ShortExactSequence.horseshoeObj, horseshoe_step,
      ShortExactSequence.horseshoeBase, horseshoe_π, horseshoe_base_π, ChainComplex.toSingle₀Equiv]
    simp

end ShortExactSequence

