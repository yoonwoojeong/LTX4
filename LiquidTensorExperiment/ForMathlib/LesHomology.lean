import Mathlib.Data.Matrix.Notation
import LiquidTensorExperiment.ForMathlib.SnakeLemma2
import LiquidTensorExperiment.ForMathlib.ShortExactSequence

#align_import for_mathlib.les_homology

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

theorem Preadditive.exact_of_iso_of_exact' {D : Type _} [Category D] [Abelian D]
    {A₁ B₁ C₁ A₂ B₂ C₂ : D} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁) (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂)
    (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂) (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom)
    (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom) (h : Exact f₁ g₁) : Exact f₂ g₂ :=
  Preadditive.exact_of_iso_of_exact f₁ g₁ f₂ g₂ (Arrow.isoMk α β hsq₁) (Arrow.isoMk β γ hsq₂) rfl h

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {ι : Type _} {c : ComplexShape ι}

def modBoundaries (A : HomologicalComplex C c) (j : ι) : C :=
  cokernel (A.boundaries j).arrow

def modBoundariesMap {A B : HomologicalComplex C c} (f : A ⟶ B) (j : ι) :
    A.modBoundaries j ⟶ B.modBoundaries j :=
  cokernel.map _ _ (boundariesMap f j) (f.f j) <| by rw [image_subobject_map_arrow]; rfl

@[simps]
def modBoundariesFunctor (j : ι) : HomologicalComplex C c ⥤ C
    where
  obj A := A.modBoundaries j
  map A B f := modBoundariesMap f j
  map_id' A := by
    delta mod_boundaries mod_boundaries_map cokernel.map; ext
    show cokernel.π (A.boundaries j).arrow ≫ _ = cokernel.π (A.boundaries j).arrow ≫ _
    simp only [cokernel.π_desc, category.id_comp, id_f, category.comp_id]
  map_comp' X Y Z f g :=
    by
    delta mod_boundaries mod_boundaries_map cokernel.map; ext
    show cokernel.π (X.boundaries j).arrow ≫ _ = cokernel.π (X.boundaries j).arrow ≫ _
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc]

-- generalize to chain complexes over other shapes
@[simps]
def homologyToModBoundaries (i : ι) : homology'Functor C c i ⟶ modBoundariesFunctor i
    where
  app A :=
    cokernel.map _ _ (𝟙 _) (A.cycles' i).arrow
      (by simp only [category.id_comp, imageToKernel_arrow])
  naturality' A B f := by
    ext
    simp only [homology'Functor_map, mod_boundaries_functor_map, homology'.π_map_assoc]
    delta mod_boundaries_map homology'.π cokernel.map cycles
    simp only [cokernel.π_desc, cokernel.π_desc_assoc, comp_f, category.assoc,
      kernel_subobject_map_arrow_assoc, hom.sq_from_left]

variable (A : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)

def deltaToBoundaries : A.pt i ⟶ A.boundaries j :=
  (xPrevIso A hij).inv ≫ factorThruImageSubobject _

instance deltaToBoundaries_epi : Epi (deltaToBoundaries A i j hij) :=
  epi_comp _ _

@[ext]
theorem boundaries.ext' {X : C} (f g : (boundaries A j : C) ⟶ X)
    (h : factorThruImageSubobject _ ≫ f = factorThruImageSubobject _ ≫ g) : f = g := by
  rwa [cancel_epi (factor_thru_image_subobject (A.d_to j))] at h 

@[simp, reassoc]
theorem deltaToBoundaries_comp_arrow :
    deltaToBoundaries A i j hij ≫ (boundaries A j).arrow = A.d i j := by
  rw [delta_to_boundaries, category.assoc, image_subobject_arrow_comp, X_prev_iso_comp_d_to]

@[simp, reassoc]
theorem boundaries_arrow_comp_deltaToBoundaries :
    (boundaries _ i).arrow ≫ deltaToBoundaries A i j hij = 0 :=
  by
  ext
  simp only [image_subobject_arrow_comp_assoc, category.assoc, delta_to_boundaries_comp_arrow,
    comp_zero, zero_comp, ← d_from_comp_X_next_iso A hij, reassoc_of (d_to_comp_d_from A)]

def deltaToCycles : A.pt i ⟶ A.cycles' j :=
  deltaToBoundaries _ i j hij ≫ boundariesToCycles' _ _

@[simp, reassoc]
theorem deltaToCycles_comp_arrow : deltaToCycles A i j hij ≫ (cycles' A j).arrow = A.d i j := by
  rw [delta_to_cycles, category.assoc, imageToKernel_arrow, delta_to_boundaries_comp_arrow]

@[simp, reassoc]
theorem boundaries_arrow_comp_deltaToCycles :
    (boundaries _ _).arrow ≫ deltaToCycles A i j hij = 0 := by
  rw [delta_to_cycles, ← category.assoc, boundaries_arrow_comp_delta_to_boundaries, zero_comp]

@[simps]
def modBoundariesToCycles : modBoundariesFunctor i ⟶ cycles'Functor C c j
    where
  app A := cokernel.desc _ (deltaToCycles _ i j hij) (boundaries_arrow_comp_deltaToCycles _ i j hij)
  naturality' A B f := by
    ext; show cokernel.π _ ≫ _ = cokernel.π _ ≫ _
    simp only [homology'Functor_map, mod_boundaries_functor_map, homology'.π_map_assoc]
    delta mod_boundaries_map homology'.π cokernel.map
    simp only [category.assoc, cycles'Functor_map, cycles'Map_arrow, hom.comm,
      cokernel.π_desc_assoc, delta_to_cycles_comp_arrow_assoc, delta_to_cycles_comp_arrow]

@[simps]
def cyclesToHomology : cycles'Functor C c i ⟶ homology'Functor C c i
    where
  app A := cokernel.π _
  naturality' A B f := by
    simp only [cycles'Functor_map, homology'Functor_map]
    delta homology'.map
    rw [cokernel.π_desc]; rfl

open scoped ZeroObject

theorem Option.eq_none_or_eq_some {α : Type _} : ∀ o : Option α, o = none ∨ ∃ a, o = some a
  | Option.none => Or.inl rfl
  | Option.some a => Or.inr ⟨a, rfl⟩

theorem exact_next {A₁ A₂ A₃ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (i j : ι)
    (hij : c.Rel i j) (h : Exact (f.f j) (g.f j)) : Exact (f.next i) (g.next i) := by
  refine'
      Preadditive.exact_of_iso_of_exact' (f.f j) (g.f j) _ _ (X_next_iso A₁ hij).symm
        (X_next_iso A₂ hij).symm (X_next_iso A₃ hij).symm _ _ h <;>
    simp only [hom.next_eq _ hij, iso.symm_hom, iso.inv_hom_id_assoc]

theorem exact_next' {A₁ A₂ A₃ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (i : ι)
    (h : ∀ n, Exact (f.f n) (g.f n)) : Exact (f.next i) (g.next i) :=
  h _

theorem exact_prev {A₁ A₂ A₃ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (i j : ι)
    (hij : c.Rel i j) (h : Exact (f.f i) (g.f i)) : Exact (f.prev j) (g.prev j) := by
  refine'
      Preadditive.exact_of_iso_of_exact' (f.f i) (g.f i) _ _ (X_prev_iso A₁ hij).symm
        (X_prev_iso A₂ hij).symm (X_prev_iso A₃ hij).symm _ _ h <;>
    simp only [hom.prev_eq _ hij, iso.symm_hom, iso.inv_hom_id_assoc]

theorem exact_prev' {A₁ A₂ A₃ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (j : ι)
    (h : ∀ n, Exact (f.f n) (g.f n)) : Exact (f.prev j) (g.prev j) :=
  h _

theorem mono_next {A₁ A₂ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (i j : ι) (hij : c.Rel i j)
    [Mono (f.f j)] : Mono (f.next i) :=
  by
  rw [hom.next_eq _ hij]
  apply (config := { instances := false }) mono_comp
  · infer_instance
  · apply mono_comp

instance mono_next' {A₁ A₂ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (i : ι) [∀ n, Mono (f.f n)] :
    Mono (f.next i) := by apply_assumption

theorem epi_prev {A₁ A₂ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (i j : ι) (hij : c.Rel i j)
    [Epi (f.f i)] : Epi (f.prev j) := by
  rw [hom.prev_eq _ hij]
  apply (config := { instances := false }) epi_comp
  · infer_instance
  · apply epi_comp

instance epi_prev' {A₁ A₂ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (j : ι) [∀ n, Epi (f.f n)] :
    Epi (f.prev j) := by apply_assumption

instance {A B : HomologicalComplex C c} (f : A ⟶ B) [∀ n, Epi (f.f n)] (i : ι) :
    Epi (boundariesMap f i) := by
  let sq := hom.sq_to f i
  haveI : epi sq.left := by dsimp; infer_instance
  apply (config := { instances := false }) epi_of_epi (factor_thru_image_subobject _)
  suffices
    factor_thru_image_subobject (A.d_to i) ≫ boundariesMap f i =
      sq.left ≫ factor_thru_image_subobject (B.d_to i)
    by rw [this]; apply epi_comp
  ext
  simp only [category.assoc, image_subobject_map_arrow, hom.sq_to_right,
    image_subobject_arrow_comp_assoc, hom.sq_to_left, image_subobject_arrow_comp, hom.comm_to]

theorem exact_kernelSubobject_arrow (A B : C) (f : A ⟶ B) : Exact (kernelSubobject f).arrow f := by
  rw [← kernel_subobject_arrow, exact_iso_comp]; exact exact_kernel_ι

theorem exact_cycles'_arrow (A : HomologicalComplex C c) (i : ι) :
    Exact (cycles' A i).arrow (dFrom A i) :=
  exact_kernelSubobject_arrow _ _ _

theorem exact_cycles'Map {A₁ A₂ A₃ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (j : ι) : Exact (cycles'Map f j) (cycles'Map g j) :=
  by
  have sq₁ : d_from A₁ j ≫ f.next j = f.f j ≫ d_from A₂ j := (hom.comm_from _ _).symm
  have sq₂ : d_from A₂ j ≫ g.next j = g.f j ≫ d_from A₃ j := (hom.comm_from _ _).symm
  suffices S :
    snake (↑(cycles A₁ j)) (↑(cycles A₂ j)) (↑(cycles A₃ j)) (A₁.X j) (A₂.X j) (A₃.X j) _ _ _ _ _ _
      (cycles'Map f j) (cycles'Map g j) (cycles _ j).arrow (cycles _ j).arrow (cycles _ j).arrow
      (f.f j) (g.f j) (A₁.d_from j) (A₂.d_from j) (A₃.d_from j) (f.next j) (g.next j)
      (cokernel.π <| A₁.d_from j) (cokernel.π <| A₂.d_from j) (cokernel.π <| A₃.d_from j)
      (cokernel.map _ _ _ _ sq₁) (cokernel.map _ _ _ _ sq₂)
  · exact S.six_term_exact_seq.pair
  have hfg_epi := fun j => (hfg j).Epi
  have hfg_mono := fun j => (hfg j).mono
  skip
  fconstructor
  · exact (hfg j).exact
  · exact exact_next' _ _ _ fun i => (hfg i).exact
  · refine' (exact_cycles_arrow _ _).cons (abelian.exact_cokernel _).ExactSeq
  · refine' (exact_cycles_arrow _ _).cons (abelian.exact_cokernel _).ExactSeq
  · refine' (exact_cycles_arrow _ _).cons (abelian.exact_cokernel _).ExactSeq
  · rw [cycles'Map_arrow]
  · rw [cycles'Map_arrow]
  · exact sq₁
  · exact sq₂
  · apply cokernel.π_desc
  · apply cokernel.π_desc

variable {A₁ A₂ A₃ : HomologicalComplex C c} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)

variable (hfg : ∀ n, ShortExact (f.f n) (g.f n))

theorem mono_cycles'Map (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (i : ι) : Mono (cycles'Map f i) :=
  by
  apply (config := { instances := false }) mono_of_mono _ (subobject.arrow _)
  rw [cycles'Map_arrow]
  haveI : mono (f.f i) := (hfg i).mono
  apply mono_comp

@[simp]
theorem imageSubobject_arrow {X : C} (S : Subobject X) : imageSubobject S.arrow = S :=
  by
  delta image_subobject
  ext
  swap
  · exact limits.image_mono_iso_source _
  · simp

@[simp]
theorem KernelSubobjectCokernel.π {X : C} (S : Subobject X) :
    kernelSubobject (cokernel.π S.arrow) = S :=
  by
  delta kernel_subobject
  ext
  swap
  · exact (abelian.image_iso_image _).trans (limits.image_mono_iso_source _)
  · simp

theorem Exact.congr {X₁ X₂ Y Z₁ Z₂ : C} (f₁ : X₁ ⟶ Y) (g₁ : Y ⟶ Z₁) (f₂ : X₂ ⟶ Y) (g₂ : Y ⟶ Z₂)
    (h : Exact f₁ g₁) (him : imageSubobject f₁ = imageSubobject f₂)
    (hker : kernelSubobject g₁ = kernelSubobject g₂) : Exact f₂ g₂ := by
  rwa [abelian.exact_iff_image_eq_kernel, ← him, ← hker, ← abelian.exact_iff_image_eq_kernel]

theorem exact_column :
    ExactSeq C [kernel.ι (A.dTo j), A.dTo j, cokernel.π (A.boundaries j).arrow] :=
  exact_kernel_ι.cons <|
    (Exact.congr (boundaries A j).arrow _ _ _ (Abelian.exact_cokernel _) (imageSubobject_arrow _)
        rfl).ExactSeq

theorem exact_modBoundariesMap (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (j : ι) :
    Exact (modBoundariesMap f j) (modBoundariesMap g j) :=
  by
  have sq1 : A₁.d_to j ≫ f.f j = f.prev j ≫ A₂.d_to j := (f.comm_to _).symm
  have sq2 : A₂.d_to j ≫ g.f j = g.prev j ≫ A₃.d_to j := (g.comm_to _).symm
  suffices S :
    snake
      (-- the objects
        kernel
        _)
      (kernel _) (kernel _) (A₁.X_prev j) (A₂.X_prev j) (A₃.X_prev j) (A₁.X j) (A₂.X j) (A₃.X j)
      (mod_boundaries _ j) (mod_boundaries _ j) (mod_boundaries _ j)
      (-- the morphisms
        kernel.map
        _ _ _ _ sq1)
      (kernel.map _ _ _ _ sq2) (kernel.ι <| A₁.d_to j) (kernel.ι <| A₂.d_to j)
      (kernel.ι <| A₃.d_to j) (f.prev j) (g.prev j) (A₁.d_to j) (A₂.d_to j) (A₃.d_to j) (f.f j)
      (g.f j) (cokernel.π _) (cokernel.π _) (cokernel.π _) (mod_boundaries_map f j)
      (mod_boundaries_map g j)
  · exact (S.six_term_exact_seq.drop 3).pair
  have hfg_epi := fun n => (hfg n).Epi
  have hfg_mono := fun n => (hfg n).mono
  skip
  fconstructor
  · exact exact_prev' _ _ _ fun n => (hfg n).exact
  · exact (hfg j).exact
  · apply exact_column
  · apply exact_column
  · apply exact_column
  · simp
  · simp
  · exact sq1
  · exact sq2
  · simp [mod_boundaries_map]
  · simp [mod_boundaries_map]

theorem epi_modBoundariesMap (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (i : ι) :
    Epi (modBoundariesMap g i) :=
  by
  apply (config := { instances := false }) epi_of_epi (cokernel.π _)
  haveI : epi (g.f i) := (hfg i).Epi
  have : cokernel.π _ ≫ mod_boundaries_map g i = g.f i ≫ cokernel.π _ := cokernel.π_desc _ _ _
  rw [this]
  apply epi_comp

theorem mono_homologyToModBoundaries : Mono ((homologyToModBoundaries i).app A) :=
  Cokernel.map_mono_of_epi_of_mono (boundaries A i) (cycles' A i) (boundaries A i) (A.pt i) _ _ _ _
    _

variable {C}

@[simp]
theorem imageSubobject_comp_eq_of_epi {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g :=
  by
  delta image_subobject
  haveI : is_iso (image.pre_comp f g) := is_iso_of_mono_of_epi _
  ext; swap
  · exact as_iso (image.pre_comp f g)
  · simp only [as_iso_hom, image.pre_comp_ι]

@[simp]
theorem kernelSubobject_comp_eq_of_mono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    kernelSubobject (f ≫ g) = kernelSubobject f :=
  by
  delta kernel_subobject
  ext; swap
  · exact kernel_comp_mono f g
  · simp only [kernel_comp_mono_hom, kernel.lift_ι]

theorem exact_cycles'_arrow_deltaToCycles : Exact (A.cycles' i).arrow (deltaToCycles A i j hij) :=
  by
  rw [CategoryTheory.Abelian.exact_iff_image_eq_kernel]
  dsimp [delta_to_cycles, delta_to_boundaries]
  simp only [image_subobject_arrow, kernel_subobject_comp_eq_of_mono]
  delta cycles
  let g : ↑(A.boundaries j) ⟶ X_next A i := (A.boundaries j).arrow ≫ (X_next_iso _ hij).inv
  haveI : mono g := mono_comp _ _
  suffices aux : delta_to_boundaries _ i j hij ≫ g = d_from A i
  · simp_rw [← aux, kernel_subobject_comp_eq_of_mono]; rfl
  simp only [delta_to_boundaries_comp_arrow_assoc, iso.comp_inv_eq, d_from_comp_X_next_iso]

theorem exact_homologyToModBoundaries_to_cycles :
    Exact ((homologyToModBoundaries i).app A) ((modBoundariesToCycles i j hij).app A) :=
  by
  let φ : homology' A i ⟶ mod_boundaries A i :=
    limits.cokernel.desc _ ((kernel_subobject _).arrow ≫ cokernel.π _) (by simp)
  suffices S :
    snake (0 : C) 0 0 (A.boundaries i) (boundaries A i) 0 (A.cycles i) (A.X i) (A.cycles j)
      (homology' A i) (mod_boundaries A i) (A.cycles j) 0 0 0 0 0 (𝟙 _) 0 (boundaries_to_cycles _ _)
      (A.boundaries i).arrow 0 (A.cycles i).arrow (delta_to_cycles _ i j hij) (homology'.π _ _ _)
      (cokernel.π _) (𝟙 _) φ ((mod_boundaries_to_cycles i j hij).app A)
  · exact (S.six_term_exact_seq.drop 3).pair
  letI : exact (cycles A i).arrow (delta_to_cycles A i j hij) :=
    exact_cycles_arrow_delta_to_cycles _ i j hij
  letI : epi (homology'.π (d_to A i) (d_from A i) (A.d_to_comp_d_from i)) := coequalizer.π_epi
  fconstructor
  · rw [← epi_iff_exact_zero_right]; infer_instance
  · apply exact_cycles_arrow_delta_to_cycles
  · exact (CategoryTheory.exact_zero_mono _).cons (abelian.exact_cokernel _).ExactSeq
  · exact (CategoryTheory.exact_zero_mono _).cons (abelian.exact_cokernel _).ExactSeq
  · exact (CategoryTheory.exact_zero_mono _).cons (exact_zero_left_of_mono _).ExactSeq
  · simp only [zero_comp]
  · simp only [zero_comp]
  · simp only [imageToKernel_arrow, category.id_comp]
  · simp only [boundaries_arrow_comp_delta_to_cycles, zero_comp]
  · dsimp [homology'.π]; simp only [cokernel.π_desc]
  · simp only [mod_boundaries_to_cycles_app, cokernel.π_desc, category.comp_id]

theorem exact_modBoundariesToCycles_to_homology :
    Exact ((modBoundariesToCycles i j hij).app A) ((cyclesToHomology j).app A) :=
  by
  refine' exact.congr (boundaries_to_cycles _ _) _ _ _ _ _ rfl
  · exact abelian.exact_cokernel _
  · simp only [mod_boundaries_to_cycles_app]
    delta delta_to_cycles
    rw [← image_subobject_comp_eq_of_epi (cokernel.π _)]
    simp only [cokernel.π_desc, image_subobject_comp_eq_of_epi]

theorem epi_cyclesToHomology : Epi ((cyclesToHomology j).app A) :=
  coequalizer.π_epi

theorem exactSeq_column :
    ExactSeq C
      [(homologyToModBoundaries i).app A₁, (modBoundariesToCycles i j hij).app A₁,
        (cyclesToHomology j).app A₁] :=
  (exact_homologyToModBoundaries_to_cycles _ _ _ _).cons
    (exact_modBoundariesToCycles_to_homology _ _ _ _).ExactSeq

theorem snake (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (i j : ι) (hij : c.Rel i j) :
    Snake
      (-- the objects
          A₁.homology'
        i)
      (A₂.homology' i) (A₃.homology' i) (A₁.modBoundaries i) (A₂.modBoundaries i)
      (A₃.modBoundaries i) (A₁.cycles' j) (A₂.cycles' j) (A₃.cycles' j) (A₁.homology' j)
      (A₂.homology' j) (A₃.homology' j)
      ((-- the morphisms
            homology'Functor
            _ _ i).map
        f)
      ((homology'Functor _ _ i).map g) ((homologyToModBoundaries i).app A₁)
      ((homologyToModBoundaries i).app A₂) ((homologyToModBoundaries i).app A₃)
      ((modBoundariesFunctor i).map f) ((modBoundariesFunctor i).map g)
      ((modBoundariesToCycles i j hij).app A₁) ((modBoundariesToCycles i j hij).app A₂)
      ((modBoundariesToCycles i j hij).app A₃) ((cycles'Functor _ _ j).map f)
      ((cycles'Functor _ _ j).map g) ((cyclesToHomology j).app A₁) ((cyclesToHomology j).app A₂)
      ((cyclesToHomology j).app A₃) ((homology'Functor _ _ j).map f)
      ((homology'Functor _ _ j).map g) :=
  { row_exact₁ := exact_modBoundariesMap f g hfg _
    row_exact₂ := exact_cycles'Map f g hfg _
    row_epi := epi_modBoundariesMap f g hfg _
    row_mono := mono_cycles'Map f g hfg _
    col_exact_a := exactSeq_column _ _ _
    col_exact_b := exactSeq_column _ _ _
    col_exact_c := exactSeq_column _ _ _
    col_mono_a := mono_homologyToModBoundaries _ _
    col_mono_b := mono_homologyToModBoundaries _ _
    col_mono_c := mono_homologyToModBoundaries _ _
    col_epi_a := epi_cyclesToHomology _ _
    col_epi_b := epi_cyclesToHomology _ _
    col_epi_c := epi_cyclesToHomology _ _
    sq_a₀ := ((homologyToModBoundaries _).naturality _).symm
    sq_b₀ := ((homologyToModBoundaries _).naturality _).symm
    sq_a₁ := ((modBoundariesToCycles _ _ _).naturality _).symm
    sq_b₁ := ((modBoundariesToCycles _ _ _).naturality _).symm
    sq_a₂ := ((cyclesToHomology _).naturality _).symm
    sq_b₂ := ((cyclesToHomology _).naturality _).symm }

def δ (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (i j : ι) (hij : c.Rel i j) :
    homology' A₃ i ⟶ homology' A₁ j :=
  (snake f g hfg i j hij).δ

theorem six_term_exactSeq (hfg : ∀ n, ShortExact (f.f n) (g.f n)) (i j : ι) (hij : c.Rel i j) :
    ExactSeq C
      [(homology'Functor _ _ i).map f,
        (-- Hⁱ(A₁) ⟶ Hⁱ(A₂)
              homology'Functor
              _ _ i).map
          g,-- Hⁱ(A₂) ⟶ Hⁱ(A₃)
          δ
          f g hfg i j hij,
        (-- Hⁱ(A₃) ⟶ Hʲ(A₁)
              homology'Functor
              _ _ j).map
          f,
        (-- Hʲ(A₁) ⟶ Hʲ(A₂)
              homology'Functor
              _ _ j).map
          g] :=
  (-- Hʲ(A₁) ⟶ Hʲ(A₃)
      snake
      f g hfg i j hij).six_term_exactSeq

end HomologicalComplex

