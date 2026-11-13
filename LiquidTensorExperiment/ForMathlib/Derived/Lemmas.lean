import LiquidTensorExperiment.ForMathlib.HomotopyCategoryPretriangulated
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.Derived.Homological
import LiquidTensorExperiment.ForMathlib.Derived.Defs
import Mathlib.CategoryTheory.Abelian.Projective
import LiquidTensorExperiment.ForMathlib.SnakeLemma3
import LiquidTensorExperiment.ForMathlib.LesHomology
import LiquidTensorExperiment.ForMathlib.ExactSeq3
import LiquidTensorExperiment.ForMathlib.TriangleShift
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.ProjectiveReplacement
import LiquidTensorExperiment.ForMathlib.HomologyExact
import LiquidTensorExperiment.ForMathlib.IsIsoNeg

#align_import for_mathlib.derived.lemmas

-- import for_mathlib.arrow_preadditive
-- import for_mathlib.arrow_preadditive
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

open HomologicalComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace HomotopyCategory

local notation "𝒦" => HomotopyCategory A (ComplexShape.up ℤ)

local notation "HH" i => HomotopyCategory.homology'Functor A (ComplexShape.up ℤ) i

-- Move this
instance homology'Functor_additive (i : ℤ) : Functor.Additive (HH i) :=
  Functor.Additive.mk <| by
    rintro X Y ⟨f⟩ ⟨g⟩
    dsimp [HomotopyCategory.homology'Functor]
    erw [← (_root_.homology_functor _ _ _).map_add]
    rfl
    infer_instance

theorem CategoryTheory.CochainComplex.exact_cone_in_cone_out (i : ℤ) (X Y : CochainComplex A ℤ)
    (f : X ⟶ Y) :
    Exact ((homology'Functor _ _ i).map (cone.in f)) ((homology'Functor _ _ i).map (cone.out f)) :=
  by
  refine' (HomologicalComplex.six_term_exactSeq (cone.in f) (cone.out f) _ i (i + 1) rfl).pair
  intro n
  refine' (cone.termwise_split _ _).ShortExact

/-
lemma _root_.category_theory.cochain_complex.exact_to_cone_in
  (X Y : cochain_complex A ℤ) (f : X ⟶ Y) :
  exact ((_root_.homology_functor _ _ 0).map f)
    ((_root_.homology_functor _ _ 0).map (cone.in f)) :=
begin
  admit
end
-/
theorem CategoryTheory.Abelian.exact_neg_left (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f g) :
    Exact (-f) g :=
  by
  refine' Preadditive.exact_of_iso_of_exact' f g (-f) g _ (iso.refl _) (iso.refl _) _ _ h
  · have : (-𝟙 X) ≫ (-𝟙 X) = 𝟙 X := by simp only [preadditive.comp_neg, category.comp_id, neg_neg]
    exact ⟨-𝟙 X, -𝟙 X, this, this⟩
  ·
    simp only [preadditive.comp_neg, category.comp_id, iso.refl_hom, category.id_comp,
      preadditive.neg_comp, neg_neg]
  · simp only [iso.refl_hom, category.id_comp, category.comp_id]

theorem CategoryTheory.Abelian.exact_neg_left_iff (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact (-f) g ↔ Exact f g :=
  by
  refine' ⟨_, CategoryTheory.Abelian.exact_neg_left _ _ _ _ _⟩
  intro h
  simpa only [neg_neg] using CategoryTheory.Abelian.exact_neg_left _ _ _ _ _ h

theorem CategoryTheory.Abelian.exact_neg_right (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Exact f g) :
    Exact f (-g) :=
  by
  refine' Preadditive.exact_of_iso_of_exact' f g f (-g) (iso.refl _) (iso.refl _) _ _ _ h
  · have : (-𝟙 Z) ≫ (-𝟙 Z) = 𝟙 Z := by simp only [preadditive.comp_neg, category.comp_id, neg_neg]
    exact ⟨-𝟙 Z, -𝟙 Z, this, this⟩
  · simp only [iso.refl_hom, category.id_comp, category.comp_id]
  · simp only [preadditive.comp_neg, category.comp_id, iso.refl_hom, category.id_comp]

theorem CategoryTheory.Abelian.exact_neg_right_iff (X Y Z : A) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f (-g) ↔ Exact f g :=
  by
  refine' ⟨_, CategoryTheory.Abelian.exact_neg_right _ _ _ _ _⟩
  intro h
  simpa only [neg_neg] using CategoryTheory.Abelian.exact_neg_right _ _ _ _ _ h

instance homologyFunctorHomological (i : ℤ) : homologicalFunctor (HH i) :=
  by
  apply homological_of_rotate
  intro T hT
  erw [mem_distinguished_iff_exists_iso_cone] at hT 
  obtain ⟨X, Y, f, ⟨E⟩⟩ := hT
  let E' :
    T.rotate ≅
      ((neg₃_functor (HomotopyCategory A (ComplexShape.up ℤ))).obj (cone.triangleₕ f)).rotate :=
    ⟨E.hom.rotate, E.inv.rotate, _, _⟩
  rotate_left
  · ext <;> dsimp
    · change (E.hom ≫ E.inv).hom₂ = _; rw [iso.hom_inv_id]; rfl
    · change (E.hom ≫ E.inv).hom₃ = _; rw [iso.hom_inv_id]; rfl
    · simp only [← functor.map_comp]
      change (CategoryTheory.shiftFunctor 𝒦 (1 : ℤ)).map (E.hom ≫ E.inv).hom₁ = _
      rw [iso.hom_inv_id]; rfl
  · ext <;> dsimp
    · change (E.inv ≫ E.hom).hom₂ = _; rw [iso.inv_hom_id]; rfl
    · change (E.inv ≫ E.hom).hom₃ = _; rw [iso.inv_hom_id]; rfl
    · simp only [← functor.map_comp]
      change (CategoryTheory.shiftFunctor 𝒦 (1 : ℤ)).map (E.inv ≫ E.hom).hom₁ = _
      rw [iso.inv_hom_id]; rfl
  refine' homological_of_exists_aux _ _ _ E'.inv _
  dsimp
  simp only [functor.map_neg]
  apply CategoryTheory.Abelian.exact_neg_right
  apply CategoryTheory.CochainComplex.exact_cone_in_cone_out

variable (A)

def homologyShiftIso (i j : ℤ) :
    CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) i ⋙
        homology'Functor A (ComplexShape.up ℤ) j ≅
      homology'Functor A (ComplexShape.up ℤ) (j + i) :=
  NatIso.ofComponents (fun X : 𝒦 => homologyShiftObjIso X.as i j : _)
    (by
      intro X Y f
      rw [← quotient_map_out f]
      dsimp
      erw [homotopy_category.shift_functor_map_quotient]
      rw [← homology_functor_map_factors]
      erw [(homology_shift_iso A i j).Hom.naturality]
      erw [← homology_functor_map_factors]
      rfl)

def homologyZeroShiftIso (i : ℤ) :
    CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) i ⋙
        homology'Functor A (ComplexShape.up ℤ) 0 ≅
      homology'Functor A (ComplexShape.up ℤ) i :=
  homologyShiftIso _ _ _ ≪≫ eqToIso (by rw [zero_add])

variable {A}

theorem isAcyclic_iff (X : 𝒦) :
    (∀ i : ℤ, IsZero ((HomotopyCategory.homology'Functor _ _ 0).obj (X⟦i⟧))) ↔ IsAcyclic X :=
  by
  constructor
  · intro h
    constructor
    intro i
    apply is_zero_of_iso_of_zero (h i)
    apply (homology_zero_shift_iso A i).app _
  · intro h i
    apply (is_acyclic.cond _ i).of_iso ((homology_zero_shift_iso A _).app _)
    assumption

theorem isQuasiIso_iff {X Y : 𝒦} (f : X ⟶ Y) :
    (∀ i : ℤ, IsIso ((HomotopyCategory.homology'Functor _ _ 0).map (f⟦i⟧'))) ↔ IsQuasiIso f :=
  by
  constructor
  · intro h
    constructor
    intro i
    specialize h i
    have := (homology_zero_shift_iso A i).Hom.naturality f
    rw [← is_iso.inv_comp_eq] at this 
    rw [← this]
    apply (config := { instances := false }) is_iso.comp_is_iso
    infer_instance
    apply (config := { instances := false }) is_iso.comp_is_iso
    exact h
    infer_instance
  · intro h i
    have := (homology_zero_shift_iso A i).Hom.naturality f
    rw [← is_iso.eq_comp_inv] at this 
    erw [this]
    apply (config := { instances := false }) is_iso.comp_is_iso
    apply (config := { instances := false }) is_iso.comp_is_iso
    infer_instance
    apply is_quasi_iso.cond
    infer_instance

instance isIso_of_is_quasi_iso' {X Y : 𝒦} (f : X ⟶ Y) [h : IsQuasiIso f] (i : ℤ) :
    IsIso ((HomotopyCategory.homology'Functor _ _ 0).map (f⟦i⟧')) :=
  by
  rw [← is_quasi_iso_iff] at h 
  apply h

instance isIso_of_isQuasiIso {X Y : 𝒦} (f : X ⟶ Y) [IsQuasiIso f] (i : ℤ) :
    IsIso ((HomotopyCategory.homology'Functor _ _ i).map f) := by apply is_quasi_iso.cond

instance isQuasiIsoComp {X Y Z : 𝒦} (f : X ⟶ Y) (g : Y ⟶ Z) [IsQuasiIso f] [IsQuasiIso g] :
    IsQuasiIso (f ≫ g) := by
  constructor; intro i
  simp only [functor.map_comp]
  infer_instance

instance isQuasiIsoOfIsIso {X Y : 𝒦} (f : X ⟶ Y) [IsIso f] : IsQuasiIso f :=
  by
  constructor
  intro i; infer_instance

example {X Y Z : 𝒦} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : IsQuasiIso f] [hg : IsIso g] :
    IsQuasiIso (f ≫ g) :=
  inferInstance

/-
instance is_quasi_iso_comp_iso {X Y Z : 𝒦} (f : X ⟶ Y) (g : Y ⟶ Z)
  [hf : is_quasi_iso f] [hg : is_iso g] :
  is_quasi_iso (f ≫ g) := infer_instance
{ cond := λ i, by { rw (homology_functor A (complex_shape.up ℤ) i).map_comp, apply_instance, } }
-/
-- TODO(!): Why is this needed!?!?
instance : HasShift (triangle 𝒦) ℤ :=
  Triangle.hasShift (HomotopyCategory A (ComplexShape.up ℤ))

open CategoryTheory.Preadditive

/-- If `A → B → C → A[1]` is a distinguished triangle,
then `A → B` is a quasi-isomorphism if and only if `C` is acyclic. -/
theorem isQuasiIso_iff_isAcyclic (T : triangle 𝒦) (hT : T ∈ (dist_triang 𝒦)) :
    IsQuasiIso T.mor₁ ↔ IsAcyclic T.obj₃ :=
  by
  let H := homology'Functor A (ComplexShape.up ℤ) 0
  rw [← is_acyclic_iff]
  let S : ℤ → triangle 𝒦 := fun i => T⟦i⟧
  have hS : ∀ i : ℤ, S i ∈ (dist_triang 𝒦) := by apply pretriangulated.shift_of_dist_triangle;
    assumption
  have hSmor₁ : ∀ i, (S i).mor₁ = i.neg_one_pow • T.mor₁⟦i⟧' := by intro i; rfl
  have aux : ∀ i, is_iso (H.map (S i).mor₁) ↔ is_iso (H.map (T.mor₁⟦i⟧')) := by intro i;
    rw [hSmor₁, H.map_zsmul, isIso_negOnePow_iff]
  show _ ↔ ∀ i : ℤ, is_zero (H.obj (S i).obj₃)
  constructor <;> intro hh
  · intro i
    have : is_iso (H.map (S i).rotate.mor₃) :=
      by
      dsimp [triangle.rotate_mor₃]
      rw [functor.map_neg, isIso_neg_iff]
      let EE :
        (CategoryTheory.shiftFunctor 𝒦 i ⋙ CategoryTheory.shiftFunctor 𝒦 (1 : ℤ)) ⋙ H ≅
          homology'Functor _ _ (i + 1) :=
        by
        refine' iso_whisker_right _ _ ≪≫ homology_zero_shift_iso _ (i + 1)
        refine' (shift_functor_add _ _ _).symm
      suffices is_iso ((homology'Functor _ _ (i + 1)).map T.mor₁)
        by
        have hhh := EE.hom.naturality T.mor₁
        rw [← is_iso.eq_comp_inv] at hhh 
        dsimp only [functor.comp_map] at hhh 
        simp only [functor.map_zsmul]
        rw [isIso_negOnePow_iff]
        rw [hhh]
        apply (config := { instances := false }) is_iso.comp_is_iso
        apply (config := { instances := false }) is_iso.comp_is_iso
        all_goals
          first
          | infer_instance
          | assumption
      apply is_quasi_iso.cond
    have : is_iso (H.map (S i).mor₁) := by simp only [← is_quasi_iso_iff, ← aux] at hh ; exact hh i
    have E' := fun i : ℤ => five_term_exact_seq' H (S i) (hS i)
    apply is_zero_of_exact_seq_of_is_iso_of_is_iso _ _ _ _ (E' i)
  · simp only [← is_quasi_iso_iff, ← aux]
    intro i
    have E := five_term_exact_seq H (S i) (hS i)
    apply E.is_iso_of_zero_of_zero
    · apply is_zero.eq_of_src
      let EE :
        (CategoryTheory.shiftFunctor 𝒦 i ⋙ CategoryTheory.shiftFunctor 𝒦 (-1 : ℤ)) ⋙ H ≅
          CategoryTheory.shiftFunctor 𝒦 (i + -1) ⋙ H :=
        by refine' iso_whisker_right _ _; refine' (shift_functor_add _ _ _).symm
      let e := EE.app T.obj₃
      -- let e := (homology_zero_shift_iso _ (-1 : ℤ)).app (S i).obj₃,
      refine' is_zero_of_iso_of_zero _ e.symm;
      clear e
      exact hh _
    · apply (hh i).eq_of_tgt

/-- If `A → B → C → A[1]` is a distinguished triangle, and `A → B` is a quasi-isomorphism,
then `C` is acyclic. -/
theorem isAcyclicOfDistTriangOfIsQuasiIso (T : triangle 𝒦) (hT : T ∈ (dist_triang 𝒦))
    [h : IsQuasiIso T.mor₁] : IsAcyclic T.obj₃ := by rwa [← is_quasi_iso_iff_is_acyclic T hT]

instance isAcyclicShift (T : 𝒦) [h : IsAcyclic T] (i : ℤ) : IsAcyclic (T⟦i⟧) :=
  by
  rw [← is_acyclic_iff]
  intro j
  let H := homology'Functor A (ComplexShape.up ℤ) 0
  let e : H.obj (T⟦i⟧⟦j⟧) ≅ (homology'Functor A (ComplexShape.up ℤ) (i + j)).obj T :=
    _ ≪≫ (homology_zero_shift_iso _ (i + j)).app T
  swap
  · let e := (iso_whisker_right (shift_functor_add _ i j).symm H).app T
    refine' _ ≪≫ e
    refine' iso.refl _
  apply is_zero_of_iso_of_zero _ e.symm
  apply is_acyclic.cond

instance isQuasiIsoShift (X Y : 𝒦) (f : X ⟶ Y) [IsQuasiIso f] (i : ℤ) : IsQuasiIso (f⟦i⟧') :=
  by
  rw [← is_quasi_iso_iff]
  intro j
  have := (CategoryTheory.shiftFunctorAdd 𝒦 i j).Hom.naturality f
  apply_fun fun e => (homology'Functor _ _ 0).map e at this 
  simp only [functor.map_comp, functor.comp_map] at this 
  rw [← is_iso.inv_comp_eq] at this 
  rw [← this]
  apply is_iso.comp_is_iso

theorem hom_K_projective_bijective {X Y : 𝒦} (P : 𝒦) [IsKProjective P] (f : X ⟶ Y)
    [hf : IsQuasiIso f] : Function.Bijective fun e : P ⟶ X => e ≫ f :=
  by
  /-
    Steps:
    1. Complete `f` to a dist triang `X → Y → Z → X[1]`.
    2. Use LES assoc. to `Hom(P,-)`, proved in `for_mathlib/derived/homological.lean`.
    3. Use lemma above + def of K-projective to see that `Hom(P,Z) = 0`.
    -/
  obtain ⟨Z, g, h, hT⟩ := pretriangulated.distinguished_cocone_triangle _ _ f
  let T := triangle.mk _ f g h
  change T ∈ _ at hT 
  let H : 𝒦 ⥤ Ab := preadditive_yoneda.flip.obj (Opposite.op P)
  have EE : exact_seq Ab [arrow.mk (H.map T.inv_rotate.mor₁), arrow.mk (H.map f), H.map g] :=
    by
    apply exact_seq.cons
    apply homological_functor.cond H T.inv_rotate
    apply inv_rotate_mem_distinguished_triangles
    assumption
    rw [← exact_iff_exact_seq]
    apply homological_functor.cond H T hT
  constructor
  · intro e₁ e₂ hh
    let ee := (EE.extract 0 2).pair
    rw [AddCommGroupCat.exact_iff] at ee 
    dsimp at hh 
    rw [← sub_eq_zero, ← preadditive.sub_comp] at hh 
    change _ ∈ (H.map f).ker at hh 
    rw [← ee] at hh 
    obtain ⟨g, hg⟩ := hh
    let g' : P ⟶ _ := g
    have : is_acyclic T.inv_rotate.obj₁ :=
      by
      change is_acyclic (T.obj₃⟦(-1 : ℤ)⟧)
      apply (config := { instances := false }) HomotopyCategory.isAcyclicShift
      haveI : is_quasi_iso T.mor₁ := hf
      apply is_acyclic_of_dist_triang_of_is_quasi_iso
      exact hT
    have : g' = 0 := by apply is_K_projective.cond
    change g' ≫ _ = _ at hg 
    rw [this, zero_comp] at hg 
    rw [← sub_eq_zero]
    exact hg.symm
  · intro q
    have : q ≫ g = 0 :=
      by
      have : is_acyclic Z := by
        change is_acyclic T.obj₃
        apply (config := { instances := false }) is_acyclic_of_dist_triang_of_is_quasi_iso
        assumption
        exact hf
      apply is_K_projective.cond
    let ee := (EE.extract 1 3).pair
    rw [AddCommGroupCat.exact_iff] at ee 
    change _ ∈ (H.map g).ker at this 
    rwa [← ee] at this 

instance (X : 𝒦) [IsBoundedAbove X] (i : ℤ) : IsBoundedAbove (X⟦i⟧) :=
  by
  obtain ⟨a, ha⟩ := is_bounded_above.cond X
  use a - i
  intro j hj
  apply ha
  linarith

theorem isKProjectiveOfIso (P Q : 𝒦) [IsKProjective P] (e : P ≅ Q) : IsKProjective Q :=
  by
  constructor
  intro Y _ f
  apply_fun fun q => e.hom ≫ q
  dsimp
  rw [comp_zero]
  apply is_K_projective.cond
  intro a b h
  apply_fun fun q => e.inv ≫ q at h 
  simpa using h

instance isKProjectiveShift (P : 𝒦) [IsKProjective P] (i : ℤ) : IsKProjective (P⟦i⟧) :=
  by
  constructor
  intro Y _ f
  let e := (shift_functor_comp_shift_functor_neg _ i).app P
  dsimp at e 
  haveI : is_K_projective (P⟦i⟧⟦-i⟧) := is_K_projective_of_iso _ _ e.symm
  apply (CategoryTheory.shiftFunctor 𝒦 (-i)).map_injective
  simp
  apply is_K_projective.cond

theorem isQuasiIsoOfTriangle (T₁ T₂ : triangle 𝒦) (h₁ : T₁ ∈ (dist_triang 𝒦))
    (h₂ : T₂ ∈ (dist_triang 𝒦)) (f : T₁ ⟶ T₂) [IsQuasiIso f.hom₁] [IsQuasiIso f.hom₂] :
    IsQuasiIso f.hom₃ :=
  by
  -- Another application of the five lemma...
  let H : 𝒦 ⥤ _ := HomotopyCategory.homology'Functor _ _ 0
  rw [← is_quasi_iso_iff]
  intro i
  let S₁ := T₁⟦i⟧
  let S₂ := T₂⟦i⟧
  let g : S₁ ⟶ S₂ := f⟦i⟧'
  have aux1 : exact (H.map S₁.mor₁) (H.map S₁.mor₂) :=
    by
    apply homological_functor.cond
    apply pretriangulated.shift_of_dist_triangle
    assumption
  have aux2 : exact (H.map S₁.mor₂) (H.map S₁.mor₃) :=
    by
    apply homological_functor.cond H S₁.rotate
    apply pretriangulated.rot_of_dist_triangle
    apply pretriangulated.shift_of_dist_triangle
    assumption
  have aux3 : exact (H.map S₁.mor₃) (H.map S₁.rotate.mor₃) :=
    by
    apply homological_functor.cond H S₁.rotate.rotate
    apply pretriangulated.rot_of_dist_triangle
    apply pretriangulated.rot_of_dist_triangle
    apply pretriangulated.shift_of_dist_triangle
    assumption
  have aux4 : exact (H.map S₂.mor₁) (H.map S₂.mor₂) :=
    by
    apply homological_functor.cond
    apply pretriangulated.shift_of_dist_triangle
    assumption
  have aux5 : exact (H.map S₂.mor₂) (H.map S₂.mor₃) :=
    by
    apply homological_functor.cond H S₂.rotate
    apply pretriangulated.rot_of_dist_triangle
    apply pretriangulated.shift_of_dist_triangle
    assumption
  have aux6 : exact (H.map S₂.mor₃) (H.map S₂.rotate.mor₃) :=
    by
    apply homological_functor.cond H S₂.rotate.rotate
    apply pretriangulated.rot_of_dist_triangle
    apply pretriangulated.rot_of_dist_triangle
    apply pretriangulated.shift_of_dist_triangle
    assumption
  have : is_iso (H.map g.hom₁) :=
    by
    change is_iso (H.map (f.hom₁⟦i⟧'))
    infer_instance
  have : is_iso (H.map g.hom₂) :=
    by
    change is_iso (H.map (f.hom₂⟦i⟧'))
    infer_instance
  have : is_iso (H.map (g.hom₁⟦(1 : ℤ)⟧')) :=
    by
    change is_iso (H.map (f.hom₁⟦i⟧'⟦(1 : ℤ)⟧'))
    have := (CategoryTheory.shiftFunctorAdd 𝒦 i 1).Hom.naturality f.hom₁
    apply_fun fun e => H.map e at this 
    simp only [H.map_comp, functor.comp_map] at this 
    rw [← is_iso.inv_comp_eq] at this 
    rw [← this]
    apply is_iso.comp_is_iso
  have : is_iso (H.map (g.hom₂⟦(1 : ℤ)⟧')) :=
    by
    change is_iso (H.map (f.hom₂⟦i⟧'⟦(1 : ℤ)⟧'))
    have := (CategoryTheory.shiftFunctorAdd 𝒦 i 1).Hom.naturality f.hom₂
    apply_fun fun e => H.map e at this 
    simp only [H.map_comp, functor.comp_map] at this 
    rw [← is_iso.inv_comp_eq] at this 
    rw [← this]
    apply is_iso.comp_is_iso
  refine'
    @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso A _ _ (H.obj S₁.obj₁) (H.obj S₁.obj₂)
      (H.obj S₁.obj₃) (H.obj (S₁.obj₁⟦(1 : ℤ)⟧)) (H.obj S₂.obj₁) (H.obj S₂.obj₂) (H.obj S₂.obj₃)
      (H.obj (S₂.obj₁⟦(1 : ℤ)⟧)) (H.map S₁.mor₁) (H.map S₁.mor₂) (H.map S₁.mor₃) (H.map S₂.mor₁)
      (H.map S₂.mor₂) (H.map S₂.mor₃) (H.map g.hom₁) (H.map g.hom₂) (H.map g.hom₃)
      (H.map (g.hom₁⟦(1 : ℤ)⟧')) _ _ _ (H.obj (S₁.obj₂⟦(1 : ℤ)⟧)) (H.obj (S₂.obj₂⟦(1 : ℤ)⟧))
      (H.map S₁.rotate.mor₃) (H.map S₂.rotate.mor₃) (H.map (g.hom₂⟦(1 : ℤ)⟧')) _ aux1 aux2 aux3 aux4
      aux5 aux6 _ _ _ _
  · simp only [← H.map_comp, g.comm₁]
  · simp only [← H.map_comp, g.comm₂]
  · simp only [← H.map_comp, g.comm₃]
  · simp only [← functor.map_comp]
    congr 1
    dsimp
    simp only [preadditive.comp_neg, preadditive.neg_comp, neg_inj, ← functor.map_comp, f.comm₁,
      preadditive.zsmul_comp, preadditive.comp_zsmul]

theorem isKProjectiveOfTriangle (T : triangle 𝒦) (hT : T ∈ (dist_triang 𝒦)) [IsKProjective T.obj₁]
    [IsKProjective T.obj₂] : IsKProjective T.obj₃ :=
  by
  constructor
  intro Y _ f
  let H : 𝒦 ⥤ Abᵒᵖ := (preadditive_yoneda.obj Y).rightOp
  haveI : homological_functor H := inferInstance
  -- sanity check
  have e := homological_functor.cond H T.rotate (rotate_mem_distinguished_triangles _ hT)
  dsimp [H] at e 
  let a := _; let b := _; change exact a b at e ; have e' : exact b.unop a.unop := e.unop
  dsimp at e' 
  rw [AddCommGroupCat.exact_iff] at e' 
  let a' := _; let b' := _; change AddMonoidHom.range a' = AddMonoidHom.ker b' at e' 
  have : f ∈ b'.ker := by
    change _ ≫ _ = 0
    apply (config := { instances := false }) is_K_projective.cond
    dsimp
    infer_instance
    infer_instance
  rw [← e'] at this 
  obtain ⟨g, hg⟩ := this
  dsimp at hg 
  rw [← hg]
  have : g = 0 := by apply is_K_projective.cond
  simp [this]

variable [EnoughProjectives A]

theorem exists_bounded_K_projective_replacement_of_bounded (a : ℤ) (X : 𝒦) (H : X.BoundedBy a) :
    ∃ (P : 𝒦) (_ : IsKProjective P) (hP : P.BoundedBy a) (f : P ⟶ X),
      IsQuasiIso f ∧ ∀ k, Projective (P.as.pt k) :=
  by
  use projective.replacement X.as a H
  refine' ⟨⟨_⟩, _, (Quotient _ _).map (projective.replacement.hom X.as a H), ⟨_⟩, _⟩
  · intro Y hY f
    convert
      eq_of_homotopy _ _
        (projective.null_homotopic_of_projective_to_acyclic f.out a
          (projective.replacement_is_projective X.as a H)
          (projective.replacement_is_bounded X.as a H) hY.1)
    simp
  · apply projective.replacement_is_bounded
  · intro i
    erw [← homology_functor_map_factors]
    infer_instance
  · intro k; dsimp; apply projective.replacement_is_projective

theorem exists_K_projective_replacement_of_uniformly_bounded_above {α : Type _} (X : α → 𝒦)
    [IsUniformlyBoundedAbove X] :
    ∃ (P : α → 𝒦) (_ : ∀ a, IsKProjective (P a)) (_ : IsUniformlyBoundedAbove P) (f :
      ∀ a, P a ⟶ X a), (∀ a, IsQuasiIso (f a)) ∧ ∀ a k, Projective ((P a).as.pt k) :=
  by
  obtain ⟨a, H⟩ := is_uniformly_bounded_above.cond X
  have := fun t => exists_bounded_K_projective_replacement_of_bounded a _ (H t)
  choose P H1 H2 f H3 H4 using this
  refine' ⟨P, H1, ⟨⟨a, H2⟩⟩, f, H3, H4⟩

theorem exists_K_projective_replacement_of_bounded (X : 𝒦) [IsBoundedAbove X] :
    ∃ (P : 𝒦) (_ : IsKProjective P) (_ : IsBoundedAbove P) (f : P ⟶ X),
      IsQuasiIso f ∧ ∀ k, Projective (P.as.pt k) :=
  by
  obtain ⟨a, H⟩ := is_bounded_above.cond X
  have := exists_bounded_K_projective_replacement_of_bounded a _ H
  choose P H1 H2 f H3 H4 using this
  refine' ⟨P, H1, ⟨⟨a, H2⟩⟩, f, H3, H4⟩

instance isKProjectiveOfBoundedTermwiseProjective (P : BoundedHomotopyCategory A)
    [hP : ∀ k, Projective (P.val.as.pt k)] : P.val.IsKProjective :=
  ⟨fun Y hY f => by
    suffices H : Homotopy f.out 0
    · have h := HomotopyCategory.eq_of_homotopy f.out 0 H
      simpa only [HomotopyCategory.quotient_map_out] using h
    exact
      projective.null_homotopic_of_projective_to_acyclic _ P.bdd.1.some hP P.bdd.1.choose_spec hY.1⟩

end HomotopyCategory

