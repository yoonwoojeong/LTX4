import LiquidTensorExperiment.ForMathlib.Derived.Lemmas
import LiquidTensorExperiment.ForMathlib.Derived.Les
import LiquidTensorExperiment.ForMathlib.Derived.DerivedCat

#align_import for_mathlib.derived.les2

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Triangulated

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "𝒦" => HomotopyCategory A (ComplexShape.up ℤ)

namespace HomologicalComplex

variable {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

noncomputable section

-- The 5-lemma with no instances... I think this is more convenient to apply in practice.
theorem CategoryTheory.Abelian.isIso_of_isIso_of_isIso_of_isIso_of_is_iso' :
    ∀ {U B C D A' B' C' D' : A} {f : U ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
      {h' : C' ⟶ D'} {α : U ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'},
      α ≫ f' = f ≫ β →
        β ≫ g' = g ≫ γ →
          γ ≫ h' = h ≫ δ →
            ∀ {E E' : A} {i : D ⟶ E} {i' : D' ⟶ E'} {ε : E ⟶ E'},
              δ ≫ i' = i ≫ ε →
                Exact f g →
                  Exact g h →
                    Exact h i →
                      Exact f' g' →
                        Exact g' h' →
                          Exact h' i' → IsIso α → IsIso β → IsIso δ → IsIso ε → IsIso γ :=
  by
  intro U B C D A' B' C' D' f g h f' g' h' α β γ δ w1 w2 w3 E E' i i' ε w4
  intro hfg hgh hhi hf'g' hg'h' hh'i' hα hβ hδ hε; skip
  apply
    Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono w1 w2 w3 w4 hfg hgh hhi hf'g' hg'h' hh'i'

namespace IsIsoConeSetup

-- This follows from the fact that homology is a homological functor.
theorem isZero_homology'_cone_id (n : ℤ) : IsZero ((cone (𝟙 X)).homology' n) :=
  by
  let T : triangle (HomotopyCategory A (ComplexShape.up ℤ)) :=
    (neg₃_functor _).obj (cone.triangleₕ (𝟙 X))
  have hT : T ∈ (dist_triang 𝒦) :=
    by
    erw [HomotopyCategory.mem_distinguished_iff_exists_iso_cone]
    refine' ⟨_, _, 𝟙 X, ⟨iso.refl _⟩⟩
  have E := five_term_exact_seq' (HomotopyCategory.homology'Functor A (ComplexShape.up ℤ) n) T hT
  dsimp [T] at E 
  apply CategoryTheory.isZero_of_exactSeq_of_is_iso_of_is_iso _ _ _ _ E

def coneIdToCone : cone (𝟙 X) ⟶ cone f
    where
  f i := biprod.lift biprod.fst (biprod.snd ≫ f.f _)
  comm' :=
    by
    -- This proof is a bit slow...
    rintro i j ⟨rfl⟩
    apply CategoryTheory.Limits.biprod.hom_ext'
    apply CategoryTheory.Limits.biprod.hom_ext
    · simp; dsimp [cone, Cone.d]; simp
    · simp; dsimp [cone, Cone.d]; simp
    · apply CategoryTheory.Limits.biprod.hom_ext
      simp; dsimp [cone, Cone.d]; simp; dsimp [cone, Cone.d]; simp

def kernelConeπIso (w) (n : ℤ) :
    Limits.kernel ((cone.π f g w).f n) ≅ biprod (X.pt (n + 1)) (Limits.kernel (g.f n))
    where
  hom :=
    biprod.lift (Limits.kernel.ι _ ≫ biprod.fst)
      (Limits.kernel.lift _ (Limits.kernel.ι _ ≫ biprod.snd)
        (by
          simp
          let t := _; change _ ≫ t = _
          have ht : t = (cone.π f g w).f n := by ext; dsimp [cone.π]; simp; dsimp [cone.π]; simp
          rw [ht, Limits.kernel.condition]))
  inv :=
    biprod.desc (Limits.kernel.lift _ biprod.inl (by dsimp [cone.π]; simp))
      (Limits.kernel.lift _ (Limits.kernel.ι _ ≫ biprod.inr) (by simp))
  hom_inv_id := by ext; dsimp; simp; dsimp; simp
  inv_hom_id := by ext; dsimp; simp; dsimp; simp; dsimp; simp; dsimp; simp

def cokernelConeIdToConeIso (n) : cokernel ((coneIdToCone f).f n) ≅ cokernel (f.f n)
    where
  hom :=
    cokernel.desc _ (biprod.desc 0 (cokernel.π _)) (by dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone]; ext; simp; simp)
  inv :=
    cokernel.desc _ (biprod.inr ≫ cokernel.π _)
      (by
        rw [← Category.assoc]
        let t := _; change t ≫ _ = _
        have ht : t = biprod.inr ≫ (HomologicalComplex.IsIsoConeSetup.coneIdToCone f).f n :=
          by
          ext; dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone]; simp; simp
          dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone]; simp
        simp [ht])
  hom_inv_id := by
    ext; dsimp; simp; dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone]; simp
    let t := _; let s := _; change _ = t ≫ cokernel.π s
    have ht : t = biprod.inl ≫ s := by ext; simp; simp
    rw [ht]; simp
    simp
  inv_hom_id := by ext; dsimp; simp

-- `0 → C(𝟙 X) → C(f) → Z → 0` is a SES of complexes.
theorem coneIdToCone_shortExact (ses : ∀ i : ℤ, ShortExact (f.f i) (g.f i)) (n : ℤ) :
    ShortExact ((coneIdToCone f).f n) ((cone.π f g fun i => (ses i).exact.w).f _) :=
  { mono := by
      constructor; intro Z i j h
      dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone] at h 
      apply biprod.hom_ext
      · apply_fun fun e => e ≫ biprod.fst at h 
        simpa using h
      · apply_fun fun e => e ≫ biprod.snd at h 
        simp at h ; simp_rw [← Category.assoc] at h 
        haveI : mono (f.f n) := (ses n).mono
        rwa [cancel_mono] at h 
    Epi := by
      constructor; intro W i j h
      dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone] at h 
      simp only [Category.assoc] at h 
      rw [cancel_epi] at h 
      haveI : epi (g.f n) := (ses n).Epi
      rwa [cancel_epi] at h 
    exact := by
      rw [Abelian.exact_iff]; constructor
      · dsimp [HomologicalComplex.IsIsoConeSetup.coneIdToCone]; ext; simp
        erw [biprod.lift_snd_assoc]
        simp [(ses n).exact.w]
      · rw [← cancel_epi (kernel_cone_π_iso f g _ _).inv]
        swap; infer_instance
        rw [← cancel_mono (HomologicalComplex.IsIsoConeSetup.cokernelConeIdToConeIso f n).hom]
        dsimp [kernel_cone_π_iso, HomologicalComplex.IsIsoConeSetup.cokernelConeIdToConeIso]
        ext; simp
        simp
        have := (ses n).exact; rw [Abelian.exact_iff] at this 
        exact this.2 }

/-
Now combine both results above to see that the map
`H^i(C(f)) → H^i(Z)`
is an isomorphism, using the LES for short exact sequences of complexes.
-/
theorem isIso_homology_map_cone_π (ses : ∀ i : ℤ, ShortExact (f.f i) (g.f i)) (n : ℤ) :
    IsIso ((homology'Functor _ _ n).map (cone.π f g fun i => (ses i).exact.w)) :=
  by
  have E :=
    six_term_exact_seq (HomologicalComplex.IsIsoConeSetup.coneIdToCone f) (cone.π f g fun i => (ses i).exact.w)
      (HomologicalComplex.IsIsoConeSetup.coneIdToCone_shortExact _ _ _)
  apply CategoryTheory.isIso_of_exact_of_isZero_of_isZero _ _ _ _ _ ((E n (n + 1) rfl).extract 0 3)
  apply HomologicalComplex.IsIsoConeSetup.isZero_homology'_cone_id
  apply HomologicalComplex.IsIsoConeSetup.isZero_homology'_cone_id

end IsIsoConeSetup

/-
-- Why is this SO SLOW?!
lemma is_iso_homology_functor_map_aux (n : ℤ) (ses : ∀ i : ℤ, short_exact (f.f i) (g.f i)) :
  (homology_functor A (complex_shape.up ℤ) n).map (cone.π f g (λ i, (ses i).exact.w)) ≫
    δ f g ses n (n + 1) rfl =
  (homotopy_category.homology_functor A (complex_shape.up ℤ) n).map
    ((neg₃_functor (homotopy_category A (complex_shape.up ℤ))).obj
      (cone.triangleₕ f)).mor₃ ≫ ((homology_shift_iso A 1 n).app
    ((neg₃_functor (homotopy_category A (complex_shape.up ℤ))).obj
      (cone.triangleₕ f)).obj₁.as).hom :=
begin
  admit
end

theorem is_iso_homology_functor_map (n : ℤ) (ses : ∀ (i : ℤ), short_exact (f.f i) (g.f i)) :
  is_iso ((homology_functor _ _ n).map (cone.π f g (λ i, (ses i).exact.w))) :=
begin
  let X' : 𝒦 := (homotopy_category.quotient _ _).obj X,
  let Y' : 𝒦 := (homotopy_category.quotient _ _).obj Y,
  let Z' : 𝒦 := (homotopy_category.quotient _ _).obj Z,
  let f' : X' ⟶ Y' := (homotopy_category.quotient _ _).map f,
  let g' : Y' ⟶ Z' := (homotopy_category.quotient _ _).map g,
  let T : triangle (homotopy_category A (complex_shape.up ℤ)) :=
    (neg₃_functor _).obj (cone.triangleₕ f),
  have hT : T ∈ dist_triang 𝒦,
  { erw homotopy_category.mem_distinguished_iff_exists_iso_cone,
    refine ⟨_, _, f, ⟨iso.refl _⟩⟩ },
  have E1 := five_term_exact_seq' (homotopy_category.homology_functor A (complex_shape.up ℤ) n)
    T hT,
  have E2 := six_term_exact_seq f g ses n (n+1) rfl,
  let EE := homology_shift_iso A 1 n,
  --rw zero_add at EE,
  have key := @_root_.category_theory.abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso' _ _ _
    ((homotopy_category.homology_functor _ _ n).obj T.obj₁)
    ((homotopy_category.homology_functor _ _ n).obj T.obj₂)
    ((homotopy_category.homology_functor _ _ n).obj T.obj₃)
    ((homotopy_category.homology_functor _ _ n).obj (T.obj₁⟦(1 : ℤ)⟧))
    ((homology_functor _ _ n).obj X)
    ((homology_functor _ _ n).obj Y)
    ((homology_functor _ _ n).obj Z)
    ((homology_functor _ _ (n+1)).obj X)
    ((homotopy_category.homology_functor _ _ n).map T.mor₁)
    ((homotopy_category.homology_functor _ _ n).map T.mor₂)
    ((homotopy_category.homology_functor _ _ n).map T.mor₃)
    ((homology_functor _ _ n).map f)
    ((homology_functor _ _ n).map g)
    (δ f g ses n (n+1) rfl)
    (𝟙 _) (𝟙 _)
    ((homology_functor _ _ n).map (cone.π f g _))
    (EE.app _).hom _ _ _
    ((homotopy_category.homology_functor _ _ n).obj (T.obj₂⟦(1 : ℤ)⟧))
    ((homology_functor _ _ (n+1)).obj Y)
    ((homotopy_category.homology_functor A (complex_shape.up ℤ) n).map T.rotate.mor₃)
    ((homology_functor A (complex_shape.up ℤ) (n+1)).map f)
    (-(EE.app _)).hom,
    apply key, any_goals { apply_instance },
  { dsimp [triangle.rotate],
    simp only [functor.map_neg, preadditive.comp_neg, preadditive.neg_comp, neg_neg],
    symmetry,
    apply EE.hom.naturality },
  { exact E1.pair },
  { exact (E1.drop 1).pair },
  { exact (E1.drop 2).pair },
  { exact E2.pair },
  { exact (E2.drop 1).pair },
  { exact (E2.drop 2).pair },
  { simp only [category.id_comp, category.comp_id], refl },
  { rw category.id_comp,
    change _ = (homology_functor _ _ _).map _ ≫ _,
    rw ← functor.map_comp,
    congr' 1, ext i, symmetry, apply biprod.inr_snd_assoc },
  { apply is_iso_homology_functor_map_aux },
end .
-/
instance isQuasiIsoMapConeπ (ses : ∀ i : ℤ, ShortExact (f.f i) (g.f i)) :
    HomotopyCategory.IsQuasiIso
      ((HomotopyCategory.quotient _ _).map (cone.π f g fun i => (ses i).exact.w)) :=
  by
  constructor; intro i
  apply IsIsoConeSetup.isIso_homology_map_cone_π

--apply is_iso_homology_functor_map,
end HomologicalComplex

namespace HomotopyCategory

variable {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

open HomologicalComplex

def cone :=
  (HomotopyCategory.quotient _ _).obj (cone f)

def cone.π (w) : cone f ⟶ (HomotopyCategory.quotient _ _).obj Z :=
  (HomotopyCategory.quotient _ _).map (cone.π f g w)

instance isQuasiIsoConeπ (w : ∀ i, ShortExact (f.f i) (g.f i)) : IsQuasiIso (cone.π f g _) :=
  HomologicalComplex.isQuasiIsoMapConeπ _ _ w

end HomotopyCategory

namespace HomologicalComplex

end HomologicalComplex

namespace BoundedHomotopyCategory

variable {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

open HomologicalComplex

def cone [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] (f : X ⟶ Y) :
    BoundedHomotopyCategory A where
  val := HomotopyCategory.cone f
  bdd :=
    by
    obtain ⟨a, ha⟩ := HomotopyCategory.IsBoundedAbove.cond ((HomotopyCategory.quotient _ _).obj X)
    obtain ⟨b, hb⟩ := HomotopyCategory.IsBoundedAbove.cond ((HomotopyCategory.quotient _ _).obj Y)
    constructor; use max a b + 1
    intro t ht
    apply CategoryTheory.Limits.isZero_biprod
    · apply ha; refine' le_trans (le_trans _ ht) _
      refine' le_trans (le_max_left a b) _
      all_goals linarith
    · apply hb
      refine' le_trans _ ht; refine' le_trans (le_max_right a b) _
      linarith

def cone.π [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)] (w) :
    cone f ⟶ of' Z :=
  HomotopyCategory.cone.π f g w

instance isQuasiIsoConeπ [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) : HomotopyCategory.IsQuasiIso (cone.π f g _) :=
  HomologicalComplex.isQuasiIsoMapConeπ _ _ w

def coneTriangle [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] :
    triangle (BoundedHomotopyCategory A)
    where
  obj₁ := of' X
  obj₂ := of' Y
  obj₃ := cone f
  mor₁ := ofHom f
  mor₂ := (cone.triangleₕ f).mor₂
  mor₃ := -(cone.triangleₕ f).mor₃

theorem dist_coneTriangle [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] :
    coneTriangle f ∈ (dist_triang BoundedHomotopyCategory A) :=
  HomotopyCategory.cone_triangleₕ_mem_distinguishedTriangles _ _ f

instance isIso_ext_map_cone_π (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) :
    IsIso (((ext n).flip.obj W).rightOp.map (cone.π f g fun i => (w i).exact.w)) :=
  by
  dsimp [Functor.rightOp]
  apply (config := { instances := false }) CategoryTheory.isIso_op
  apply BoundedHomotopyCategory.isIso_ext_flip_obj_map_of_isQuasiIso

def connectingHom' (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) :
    ((ext n).flip.obj W).rightOp.obj (of' Z) ⟶ ((ext n).flip.obj W).rightOp.obj (of' X⟦(1 : ℤ)⟧) :=
  inv (((ext n).flip.obj W).rightOp.map (cone.π f g fun i => (w i).exact.w)) ≫
    ((ext n).flip.obj W).rightOp.map (coneTriangle f).mor₃

def ext_five_term_exactSeq (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) :
    let E := ((ext n).flip.obj W).rightOp
    ExactSeq Ab.{v}ᵒᵖ <|
      [E.map (ofHom f), E.map (ofHom g), connectingHom' f g n W w, E.map (-ofHom f⟦(1 : ℤ)⟧')] :=
  by
  intro E
  have hg : of_hom g = (BoundedHomotopyCategory.coneTriangle f).mor₂ ≫ cone.π f g fun i => (w i).exact.w :=
    by
    dsimp [of_hom, BoundedHomotopyCategory.coneTriangle, cone.π, HomotopyCategory.cone.π]
    erw [← Functor.map_comp]; congr 1
    ext ii
    dsimp [cone.in]; rw [biprod.inr_snd_assoc]
  let e := E.map (cone.π f g fun i => (w i).exact.w)
  let ee := CategoryTheory.asIso e
  have firsttwo := homologicalFunctor.cond E (BoundedHomotopyCategory.coneTriangle f) (BoundedHomotopyCategory.dist_coneTriangle _)
  apply ExactSeq.cons
  · rw [hg, Functor.map_comp]
    rw [exact_comp_iso]
    apply firsttwo
  apply ExactSeq.cons
  · have next_two := homologicalFunctor.cond E (BoundedHomotopyCategory.coneTriangle f).rotate _
    dsimp only [BoundedHomotopyCategory.connectingHom']; rw [hg, Functor.map_comp]
    change exact (_ ≫ ee.hom) (ee.inv ≫ _)
    rw [CategoryTheory.exact_comp_hom_inv_comp_iff]
    exact next_two
    apply Pretriangulated.rot_of_distTriang; apply BoundedHomotopyCategory.dist_coneTriangle
  rw [← CategoryTheory.exact_iff_exactSeq]
  · dsimp only [BoundedHomotopyCategory.connectingHom']
    rw [exact_iso_comp]
    apply homologicalFunctor.cond E (BoundedHomotopyCategory.coneTriangle f).rotate.rotate
    apply Pretriangulated.rot_of_distTriang
    apply Pretriangulated.rot_of_distTriang
    apply BoundedHomotopyCategory.dist_coneTriangle

-- Do we not have this?!
-- TODO: Move this!
def shiftOfEq {C : Type u} [Category.{v} C] [HasShift C ℤ] (i j : ℤ) (h : i = j) (X : C) :
    X⟦i⟧ ≅ X⟦j⟧ := by rw [h]

@[simps]
def shiftIsoAux {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] (n m : ℤ) (X Y : C) :
    (X⟦n⟧ ⟶ Y⟦m + n⟧) ≃+ (X ⟶ Y⟦m⟧)
    where
  toFun f := (shiftShiftNeg X n).inv ≫ (f ≫ (shiftAdd Y m n).hom)⟦-n⟧' ≫ (shiftShiftNeg _ n).hom
  invFun f := f⟦n⟧' ≫ (shiftAdd _ _ _).inv
  left_inv f := by
    dsimp only
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Category.comp_id, Category.id_comp,
      shift_shift_neg_inv_shift, shift_shift_neg_hom_shift, shift_neg_shift', Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  right_inv f := by
    simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id,
      shift_shift_neg']
  map_add' x y := by
    simp only [(CategoryTheory.shiftFunctor C (-n)).map_add, Preadditive.comp_add,
      Preadditive.add_comp, Preadditive.comp_add_assoc, Preadditive.add_comp_assoc]

end BoundedHomotopyCategory

