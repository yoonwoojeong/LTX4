import LiquidTensorExperiment.ForMathlib.Imker

#align_import for_mathlib.truncation

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

variable (C : CochainComplex 𝓐 ℤ)

open scoped ZeroObject

--This should be the canonical truncation functor `τ_{≤n}` for cochain complexes.
--It is the functor (3) in the second set of truncation functors on this page:
--https://stacks.math.columbia.edu/tag/0118
/-- The "canonical truncation" of a cochain complex (Cⁱ) at an integer `n`,
defined as ... ⟶ Cⁿ⁻² ⟶ Cⁿ⁻¹ ⟶ ker(d : Cⁿ ⟶ Cⁿ⁺¹) ⟶ 0 ⟶ 0 ⟶ ..., with the kernel
in degree `n`. -/
def truncation (C : CochainComplex 𝓐 ℤ) (n : ℤ) : CochainComplex 𝓐 ℤ
    where
  pt i := if i < n then C.pt i else if i = n then kernel (C.d n (n + 1)) else 0
  d i j :=
    if hi : i + 1 = j then
      -- (complex_shape.up ℤ).rel i j
        if hj : j < n then
        eqToHom (by rw [if_pos (lt_trans (show i < j by linarith) hj)]) ≫
          C.d i j ≫ eqToHom (by rw [if_pos hj])
      else
        if hj_eq : j = n then
          eqToHom (by rw [if_pos (show i < n by linarith)]) ≫
            eqToHom (by rw [show i = n - 1 by linarith]) ≫
              (kernel.lift (C.d n (n + 1)) (C.d (n - 1) n) (C.d_comp_d (n - 1) n (n + 1)) :
                  C.pt (n - 1) ⟶ kernel (C.d n (n + 1))) ≫
                eqToHom (by rw [if_neg hj, if_pos hj_eq])
        else 0
    else 0
  shape' i j := by
    rintro h : ¬i + 1 = j
    rw [dif_neg h]
  d_comp_d' i j k := by
    rintro (rfl : i + 1 = j) (rfl : i + 1 + 1 = k)
    rw [dif_pos rfl]
    by_cases hin : i + 1 < n
    · rw [dif_pos hin]
      rw [dif_pos rfl]
      by_cases hin' : i + 1 + 1 < n
      · rw [dif_pos hin']
        simp only [Category.assoc, CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp,
          HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]
      · rw [dif_neg hin']
        have hn : n = i + 1 + 1; linarith
        subst hn
        rw [dif_pos rfl]
        simp only [CategoryTheory.eqToHom_trans_assoc, Category.assoc, Preadditive.IsIso.comp_left_eq_zero]
        rw [← Category.assoc, ← Category.assoc, comp_mono_zero_iff]
        ext
        simp
    · rw [dif_neg hin]
      by_cases hn : i + 1 = n
      ·
        rw [dif_pos hn, dif_pos rfl, dif_neg (show ¬i + 1 + 1 < n by linarith),
          dif_neg (show ¬i + 1 + 1 = n by linarith), comp_zero]
      · rw [dif_neg hn, zero_comp]

namespace Truncation

@[reducible]
def xIsoOfLt {i n : ℤ} (h : i < n) : (C.truncation n).pt i ≅ C.pt i :=
  eqToIso (by simp [truncation, if_pos h])

-- don't know whether to go for kernel of d_n or of d_i!
@[reducible]
def xIsoOfEq {i n : ℤ} (h : i = n) : (C.truncation n).pt i ≅ kernel (C.d n (n + 1)) :=
  eqToIso (by subst h <;> simp [truncation, if_neg (show ¬i < i by linarith)])

@[reducible]
def xIsoOfEq' {i n : ℤ} (h : i = n) : (C.truncation n).pt i ≅ kernel (C.d i (i + 1)) :=
  eqToIso (by subst h <;> simp [truncation, if_neg (show ¬i < i by linarith)])

theorem isZero_x_of_lt {i n : ℤ} (h : n < i) : IsZero ((C.truncation n).pt i) := by
  simp [truncation, if_neg (show ¬i < n by linarith), if_neg (show ¬i = n by linarith),
    is_zero_zero]

theorem boundedBy (n : ℤ) :
    ((HomotopyCategory.quotient _ _).obj (C.truncation n)).BoundedBy (n + 1) :=
  by
  intro i hi
  dsimp only [HomotopyCategory.quotient_obj_as, truncation]
  rw [if_neg, if_neg]
  · apply is_zero_zero
  · linarith
  · linarith

instance isBoundedAbove (n : ℤ) :
    ((HomotopyCategory.quotient _ _).obj (C.truncation n)).IsBoundedAbove :=
  ⟨⟨n + 1, boundedBy C n⟩⟩

def ι (n : ℤ) : C.truncation n ⟶ C
    where
  f i :=
    if hin : i < n then (xIsoOfLt C hin).hom
    else if hi : i = n then (xIsoOfEq C hi).hom ≫ kernel.ι _ ≫ eqToHom (by rw [hi]) else 0
  comm' i j := by
    rintro (rfl : i + 1 = j)
    dsimp only [truncation]
    simp only [eq_self_iff_true, CategoryTheory.eqToHom_trans_assoc, dif_pos]
    by_cases hiltn : i < n
    · rw [dif_pos hiltn]
      by_cases hi1ltn : i + 1 < n
      · rw [dif_pos hi1ltn, dif_pos hi1ltn]
        simp
        rfl
      · have hn : i + 1 = n; linarith
        subst hn
        rw [dif_neg hi1ltn, dif_neg hi1ltn]
        rw [dif_pos rfl, dif_pos rfl]
        simp only [eqToIso.hom, CategoryTheory.eqToHom_refl, Category.comp_id, Category.assoc,
          CategoryTheory.eqToHom_trans_assoc, Category.id_comp, kernel.lift_ι]
        congr <;> linarith
    · rw [dif_neg hiltn]
      by_cases hin : i = n
      · subst hin
        simp
      · rw [dif_neg hin]
        rw [dif_neg (show ¬i + 1 < n by linarith)]
        rw [dif_neg (show ¬i + 1 = n by linarith)]
        simp

def ιInv (n : ℤ) (hn : IsZero (C.pt (n + 1))) : C ⟶ C.truncation n
    where
  f i :=
    if hin : i < n then (xIsoOfLt C hin).inv
    else
      if hi : i = n then
        (eqToHom (by rw [hi]) : C.pt i ⟶ C.pt n) ≫
          kernel.lift (C.d n (n + 1)) (𝟙 (C.pt n)) (hn.eq_zero_of_tgt _) ≫ (xIsoOfEq C hi).inv
      else 0
  comm' i j := by
    rintro (rfl : i + 1 = j)
    dsimp only [truncation]
    simp only [eq_self_iff_true, eqToIso.inv, CategoryTheory.eqToHom_trans_assoc, dif_pos]
    by_cases hiltn : i < n
    · rw [dif_pos hiltn]
      by_cases hi1ltn : i + 1 < n
      · simp [dif_pos hi1ltn]
      · have hi1n : i + 1 = n; linarith
        subst hi1n
        simp only [eq_self_iff_true, add_left_inj, lt_self_iff_false, not_false_iff, dif_pos,
          dif_neg, CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp, ← Category.assoc]
        congr 1
        ext
        simp
    · rw [dif_neg hiltn]
      by_cases hin : i = n
      · simp [hin]
      · rw [dif_neg hin, zero_comp]
        rw [dif_neg (show ¬i + 1 < n by linarith)]
        rw [dif_neg (show ¬i + 1 = n by linarith), comp_zero]

theorem ι_iso (n : ℤ) (hC : ((HomotopyCategory.quotient _ _).obj C).BoundedBy (n + 1)) :
    IsIso (truncation.ι C n) :=
  {
    out :=
      ⟨ιInv C n (hC (n + 1) (by rfl)), by
        ext i
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ι, ι_inv, eqToIso.hom,
          eqToIso.inv]
        by_cases hiltn : i < n
        · simp [dif_pos hiltn]
        · rw [dif_neg hiltn, dif_neg hiltn]
          by_cases hin : i = n
          · subst hin
            simp only [eq_self_iff_true, CategoryTheory.eqToHom_refl, dif_pos, Category.id_comp, Category.assoc]
            rw [← Category.assoc (kernel.ι (C.d i (i + 1)))]
            suffices kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d i (i + 1)) (𝟙 (C.X i)) _ = 𝟙 _ by
              simp [this]
            · ext
              simp
            · apply IsZero.eq_zero_of_tgt
              simpa using hC (i + 1) (by rfl)
          · apply IsZero.eq_of_tgt
            apply is_zero_X_of_lt
            push_neg at hiltn 
            obtain h1 | h2 := lt_or_eq_of_le hiltn
            · exact h1
            · exact (hin h2.symm).elim, by
        ext i
        simp only [ι, ι_inv, eqToIso.inv, eqToIso.hom, HomologicalComplex.comp_f,
          HomologicalComplex.id_f]
        by_cases hiltn : i < n
        · simp [dif_pos hiltn]
        · rw [dif_neg hiltn, dif_neg hiltn]
          by_cases hin : i = n
          · subst hin
            simp only [CategoryTheory.eqToHom_refl, Category.id_comp, dif_pos, Category.comp_id, Category.assoc,
              CategoryTheory.eqToHom_trans_assoc, kernel.lift_ι]
          · apply IsZero.eq_of_tgt
            simpa using hC i _
            push_neg at hiltn 
            obtain h1 | h2 := lt_or_eq_of_le hiltn
            · exact int.add_one_le_iff.mpr h1
            · exact (hin h2.symm).elim⟩ }

/-- The obvious "inclusion" from the m'th truncation to the n'th, if m<=n. -/
def mapOfLe (m n : ℤ) (h : m ≤ n) : C.truncation m ⟶ C.truncation n
    where
  f i :=
    if him : i < m then (xIsoOfLt C him).hom ≫ (xIsoOfLt C (lt_of_lt_of_le him h)).inv
    else-- id
        if him' : i = m then
        -- domain is ker(d)
          if hin : i < n then
          (xIsoOfEq C him').hom ≫
            kernel.ι _ ≫ (eqToHom (by rw [him']) : C.pt m ⟶ C.pt i) ≫ (xIsoOfLt C hin).inv
        else
          (-- kernel.ι
                xIsoOfEq'
                C him').hom ≫
            (xIsoOfEq' C (by linarith : i = n)).inv
      else-- identity
        0
  comm' i j := by
    rintro (rfl : _ = _)
    delta truncation
    dsimp only [zero_add, neg_zero, add_zero, zero_lt_one, neg_neg, neg_eq_zero,
      HomologicalComplex.d_comp_d, dif_neg, dif_pos, Category.assoc, CategoryTheory.eqToHom_trans_assoc,
      CategoryTheory.eqToHom_refl, Category.id_comp, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero,
      Preadditive.IsIso.comp_left_eq_zero, comp_mono_zero_iff, HomologicalComplex.d_comp_eqToHom,
      add_tsub_cancel_right, ComplexShape.up_Rel, add_left_inj, eq_self_iff_true,
      equalizer_as_kernel, kernel.lift_ι, mul_one]
    simp only [eq_self_iff_true, eqToIso.hom, eqToIso.inv, CategoryTheory.eqToHom_trans,
      CategoryTheory.eqToHom_trans_assoc, dif_pos]
    by_cases him : i < m
    · rw [dif_pos him]
      by_cases hi1n : i + 1 < n
      · rw [dif_pos hi1n]
        by_cases hi1m : i + 1 < m
        · simp [dif_pos hi1m]
        · have hm : i + 1 = m; linarith
          subst hm
          rw [dif_neg hi1m, dif_pos rfl, dif_neg hi1m, dif_pos rfl, dif_pos hi1n]
          simp only [CategoryTheory.eqToHom_trans_assoc, Category.assoc, CategoryTheory.eqToHom_refl, Category.id_comp,
            kernel.lift_ι_assoc]
          congr <;> ring
      · rw [dif_neg hi1n]
        have hn : i + 1 = n; linarith
        subst hn
        have hm : m = i + 1; linarith
        subst hm
        simp
    · rw [dif_neg him]
      by_cases hm : i = m
      · subst hm
        rw [dif_pos rfl, dif_neg (show ¬i + 1 < i by linarith),
          dif_neg (show ¬i + 1 = i by linarith), zero_comp]
        obtain hn | rfl := lt_or_eq_of_le h
        · rw [dif_pos hn]
          by_cases hi1n : i + 1 < n
          · rw [dif_pos hi1n]
            simp
          · rw [dif_neg hi1n]
            have hn2 : i + 1 = n; linarith
            subst hn2
            simp
            have hi :
              eq_to_hom _ ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d (i + 1 - 1) (i + 1)) _ =
                kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) _ :=
              by ext; simp
            rw [← Category.assoc (eq_to_hom _), hi]
            swap; apply C.d_comp_d
            rw [← Category.assoc]
            convert zero_comp
            ext; simp
        ·
          rw [dif_neg him, dif_neg (show ¬i + 1 < i by linarith),
            dif_neg (show i + 1 ≠ i by linarith), comp_zero]
      ·
        rw [dif_neg hm, zero_comp, dif_neg (show ¬i + 1 < m by linarith),
          dif_neg (show i + 1 ≠ m by linarith), zero_comp]

def ιSucc (n : ℤ) : C.truncation n ⟶ C.truncation (n + 1) :=
  truncation.mapOfLe _ _ _ <| by simp only [le_add_iff_nonneg_right, zero_le_one]

theorem ιSucc_f_self {n : ℤ} :
    (ιSucc C n).f n =
      (xIsoOfEq C (rfl : n = n)).hom ≫ kernel.ι (C.d n (n + 1)) ≫ (xIsoOfLt C (by simp)).inv :=
  by simp [ι_succ, map_of_le]

--move
theorem HomologicalComplex.dFrom_eq_d_comp_xNextIso_inv {ι V : Type _} [Category V]
    [HasZeroMorphisms V] {c : ComplexShape ι} (C : HomologicalComplex V c) {i j : ι}
    (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv := by simp [C.d_from_eq r]

--- move
@[simp, reassoc]
theorem CategoryTheory.Limits.EqToHomCompImage.ι {C : Type _} [Category C] {X Y : C} {f f' : X ⟶ Y}
    [HasImage f] [HasImage f'] [HasEqualizers C] (h : f = f') :
    eqToHom (by simp_rw [h]) ≫ image.ι f' = image.ι f :=
  by
  subst h
  simp

--- move
@[simp, reassoc]
theorem CategoryTheory.Limits.EqToHomCompKernel.ι {C : Type _} [Category C] [Abelian C] {X Y : C}
    {f f' : X ⟶ Y} (h : f = f') : eqToHom (by simp_rw [h]) ≫ kernel.ι f' = kernel.ι f :=
  by
  subst h
  simp

-- move
attribute [reassoc] HomologicalComplex.d_comp_eqToHom

-- move
theorem CategoryTheory.Limits.factorThruImage_of_eq {A B : 𝓐} {f f' : A ⟶ B} (h : f = f') :
    factorThruImage f ≫ eqToHom (by rw [h]) = factorThruImage f' :=
  by
  subst h
  simp

-- lemma _root_.category_theory.limits.factor_thru_image_comp {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) :
--   factor_thru_image (f ≫ g) ≫ image.pre_comp f g = f ≫ factor_thru_image g :=
-- begin
--   exact image.factor_thru_image_pre_comp f g
-- end
theorem CategoryTheory.Limits.factorThruImage_iso_comp {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C)
    [IsIso f] : factorThruImage (f ≫ g) = f ≫ factorThruImage g ≫ inv (image.preComp f g) := by
  simp [← image.factorThruImage_preComp_assoc]

-- move
@[ext]
theorem Image.ι.hom_ext {A B X : 𝓐} (f : A ⟶ B) (s t : X ⟶ image f)
    (h : s ≫ image.ι f = t ≫ image.ι f) : s = t := by rwa [cancel_mono] at h 

-- move
@[reassoc]
theorem comp_factorThruImage_eq_zero {A B C : 𝓐} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0) :
    f ≫ factorThruImage g = 0 := by
  ext
  simp [w]

@[simp, reassoc]
theorem kernel_ι_comp_factorThruImage {A B : 𝓐} {f : A ⟶ B} : kernel.ι f ≫ factorThruImage f = 0 :=
  comp_factorThruImage_eq_zero (kernel.condition f)

def toImker (n : ℤ) : C.truncation n ⟶ imker C n
    where
  f i :=
    if hi : i = n - 1 then
      (xIsoOfLt C (show i < n by linarith)).hom ≫
        eqToHom (by rw [hi]) ≫
          factorThruImage (C.d (n - 1) n) ≫
            eqToHom (by rw [← C.X_prev_iso_comp_d_to]; show n - 1 + 1 = n; ring) ≫
              image.preComp (C.xPrevIso (show n - 1 + 1 = n by ring)).inv (C.dTo n) ≫
                (imker.xIsoImageOfEq C hi).inv
    else-- C(n-1) ⟶ Im(d^{n-1})
        if hn : i = n then
        (xIsoOfEq C hn).hom ≫
          kernel.lift (C.d n (n + 1) ≫ (C.xNextIso (show n + 1 = n + 1 from rfl)).inv) (kernel.ι _)
              (by rw [← Category.assoc, kernel.condition, zero_comp]) ≫
            eqToHom (by simp_rw [← C.d_from_eq_d_comp_X_next_iso_inv]) ≫
              (imker.kernelIsoXOfEq C hn).hom
      else 0
  comm' i j := by
    rintro (rfl : _ = _)
    by_cases hi : i = n - 1
    · rw [dif_pos hi]
      subst hi
      delta imker truncation; dsimp only
      rw [dif_pos rfl, dif_pos (show n - 1 + 1 = n by ring), dif_pos rfl,
        dif_neg (show ¬n - 1 + 1 < n by linarith), dif_pos (show n - 1 + 1 = n by ring),
        dif_neg (show n - 1 + 1 ≠ n - 1 by linarith), dif_pos (show n - 1 + 1 = n by ring)]
      simp only [← Category.assoc]
      congr 1
      ext
      delta imageToKernel'
      simp only [HomologicalComplex.xPrevIso_comp_dTo, Category.assoc, eqToIso.hom,
        CategoryTheory.eqToHom_refl, Category.comp_id, imker.xIsoImageOfEq_inv, CategoryTheory.eqToHom_trans,
        kernel.lift_ι, image.preComp_ι, CategoryTheory.Limits.EqToHomCompImage.ι, image.fac,
        CategoryTheory.Limits.EqToHomCompKernel.ι]
      rfl
    · rw [dif_neg hi]
      by_cases hn : i = n
      · subst hn
        simp only [dif_neg (show i + 1 ≠ i - 1 by linarith), imker.d_def, add_right_eq_self,
          one_ne_zero, not_false_iff, dif_neg, dite_eq_ite, if_t_t, comp_zero]
      · rw [dif_neg hn]
        by_cases hin : i + 1 = n - 1
        · rw [dif_pos hin]
          have hi : i = n - 2; linarith; subst hi
          delta truncation; dsimp only
          simp only [dif_pos (show n - 2 + 1 < n by linarith),
            C.d_comp_eq_to_hom_assoc (show n - 2 + 1 = n - 1 by ring),
            comp_factorThruImage_eq_zero_assoc, HomologicalComplex.d_comp_d, eqToIso.hom,
            zero_comp, CategoryTheory.eqToHom_trans_assoc, dif_pos, Category.assoc, ComplexShape.up_Rel,
            comp_zero]
        · rw [dif_neg hin]
          rw [dif_neg (show i + 1 ≠ n by intro h; apply hi; linarith)]
          rw [zero_comp, comp_zero]

example {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso f] : IsIso (image.preComp f g) :=
  inferInstance

example {𝒞 : Type} [Category 𝒞] {A B C D E P Q R : 𝒞} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (i : D ⟶ E) (φ : A ⟶ P) (ψ : P ⟶ Q) (ρ : Q ⟶ R) (σ : R ⟶ D)
    (commutes : f ≫ g ≫ h = φ ≫ ψ ≫ ρ ≫ σ) : f ≫ g ≫ h ≫ i = φ ≫ ψ ≫ ρ ≫ σ ≫ i := by
  simp [reassoc_of commutes]

--def kernel_comp_is_iso {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
--  kernel (f ≫ g) ≅ kernel f :=
--{ hom := kernel.lift _ (kernel.ι _) (begin rw [← cancel_mono g, category.assoc], simp, end),
--  inv := kernel.lift _ (kernel.ι _) (by simp), }
-- image f ⟶ image e ≫ f
def imageCompIsIsoLeft {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : image (f ≫ g) ≅ image g
    where
  hom :=
    image.lift
      ({  i := image g
          m := image.ι g
          e := f ≫ factorThruImage g } : MonoFactorisation (f ≫ g))
  inv :=
    image.lift
      ({  i := image (f ≫ g)
          m := image.ι (f ≫ g)
          e := inv f ≫ factorThruImage (f ≫ g) } : MonoFactorisation g)
  hom_inv_id := by dsimp at *; ext1; simp at *
  inv_hom_id := by dsimp at *; ext1; simp at *

@[simp]
theorem imageCompIsIsoLeft_comp_ι {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    (imageCompIsIsoLeft f g).hom ≫ image.ι g = image.ι (f ≫ g) := by simp [CochainComplex.truncation.imageCompIsIsoLeft]

@[simp]
theorem imageCompIsIsoLeft_comp_ι' {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] :
    (imageCompIsIsoLeft f g).inv ≫ image.ι (f ≫ g) = image.ι g := by simp [CochainComplex.truncation.imageCompIsIsoLeft]

theorem Image.lift_image_ι {A A' B : 𝓐} (f : A ⟶ B) (f' : A' ⟶ B) (e : A' ⟶ A) [IsIso e]
    (w : f' = e ≫ f) :
    image.lift
          ({  i := image f'
              m := image.ι f'
              e := factorThruImage f ≫ (imageCompIsIsoLeft e f).inv ≫ (imageIsoOfEq w.symm).hom
              fac := by subst w; simp [CochainComplex.truncation.imageCompIsIsoLeft, CategoryTheory.Limits.imageIsoOfEq] } :
            MonoFactorisation f) ≫
        image.ι f' =
      image.ι f :=
  by simp

theorem toImker_f_succ {n : ℤ} :
    (toImker C (n + 1)).f n =
      (xIsoOfLt C (by simp)).hom ≫ factorThruImage (C.d n (n + 1)) ≫ (imker.xIsoImage' C n).inv :=
  by
  delta CochainComplex.truncation.toImker
  dsimp only
  rw [dif_pos (show n = n + 1 - 1 by ring)]
  --  delta imker.X_iso_image',
  simp only [imker.xIsoImage, eqToIso.hom, imker.xIsoImageOfEq_inv, CategoryTheory.eqToHom_trans_assoc,
    Iso.trans_inv, imker.xIsoImage_inv, Category.assoc, eqToIso.inv, CategoryTheory.eqToHom_trans]
  simp only [imker.xIsoImage'_inv]
  --    top is `image (homological_complex.d_to C (n + 1)) ⟶ (C.imker (n + 1)).X n`
  -- bottom is `image (homological_complex.d_to C (n + 1)) ⟶ (C.imker (n + 1)).X n`
  simp only [← Category.assoc]
  congr 1
  ext
  simp only [HomologicalComplex.xPrevIso_comp_dTo, Category.assoc, image.preComp_ι,
    CategoryTheory.Limits.EqToHomCompImage.ι, image.fac]
  have foo :
    (image.isIsoComp (C.d n (n + 1))).inv ≫
        (CategoryTheory.Limits.imageIsoOfEq (C.d_to_eq rfl)).inv ≫ image.ι (HomologicalComplex.dTo C (n + 1)) =
      (image.ι (C.d n (n + 1)) : image (C.d n (n + 1)) ⟶ C.X (n + 1)) :=
    by
    ext; simp
    -- is this the right move? Surely?
    convert image.fac (C.d n (n + 1))
    /-
        𝓐 : Type u_1,
        _inst_1 : category 𝓐,
        _inst_2 : abelian 𝓐,
        C : cochain_complex 𝓐 ℤ,
        n : ℤ
        ⊢ (image.is_iso_comp (C.d n (n + 1))).inv ≫
              (image_iso_of_eq _).inv ≫ image.ι (homological_complex.d_to C (n + 1)) =
            image.ι (C.d n (n + 1))
        -/
    rw [← Category.assoc]
    convert Image.lift_image_ι _ _ _ (C.d_to_eq rfl); swap; infer_instance
    simp [image.isIsoComp, CategoryTheory.Limits.imageIsoOfEq]
    rw [← IsIso.eq_comp_inv]
    ext
    simp
    /-
        𝓐 : Type u_1,
        _inst_1 : category 𝓐,
        _inst_2 : abelian 𝓐,
        C : cochain_complex 𝓐 ℤ,
        n : ℤ
        ⊢ C.d n (n + 1) =
            factor_thru_image (C.d n (n + 1)) ≫
              (image_comp_is_iso_left (homological_complex.X_prev_iso C rfl).hom (C.d n (n + 1))).inv ≫
                (image_iso_of_eq _).hom ≫
                  eq_to_hom _ ≫ image.ι ((homological_complex.X_prev_iso C rfl).hom ≫ C.d n (n + 1))
        -/
    convert (image.fac (C.d n (n + 1))).symm
    /-
        𝓐 : Type u_1,
        _inst_1 : category 𝓐,
        _inst_2 : abelian 𝓐,
        C : cochain_complex 𝓐 ℤ,
        n : ℤ
        ⊢ (image_comp_is_iso_left (homological_complex.X_prev_iso C rfl).hom (C.d n (n + 1))).inv ≫
              (image_iso_of_eq _).hom ≫
                eq_to_hom _ ≫ image.ι ((homological_complex.X_prev_iso C rfl).hom ≫ C.d n (n + 1)) =
            image.ι (C.d n (n + 1))
        -/
    convert image_comp_is_iso_left_comp_ι' _ _
    delta CategoryTheory.Limits.imageIsoOfEq
    simp
  rw [foo]
  simp
  have := C.eq_to_hom_comp_d (rfl : n + 1 = n + 1) (show n + 1 - 1 + 1 = n + 1 by ring)
  rw [← this]
  simp only [← Category.assoc]
  congr 1; clear this foo
  simp

-- move!
theorem lt_of_not_lt_of_ne {a b : ℤ} (h1 : ¬a < b) (h2 : ¬a = b) : b < a :=
  by
  rcases lt_trichotomy a b with (h3 | rfl | h3)
  · contradiction
  · exact h2.elim rfl
  · exact h3

-- move!
instance Kernel.lift_iso_of_comp_mono {A B C : 𝓐} (f : A ⟶ B) (e : B ⟶ C) [Mono e] :
    IsIso
      (kernel.lift (f ≫ e) (kernel.ι f) (by rw [kernel.condition_assoc, zero_comp]) :
        kernel f ⟶ kernel (f ≫ e)) :=
  ⟨⟨kernel.lift _ (kernel.ι (f ≫ e)) (by rw [← cancel_mono e]; simp), by ext; simp, by ext; simp⟩⟩

theorem Kernel.ι_comp_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso g] :
    kernel.ι (f ≫ g) =
      inv (kernel.lift (f ≫ g) (kernel.ι f) (by simp) : kernel f ⟶ kernel (f ≫ g)) ≫ kernel.ι f :=
  by rw [IsIso.eq_inv_comp, kernel.lift_ι]

/-- Factors kernel.ι (iso ≫ g) as iso ≫ kernel.ι g ≫ iso. -/
theorem Kernel.ι_iso_comp {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso f] :
    kernel.ι (f ≫ g) =
      (kernel.lift g (kernel.ι (f ≫ g) ≫ f) (by simp) : kernel (f ≫ g) ⟶ kernel g) ≫
        kernel.ι g ≫ inv f :=
  by rw [← Category.assoc, kernel.lift_ι, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

instance Cokernel.desc_iso_of_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso f] :
    IsIso (cokernel.desc (f ≫ g) (cokernel.π g) (by simp) : cokernel (f ≫ g) ⟶ cokernel g) :=
  ⟨⟨cokernel.desc _ (cokernel.π (f ≫ g)) (by rw [← cancel_epi f, ← Category.assoc]; simp), by ext;
      simp, by ext; simp⟩⟩

instance Cokernel.desc_iso_of_iso' {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso g] :
    IsIso
      (cokernel.desc _ (g ≫ cokernel.π _) (by rw [← Category.assoc, cokernel.condition]) :
        cokernel f ⟶ cokernel (f ≫ g)) :=
  ⟨⟨cokernel.desc _ (inv g ≫ cokernel.π f) (by simp), by ext; simp, by ext; simp⟩⟩

theorem Cokernel.π_iso_comp {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso f] :
    cokernel.π (f ≫ g) =
      cokernel.π g ≫
        inv (cokernel.desc _ (cokernel.π g) (by simp) : cokernel (f ≫ g) ⟶ cokernel g) :=
  by rw [IsIso.eq_comp_inv, cokernel.π_desc]

/-- Factors cokernel.π (f ≫ iso) as iso ≫ cokernel.π f ≫ iso. -/
theorem Cokernel.π_comp_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [IsIso g] :
    cokernel.π (f ≫ g) =
      inv g ≫
        cokernel.π f ≫
          cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← Category.assoc, cokernel.condition]) :=
  by rw [cokernel.π_desc, IsIso.inv_hom_id_assoc]

instance {i n : ℤ} : Epi ((toImker C i).f n) :=
  by
  delta CochainComplex.truncation.toImker; dsimp only
  split_ifs with hn hi
  · subst hn
    simp only [CategoryTheory.Limits.epi_comp_isIso_iff_epi, CategoryTheory.Limits.epi_isIso_comp_iff_epi,
      factor_thru_image.category_theory.epi]
  · subst hi
    simp
    infer_instance
  · apply epi_of_target_iso_zero
    exact IsZero.isoZero (imker.x_isZero_of_ne C hn hi)

theorem mapOfLe_mono {m n : ℤ} (h : m ≤ n) (i : ℤ) : Mono ((mapOfLe C m n h).f i) :=
  by
  delta map_of_le; dsimp only
  split_ifs with hnotlt hnoteq <;> try infer_instance
  apply mono_of_source_iso_zero
  exact IsZero.isoZero (is_zero_X_of_lt C (lt_of_not_lt_of_ne hnotlt hnoteq))

instance ιSucc_mono {i n : ℤ} : Mono ((ιSucc C i).f n) :=
  by
  delta ι_succ
  apply CochainComplex.truncation.mapOfLe_mono

-- has_homology version of exact
theorem Abelian.exact_iff_hasHomology_zero {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) :
    Exact f g ↔ ∃ w : f ≫ g = 0, Nonempty (HasHomology f g 0) :=
  by
  rw [Preadditive.exact_iff_homology'_zero]
  apply exists_congr
  intro w
  constructor
  · rintro ⟨h⟩
    exact ⟨(homology'.has f g w).of_iso h⟩
  · rintro ⟨h⟩
    exact ⟨(homology'.has f g w).Iso h⟩

theorem ιSucc.comp_toImker_zero {i n : ℤ} : (ιSucc C i).f n ≫ (toImker C (i + 1)).f n = 0 :=
  by
  delta ι_succ map_of_le CochainComplex.truncation.toImker
  dsimp only
  by_cases h : n < i
  ·
    rw [dif_pos h, dif_neg (show n ≠ i + 1 - 1 by linarith), dif_neg (show n ≠ i + 1 by linarith),
      comp_zero]
  · rw [dif_neg h]
    by_cases hn : n = i
    · rw [dif_pos hn]
      subst hn
      rw [dif_pos (show n < n + 1 by linarith), dif_pos (show n = n + 1 - 1 by ring), ←
        image.factorThruImage_preComp_assoc, ←
        CategoryTheory.Limits.factorThruImage_of_eq
          (C.eq_to_hom_comp_d rfl (show n + 1 - 1 + 1 = n + 1 by ring)).symm]
      simp
    · rw [dif_neg hn, zero_comp]

theorem comp_zero_cancel_left {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (h : g = 0) : f ≫ g = 0 := by
  rw [h, comp_zero]

theorem comp_zero_cancel_right {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (h : f = 0) : f ≫ g = 0 := by
  rw [h, zero_comp]

theorem Kernel.ι_factorThruImage {A B : 𝓐} (f : A ⟶ B) :
    kernel.ι (factorThruImage f) =
      kernel.lift (factorThruImage f ≫ image.ι f) (kernel.ι (factorThruImage f))
          (by rw [kernel.condition_assoc, zero_comp]) ≫
        eqToHom (by simp) ≫ kernel.ι f :=
  by simp only [image.fac, CategoryTheory.Limits.EqToHomCompKernel.ι, kernel.lift_ι]

theorem Kernel.ι_factorThruImage_comp_cokernel_π {A B : 𝓐} (f : A ⟶ B) :
    kernel.ι (factorThruImage f) ≫ cokernel.π (kernel.ι f) = 0 :=
  by
  rw [kernel.ι_factor_thru_image, Category.assoc, Category.assoc, cokernel.condition]
  simp only [comp_zero]

theorem Kernel.ι_iso_is_zero {A B : 𝓐} (f : A ⟶ B) [IsIso f] : kernel.ι f = 0 :=
  IsZero.eq_zero_of_src (isZero_kernel_of_mono f) _

theorem Cokernel.π_iso_is_zero {A B : 𝓐} (f : A ⟶ B) [IsIso f] : cokernel.π f = 0 :=
  IsZero.eq_zero_of_tgt (isZero_cokernel_of_epi f) _

theorem ιSucc_toImker_π_ι {i n : ℤ} :
    kernel.ι ((toImker C (i + 1)).f n) ≫ cokernel.π ((ιSucc C i).f n) = 0 :=
  by
  delta CochainComplex.truncation.toImker ι_succ map_of_le
  dsimp only
  by_cases hn : n = i
  · subst hn
    -- I seem to have to do all the work myself here :-(
    rw [dif_pos (show n = n + 1 - 1 by ring), dif_neg (show ¬n < n by linarith),
      dif_pos (rfl : n = n), dif_pos (show n < n + 1 by linarith)]
    rw [kernel.ι_iso_comp, Category.assoc]
    apply comp_zero_cancel_left
    rw [kernel.ι_iso_comp, Category.assoc, Category.assoc]
    apply comp_zero_cancel_left
    rw [kernel.ι_comp_iso, Category.assoc, Category.assoc]
    apply comp_zero_cancel_left
    rw [cokernel.π_iso_comp, ← Category.assoc _ _ (inv _), ← Category.assoc _ _ (inv _), ←
      Category.assoc _ _ (inv _)]
    apply comp_zero_cancel_right
    rw [cokernel.π_comp_iso, ← Category.assoc _ _ (cokernel.desc _ _ _), ←
      Category.assoc _ _ (cokernel.desc _ _ _), ← Category.assoc _ _ (cokernel.desc _ _ _), ←
      Category.assoc _ _ (cokernel.desc _ _ _)]
    apply comp_zero_cancel_right
    rw [←
      CategoryTheory.Limits.EqToHomCompKernel.ι
        (CategoryTheory.Limits.factorThruImage_of_eq
            (C.eq_to_hom_comp_d (show n + 1 - 1 + 1 = n + 1 by ring) rfl)).symm]
    rw [kernel.ι_comp_iso, Category.assoc, Category.assoc]
    apply comp_zero_cancel_left
    apply comp_zero_cancel_left
    have foo :=
      CategoryTheory.Limits.factorThruImage_iso_comp
        (eq_to_hom (by rw [show n + 1 - 1 = n by ring]) : C.X (n + 1 - 1) ⟶ C.X n) (C.d n (n + 1))
    rw [CategoryTheory.Limits.factorThruImage_iso_comp
        (eq_to_hom (by rw [show n + 1 - 1 = n by ring]) : C.X (n + 1 - 1) ⟶ C.X n) (C.d n (n + 1))]
    rw [kernel.ι_iso_comp, Category.assoc]
    apply comp_zero_cancel_left
    simp only [kernel.ι_comp_iso, kernel.ι_factor_thru_image_comp_cokernel_π, CategoryTheory.inv_eqToHom,
      Category.assoc, eqToIso.hom, CategoryTheory.eqToHom_refl, eqToIso.inv, Category.id_comp,
      CategoryTheory.eqToHom_trans_assoc, comp_zero]
  · rw [dif_neg (show n ≠ i + 1 - 1 by intro h; apply hn; linarith)]
    by_cases hn1 : n = i + 1
    · rw [dif_pos hn1]
      apply comp_zero_cancel_right
      -- kernel of iso is 0
      apply kernel.ι_iso_is_zero
    · rw [dif_neg hn1]
      by_cases hni : n < i
      · rw [dif_pos hni]
        apply comp_zero_cancel_left
        -- cokernel of iso is 0
        apply cokernel.π_iso_is_zero
      · rw [dif_neg hni, dif_neg hn]
        -- middle term is 0
        apply comp_zero_cancel_right
        apply IsZero.eq_zero_of_tgt
        apply is_zero_X_of_lt
        rw [not_lt] at hni 
        obtain hlt | rfl := lt_or_eq_of_le hni
        · rw [Int.lt_iff_add_one_le] at hlt 
          obtain hlt' | rfl := lt_or_eq_of_le hlt
          · exact hlt'
          · exact hn1.elim rfl
        · exact hn.elim rfl

-- image.factor_thru_image_pre_comp
--example {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [is_iso f] : is_iso (image.pre_comp f g) :=
--infer_instance
def kernelFactorThruImageIso {A B : 𝓐} (f : A ⟶ B) : kernel (factorThruImage f) ≅ kernel f :=
  (kernelCompMono (factorThruImage f) (image.ι f)).symm.trans (kernelIsoOfEq (by simp))

-- lemma factor_thru_image_comp {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) :
-- factor_thru_image (f ≫ g) ≫ (image.pre_comp f g) = f ≫ factor_thru_image g :=
-- begin
--   exact image.factor_thru_image_pre_comp f g,
-- end
theorem epi_kernel_lift_zero_iff_epi {A B C : 𝓐} (f : A ⟶ B) :
    Epi (kernel.lift (0 : B ⟶ C) f comp_zero) ↔ Epi f :=
  by
  conv_rhs => rw [← kernel.lift_ι (0 : B ⟶ C) f comp_zero]
  rw [CategoryTheory.Limits.epi_isIso_comp_iff_epi]

def kernelCompIsIso {X Y Z : 𝓐} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : kernel (f ≫ g) ≅ kernel f
    where
  hom := kernel.lift _ (kernel.ι _) (by rw [← cancel_mono g, Category.assoc]; simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

def kernelIsoAssoc {A B C D : 𝓐} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    kernel (f ≫ g ≫ h) ≅ kernel ((f ≫ g) ≫ h) :=
  kernelIsoOfEq (by rw [Category.assoc])

@[simp]
theorem mono_comp_iso_iff_mono {V : Type _} [Category V] {A B C : V} (e : A ≅ B) (f : B ⟶ C) :
    Mono (e.hom ≫ f) ↔ Mono f := by
  constructor
  · intro h
    have := mono_comp e.inv (e.hom ≫ f)
    simpa using this
  · apply mono_comp

@[simp]
theorem mono_comp_isIso_iff_mono {V : Type _} [Category V] {A B C : V} (e : A ⟶ B) [IsIso e]
    (f : B ⟶ C) : Mono (e ≫ f) ↔ Mono f :=
  mono_comp_iso_iff_mono (asIso e) _

theorem ιSucc_toImker_ex_π_aux₁ {i n : ℤ} (h : n = i) :
    Epi (kernel.lift ((toImker C (i + 1)).f n) ((ιSucc C i).f n) (ιSucc.comp_toImker_zero C)) :=
  by
  delta CochainComplex.truncation.toImker ι_succ map_of_le; dsimp only
  have hn : n = n + 1 - 1 := by ring
  subst h
  -- `simp_rw dif_pos (show n = n + 1 - 1, by ring)` fails so we hack our way around it.
  suffices :
    epi
      (kernel.lift
        ((X_iso_of_lt C _).hom ≫
          eq_to_hom _ ≫
            factor_thru_image (C.d (n + 1 - 1) (n + 1)) ≫
              eq_to_hom _ ≫
                image.preComp (HomologicalComplex.xPrevIso C _).inv
                    (HomologicalComplex.dTo C (n + 1)) ≫
                  (imker.xIsoImageOfEq C (show n = n + 1 - 1 by ring)).inv)
        _ _)
  -- 14 goals but bear with me
  convert this
  -- 11 goals
  rw [dif_pos hn]
  -- 4 goals
  rw [dif_pos hn]
  -- 3 goals
  swap;
  infer_instance
  -- 2 goals
  swap
  · convert ι_succ.comp_toImker_zero C
    delta CochainComplex.truncation.toImker; dsimp only; rw [dif_pos hn]
  -- rw finally works!,
  -- back to 1 goal
  simp only [zero_lt_one, dif_pos, dif_neg, CategoryTheory.eqToHom_refl, Category.id_comp, eq_self_iff_true,
    not_false_iff, eqToIso.hom, CategoryTheory.eqToHom_trans, lt_add_iff_pos_right, lt_self_iff_false,
    eqToIso.inv]
  -- goal is epi (mess : ker(d)->)
  rw [← epi_iso_comp_iff_epi _ (CategoryTheory.Limits.kernelIsIsoComp _ _)]
  -- now knock them off the other end
  rw [← epi_iso_comp_iff_epi _ (CochainComplex.truncation.kernelIsoAssoc _ _ _)]
  rw [← epi_iso_comp_iff_epi _ (CochainComplex.truncation.kernelCompIsIso _ _)]
  -- simp now goes down the wrong track
  /- The goal is now to prove that some monstrous map
  
    (C.truncation n).X n ⟶ kernel (eq_to_hom _ ≫ factor_thru_image (C.d (n + 1 - 1) (n + 1)))
  
    is an epimorphism. This map is essentially the identity map
    from ker C.d n (n+1) to itself, modulo the usual cannonical
    isomorphisms. My plan is to pre and post compose with some more
    canonical isomorphisms to actually get a map from an object
    to itself and then claim that it is epi because it's the identity
    and then hopefully `ext, simp` will do it.
    -/
  rw [← epi_comp_iso_iff_epi (X_iso_of_eq C rfl).symm]
  have foo : eq_to_hom _ ≫ C.d (n + 1 - 1) (n + 1) = C.d n (n + 1) :=
    C.eq_to_hom_comp_d (show n + 1 = n + 1 by rfl) (show n + 1 - 1 + 1 = n + 1 by ring)
  rw [← epi_iso_comp_iff_epi _ (CategoryTheory.Limits.kernelIsoOfEq (image.factorThruImage_preComp _ _).symm)]
  swap; infer_instance; swap; infer_instance
  rw [← epi_iso_comp_iff_epi _ (CochainComplex.truncation.kernelCompIsIso _ _)]
  rw [← epi_iso_comp_iff_epi _ (CochainComplex.truncation.kernelFactorThruImageIso _)]
  rw [← epi_iso_comp_iff_epi _ (CategoryTheory.Limits.kernelIsoOfEq foo)]
  let t := _; change epi t
  suffices t = 𝟙 _ by rw [this]; infer_instance
  apply equalizer.hom_ext
  dsimp only [t, CochainComplex.truncation.kernelCompIsIso, CochainComplex.truncation.kernelIsoAssoc, CochainComplex.truncation.kernelFactorThruImageIso, Iso.trans_hom,
    Iso.symm_hom]
  simp only [Category.id_comp, Category.assoc, kernel_iso_of_eq_hom_comp_ι,
    kernel_iso_of_eq_hom_comp_ι_assoc, CategoryTheory.Limits.kernelCompMono_inv, kernel.lift_ι, CategoryTheory.Limits.kernelIsIsoComp_hom,
    kernel.lift_ι_assoc]
  simp only [eqToIso.inv, eqToIso.hom, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl, Category.comp_id,
    CategoryTheory.eqToHom_trans_assoc, Category.id_comp]

theorem ιSucc_toImker_ex_π {i n : ℤ} :
    Epi (kernel.lift ((toImker C (i + 1)).f n) ((ιSucc C i).f n) (ιSucc.comp_toImker_zero C)) :=
  by
  by_cases h : n = i
  · apply ι_succ_to_imker_ex_π_aux₁; exact h
  delta CochainComplex.truncation.toImker ι_succ map_of_le; dsimp only
  by_cases hn : n = i + 1
  · apply epi_of_target_iso_zero
    apply IsZero.isoZero
    apply @CategoryTheory.Limits.isZero_kernel_of_mono _ _ _ _ _ _ _
    subst hn
    rw [dif_neg (show i + 1 ≠ i + 1 - 1 by linarith), dif_pos rfl]
    apply mono_comp
  · suffices epi (kernel.lift (0 : (C.truncation (i + 1)).pt n ⟶ (C.imker (i + 1)).pt n) _ _)
      by
      convert this
      rw [dif_neg (show n ≠ i + 1 - 1 by ring_nf <;> exact h)]
      rw [dif_neg hn]
      rw [dif_neg (show n ≠ i + 1 - 1 by ring_nf <;> exact h)]
      rw [dif_neg hn]
    swap
    · convert ι_succ.comp_toImker_zero C
      delta CochainComplex.truncation.toImker; dsimp only
      rw [dif_neg (show n ≠ i + 1 - 1 by ring_nf <;> exact h)]
      rw [dif_neg hn]
    rw [epi_kernel_lift_zero_iff_epi]
    by_cases hi : n < i
    · rw [dif_pos hi]
      infer_instance
    · rw [dif_neg hi]
      rw [dif_neg h]
      apply epi_of_target_iso_zero
      apply IsZero.isoZero
      apply is_zero_X_of_lt
      -- we've been here before
      rw [not_lt] at hi 
      obtain hlt | rfl := lt_or_eq_of_le hi
      · rw [Int.lt_iff_add_one_le] at hlt 
        obtain hlt' | rfl := lt_or_eq_of_le hlt
        · exact hlt'
        · exact hn.elim rfl
      · exact h.elim rfl

theorem mono_of_epi_of_comp_mono {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [Epi f] [Mono (f ≫ g)] :
    Mono g := by
  haveI : mono f := mono_of_mono f g
  haveI : is_iso f := is_iso_of_mono_of_epi _
  exact (CochainComplex.truncation.mono_comp_isIso_iff_mono f g).mp inferInstance

theorem mono_coker_desc_congr {A B C : 𝓐} {f f' : A ⟶ B} (h : f = f') (g : B ⟶ C) (w : f ≫ g = 0) :
    Mono (cokernel.desc f g w) ↔ Mono (cokernel.desc f' g (h ▸ w)) := by subst h

theorem Cokernel.desc_comp_iso_left {A B C D : 𝓐} {e : A ⟶ B} [IsIso e] (f : B ⟶ C) (g : C ⟶ D)
    (w : f ≫ g = 0) :
    cokernel.desc (e ≫ f) g (by simp [w]) =
      cokernel.desc _ (cokernel.π f) (by simp) ≫ cokernel.desc f g w :=
  by
  ext
  simp

theorem Cokernel.desc_comp_snd_right {A B C D : 𝓐} {e : A ⟶ B} (f : B ⟶ C) (g : C ⟶ D)
    (w : e ≫ f = 0) :
    cokernel.desc e (f ≫ g) (by rw [← Category.assoc, w, zero_comp]) = cokernel.desc e f w ≫ g :=
  by
  ext
  simp

theorem yet_another_cokernel_lemma {A B C D : 𝓐} {e : A ⟶ B} (f : B ⟶ C) (g : C ⟶ D)
    (w : e ≫ f ≫ g = 0) :
    cokernel.desc _ (f ≫ cokernel.π _) (by rw [← Category.assoc, cokernel.condition]) ≫
        cokernel.desc (e ≫ f) g (by simp [w]) =
      cokernel.desc e (f ≫ g) w :=
  by
  ext
  simp

theorem meh {A B C D : 𝓐} {f : A ⟶ B} (e : C ≅ B) (g : B ⟶ D) (w : f ≫ g = 0) :
    Mono (cokernel.desc (f ≫ e.inv) (e.hom ≫ g) (by simp [w])) ↔ Mono (cokernel.desc f g w) :=
  by
  rw [← yet_another_cokernel_lemma]
  convert CochainComplex.truncation.mono_comp_isIso_iff_mono _ _; simp; simp
  --  rw ← yet_another_cokernel_lemma,
  --  apply @is_iso.comp_is_iso _ _ _ _ _ _ _ infer_instance infer_instance,
  clear w g
  apply Cokernel.desc_iso_of_iso'

theorem first_isomorphism_theorem {A B : 𝓐} (f : A ⟶ B) :
    IsIso
      (cokernel.desc (kernel.ι f) (factorThruImage f)
        (by simp only [kernel_ι_comp_factor_thru_image])) :=
  by
  convert (inferInstance : is_iso (Abelian.coimageIsoImage' f).hom)
  simp [← cancel_mono (image.ι f), ← cancel_epi (cokernel.π (kernel.ι f))]

/-
instance cokernel.desc_iso_of_iso {A B C : 𝓐} (f : A ⟶ B) (g : B ⟶ C) [is_iso f] :
  is_iso (cokernel.desc (f ≫ g) (cokernel.π g) (by simp) : cokernel (f ≫ g) ⟶ cokernel g) :=
  -/
theorem ιSucc_toImker_ι_ex_aux {n : ℤ} :
    Mono (cokernel.desc ((ιSucc C n).f n) ((toImker C (n + 1)).f n) (ιSucc.comp_toImker_zero C)) :=
  by
  rw [mono_coker_desc_congr (ι_succ_f_self C)]
  /-
    𝓐 : Type u_1,
    _inst_1 : category 𝓐,
    _inst_2 : abelian 𝓐,
    C : cochain_complex 𝓐 ℤ,
    n : ℤ
    ⊢ mono
        (cokernel.desc ((X_iso_of_eq C rfl).hom ≫ kernel.ι (C.d n (n + 1)) ≫ (X_iso_of_lt C _).inv)
           ((to_imker C (n + 1)).f n)
           _)
    -/
  simp_rw [CochainComplex.truncation.toImker_f_succ C]
  rw [Cokernel.desc_comp_iso_left]; swap;
  simp [_root_.category_theory.limits.factorThruImage_iso_comp]
  apply @mono_comp _ _ _ _ _ _ _ _ _; infer_instance
  rw [meh]; swap; simp
  simp
  /-
    𝓐 : Type u_1,
    _inst_1 : category 𝓐,
    _inst_2 : abelian 𝓐,
    C : cochain_complex 𝓐 ℤ,
    n : ℤ
    ⊢ mono
        (cokernel.desc (kernel.ι (C.d n (n + 1)) ≫ (X_iso_of_lt C _).inv)
           ((X_iso_of_lt C _).hom ≫ factor_thru_image (C.d n (n + 1)) ≫ (imker.X_iso_image' C n).inv)
           _)
    -/
  rw [Cokernel.desc_comp_snd_right];
  swap; simp
  apply @mono_comp _ _ _ _ _ _ _ _ _; swap; infer_instance
  apply @IsIso.mono_of_iso _ _ _ _ _ _
  apply first_isomorphism_theorem

theorem ιSucc_toImker_ι_ex {i n : ℤ} :
    Mono (cokernel.desc ((ιSucc C i).f n) ((toImker C (i + 1)).f n) (ιSucc.comp_toImker_zero C)) :=
  by
  by_cases h : n = i
  · subst h
    --    delta ι_succ map_of_le, dsimp,
    apply ι_succ_to_imker_ι_ex_aux
  · by_cases hni : n < i
    · apply mono_of_source_iso_zero
      apply IsZero.isoZero
      apply @CategoryTheory.Limits.isZero_cokernel_of_epi _ _ _ _ _ _ _
      dsimp only [ι_succ]
      dsimp only [ι_succ, map_of_le]; dsimp only
      simp [dif_pos hni]
      infer_instance
    · by_cases hni1 : n = i + 1
      -- or aomwrhibf
      · subst hni1
        suffices mono ((CochainComplex.truncation.toImker C (i + 1)).f (i + 1))
          by
          rw [←
            cokernel.π_desc ((ι_succ C i).f (i + 1)) ((CochainComplex.truncation.toImker C (i + 1)).f (i + 1))
              (ι_succ.comp_toImker_zero C)] at
            this 
          exact @mono_of_epi_of_comp_mono _ _ _ _ _ _ _ _ _ this
        delta CochainComplex.truncation.toImker
        dsimp only
        rw [dif_neg (show i + 1 ≠ i + 1 - 1 by linarith)]
        rw [dif_pos rfl]
        simp
        infer_instance
      · apply mono_of_source_iso_zero
        apply IsZero.isoZero
        apply @CategoryTheory.Limits.isZero_cokernel_of_epi _ _ _ _ _ _ _
        apply epi_of_target_iso_zero
        apply IsZero.isoZero
        apply is_zero_X_of_lt
        apply lt_of_not_lt_of_ne _ hni1
        push_neg at hni ⊢
        obtain hni | rfl := lt_or_eq_of_le hni
        · linarith
        · exact h.elim rfl

def ιSuccToImkerHasHomologyZero {i n : ℤ} :
    HasHomology ((ιSucc C i).f n) ((toImker C (i + 1)).f n) 0
    where
  w := ιSucc.comp_toImker_zero C
  π := 0
  ι := 0
  π_ι := by simp [ι_succ_to_imker_π_ι]
  ex_π := by rw [← epi_iff_exact_zero_right]; apply ι_succ_to_imker_ex_π
  ι_ex := by rw [← mono_iff_exact_zero_left]; apply ι_succ_to_imker_ι_ex
  epi_π := epi_of_target_iso_zero _ (Iso.refl _)
  mono_ι := mono_of_source_iso_zero _ (Iso.refl _)

theorem shortExact_ιSucc_toImker (i : ℤ) (n : ℤ) :
    ShortExact ((ιSucc C i).f n) ((toImker C (i + 1)).f n) :=
  { mono := inferInstance
    Epi := inferInstance
    exact := by
      rw [Abelian.exact_iff_hasHomology_zero]
      exact ⟨ι_succ.comp_toImker_zero C, ⟨ι_succ_to_imker_has_homology_zero C⟩⟩ }

end Truncation

end CochainComplex

