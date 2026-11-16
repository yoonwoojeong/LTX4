import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Exact
import LiquidTensorExperiment.ForMathlib.HomologicalComplexShift
import LiquidTensorExperiment.ForMathlib.SplitExact
import Mathlib.CategoryTheory.Triangulated.Rotate
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.Additive
import LiquidTensorExperiment.ForMathlib.HomologicalComplexAbelian
import LiquidTensorExperiment.ForMathlib.HomotopyCategory
import LiquidTensorExperiment.ForMathlib.Triangle

#align_import for_mathlib.mapping_cone

noncomputable section

universe v u

open scoped Classical

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

-- Porting note: Lean 3's `@[simp, reassoc]` is `@[reassoc (attr := simp)]` in Lean 4 (`reassoc (attr := simp)`
-- only adds `simp` to the `_assoc` version).
namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [Abelian V]

variable (A B C : CochainComplex V ℤ) (f : A ⟶ B) (g : B ⟶ C)

@[reassoc (attr := simp)]
theorem Homotopy.comp_xEqToIso {X Y : CochainComplex V ℤ} {f g : X ⟶ Y} (h : Homotopy f g) (i : ℤ)
    {j k : ℤ} (e : j = k) : h.hom i j ≫ (Y.xEqToIso e).hom = h.hom i k := by subst e; simp

@[reassoc (attr := simp)]
theorem Homotopy.xEqToIso_comp {X Y : CochainComplex V ℤ} {f g : X ⟶ Y} (h : Homotopy f g) {i j : ℤ}
    (e : i = j) (k : ℤ) : (X.xEqToIso e).hom ≫ h.hom j k = h.hom i k := by subst e; simp

@[simp]
theorem xEqToIso_shift (n i j : ℤ) (h : i = j) : xEqToIso (A⟦n⟧) h = A.xEqToIso (congr_arg (· + n) h) :=
  rfl

@[reassoc (attr := simp)]
theorem retraction_x_eq_to_hom (h : ∀ i, Splitting (f.f i) (g.f i)) {i j : ℤ} (e : i = j) :
    (h i).retraction ≫ (A.xEqToIso e).hom = (B.xEqToIso e).hom ≫ (h j).retraction := by
  subst e
  simp

@[reassoc (attr := simp)]
theorem section_x_eq_to_hom (h : ∀ i, Splitting (f.f i) (g.f i)) {i j : ℤ} (e : i = j) :
    (h i).section ≫ (B.xEqToIso e).hom = (C.xEqToIso e).hom ≫ (h j).section := by subst e; simp

-- Porting note: made reducible so that `ext` lemmas for `biprod` apply to maps out of / into `Cone.x`
@[reducible]
def Cone.x : ℤ → V := fun i => A.X (i + 1) ⊞ B.X i

variable {A B C}

def Cone.d : ∀ i j : ℤ, Cone.x A B i ⟶ Cone.x A B j := fun i j =>
  if hij : i + 1 = j then
    biprod.lift (biprod.desc (-A.d _ _) 0) (biprod.desc (f.f _ ≫ (B.xEqToIso hij).hom) (B.d _ _))
  else 0

/-- The mapping cone of a morphism `f : A → B` of homological complexes. -/
def cone : CochainComplex V ℤ where
  X := Cone.x A B
  d := Cone.d f
  shape i j hij := dif_neg hij
  d_comp_d' i j k (hij : _ = _) (hjk : _ = _) :=
    by
    substs hij hjk
    apply biprod.hom_ext <;> ext <;> simp [Cone.d]

@[simp]
theorem cone_x (i : ℤ) : (cone f).X i = (A.X (i + 1) ⊞ B.X i) :=
  rfl

@[simp]
theorem cone_d : (cone f).d = Cone.d f :=
  rfl

def cone.in : B ⟶ cone f where
  f i := biprod.inr
  comm' i j hij := by
    dsimp [cone_d, Cone.d]; dsimp at hij ; rw [dif_pos hij]
    ext <;>
      simp only [comp_zero, Category.assoc, Category.comp_id, biprod.inr_desc, biprod.inr_fst,
        biprod.lift_fst, biprod.inr_snd, biprod.lift_snd]

attribute [local instance] CategoryTheory.endofunctorMonoidalCategory Discrete.addMonoidal

def cone.out : cone f ⟶ A⟦(1 : ℤ)⟧ where
  f i := biprod.fst
  comm' i j (hij : _ = _) := by
    subst hij
    dsimp [cone_d, Cone.d]
    ext <;> simp

@[simps]
def cone.triangle : Triangle (CochainComplex V ℤ)
    where
  obj₁ := A
  obj₂ := B
  obj₃ := cone f
  mor₁ := f
  mor₂ := cone.in f
  mor₃ := cone.out f

variable (V)

@[simps]
def HomotopyCategory.liftTriangle :
    Triangle (CochainComplex V ℤ) ⥤
      Triangle (HomotopyCategory V (ComplexShape.up ℤ))
    where
  obj t :=
    Triangle.mk ((HomotopyCategory.quotient _ _).map t.mor₁)
      ((HomotopyCategory.quotient _ _).map t.mor₂) ((HomotopyCategory.quotient _ _).map t.mor₃)
  map {t t'} f :=
    { hom₁ := (HomotopyCategory.quotient _ _).map f.hom₁
      hom₂ := (HomotopyCategory.quotient _ _).map f.hom₂
      hom₃ := (HomotopyCategory.quotient _ _).map f.hom₃
      comm₁ := by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, f.comm₁]
      comm₂ := by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, f.comm₂]
      comm₃ := by dsimp; rw [← Functor.map_comp, ← Functor.map_comp, f.comm₃] }
  map_id X := by
    ext <;> exact CategoryTheory.Functor.map_id (HomotopyCategory.quotient V (ComplexShape.up ℤ)) _
  map_comp {X Y Z} f g := by
    ext <;> exact CategoryTheory.Functor.map_comp (HomotopyCategory.quotient V (ComplexShape.up ℤ)) _ _

variable {V}

@[simps]
def cone.triangleₕ : Triangle (HomotopyCategory V (ComplexShape.up ℤ)) :=
  (HomotopyCategory.liftTriangle _).obj (cone.triangle f)

section ConeFunctorial

variable {f} {A' B' : CochainComplex V ℤ} {f' : A' ⟶ B'} {i₁ : A ⟶ A'} {i₂ : B ⟶ B'}

variable (comm : Homotopy (f ≫ i₂) (i₁ ≫ f'))

def cone.map : cone f ⟶ cone f'
    where
  f i := biprod.lift (biprod.desc (i₁.f _) 0) (biprod.desc (comm.hom _ _) (i₂.f _))
  comm' i j r := by
    change i + 1 = j at r 
    dsimp [cone_d, Cone.d]
    simp_rw [dif_pos r]
    apply CategoryTheory.Limits.biprod.hom_ext <;>
        simp only [biprod.lift_desc, add_zero, Preadditive.comp_neg, Category.assoc, comp_zero,
          biprod.lift_fst, biprod.lift_snd] <;>
      ext
    · simp only [Preadditive.comp_neg, biprod.inl_desc_assoc, Hom.comm, Preadditive.neg_comp]
    · simp only [Preadditive.comp_neg, biprod.inr_desc_assoc, zero_comp, neg_zero]
    · simp only [xEqToIso_f, Preadditive.comp_add, biprod.inl_desc_assoc, Category.assoc,
        Preadditive.neg_comp]
      have := comm.comm (i + 1)
      dsimp at this 
      rw [reassoc_of% this]
      subst r
      delta HomologicalComplex.dFrom fromNext toPrev HomologicalComplex.dTo
      simp only [xEqToIso_refl, Category.comp_id, AddMonoidHom.mk'_apply]
      have aux₁ : (ComplexShape.up ℤ).next (i + 1) = i + 1 + 1 := by simp only [CochainComplex.next]
      have aux₂ : i = (ComplexShape.up ℤ).prev (i + 1) := by
        simp only [CochainComplex.prev, add_tsub_cancel_right]
      rw [← aux₁]
      simp only [← add_assoc, add_left_neg, zero_add, add_comm (i₁.f (i + 1) ≫ f'.f (i + 1)),
        add_left_inj]
      congr 2
    · simp only [Preadditive.comp_add, biprod.inr_desc_assoc, zero_comp, Hom.comm]

@[reassoc (attr := simp)]
theorem cone.in_map : cone.in f ≫ cone.map comm = i₂ ≫ cone.in f' := by
  -- Porting note: Lean 3's recursive `ext` replaced by explicit `biprod.hom_ext`
  ext i
  dsimp [cone.map, cone.in]
  apply biprod.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem cone.map_out : cone.map comm ≫ cone.out f' = cone.out f ≫ i₁⟦(1 : ℤ)⟧' := by
  ext i
  dsimp [cone.map, cone.out]
  apply biprod.hom_ext' <;> simp

-- I suppose this is not true?
-- def cone.map_homotopy_of_homotopy' (comm' : homotopy (f ≫ i₂) (i₁ ≫ f')) :
--   homotopy (cone.map comm) (cone.map comm') := by admit
@[simps]
def cone.triangleₕMap : cone.triangleₕ f ⟶ cone.triangleₕ f'
    where
  hom₁ := (HomotopyCategory.quotient _ _).map i₁
  hom₂ := (HomotopyCategory.quotient _ _).map i₂
  hom₃ := (HomotopyCategory.quotient _ _).map <| cone.map comm
  comm₁ := by
    dsimp [cone.triangleₕ]; simp_rw [← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ comm
  comm₂ := by dsimp [cone.triangleₕ]; simp_rw [← Functor.map_comp]; simp
  comm₃ := by dsimp [cone.triangleₕ]; simp_rw [← Functor.map_comp]; simp

@[simps]
def cone.triangleMap (h : f ≫ i₂ = i₁ ≫ f') : cone.triangle f ⟶ cone.triangle f'
    where
  hom₁ := i₁
  hom₂ := i₂
  hom₃ := cone.map (Homotopy.ofEq h)
  comm₁ := by simpa [cone.triangle]
  comm₂ := by dsimp [cone.triangle]; simp
  comm₃ := by dsimp [cone.triangle]; simp

@[simp]
theorem cone.map_id (f : A ⟶ B) :
    cone.map (Homotopy.ofEq <| (Category.comp_id f).trans (Category.id_comp f).symm) = 𝟙 _ := by
  ext i
  dsimp [cone.map, cone]
  ext <;> simp

@[simp]
theorem cone.triangleMap_id (f : A ⟶ B) :
    cone.triangleMap ((Category.comp_id f).trans (Category.id_comp f).symm) = 𝟙 _ := by
  ext <;> simp

def cone.triangleFunctorial :
    Arrow (CochainComplex V ℤ) ⥤ Triangle (CochainComplex V ℤ)
    where
  obj f := cone.triangle f.hom
  map {f g} c := cone.triangleMap c.w.symm
  map_id X := cone.triangleMap_id _
  map_comp {X Y Z} f g := by
    -- Porting note: Lean 3's recursive `ext` replaced by explicit `biprod.hom_ext`
    ext
    · rfl
    · rfl
    · dsimp [cone.map, cone]
      apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

-- I suppose this is also not true?
-- def cone.triangleₕ_functorial :
--   arrow (homotopy_category V (complex_shape.up ℤ)) ⥤
--     Triangle (homotopy_category V (complex_shape.up ℤ)) :=
-- { obj := λ f, cone.triangleₕ f.hom.out,
--   map := λ f g c, @cone.triangleₕ_map _ _ _ _ _ _ _ _ _ c.left.out c.right.out
--   begin
--     refine homotopy_category.homotopy_of_eq _ _ _,
--     simpa [-arrow.w] using c.w.symm
--   end,
--   map_id' := by admit,
--   map_comp' := by admit }
open scoped ZeroObject

theorem HomologicalComplex.zero_x {ι : Type _} {c : ComplexShape ι} {C : HomologicalComplex V c}
    (hC : IsZero C) (i : ι) : IsZero (C.X i) :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero, ← HomologicalComplex.eval_obj, ←
    (HomologicalComplex.eval V c i).map_id, hC.eq_of_src (𝟙 C) 0]
  rfl

-- Porting note: Lean 3's recursive `ext` replaced by explicit `biprod.hom_ext`
def coneFromZero (A : CochainComplex V ℤ) : cone (0 : 0 ⟶ A) ≅ A
    where
  hom :=
    { f := fun i => biprod.snd
      comm' := by
        introv r
        dsimp [Cone.d] at *
        rw [dif_pos r]
        apply biprod.hom_ext' <;> simp }
  inv := cone.in _
  inv_hom_id := by
    ext i
    dsimp [cone.in]
    simp only [biprod.inr_snd]
  hom_inv_id := by
    ext i
    dsimp [cone.in]
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp
    all_goals
      apply IsZero.eq_of_src
      apply HomologicalComplex.zero_x
      apply Limits.isZero_zero

def coneToZero (A : CochainComplex V ℤ) : cone (0 : A ⟶ 0) ≅ A⟦(1 : ℤ)⟧
    where
  hom := cone.out _
  inv :=
    { f := fun i => biprod.inl
      comm' := by
        introv r
        dsimp [Cone.d] at *
        rw [dif_pos r]
        apply biprod.hom_ext <;> simp }
  hom_inv_id := by
    ext i
    dsimp [cone.out]
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp
    all_goals
      apply IsZero.eq_of_src
      apply HomologicalComplex.zero_x
      apply Limits.isZero_zero
  inv_hom_id := by
    ext i
    dsimp [cone.out]
    simp

def cone.descOfNullHomotopic (h : Homotopy (f ≫ g) 0) : cone f ⟶ C :=
  cone.map (h.trans (Homotopy.ofEq (comp_zero.symm : 0 = 0 ≫ 0))) ≫ (coneFromZero _).hom

def cone.liftOfNullHomotopic (h : Homotopy (f ≫ g) 0) : A ⟶ cone g⟦(-1 : ℤ)⟧ :=
  (shiftShiftNeg A (1 : ℤ)).inv ≫
    (shiftFunctor _ (-1 : ℤ)).map
      ((coneToZero _).inv ≫ cone.map (h.trans (Homotopy.ofEq (comp_zero.symm : 0 = 0 ≫ 0))).symm)

@[simps]
def ofTermwiseSplitMono (H : ∀ i, SplitMono (f.f i)) : B ⟶ B'
    where
  f i :=
    i₂.f i - (H i).retraction ≫ comm.hom i (i - 1) ≫ B'.d (i - 1) i -
      B.d i (i + 1) ≫ (H (i + 1)).retraction ≫ comm.hom (i + 1) i
  comm' i j (r : i + 1 = j) := by
    subst r;
    simp only [d_comp_d, sub_zero, Category.assoc, comp_zero, Preadditive.comp_sub, Hom.comm,
      Preadditive.sub_comp, zero_comp, sub_right_inj, d_comp_d_assoc]
    congr <;> ring

@[reassoc (attr := simp)]
theorem ofTermwiseSplitMono_commutes (H : ∀ i, SplitMono (f.f i)) :
    f ≫ ofTermwiseSplitMono comm H = i₁ ≫ f' :=
  by
  ext i
  dsimp
  have :
    f.f i ≫ i₂.f i =
      A.d i (i + 1) ≫ comm.hom (i + 1) i + comm.hom i (i - 1) ≫ B'.d (i - 1) i + i₁.f i ≫ f'.f i :=
    by
    rw [← HomologicalComplex.comp_f, comm.comm i]
    simp only [dNext, prevD, AddMonoidHom.mk'_apply, comp_f, add_left_inj]
    rw [← CochainComplex.next, ← CochainComplex.prev]
  simp only [Hom.comm_assoc, Preadditive.comp_sub, this]
  erw [SplitMono.id_assoc, SplitMono.id_assoc]
  simp [add_right_comm]

def ofTermwiseSplitMonoHomotopy (H : ∀ i, SplitMono (f.f i)) :
    Homotopy i₂ (ofTermwiseSplitMono comm H)
    where
  hom i j := (H i).retraction ≫ comm.hom i j
  zero _ _ r := by
    dsimp only
    rw [comm.zero _ _ r, comp_zero]
  comm i :=
    by
    simp only [dNext, prevD, AddMonoidHom.mk'_apply, Category.assoc, HomologicalComplex.ofTermwiseSplitMono_f]
    rw [← CochainComplex.next, ← CochainComplex.prev]; abel

@[simps]
def ofTermwiseSplitEpi (H : ∀ i, SplitEpi (f'.f i)) : A ⟶ A'
    where
  f i :=
    i₁.f i + comm.hom i (i - 1) ≫ (H (i - 1)).section_ ≫ A'.d (i - 1) i +
      A.d i (i + 1) ≫ comm.hom (i + 1) i ≫ (H i).section_
  comm' i j (r : i + 1 = j) := by
    subst r;
    simp only [add_zero, d_comp_d, Preadditive.comp_add, Category.assoc, comp_zero, add_right_inj,
      Hom.comm, zero_comp, Preadditive.add_comp, d_comp_d_assoc]
    congr <;> ring

@[reassoc (attr := simp)]
theorem ofTermwiseSplitEpi_commutes (H : ∀ i, SplitEpi (f'.f i)) :
    ofTermwiseSplitEpi comm H ≫ f' = f ≫ i₂ := by
  ext i
  dsimp
  have :
    f.f i ≫ i₂.f i =
      A.d i (i + 1) ≫ comm.hom (i + 1) i + comm.hom i (i - 1) ≫ B'.d (i - 1) i + i₁.f i ≫ f'.f i :=
    by
    rw [← HomologicalComplex.comp_f, comm.comm i]
    simp only [dNext, prevD, AddMonoidHom.mk'_apply, comp_f, add_left_inj]
    rw [← CochainComplex.next, ← CochainComplex.prev]
  simp only [this, Category.assoc, Preadditive.add_comp, ← f'.comm]
  erw [SplitEpi.id, SplitEpi.id_assoc]
  rw [add_comm, add_comm (i₁.f i ≫ f'.f i), ← add_assoc, Category.comp_id]

def ofTermwiseSplitEpiHomotopy (H : ∀ i, SplitEpi (f'.f i)) :
    Homotopy (ofTermwiseSplitEpi comm H) i₁
    where
  hom i j := comm.hom i j ≫ (H j).section_
  zero _ _ r := by
    dsimp only
    rw [comm.zero _ _ r, zero_comp]
  comm i :=
    by
    simp only [dNext, prevD, AddMonoidHom.mk'_apply, Category.assoc, HomologicalComplex.ofTermwiseSplitEpi_f]
    rw [← CochainComplex.next, ← CochainComplex.prev]; abel

end ConeFunctorial

-- Porting note: component lemmas for `shiftNegShift` and `shiftShiftNeg` (these were `rfl` in Lean 3)
theorem shiftNegShift_hom_f (X : CochainComplex V ℤ) (n i : ℤ) :
    Hom.f (shiftNegShift X n).hom i = (X.xEqToIso (by ring)).hom := by
  dsimp [shiftNegShift, shiftFunctorCompIsoId, shiftFunctorAdd', shiftFunctorZero, shiftFunctorAdd]
  simp only [HomologicalComplex.xEqToIso, eqToHom_map, eqToHom_app, eqToIso.hom, HomologicalComplex.eqToHom_f, comp_f, eqToHom_trans, shift_μ_inv_app_f, shift_ε_hom_app_f, shift_ε_inv_app_f, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]

theorem shiftShiftNeg_hom_f (X : CochainComplex V ℤ) (n i : ℤ) :
    Hom.f (shiftShiftNeg X n).hom i = (X.xEqToIso (by ring)).hom := by
  dsimp [shiftShiftNeg, shiftFunctorCompIsoId, shiftFunctorAdd', shiftFunctorZero, shiftFunctorAdd]
  simp only [HomologicalComplex.xEqToIso, eqToHom_map, eqToHom_app, eqToIso.hom, HomologicalComplex.eqToHom_f, comp_f, eqToHom_trans, shift_μ_inv_app_f, shift_ε_hom_app_f, shift_ε_inv_app_f, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]

theorem shiftNegShift_inv_f (X : CochainComplex V ℤ) (n i : ℤ) :
    Hom.f (shiftNegShift X n).inv i = (X.xEqToIso (by ring)).hom := by
  rw [← cancel_epi (Hom.f (shiftNegShift X n).hom i), ← comp_f, Iso.hom_inv_id, shiftNegShift_hom_f]
  simp

theorem shiftShiftNeg_inv_f (X : CochainComplex V ℤ) (n i : ℤ) :
    Hom.f (shiftShiftNeg X n).inv i = (X.xEqToIso (by ring)).hom := by
  rw [← cancel_epi (Hom.f (shiftShiftNeg X n).hom i), ← comp_f, Iso.hom_inv_id, shiftShiftNeg_hom_f]
  simp

section TermwiseSplitMonoLift

@[simps]
def termwiseSplitMonoLift (f : A ⟶ B) : A ⟶ biproduct B (cone (𝟙 A)) :=
  biproduct.lift f (cone.in _)

@[simps]
def termwiseSplitMonoDesc (f : A ⟶ B) : biproduct B (cone (𝟙 A)) ⟶ B :=
  biproduct.fst

@[simps]
def termwiseSplitMonoSection (f : A ⟶ B) : B ⟶ biproduct B (cone (𝟙 A)) :=
  biproduct.inl

@[reassoc (attr := simp)]
theorem termwiseSplitMonoSection_desc (f : A ⟶ B) :
    termwiseSplitMonoSection f ≫ termwiseSplitMonoDesc f = 𝟙 _ := by ext; simp

theorem termwise_split_mono_desc_section_aux (i : ℤ) :
    𝟙 (B.X i ⊞ A.X (i + 1) ⊞ A.X i) =
      biprod.snd ≫ biprod.desc (𝟙 (A.X (i + 1))) (A.d i (i + 1)) ≫ biprod.inl ≫ biprod.inr +
          biprod.snd ≫
            biprod.snd ≫
              (xEqToIso A (sub_add_cancel i 1).symm).hom ≫
                biprod.inl ≫
                  biprod.lift (biprod.desc (-A.d (i - 1 + 1) (i + 1)) 0)
                      (biprod.desc (xEqToIso A (sub_add_cancel i 1)).hom (A.d (i - 1) i)) ≫
                    biprod.inr +
        biprod.fst ≫ biprod.inl :=
  by
  ext1 <;>
    simp only [zero_comp, Preadditive.comp_add, zero_add, add_zero, biprod.inr_fst_assoc,
      biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc, Category.comp_id]
  ext1; · simp
  ext1; · simp only [add_zero, Preadditive.add_comp, comp_zero, biprod.inr_fst, Category.assoc]
  ext1 <;> simp

-- Porting note: variant of the previous lemma at `i + 1`, avoiding the non-defeq index `i + 1 - 1 + 1`
theorem termwise_split_mono_desc_section_aux' (i : ℤ) :
    𝟙 (B.X (i + 1) ⊞ A.X (i + 1 + 1) ⊞ A.X (i + 1)) =
      biprod.snd ≫ biprod.desc (𝟙 (A.X (i + 1 + 1))) (A.d (i + 1) (i + 1 + 1)) ≫ biprod.inl ≫ biprod.inr +
          biprod.snd ≫
            biprod.snd ≫
              biprod.inl ≫
                biprod.lift (biprod.desc (-A.d (i + 1) (i + 1 + 1)) 0)
                      (biprod.desc (𝟙 (A.X (i + 1))) (A.d i (i + 1))) ≫
                    biprod.inr +
        biprod.fst ≫ biprod.inl := by
  ext1 <;>
    simp only [zero_comp, Preadditive.comp_add, zero_add, add_zero, biprod.inr_fst_assoc,
      biprod.inl_fst_assoc, biprod.inl_snd_assoc, biprod.inr_snd_assoc, Category.comp_id]
  ext1; · simp
  ext1; · simp only [add_zero, Preadditive.add_comp, comp_zero, biprod.inr_fst, Category.assoc]
  ext1 <;> simp

def termwiseSplitMonoDescSection (f : A ⟶ B) :
    Homotopy (𝟙 _) (termwiseSplitMonoDesc f ≫ termwiseSplitMonoSection f)
    where
  hom i j :=
    if h : i = j + 1 then biprod.snd ≫ biprod.snd ≫ (A.xEqToIso h).hom ≫ biprod.inl ≫ biprod.inr
    else 0
  zero i j r := dif_neg (Ne.symm r)
  comm i := by
    dsimp
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    have aux₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have aux₂ : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    rw [termwise_split_mono_desc_section_aux' i]
    -- Porting note: `rw` fails to match up to instances; `erw` works
    erw [dNext_eq _ aux₂, prevD_eq _ aux₁]
    rw [dif_pos rfl, dif_pos rfl]
    simp only [sub_add_cancel, biproduct_d, cone_d, xEqToIso_refl, Category.id_comp,
      biprod.map_snd_assoc, Category.assoc, biprod.inr_map, add_left_inj, Cone.d]
    simp only [dite_true]
    simp only [id_f, Category.comp_id, biprod.lift_snd_assoc]
    congr 1
    erw [biprod.map_snd_assoc, biprod.lift_snd_assoc]
    rfl

def termwiseSplitMonoLiftSplitMono (f : A ⟶ B) (i : ℤ) : SplitMono ((termwiseSplitMonoLift f).f i)
    where
  retraction := biprod.snd ≫ biprod.snd
  id := by simp [cone.in]

instance (f : A ⟶ B) (i : ℤ) : Mono ((termwiseSplitMonoLift f).f i) :=
  (termwiseSplitMonoLiftSplitMono f i).mono

-- generalize to epi
@[simp]
theorem termwiseSplitMonoLift_desc (f : A ⟶ B) :
    termwiseSplitMonoLift f ≫ termwiseSplitMonoDesc f = f := by ext; simp

/-- We will prove this is iso later -/
def fromTermwiseSplitMonoLiftTriangleₕ :
    cone.triangleₕ (termwiseSplitMonoLift f) ⟶ cone.triangleₕ f :=
  cone.triangleₕMap (Homotopy.ofEq ((termwiseSplitMonoLift_desc f).trans (Category.id_comp f).symm))

@[simps]
def termwiseSplitMonoFactorHomotopyEquiv : HomotopyEquiv (biproduct B (cone (𝟙 A))) B
    where
  hom := termwiseSplitMonoDesc f
  inv := termwiseSplitMonoSection f
  homotopyHomInvId := (termwiseSplitMonoDescSection f).symm
  homotopyInvHomId := Homotopy.ofEq (termwiseSplitMonoSection_desc f)

end TermwiseSplitMonoLift

section TermwiseSplitEpiLift

@[simps]
def termwiseSplitEpiLift (f : A ⟶ B) : A ⟶ biproduct A (cone (𝟙 (B⟦(-1 : ℤ)⟧))) :=
  biproduct.inl

@[simps]
def termwiseSplitEpiDesc (f : A ⟶ B) : biproduct A (cone (𝟙 (B⟦(-1 : ℤ)⟧))) ⟶ B :=
  biproduct.desc f (cone.out _ ≫ (shiftNegShift _ _).hom)

@[simps]
def termwiseSplitEpiRetraction (f : A ⟶ B) : biproduct A (cone (𝟙 (B⟦(-1 : ℤ)⟧))) ⟶ A :=
  biproduct.fst

@[reassoc (attr := simp)]
theorem termwiseSplitEpiLift_retraction (f : A ⟶ B) :
    termwiseSplitEpiLift f ≫ termwiseSplitEpiRetraction f = 𝟙 _ := by ext; simp

-- Porting note: the Lean 3 statement mixes `i - 1` and `i + -1`, which Lean 4's `simp` does not
-- identify; the lemma is first proved with consistent index expressions.
theorem termwise_split_epi_retraction_lift_aux'' (i : ℤ) :
    𝟙 (A.X i ⊞ B.X (i + 1 + -1) ⊞ B.X (i + -1)) =
      biprod.snd ≫ biprod.desc (𝟙 _) (-B.d (i + -1) (i + 1 + -1)) ≫ 𝟙 _ ≫ biprod.inl ≫ biprod.inr +
          biprod.snd ≫
            biprod.snd ≫
              (B⟦(-1 : ℤ)⟧.xEqToIso (sub_add_cancel _ _).symm).hom ≫
                biprod.inl ≫
                  biprod.lift (biprod.desc (B.d (i - 1 + 1 + -1) (i + 1 + -1)) 0)
                      (biprod.desc (B⟦(-1 : ℤ)⟧.xEqToIso <| sub_add_cancel _ _).hom
                        (-B.d (i - 1 + -1) (i + -1))) ≫
                    biprod.inr +
        biprod.fst ≫ biprod.inl :=
  by
  ext <;> simp

theorem termwise_split_epi_retraction_lift_aux (i : ℤ) :
    𝟙 (A.X i ⊞ B.X (i + 1 - 1) ⊞ B.X (i - 1)) =
      biprod.snd ≫ biprod.desc (𝟙 _) (-B.d (i + -1) (i + 1 + -1)) ≫ 𝟙 _ ≫ biprod.inl ≫ biprod.inr +
          biprod.snd ≫
            biprod.snd ≫
              (B⟦(-1 : ℤ)⟧.xEqToIso (sub_add_cancel _ _).symm).hom ≫
                biprod.inl ≫
                  biprod.lift (biprod.desc (B.d (i - 1 + 1 + -1) (i + 1 + -1)) 0)
                      (biprod.desc (B⟦(-1 : ℤ)⟧.xEqToIso <| sub_add_cancel _ _).hom
                        (-B.d (i - 1 + -1) (i + -1))) ≫
                    biprod.inr +
        biprod.fst ≫ biprod.inl :=
  termwise_split_epi_retraction_lift_aux'' i

def termwiseSplitEpiRetractionLift (f : A ⟶ B) :
    Homotopy (𝟙 _) (termwiseSplitEpiRetraction f ≫ termwiseSplitEpiLift f)
    where
  hom i j :=
    if h : i = j + 1 then
      biprod.snd ≫ biprod.snd ≫ (B⟦(-1 : ℤ)⟧.xEqToIso h).hom ≫ biprod.inl ≫ biprod.inr
    else 0
  zero i j r := dif_neg (Ne.symm r)
  comm i := by
    dsimp
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    have aux₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have aux₂ : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    erw [dNext_eq _ aux₂, prevD_eq _ aux₁]
    rw [dif_pos rfl, dif_pos rfl]
    simp only [sub_add_cancel, biproduct_d, cone_d, xEqToIso_refl, Category.id_comp,
      biprod.map_snd_assoc, Category.assoc, biprod.inr_map, Cone.d]
    simp only [dite_true]
    simp only [id_f, Category.comp_id]
    ext <;> simp [shift_d, Int.negOnePow'_neg_one]

def termwiseSplitEpiDescSplitEpi (f : A ⟶ B) (i : ℤ) : SplitEpi ((termwiseSplitEpiDesc f).f i)
    where
  section_ := (B.xEqToIso <| eq_add_neg_of_add_eq rfl).hom ≫ biprod.inl ≫ biprod.inr
  id := by
    dsimp
    simp [cone.out]
    erw [shiftNegShift_hom_f]
    simp

instance (f : A ⟶ B) (i : ℤ) : Epi ((termwiseSplitEpiDesc f).f i) :=
  (termwiseSplitEpiDescSplitEpi f i).epi

end TermwiseSplitEpiLift

section TermwiseSplitExact

-- Porting note: `f g` are already explicit variables

@[simps]
def connectingHom (h : ∀ i : ℤ, Splitting (f.f i) (g.f i)) : C ⟶ A⟦(1 : ℤ)⟧
    where
  f i := (h i).section ≫ B.d i (i + 1) ≫ (h (i + 1)).retraction
  comm' := by
    intro i j r
    induction r
    dsimp
    rw [← cancel_mono (𝟙 _)]
    conv_lhs => rw [← (h _).ι_retraction]
    simp only [Preadditive.comp_neg, one_zsmul, Category.assoc, neg_smul, Preadditive.neg_comp, ←
      f.comm_assoc, (h _).retraction_ι_eq_id_sub_assoc, Preadditive.sub_comp_assoc,
      Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, d_comp_d_assoc, zero_comp,
      comp_zero, ← g.comm_assoc, (h i).section_π_assoc]
    simp

@[simps]
def triangleOfTermwiseSplit (h : ∀ i : ℤ, Splitting (f.f i) (g.f i)) :
    Triangle (CochainComplex V ℤ) :=
  Triangle.mk f g (connectingHom f g h)

@[simps]
def triangleₕOfTermwiseSplit (h : ∀ i : ℤ, Splitting (f.f i) (g.f i)) :
    Triangle (HomotopyCategory V (ComplexShape.up ℤ)) :=
  (HomotopyCategory.liftTriangle V).obj (triangleOfTermwiseSplit f g h)

@[simps]
def homotopyConnectingHomOfSplittings (h h' : ∀ i : ℤ, Splitting (f.f i) (g.f i)) :
    Homotopy (connectingHom f g h) (connectingHom f g h')
    where
  hom i j := if e : j + 1 = i then (h' i).section ≫ (h i).retraction ≫ (A.xEqToIso e).inv else 0
  comm i := by
    -- Porting note: the `Epi` instance is provided before rewriting
    haveI := (h i).epi
    rw [← cancel_epi (g.f i)]
    dsimp
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    have aux₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have aux₂ : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    -- Porting note: `rw` fails to match up to instances; `erw` works
    erw [dNext_eq _ aux₂, prevD_eq _ aux₁]
    rw [dif_pos rfl, dif_pos rfl]
    simp only [dNext, prevD, Splitting.π_section_eq_id_sub_assoc,
      Preadditive.sub_comp_assoc, Category.id_comp, Category.assoc, Hom.comm,
      Preadditive.sub_comp, Splitting.ι_retraction, Category.comp_id, xEqToIso_refl, shift_d,
      Int.negOnePow'_one, neg_smul, one_zsmul, Preadditive.comp_neg, Preadditive.comp_add,
      Hom.comm_assoc, Preadditive.comp_sub, neg_sub, Splitting.ι_retraction_assoc]
    -- Porting note: `abel` fails in the type `B.X (i + 1) ⟶ (A⟦1⟧).X (i + 1)`, so we generalize the
    -- morphisms, which live in `B.X (i + 1) ⟶ A.X (i + 1 + 1)`
    generalize B.d (i + 1) (i + 1 + 1) ≫ (h (i + 1 + 1)).retraction = x
    generalize B.d (i + 1) (i + 1 + 1) ≫ (h' (i + 1 + 1)).retraction = x'
    generalize (h (i + 1)).retraction ≫ A.d (i + 1) (i + 1 + 1) = y
    generalize (h' (i + 1)).retraction ≫ A.d (i + 1) (i + 1 + 1) = y'
    abel
  zero _ _ h := dif_neg h

@[simps]
def triangleₕMapSplittingsHom (h h' : ∀ i : ℤ, Splitting (f.f i) (g.f i)) :
    triangleₕOfTermwiseSplit f g h ⟶ triangleₕOfTermwiseSplit f g h'
    where
  hom₁ := 𝟙 _
  hom₂ := 𝟙 _
  hom₃ := 𝟙 _
  comm₃ :=
    by
    simp only [Category.comp_id, triangleₕOfTermwiseSplit_mor₃, Category.id_comp,
      CategoryTheory.Functor.map_id]
    apply HomotopyCategory.eq_of_homotopy
    exact HomologicalComplex.homotopyConnectingHomOfSplittings f g h h'

@[simps]
def triangleₕMapSplittingsIso (h h' : ∀ i : ℤ, Splitting (f.f i) (g.f i)) :
    triangleₕOfTermwiseSplit f g h ≅ triangleₕOfTermwiseSplit f g h'
    where
  hom := triangleₕMapSplittingsHom f g h h'
  inv := triangleₕMapSplittingsHom f g h' h
  hom_inv_id := by ext <;> exact Category.comp_id _
  inv_hom_id := by ext <;> exact Category.comp_id _

end TermwiseSplitExact

section

variable {B'' B' : CochainComplex V ℤ} {b' : B'' ⟶ B} {b : B ⟶ B'}

variable (H₂ : ∀ i, Splitting (f.f i) (g.f i))

variable (h₂ : Homotopy (b' ≫ g) 0) (h₃ : Homotopy (f ≫ b) 0)

/-- If `A ⟶ B ⟶ C` is split exact, and `b' ≫ g` and `f ≫ b` are null-homotopic,
then so is `b' ≫ b`.

        B''
        ∣
        b'
        ↓
A - f → B - g → C
        ∣
        b
        ↓
        B'
-/
def compNullHomotopicOfRowSplitExact : Homotopy (b' ≫ b) 0 :=
  by
  have H1 := fun i => (H₂ i).splitEpi
  have H2 := fun i => (H₂ i).splitMono
  have aux := fun i => (H₂ i).shortExact.exact
  let h₁' := (h₂.trans (Homotopy.ofEq (comp_zero : 𝟙 _ ≫ 0 = 0).symm)).symm
  let h₂' := h₃.trans <| Homotopy.ofEq (zero_comp : 0 ≫ 𝟙 _ = 0).symm
  refine'
    ((HomologicalComplex.ofTermwiseSplitEpiHomotopy h₁' H1).symm.comp
          (HomologicalComplex.ofTermwiseSplitMonoHomotopy h₂' H2)).trans
      (Homotopy.ofEq _)
  apply Hom.ext
  apply funext
  intro i
  exact
    comp_eq_zero_of_exact (f.f i) (g.f i) (aux i)
      (congr_f ((HomologicalComplex.ofTermwiseSplitEpi_commutes h₁' H1).trans comp_zero) i)
      (congr_f ((HomologicalComplex.ofTermwiseSplitMono_commutes h₂' H2).trans zero_comp) i)

end

def cone.termwiseSplit (i : ℤ) : Splitting ((cone.in f).f i) ((cone.out f).f i)
    where
  iso := biprod.braiding _ _
  comp_iso_eq_inl := by
    apply biprod.hom_ext <;> simp [cone.in]
  iso_comp_snd_eq := by
    apply biprod.hom_ext' <;> simp [cone.out]

@[simp]
theorem cone.termwiseSplit_section (i : ℤ) : (cone.termwiseSplit f i).section = biprod.inl := by
  dsimp only [Splitting.«section», cone.termwiseSplit]
  apply biprod.hom_ext <;> simp

@[simp]
theorem cone.termwiseSplit_retraction (i : ℤ) : (cone.termwiseSplit f i).retraction = biprod.snd :=
  by
  dsimp only [Splitting.retraction, cone.termwiseSplit]
  simp

def coneHomotopyEquivAux (c : cone f ⟶ cone f) (h₁ : Homotopy (cone.in f ≫ c) (cone.in f))
    (h₂ : Homotopy (c ≫ cone.out f) (cone.out f)) : Homotopy (𝟙 _) (2 • c - c ≫ c) :=
  by
  have : Homotopy ((𝟙 _ - c) ≫ (𝟙 _ - c)) 0 :=
    by
    apply HomologicalComplex.compNullHomotopicOfRowSplitExact (cone.in f) (cone.out f) (cone.termwiseSplit f)
    · refine' (Homotopy.ofEq _).trans (Homotopy.equivSubZero h₂.symm); simp
    · refine' (Homotopy.ofEq _).trans (Homotopy.equivSubZero h₁.symm); simp
  refine Homotopy.equivSubZero.symm ?_
  refine' (Homotopy.ofEq _).trans this
  simp [two_smul]; abel

attribute [local simp] Preadditive.comp_nsmul Preadditive.nsmul_comp

/-- If the following diagram commutes up to homotopy, then `c` is a homotopy equivalence
A - f → B ⟶ C(f) ⟶ A⟦1⟧
|       |      ∣       ∣
𝟙       𝟙      c       𝟙
↓       ↓      ∣       ∣
A - f → B ⟶ C(f) ⟶ A⟦1⟧
-/
def coneHomotopyEquiv (c : cone f ⟶ cone f) (h₁ : Homotopy (cone.in f ≫ c) (cone.in f))
    (h₂ : Homotopy (c ≫ cone.out f) (cone.out f)) : HomotopyEquiv (cone f) (cone f)
    where
  hom := c
  inv := 2 • 𝟙 _ - c
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans (coneHomotopyEquivAux f c h₁ h₂).symm
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans (coneHomotopyEquivAux f c h₁ h₂).symm

local notation "Q" => HomotopyCategory.quotient V (ComplexShape.up ℤ)

theorem cone_triangleₕ_map_iso_of_id (φ : cone.triangleₕ f ⟶ cone.triangleₕ f) (h₁ : φ.hom₁ = 𝟙 _)
    (h₂ : φ.hom₂ = 𝟙 _) : IsIso φ.hom₃ :=
  by
  have e₂ := φ.comm₂
  have e₃ := φ.comm₃
  rw [h₂, Category.id_comp] at e₂ 
  rw [h₁, CategoryTheory.Functor.map_id, Category.comp_id] at e₃ 
  erw [← Functor.image_preimage Q φ.hom₃, ← Functor.map_comp Q] at e₂ e₃ 
  convert
    IsIso.of_iso
      (HomotopyCategory.isoOfHomotopyEquiv
        (HomologicalComplex.coneHomotopyEquiv _ _ (HomotopyCategory.homotopyOfEq _ _ e₂)
          (HomotopyCategory.homotopyOfEq _ _ e₃.symm)))
  exact (Functor.image_preimage Q _).symm

open CategoryTheory.Triangulated

theorem cone.triangleₕ_isIso {A' B' : CochainComplex V ℤ} {f : A ⟶ B} {f' : A' ⟶ B'}
    (φ : cone.triangleₕ f ⟶ cone.triangleₕ f') [IsIso φ.hom₁] [IsIso φ.hom₂] : IsIso φ :=
  by
  suffices IsIso φ.hom₃ by exact CategoryTheory.Triangulated.triangle_morphism_isIso _
  have := φ.comm₁
  dsimp at this 
  rw [← IsIso.eq_comp_inv, Category.assoc, ← IsIso.inv_comp_eq, ← Functor.image_preimage Q (inv φ.hom₁), ←
    Functor.map_comp Q, ← Functor.image_preimage Q (inv φ.hom₂), ← Functor.map_comp Q] at this 
  let T := cone.triangleₕMap (HomotopyCategory.homotopyOfEq _ _ this).symm
  haveI : IsIso (φ.hom₃ ≫ T.hom₃) := cone_triangleₕ_map_iso_of_id _ (φ ≫ T) (by simp) (by simp)
  haveI : IsIso (T.hom₃ ≫ φ.hom₃) := cone_triangleₕ_map_iso_of_id _ (T ≫ φ) (by simp) (by simp)
  haveI : Epi φ.hom₃ := epi_of_epi T.hom₃ φ.hom₃
  use T.hom₃ ≫ inv (φ.hom₃ ≫ T.hom₃)
  constructor
  · rw [← Category.assoc]; exact IsIso.hom_inv_id _
  · rw [← cancel_epi φ.hom₃, ← Category.assoc, ← Category.assoc, Category.comp_id, Category.assoc]
    exact IsIso.hom_inv_id_assoc (φ.hom₃ ≫ T.hom₃) _

instance : IsIso (fromTermwiseSplitMonoLiftTriangleₕ f) :=
  by
  have : IsIso (fromTermwiseSplitMonoLiftTriangleₕ f).hom₁ := by
    delta fromTermwiseSplitMonoLiftTriangleₕ; dsimp; infer_instance
  haveI : IsIso (fromTermwiseSplitMonoLiftTriangleₕ f).hom₂ :=
    IsIso.of_iso
      (HomotopyCategory.isoOfHomotopyEquiv (HomologicalComplex.termwiseSplitMonoFactorHomotopyEquiv f))
  apply cone.triangleₕ_isIso

-- move this
@[simp]
theorem cochainComplex_dNext (i : ℤ) (f : ∀ i j, A.X i ⟶ B.X j) :
    dNext i f = A.d i (i + 1) ≫ f (i + 1) i := by
  simp only [dNext, AddMonoidHom.mk'_apply]
  rw [CochainComplex.next ℤ i]

@[simp]
theorem cochainComplex_prevD (i : ℤ) (f : ∀ i j, A.X i ⟶ B.X j) :
    prevD i f = f i (i - 1) ≫ B.d (i - 1) i := by
  simp only [prevD, AddMonoidHom.mk'_apply]
  rw [CochainComplex.prev ℤ i]

@[simps]
def termwiseSplitToCone (h : ∀ i, Splitting (f.f i) (g.f i)) : C ⟶ cone f
    where
  f i := biprod.lift (-(connectingHom f g h).f i) (h i).section
  comm' := by
    rintro i j (rfl : i + 1 = j)
    -- Porting note: the `Epi` instance is provided before rewriting
    haveI : Epi (g.f i) := (h i).epi
    apply biprod.hom_ext
    · dsimp [Cone.d]
      rw [← cancel_epi (g.f i)]
      simp [g.comm, Splitting.π_section_eq_id_sub_assoc]
    · dsimp [Cone.d]
      rw [← cancel_epi (g.f i)]
      simp [Splitting.π_section_eq_id_sub_assoc, Splitting.π_section_eq_id_sub]

@[simps]
def compTermwiseSplitToConeHomotopy (h : ∀ i, Splitting (f.f i) (g.f i)) :
    Homotopy (g ≫ termwiseSplitToCone f g h) (cone.in f)
    where
  hom i j := if e : j + 1 = i then -(h i).retraction ≫ (A.xEqToIso e).inv ≫ biprod.inl else 0
  zero _ _ r := dif_neg r
  comm i := by
    dsimp
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    have aux₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have aux₂ : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    -- Porting note: `rw` fails to match up to instances; `erw` works
    erw [dNext_eq _ aux₂, prevD_eq _ aux₁]
    rw [dif_pos rfl, dif_pos rfl]
    simp only [dite_eq_ite, HomologicalComplex.cochainComplex_prevD, dif_pos, if_true, Category.assoc, cone_d,
      Category.id_comp, add_left_inj, sub_add_cancel, dif_ctx_congr, xEqToIso_refl, Cone.d,
      Preadditive.comp_neg, eq_self_iff_true, HomologicalComplex.cochainComplex_dNext, Preadditive.neg_comp]
    apply biprod.hom_ext
    · simp [cone.in, Splitting.π_section_eq_id_sub_assoc, ← sub_eq_add_neg,
        -retraction_x_eq_to_hom_assoc]
      abel
    · simp [cone.in, Splitting.retraction_ι_eq_id_sub, ← sub_eq_add_neg,
        -retraction_x_eq_to_hom_assoc]

@[simps]
def coneToTermwiseSplit (h : ∀ i, Splitting (f.f i) (g.f i)) : cone f ⟶ C
    where
  f i := biprod.snd ≫ g.f i
  comm' := by
    rintro i j (rfl : i + 1 = j)
    apply biprod.hom_ext' <;> simp [Cone.d, (h _).comp_eq_zero]

@[simps]
def coneToTermwiseSplitCompHomotopy (h : ∀ i, Splitting (f.f i) (g.f i)) :
    Homotopy (coneToTermwiseSplit f g h ≫ connectingHom f g h) (-cone.out f)
    where
  hom i j := if e : j + 1 = i then biprod.snd ≫ (h i).retraction ≫ (A.xEqToIso e).inv else 0
  zero _ _ r := dif_neg r
  comm := by
    intro i
    dsimp
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    have aux₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have aux₂ : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    -- Porting note: `rw` fails to match up to instances; `erw` works
    erw [dNext_eq _ aux₂, prevD_eq _ aux₁]
    rw [dif_pos rfl, dif_pos rfl]
    simp only [Category.comp_id, dite_eq_ite, HomologicalComplex.cochainComplex_prevD, cone.out, dif_pos, if_true,
      add_left_inj, sub_add_cancel, Cone.d, shift_d, dif_ctx_congr, Preadditive.comp_neg,
      eq_self_iff_true, Int.negOnePow'_one, HomologicalComplex.cochainComplex_dNext, one_zsmul, Category.assoc,
      xEqToIso_d, neg_neg, neg_smul, biprod.lift_snd_assoc, xEqToIso_refl, cone_d,
      Preadditive.neg_comp]
    ext <;>-- This is simp [Splitting.π_section_eq_id_sub_assoc, sub_eq_add_neg]
      simp only [Splitting.ι_retraction, Preadditive.comp_add, Preadditive.comp_neg,
        biprod.inl_snd_assoc, zero_comp, neg_zero, add_zero, biprod.inl_desc_assoc, biprod.inl_fst,
        add_right_neg, biprod.inr_snd_assoc, biprod.inr_desc_assoc, biprod.inr_fst,
        Splitting.π_section_eq_id_sub_assoc, sub_eq_add_neg, Hom.comm, Hom.comm_assoc,
        Preadditive.add_comp_assoc, Category.id_comp, Preadditive.neg_comp, Category.assoc,
        Preadditive.add_comp, Category.comp_id, add_left_inj, eq_self_iff_true]

def isoConeOfTermwiseSplitInvHomHomotopy (h : ∀ i, Splitting (f.f i) (g.f i)) :
    Homotopy (coneToTermwiseSplit f g h ≫ termwiseSplitToCone f g h) (𝟙 _)
    where
  hom i j :=
    if e : j + 1 = i then -biprod.snd ≫ (h i).retraction ≫ (A.xEqToIso e).inv ≫ biprod.inl else 0
  zero _ _ r := dif_neg r
  comm := by
    intro i
    dsimp
    obtain ⟨i, rfl⟩ : ∃ j, j + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
    have aux₁ : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have aux₂ : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    -- Porting note: `rw` fails to match up to instances; `erw` works
    erw [dNext_eq _ aux₂, prevD_eq _ aux₁]
    rw [dif_pos rfl, dif_pos rfl]
    simp only [Category.comp_id, dite_eq_ite, HomologicalComplex.cochainComplex_prevD, dif_pos, if_true,
      Category.id_comp, add_left_inj, sub_add_cancel, Cone.d, dif_ctx_congr, eq_self_iff_true,
      HomologicalComplex.cochainComplex_dNext, Category.assoc, biprod.lift_snd_assoc, xEqToIso_refl, cone_d]
    ext <;>-- This is simp [Splitting.π_section_eq_id_sub_assoc, Splitting.π_section_eq_id_sub]
        simp only [add_left_neg, add_zero, Category.assoc, Category.comp_id, Exact.w, Exact.w_assoc,
          biprod.inl_desc, biprod.inl_desc_assoc, biprod.inl_fst, biprod.inr_desc_assoc,
          biprod.inr_fst, biprod.inr_snd, biprod.inr_snd_assoc, biprod.lift_fst, biprod.lift_snd,
          biprod.lift_snd_assoc, comp_zero, zero_comp, Preadditive.add_comp, Preadditive.comp_add,
          Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.neg_comp, Category.comp_id,
          Splitting.ι_retraction_assoc, eq_self_iff_true, xEqToIso_d, xEqToIso_f_assoc,
          xEqToIso_refl, xEqToIso_trans, neg_neg, neg_zero, zero_add, neg_sub, Hom.comm_assoc,
          Splitting.π_section_eq_id_sub_assoc, Splitting.π_section_eq_id_sub, Category.id_comp,
          Preadditive.sub_comp_assoc, Hom.comm, Preadditive.sub_comp, Splitting.ι_retraction,
          exact_inl_snd] <;>
      abel

@[simps]
def isoConeOfTermwiseSplit (h : ∀ i, Splitting (f.f i) (g.f i)) :
    triangleₕOfTermwiseSplit f g h ≅
      (CategoryTheory.Triangulated.neg₃Functor _).obj (cone.triangleₕ f) :=
  by
  fapply CategoryTheory.Triangulated.mkTriangleIso
  exact Iso.refl _
  exact Iso.refl _
  refine' ⟨(Q).map (termwiseSplitToCone f g h), (Q).map (coneToTermwiseSplit f g h), _, _⟩
  · dsimp; erw [← Functor.map_comp Q, ← CategoryTheory.Functor.map_id Q]; congr; ext <;> dsimp; simp
  · dsimp; erw [← Functor.map_comp Q, ← CategoryTheory.Functor.map_id Q]; apply HomotopyCategory.eq_of_homotopy
    apply HomologicalComplex.isoConeOfTermwiseSplitInvHomHomotopy
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · dsimp; rw [← Functor.map_comp Q, Category.id_comp]
    apply HomotopyCategory.eq_of_homotopy; apply HomologicalComplex.compTermwiseSplitToConeHomotopy
  · dsimp; rw [CategoryTheory.Functor.map_id, Category.comp_id, ← CategoryTheory.Functor.map_neg Q, ← Functor.map_comp Q]
    congr; ext; simp [cone.out]

instance : Mono (termwiseSplitMonoLift f) :=
  mono_of_eval _

def termwiseSplitOfTermwiseSplitMono (H : ∀ i, SplitMono (f.f i)) (i : ℤ) :
    have : Mono f := haveI := fun i => (H i).mono; HomologicalComplex.mono_of_eval f
    Splitting (f.f i) ((HomologicalComplex.normalMono f).g.f i) :=
  by
  apply LeftSplit.splitting
  dsimp only [HomologicalComplex.normalMono, cokernelComplexπ]
  constructor
  · exact ⟨(H i).1, (H i).2⟩
  · exact Abelian.exact_cokernel _

/-- Every neg₃ of a cone triangle is isomorphic to some triangle associated to some
  termwise split sequence -/
def isoTermwiseSplitOfCone :
    (CategoryTheory.Triangulated.neg₃Functor _).obj (cone.triangleₕ f) ≅
      triangleₕOfTermwiseSplit (termwiseSplitMonoLift f)
        (HomologicalComplex.normalMono (termwiseSplitMonoLift f)).g
        (termwiseSplitOfTermwiseSplitMono _ <| termwiseSplitMonoLiftSplitMono _) :=
  Functor.mapIso _ (asIso <| fromTermwiseSplitMonoLiftTriangleₕ f).symm ≪≫
    (isoConeOfTermwiseSplit _ _ _).symm

-- Lemma 13.9.15. skipped
--move
@[reassoc (attr := simp)]
theorem Biprod.map_desc {C : Type _} [Category C] [HasZeroMorphisms C] {X Y X' Y' Z : C}
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct X' Y'] (f : X ⟶ X') (g : Y ⟶ Y') (f' : X' ⟶ Z)
    (g' : Y' ⟶ Z) : biprod.map f g ≫ biprod.desc f' g' = biprod.desc (f ≫ f') (g ≫ g') := by
  ext <;> simp

@[reassoc (attr := simp)]
theorem Biprod.lift_map {C : Type _} [Category C] [HasZeroMorphisms C] {W X Y X' Y' : C}
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct X' Y'] (f : X ⟶ X') (g : Y ⟶ Y') (f' : W ⟶ X)
    (g' : W ⟶ Y) : biprod.lift f' g' ≫ biprod.map f g = biprod.lift (f' ≫ f) (g' ≫ g) := by
  ext <;> simp

@[simps]
def Biprod.mapIso {C : Type _} [Category C] [HasZeroMorphisms C] {X Y X' Y' : C}
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct X' Y'] (f : X ≅ X') (g : Y ≅ Y') :
    X ⊞ Y ≅ X' ⊞ Y' :=
  ⟨biprod.map f.hom g.hom, biprod.map f.inv g.inv, by ext <;> simp, by ext <;> simp⟩

@[simps]
def isoConnectingHomShiftCone (h : ∀ i, Splitting (f.f i) (g.f i)) :
    B ≅ cone (connectingHom f g h⟦(-1 : ℤ)⟧') :=
  Hom.isoOfComponents
    (fun f =>
      (h _).iso ≪≫
        biprod.braiding _ _ ≪≫ Biprod.mapIso (C.xEqToIso (by simp)) (A.xEqToIso (by simp)))
    (by
      rintro i j (rfl : i + 1 = j)
      -- Porting note: the `Epi` instance is provided before rewriting
      haveI : Epi (g.f i) := (h i).epi
      dsimp [Cone.d]
      rw [← cancel_epi (h i).iso.inv]
      simp only [Category.comp_id, Biprod.lift_map, neg_smul_neg, if_true, Iso.inv_hom_id_assoc,
        add_left_inj, eq_self_iff_true, one_zsmul, Category.assoc, neg_neg, neg_smul]
      ext <;>
        simp only [add_zero, Category.assoc, Exact.w_assoc, biprod.inl_fst_assoc,
          biprod.inr_fst_assoc, biprod.inr_snd_assoc, biprod.lift_desc, biprod.lift_fst,
          biprod.lift_snd, comp_zero, zero_comp, Preadditive.comp_add, x_d_eq_to_iso, xEqToIso_d,
          Splitting.comp_iso_eq_inl_assoc, Splitting.inl_comp_iso_eq_assoc,
          Splitting.iso_comp_snd_eq_assoc, eq_self_iff_true, Hom.comm_assoc, zero_add,
          Splitting.iso_hom_fst_assoc, Splitting.inr_iso_inv_assoc, exact_inl_snd]
      · rw [← cancel_epi (g.f i)]
        simp only [Category.id_comp, Preadditive.sub_comp_assoc, (h _).comp_eq_zero_assoc, sub_zero,
          Category.assoc, comp_zero, Hom.comm, Preadditive.sub_comp, Limits.zero_comp,
          Splitting.π_section_eq_id_sub_assoc, Hom.comm_assoc]
        rw [← xEqToIso_f, x_d_eq_to_iso_assoc]
      · rw [← cancel_epi (g.f i)]
        simp only [Category.comp_id, x_d_eq_to_iso, Category.id_comp, Preadditive.sub_comp_assoc,
          Splitting.π_section_eq_id_sub_assoc, Category.assoc, Hom.comm, Preadditive.sub_comp,
          Splitting.ι_retraction]
        rw [← xEqToIso_f_assoc, Splitting.π_section_eq_id_sub_assoc]
        simp only [x_d_eq_to_iso_assoc, Category.comp_id, Hom.comm_assoc, retraction_x_eq_to_hom,
          Category.id_comp, Preadditive.sub_comp_assoc, xEqToIso_d_assoc, Splitting.ι_retraction,
          Preadditive.comp_sub, Hom.comm, Preadditive.sub_comp, sub_right_inj, Category.assoc]
        rw [← retraction_x_eq_to_hom_assoc, xEqToIso_d])

theorem inv_rotate_iso_cone_triangle_comm₁ (h : ∀ i, Splitting (f.f i) (g.f i)) :
    (triangleOfTermwiseSplit f g h).nonnegInvRotate.mor₁ ≫ (shiftShiftNeg A (1 : ℤ)).inv =
      𝟙 _ ≫ (cone.triangle (connectingHom f g h⟦(-1 : ℤ)⟧')).mor₁ :=
  by
  simp [Triangle.nonnegInvRotate, triangleOfTermwiseSplit, cone.triangle]

theorem inv_rotate_iso_cone_triangle_comm₂ (h : ∀ i, Splitting (f.f i) (g.f i)) :
    (triangleOfTermwiseSplit f g h).nonnegInvRotate.mor₂ ≫ (isoConnectingHomShiftCone f g h).hom =
      (shiftShiftNeg A (1 : ℤ)).inv ≫ (cone.triangle (connectingHom f g h⟦(-1 : ℤ)⟧')).mor₂ :=
  by
  ext i
  dsimp [cone.in]
  erw [shiftShiftNeg_inv_f]
  simp [isoConnectingHomShiftCone, Biprod.mapIso]
  apply biprod.hom_ext <;> simp

theorem inv_rotate_iso_cone_triangle_comm₃ (h : ∀ i, Splitting (f.f i) (g.f i)) :
    (triangleOfTermwiseSplit f g h).nonnegInvRotate.mor₃ ≫ 𝟙 _⟦(1 : ℤ)⟧' =
      (isoConnectingHomShiftCone f g h).hom ≫
        (cone.triangle (connectingHom f g h⟦(-1 : ℤ)⟧')).mor₃ :=
  by
  ext
  dsimp [cone.out]
  erw [shiftNegShift_inv_f]
  simp

def invRotateIsoConeTriangle (h : ∀ i, Splitting (f.f i) (g.f i)) :
    (triangleOfTermwiseSplit f g h).nonnegInvRotate ≅
      cone.triangle (connectingHom f g h⟦(-1 : ℤ)⟧') :=
  by
  fapply CategoryTheory.Triangulated.mkTriangleIso
  exacts [Iso.refl _, (CategoryTheory.shiftShiftNeg A (1 : ℤ)).symm, HomologicalComplex.isoConnectingHomShiftCone f g h,
    inv_rotate_iso_cone_triangle_comm₁ _ _ _, inv_rotate_iso_cone_triangle_comm₂ _ _ _,
    inv_rotate_iso_cone_triangle_comm₃ f g h]

def triangleOfTermwiseSplitConeIso :
    triangleOfTermwiseSplit (cone.in f) (cone.out f) (cone.termwiseSplit f) ≅
      (cone.triangle f).nonnegRotate :=
  mkTriangleIso (Iso.refl _) (Iso.refl _) (Iso.refl _) (by dsimp; simp) (by dsimp; simp)
    (by ext; dsimp [Cone.d]; simp)

end HomologicalComplex

