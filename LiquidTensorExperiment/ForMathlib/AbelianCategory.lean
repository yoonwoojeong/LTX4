import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.EilenbergMoore
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Generator
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.CategoryTheory.Preadditive.InjectiveResolution
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Preadditive.OfBiproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

#align_import for_mathlib.abelian_category

namespace CategoryTheory

namespace Limits

open CategoryTheory.Limits

variable {C : Type _} [Category C] [HasZeroMorphisms C]

open scoped ZeroObject

theorem isZero_iff_id_eq_zero {X : C} : IsZero X ↔ 𝟙 X = 0 :=
  by
  constructor
  · exact fun h => h.eq_of_src _ _
  -- Porting note: Lean 3 `use 0, intro f` built the `unique` from `0`; done explicitly here.
  · intro e; constructor <;> intro Y <;> refine ⟨⟨⟨0⟩, fun f => (?_ : f = 0)⟩⟩
    · rw [← cancel_epi (𝟙 _), e, comp_zero, zero_comp]
    · rw [← cancel_mono (𝟙 _), e, comp_zero, zero_comp]

theorem isZero_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (h : IsZero Y) : IsZero X := by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero, ← cancel_mono f, zero_comp, h.eq_of_tgt (𝟙 _ ≫ f)]

theorem isZero_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (h : IsZero X) : IsZero Y := by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero, ← cancel_epi f, comp_zero, h.eq_of_src (f ≫ 𝟙 Y)]

theorem isZero_of_top_le_bot [HasZeroObject C] (X : C) (h : (⊤ : Subobject X) ≤ ⊥) : IsZero X :=
  { unique_to := fun Y => by
      refine ⟨⟨⟨0⟩, fun f => (?_ : f = 0)⟩⟩
      rw [← cancel_epi (⊤ : CategoryTheory.Subobject X).arrow, ← CategoryTheory.Subobject.ofLE_arrow h]
      simp only [CategoryTheory.Subobject.bot_arrow, comp_zero, zero_comp]
    unique_from := fun Y => by
      refine ⟨⟨⟨0⟩, fun f => (?_ : f = 0)⟩⟩
      rw [← CategoryTheory.Subobject.bot_factors_iff_zero]
      exact CategoryTheory.Subobject.factors_of_le f h (CategoryTheory.Subobject.top_factors f) }

-- inline this
theorem isZero_of_iso_of_zero {C : Type _} [Category C] [HasZeroMorphisms C] {X : C} (hX : IsZero X)
    {Y : C} (h : X ≅ Y) : IsZero Y :=
  hX.of_iso h.symm

theorem isZero_of_exact_zero_zero {C : Type _} [Category C] [Abelian C] {X Y Z : C}
    (h : Exact (0 : X ⟶ Y) (0 : Y ⟶ Z)) : IsZero Y :=
  isZero_of_top_le_bot _
    (by
      rw [CategoryTheory.Abelian.exact_iff_image_eq_kernel] at h 
      rw [← @CategoryTheory.Limits.kernelSubobject_zero _ _ _ Y Z, ← @CategoryTheory.Limits.imageSubobject_zero _ _ _ _ X Y, h])

theorem exact_of_isZero {C : Type _} [Category C] [Abelian C] {X Y Z : C} (hY : IsZero Y)
    (f : X ⟶ Y) (g : Y ⟶ Z) : Exact f g := by
  simp only [CategoryTheory.Abelian.exact_iff, CategoryTheory.Limits.IsZero.eq_zero_of_tgt hY f, CategoryTheory.Limits.IsZero.eq_zero_of_tgt hY (kernel.ι g),
    zero_comp, eq_self_iff_true, and_self_iff]

theorem isZero_iff_exact_zero_zero {C : Type _} [Category C] [Abelian C] {X Y Z : C} :
    IsZero Y ↔ Exact (0 : X ⟶ Y) (0 : Y ⟶ Z) :=
  ⟨fun h => exact_of_isZero h 0 0, isZero_of_exact_zero_zero⟩

theorem isZero_of_exact_zero_zero' {C : Type _} [Category C] [Abelian C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Exact f g) (hf : f = 0) (hg : g = 0) : IsZero Y := by
  rw [hf, hg] at h
  exact CategoryTheory.Limits.isZero_of_exact_zero_zero h

theorem isZero_of_exact_isZero_isZero {C : Type _} [Category C] [Abelian C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Exact f g) (hX : IsZero X) (hZ : IsZero Z) : IsZero Y :=
  isZero_of_exact_zero_zero' f g h (hX.eq_of_src f _) (hZ.eq_of_tgt g _)

theorem isZero_cokernel_of_epi {C : Type _} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) [Epi f] :
    IsZero (cokernel f) :=
  by
  have h1 : cokernel.π f = 0 := by rwa [← CategoryTheory.Abelian.epi_iff_cokernel_π_eq_zero]
  have h2 : Exact (cokernel.π f) 0 := CategoryTheory.exact_epi_zero (cokernel.π f)
  exact CategoryTheory.Limits.isZero_of_exact_zero_zero' (cokernel.π f) 0 h2 h1 rfl

theorem epi_iff_isZero_cokernel {C : Type _} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ IsZero (cokernel f) := by
  constructor
  · intros; apply CategoryTheory.Limits.isZero_cokernel_of_epi
  · intro h
    rw [CategoryTheory.Abelian.epi_iff_cokernel_π_eq_zero]
    apply h.eq_of_tgt

theorem isZero_kernel_of_mono {C : Type _} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) [Mono f] :
    IsZero (kernel f) :=
  by
  have h1 : kernel.ι f = 0 := by rwa [← CategoryTheory.Abelian.mono_iff_kernel_ι_eq_zero]
  have h2 : Exact 0 (kernel.ι f) := CategoryTheory.exact_zero_mono (kernel.ι f)
  exact CategoryTheory.Limits.isZero_of_exact_zero_zero' 0 (kernel.ι f) h2 rfl h1

theorem mono_iff_isZero_kernel {C : Type _} [Category C] [Abelian C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ IsZero (kernel f) := by
  constructor
  · intros; apply CategoryTheory.Limits.isZero_kernel_of_mono
  · intro h
    rw [CategoryTheory.Abelian.mono_iff_kernel_ι_eq_zero]
    apply h.eq_of_src

noncomputable def imageIsoOfEq [Category C] [Abelian C] {A B : C} {f f' : A ⟶ B} (h : f = f') :
    image f ≅ image f' :=
  eqToIso (by rw [h])

noncomputable def image.isIsoComp {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {A B C : 𝓐} {f : A ⟶ B}
    [IsIso f] (g : B ⟶ C) : image (f ≫ g) ≅ image g
    where
  hom :=
    image.lift
      ({  I := _
          m := image.ι _
          m_mono := inferInstance
          e := f ≫ factorThruImage g
          fac := by simp only [CategoryTheory.Category.assoc, image.fac] } : MonoFactorisation _)
  inv :=
    image.lift
      ({  I := _
          m := image.ι _
          m_mono := inferInstance
          e := inv f ≫ factorThruImage (f ≫ g)
          fac := by simp only [CategoryTheory.Category.assoc, image.fac, CategoryTheory.IsIso.inv_hom_id_assoc] } :
        MonoFactorisation _)

theorem isIso_of_isZero_of_isZero {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {a b : 𝓐} (ha : IsZero a)
    (hb : IsZero b) (f : a ⟶ b) : IsIso f :=
  by
  rw [CategoryTheory.Limits.IsZero.eq_zero_of_src ha f]
  apply (CategoryTheory.Limits.isIsoZeroEquiv a b).symm.toFun
  exact ⟨CategoryTheory.Limits.IsZero.eq_of_src ha (𝟙 a) 0, CategoryTheory.Limits.IsZero.eq_of_src hb (𝟙 b) 0⟩

theorem obj_isZero_of_iso {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {𝓑 : Type _} [Category 𝓑]
    [Abelian 𝓑] {F G : 𝓐 ⥤ 𝓑} (h : F ≅ G) {a : 𝓐} (ha : IsZero (F.obj a)) : IsZero (G.obj a) :=
  isZero_of_iso_of_zero ha (h.app a)

theorem map_isIso_of_iso_of_map_isIso {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] {𝓑 : Type _}
    [Category 𝓑] [Abelian 𝓑] {F G : 𝓐 ⥤ 𝓑} (h : F ≅ G) {a₁ a₂ : 𝓐} (f : a₁ ⟶ a₂)
    (ha : IsIso (F.map f)) : IsIso (G.map f) :=
  by
  rw [← CategoryTheory.NatIso.naturality_1 h]
  exact CategoryTheory.IsIso.comp_isIso

@[simp]
theorem epi_comp_iso_iff_epi {V : Type _} [Category V] {A B C : V} (e : A ≅ B) (f : B ⟶ C) :
    Epi (e.hom ≫ f) ↔ Epi f := by
  constructor
  · rintro ⟨h⟩
    constructor
    intro Z s t h2
    apply h
    simp [h2]
  · rintro ⟨h⟩
    constructor
    intro Z s t h2
    apply h
    simpa using h2

@[simp]
theorem epi_iso_comp_iff_epi {V : Type _} [Category V] {A B C : V} (f : A ⟶ B) (e : B ≅ C) :
    Epi (f ≫ e.hom) ↔ Epi f := by
  constructor
  · intro h
    constructor
    intro Z s t h2
    suffices : e.inv ≫ s = e.inv ≫ t
    simpa
    rw [← cancel_epi (f ≫ e.hom)]
    simpa using h2
  · intro h
    constructor
    intro Z s t h2
    simp only [CategoryTheory.Category.assoc] at h2 
    rw [cancel_epi] at h2 
    rwa [cancel_epi] at h2 

theorem isIso_iff_isIso_comp_left {V : Type _} [Category V] {A B C : V} (f : A ⟶ B) {e : B ⟶ C}
    [IsIso f] : IsIso (f ≫ e) ↔ IsIso e := by
  constructor
  · intro h; exact CategoryTheory.IsIso.of_isIso_comp_left f e
  · intro h; exact CategoryTheory.IsIso.comp_isIso

theorem isIso_iff_isIso_comp_right {V : Type _} [Category V] {A B C : V} {f : A ⟶ B} (g : B ⟶ C)
    [IsIso g] : IsIso (f ≫ g) ↔ IsIso f := by
  constructor
  · intro; exact CategoryTheory.IsIso.of_isIso_comp_right f g
  · intro h; exact CategoryTheory.isIso_of_op (f ≫ g)

@[simp]
theorem epi_comp_isIso_iff_epi {V : Type _} [Category V] {A B C : V} (e : A ⟶ B) (f : B ⟶ C)
    [IsIso e] : Epi (e ≫ f) ↔ Epi f :=
  epi_comp_iso_iff_epi (asIso e) f

@[simp]
theorem epi_isIso_comp_iff_epi {V : Type _} [Category V] {A B C : V} (f : A ⟶ B) (e : B ⟶ C)
    [IsIso e] : Epi (f ≫ e) ↔ Epi f :=
  epi_iso_comp_iff_epi f (asIso e)

theorem zero_of_epi_comp_zero {V : Type _} [Category V] [Abelian V] {A B C : V} {f : A ⟶ B}
    {g : B ⟶ C} (w : f ≫ g = 0) [Epi f] : g = 0 :=
  (Preadditive.epi_iff_cancel_zero f).mp inferInstance C g w

@[simp]
theorem comp_mono_zero_iff {V : Type _} [Category V] [Abelian V] {A B C : V} {f : A ⟶ B} {g : B ⟶ C}
    [Mono g] : f ≫ g = 0 ↔ f = 0 :=
  ⟨(Preadditive.mono_iff_cancel_zero g).1 inferInstance A f, fun f => f.symm ▸ zero_comp⟩

theorem epi_of_epi_of_comp_epi_of_mono {V : Type _} [Category V] [Abelian V] {A B C : V} (f : A ⟶ B)
    (g : B ⟶ C) [Epi (f ≫ g)] [Mono g] : Epi f :=
  by
  have foo : IsIso g := by
    rw [CategoryTheory.isIso_iff_mono_and_epi]
    refine' ⟨inferInstance, _⟩
    apply epi_of_epi f
  simp_all

theorem isZero_initial {C : Type _} [Category C] [Abelian C] : IsZero (⊥_ C) :=
  isZero_of_iso_of_zero (isZero_zero _) <|
    { hom := 0
      inv := 0 }

theorem isZero_terminal {C : Type _} [Category C] [Abelian C] : IsZero (⊤_ C) :=
  isZero_of_iso_of_zero (isZero_zero _) <|
    { hom := 0
      inv := 0 }

universe v u₁ u₂

class PreservesZeroObjects {C D : Type _} [Category C] [HasZeroMorphisms C] [Category D]
    [HasZeroMorphisms D] (F : C ⥤ D) : Prop where
  preserves : ∀ X : C, IsZero X → IsZero (F.obj X)

instance preserves_zero_of_preserves_initial {C : Type u₁} {D : Type u₂} [Category.{v} C]
    [Abelian C] [Category.{v} D] [Abelian D] (F : C ⥤ D) [PreservesColimit (Functor.empty C) F] :
    PreservesZeroObjects F :=
  PreservesZeroObjects.mk fun X hX =>
    by
    have e : X ≅ ⊥_ _ := hX.iso CategoryTheory.Limits.isZero_initial
    replace e : F.obj X ≅ F.obj (⊥_ _) := F.mapIso e
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ e.symm
    have : F.obj (⊥_ _) ≅ ⊥_ _ := by
      -- Porting note: Lean 3 `apply_with preserves_initial.iso {instances := ff}, assumption`
      exact CategoryTheory.Limits.PreservesInitial.iso F
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ this.symm
    exact CategoryTheory.Limits.isZero_initial

-- sanity check
example {C : Type u₁} {D : Type u₂} [Category.{v} C] [Abelian C] [Category.{v} D] [Abelian D]
    (F : C ⥤ D) [PreservesColimits F] : PreservesZeroObjects F :=
  inferInstance

instance preserves_zero_of_preserves_terminal {C : Type u₁} {D : Type u₂} [Category.{v} C]
    [Abelian C] [Category.{v} D] [Abelian D] (F : C ⥤ D) [PreservesLimit (Functor.empty C) F] :
    PreservesZeroObjects F :=
  PreservesZeroObjects.mk fun X hX =>
    by
    have e : X ≅ ⊤_ _ := hX.iso CategoryTheory.Limits.isZero_terminal
    replace e : F.obj X ≅ F.obj (⊤_ _) := F.mapIso e
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ e.symm
    have : F.obj (⊤_ _) ≅ ⊤_ _ := by
      exact CategoryTheory.Limits.PreservesTerminal.iso F
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ this.symm
    exact CategoryTheory.Limits.isZero_terminal

-- sanity check
example {C : Type u₁} {D : Type u₂} [Category.{v} C] [Abelian C] [Category.{v} D] [Abelian D]
    (F : C ⥤ D) [PreservesLimits F] : PreservesZeroObjects F :=
  inferInstance

theorem isZero_of_preserves {C D : Type _} [Category C] [HasZeroMorphisms C] [Category D]
    [HasZeroMorphisms D] {X : C} (F : C ⥤ D) [PreservesZeroObjects F] (e : IsZero X) :
    IsZero (F.obj X) :=
  PreservesZeroObjects.preserves _ e

theorem isZero_biprod {C : Type u₁} [Category.{v} C] [Abelian C] (X Y : C) (hX : IsZero X)
    (hY : IsZero Y) : IsZero (biprod X Y) :=
  by
  constructor
  · intro W; refine ⟨⟨⟨0⟩, fun f => (?_ : f = 0)⟩⟩; ext; simp; apply hX.eq_of_src; simp; apply hY.eq_of_src
  · intro W; refine ⟨⟨⟨0⟩, fun f => (?_ : f = 0)⟩⟩; ext; simp; apply hX.eq_of_tgt; simp; apply hY.eq_of_tgt

end Limits

end CategoryTheory

