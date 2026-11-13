import LiquidTensorExperiment.ForMathlib.ComposableMorphisms
import Mathlib.Algebra.Homology.Additive
import LiquidTensorExperiment.ForMathlib.HomologicalComplexMapDToDFrom

#align_import for_mathlib.short_complex

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D]

section

variable (C)

-- Category of complexes `X ⟶ Y ⟶ Z`
def ShortComplex [HasZeroMorphisms C] :=
  FullSubcategory fun S : ComposableMorphisms C => S.zero
deriving Category

end

open CategoryTheory

namespace HomologicalComplex

variable [HasZeroMorphisms C] {M : Type _} {c : ComplexShape M}

theorem prev_id (X : HomologicalComplex C c) (i : M) : Hom.prev (𝟙 X) i = 𝟙 (X.xPrev i) :=
  rfl

theorem next_id (X : HomologicalComplex C c) (i : M) : Hom.next (𝟙 X) i = 𝟙 (X.xNext i) :=
  rfl

theorem prev_comp {X Y Z : HomologicalComplex C c} (f : X ⟶ Y) (g : Y ⟶ Z) (i : M) :
    Hom.prev (f ≫ g) i = Hom.prev f i ≫ Hom.prev g i :=
  rfl

theorem next_comp {X Y Z : HomologicalComplex C c} (f : X ⟶ Y) (g : Y ⟶ Z) (i : M) :
    Hom.next (f ≫ g) i = Hom.next f i ≫ Hom.next g i :=
  rfl

end HomologicalComplex

namespace ShortComplex

@[simp, reassoc]
theorem zero [HasZeroMorphisms C] (S : ShortComplex C) : S.1.f ≫ S.1.g = 0 :=
  S.2

@[simps]
def mk [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
    ShortComplex C :=
  ⟨ComposableMorphisms.mk f g, zero⟩

@[simp]
theorem mk_id_τ₁ [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
    ComposableMorphisms.Hom.τ₁ (𝟙 (mk f g zero)) = 𝟙 X :=
  rfl

@[simp]
theorem mk_id_τ₂ [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
    ComposableMorphisms.Hom.τ₂ (𝟙 (mk f g zero)) = 𝟙 Y :=
  rfl

@[simp]
theorem mk_id_τ₃ [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (zero : f ≫ g = 0) :
    ComposableMorphisms.Hom.τ₃ (𝟙 (mk f g zero)) = 𝟙 Z :=
  rfl

@[simp]
theorem comp_τ₁ [HasZeroMorphisms C] {S₁ S₂ S₃ : ShortComplex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (f ≫ g).τ₁ = f.τ₁ ≫ g.τ₁ :=
  rfl

@[simp]
theorem comp_τ₂ [HasZeroMorphisms C] {S₁ S₂ S₃ : ShortComplex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (f ≫ g).τ₂ = f.τ₂ ≫ g.τ₂ :=
  rfl

@[simp]
theorem comp_τ₃ [HasZeroMorphisms C] {S₁ S₂ S₃ : ShortComplex C} (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (f ≫ g).τ₃ = f.τ₃ ≫ g.τ₃ :=
  rfl

@[simps]
def homMk [HasZeroMorphisms C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : X₁ ⟶ Y₁} {g₁ : Y₁ ⟶ Z₁} {f₂ : X₂ ⟶ Y₂}
    {g₂ : Y₂ ⟶ Z₂} {zero₁ : f₁ ≫ g₁ = 0} {zero₂ : f₂ ≫ g₂ = 0} (τ₁ : X₁ ⟶ X₂) (τ₂ : Y₁ ⟶ Y₂)
    (τ₃ : Z₁ ⟶ Z₂) (comm₁₂ : f₁ ≫ τ₂ = τ₁ ≫ f₂) (comm₂₃ : g₁ ≫ τ₃ = τ₂ ≫ g₂) :
    mk f₁ g₁ zero₁ ⟶ mk f₂ g₂ zero₂ :=
  ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₃⟩

@[simps]
def isoMk [HasZeroMorphisms C] {S₁ S₂ : ShortComplex C} (τ₁ : S₁.1.pt ≅ S₂.1.pt)
    (τ₂ : S₁.1.y ≅ S₂.1.y) (τ₃ : S₁.1.z ≅ S₂.1.z) (comm₁₂ : S₁.1.f ≫ τ₂.Hom = τ₁.Hom ≫ S₂.1.f)
    (comm₂₃ : S₁.1.g ≫ τ₃.Hom = τ₂.Hom ≫ S₂.1.g) : S₁ ≅ S₂
    where
  Hom := ⟨τ₁.Hom, τ₂.Hom, τ₃.Hom, comm₁₂, comm₂₃⟩
  inv := by
    refine' ⟨τ₁.inv, τ₂.inv, τ₃.inv, _, _⟩
    ·
      simp only [← cancel_mono τ₂.hom, ← cancel_epi τ₁.hom, assoc, iso.inv_hom_id, comp_id,
        iso.hom_inv_id_assoc, comm₁₂]
    ·
      simp only [← cancel_mono τ₃.hom, ← cancel_epi τ₂.hom, assoc, iso.inv_hom_id, comp_id,
        iso.hom_inv_id_assoc, comm₂₃]
  hom_inv_id' := by
    ext
    · simpa only [comp_τ₁, hom_mk_τ₁, iso.hom_inv_id]
    · simpa only [comp_τ₂, hom_mk_τ₂, iso.hom_inv_id]
    · simpa only [comp_τ₃, hom_mk_τ₃, iso.hom_inv_id]
  inv_hom_id' := by
    ext
    · simpa only [iso.inv_hom_id, comp_τ₁, hom_mk_τ₁]
    · simpa only [iso.inv_hom_id, comp_τ₂, hom_mk_τ₂]
    · simpa only [iso.inv_hom_id, comp_τ₃, hom_mk_τ₃]

theorem isIso_of_is_isos [HasZeroMorphisms C] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₁ : IsIso φ.τ₁) (h₂ : IsIso φ.τ₂) (h₃ : IsIso φ.τ₃) : IsIso φ :=
  by
  let e : S₁ ≅ S₂ := iso_mk (as_iso φ.τ₁) (as_iso φ.τ₂) (as_iso φ.τ₃) φ.comm₁₂ φ.comm₂₃
  rcases φ with ⟨τ₁, τ₂, τ₃, comm₁₂, comm₂₂⟩
  exact is_iso.of_iso e

def homology [Abelian C] (S : ShortComplex C) : C :=
  homology' S.1.f S.1.g S.2

@[simps]
def homologyFunctor [Abelian C] : ShortComplex C ⥤ C
    where
  obj X := X.homology'
  map X Y φ := homology'.map X.2 Y.2 ⟨φ.τ₁, φ.τ₂, φ.comm₁₂.symm⟩ ⟨φ.τ₂, φ.τ₃, φ.comm₂₃.symm⟩ rfl
  map_id' X := by apply homology'.map_id
  map_comp' X Y Z φ ψ := by symm; apply homology'.map_comp

variable (C)

@[simps]
def functorHomologicalComplex [HasZeroMorphisms C] {M : Type _} (c : ComplexShape M) (i : M) :
    HomologicalComplex C c ⥤ ShortComplex C
    where
  obj X := mk (X.dTo i) (X.dFrom i) (X.dTo_comp_dFrom i)
  map X Y f :=
    ComposableMorphisms.Hom.mk (f.prev i) (f.f i) (f.next i) (f.comm_to i).symm (f.comm_from i).symm
  map_id' X := by
    ext
    · exact X.prev_id i
    · rfl
    · exact X.next_id i
  map_comp' X Y Z f g := by
    ext
    · exact HomologicalComplex.prev_comp f g i
    · rfl
    · exact HomologicalComplex.next_comp f g i

@[simps]
def homologyFunctorIso [Abelian C] {M : Type _} (c : ComplexShape M) (i : M) :
    homology'Functor C c i ≅ functorHomologicalComplex C c i ⋙ ShortComplex.homologyFunctor :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f => by ext;
    simpa only [iso.refl_hom, id_comp, comp_id]

end ShortComplex

namespace CategoryTheory

namespace Functor

#print CategoryTheory.Functor.mapShortComplex /-
@[simps]
def mapShortComplex [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.PreservesZeroMorphisms] : ShortComplex C ⥤ ShortComplex D :=
  FullSubcategory.lift _ (inducedFunctor _ ⋙ F.mapComposableMorphisms) fun X =>
    by
    have h := X.2
    dsimp [composable_morphisms.zero] at h ⊢
    rw [← F.map_comp, h, F.map_zero]
-/

end Functor

namespace NatTrans

@[simps]
def mapShortComplex [HasZeroMorphisms C] [HasZeroMorphisms D] {F G : C ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (φ : F ⟶ G) :
    F.mapShortComplex ⟶ G.mapShortComplex
    where app X := ⟨φ.app _, φ.app _, φ.app _, φ.naturality _, φ.naturality _⟩

end NatTrans

end CategoryTheory

open CategoryTheory

namespace ShortComplex

variable {C}

def functorHomologicalComplexMap [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {M : Type _} (c : ComplexShape M) (i : M) :
    ShortComplex.functorHomologicalComplex C c i ⋙ F.mapShortComplex ≅
      F.mapHomologicalComplex c ⋙ ShortComplex.functorHomologicalComplex D c i :=
  Iso.refl _

variable [Preadditive C] [Preadditive D] {F G : C ⥤ D} [Functor.Additive F] [Functor.Additive G]
  {M : Type _} (c : ComplexShape M) (i : M) (φ : F ⟶ G) (X : HomologicalComplex C c)

theorem NatTrans.mapShortComplex_app :
    (NatTrans.mapShortComplex φ).app ((ShortComplex.functorHomologicalComplex C c i).obj X) =
      (ShortComplex.functorHomologicalComplex D c i).map
        ((NatTrans.mapHomologicalComplex φ c).app X) :=
  rfl

theorem naturality_functorHomologicalComplexMap :
    (NatTrans.mapShortComplex φ).app ((ShortComplex.functorHomologicalComplex C c i).obj X) ≫
        (ShortComplex.functorHomologicalComplexMap G c i).Hom.app X =
      (ShortComplex.functorHomologicalComplexMap F c i).Hom.app X ≫
        (ShortComplex.functorHomologicalComplex D c i).map
          ((NatTrans.mapHomologicalComplex φ c).app X) :=
  by
  dsimp only [functor_homological_complex_map, iso.refl_hom, nat_trans.id_app]
  erw [nat_trans.map_short_complex_app, category.id_comp, category.comp_id]

end ShortComplex

