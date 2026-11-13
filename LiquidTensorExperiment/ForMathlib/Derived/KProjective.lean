import LiquidTensorExperiment.ForMathlib.HomotopyCategoryPretriangulated
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.Derived.Homological
import LiquidTensorExperiment.ForMathlib.Derived.BoundedHomotopyCategory
import Mathlib.CategoryTheory.Abelian.Projective
import LiquidTensorExperiment.ForMathlib.SnakeLemma3
import LiquidTensorExperiment.ForMathlib.LesHomology
import LiquidTensorExperiment.ForMathlib.ExactSeq3
import LiquidTensorExperiment.ForMathlib.TriangleShift
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.ProjectiveReplacement
import LiquidTensorExperiment.ForMathlib.Derived.Lemmas
import LiquidTensorExperiment.HacksAndTricks.AsyncI

#align_import for_mathlib.derived.K_projective

-- import for_mathlib.arrow_preadditive
-- import for_mathlib.arrow_preadditive
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

open HomologicalComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace BoundedHomotopyCategory

local notation "𝒦" => BoundedHomotopyCategory A

section EnoughProjectives

abbrev UniformlyBounded {α : Type _} (X : α → 𝒦) : Prop :=
  HomotopyCategory.IsUniformlyBoundedAbove (val ∘ X)

variable [EnoughProjectives A]

-- Main theorem about existence of K-projective replacements.
-- Perhaps all we need is this for bounded complexes, in which case we should
-- add an additional typeclass parameter here.
theorem exists_K_projective_replacement (X : 𝒦) :
    ∃ (P : 𝒦) (_ : HomotopyCategory.IsKProjective P.val) (f : P ⟶ X),
      HomotopyCategory.IsQuasiIso f ∧ ∀ k, Projective (P.val.as.pt k) :=
  by
  obtain ⟨P, h1, h2, f, h3⟩ := HomotopyCategory.exists_K_projective_replacement_of_bounded X.val
  skip
  exact ⟨⟨P⟩, h1, f, h3⟩

theorem exists_uniform_K_projective_replacement {α : Type _} (X : α → 𝒦) [UniformlyBounded X] :
    ∃ (P : α → 𝒦) (_ : ∀ a, HomotopyCategory.IsKProjective (P a).val) (_ : UniformlyBounded P) (f :
      ∀ a, P a ⟶ X a),
      (∀ a, HomotopyCategory.IsQuasiIso (f a)) ∧ ∀ a k, Projective ((P a).val.as.pt k) :=
  by
  obtain ⟨P, h1, h2, f, h3, h4⟩ :=
    HomotopyCategory.exists_K_projective_replacement_of_uniformly_bounded_above (val ∘ X)
  skip
  exact ⟨fun a => ⟨P a⟩, inferInstance, inferInstance, f, h3, h4⟩

open HomotopyCategory

def replace (X : 𝒦) : 𝒦 :=
  (exists_K_projective_replacement X).some

instance (X : 𝒦) : IsKProjective X.replace.val :=
  (exists_K_projective_replacement X).choose_spec.some

def π (X : 𝒦) : X.replace ⟶ X :=
  (exists_K_projective_replacement X).choose_spec.choose_spec.some

instance (X : 𝒦) : IsQuasiIso X.π :=
  (exists_K_projective_replacement X).choose_spec.choose_spec.choose_spec.1

instance (X : 𝒦) (k : ℤ) : Projective (X.replace.val.as.pt k) :=
  (exists_K_projective_replacement X).choose_spec.choose_spec.choose_spec.2 k

def replaceUniformly {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X] :
    α → BoundedHomotopyCategory A :=
  (exists_uniform_K_projective_replacement X).some

instance isKProjectiveReplaceUniformlyApply {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] (a) : HomotopyCategory.IsKProjective (replaceUniformly X a).val :=
  (exists_uniform_K_projective_replacement X).choose_spec.some _

def πUniformly {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X] :
    ∀ a, replaceUniformly X a ⟶ X a :=
  (exists_uniform_K_projective_replacement X).choose_spec.choose_spec.choose_spec.some

instance isQuasiIsoπUniformly {α : Type v} (X : α → BoundedHomotopyCategory A) [UniformlyBounded X]
    (a) : HomotopyCategory.IsQuasiIso (πUniformly X a) :=
  (exists_uniform_K_projective_replacement X).choose_spec.choose_spec.choose_spec.choose_spec.1 _

instance uniformBoundReplaceUniformly {α : Type v} (X : α → BoundedHomotopyCategory A)
    [UniformlyBounded X] : UniformlyBounded (replaceUniformly X) :=
  (exists_uniform_K_projective_replacement X).choose_spec.choose_spec.some

def lift {P X Y : 𝒦} [IsKProjective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [IsQuasiIso g] : P ⟶ X :=
  ((hom_K_projective_bijective P.val g).2 f).some

@[simp, reassoc]
theorem lift_lifts {P X Y : 𝒦} [IsKProjective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [IsQuasiIso g] :
    lift f g ≫ g = f :=
  ((hom_K_projective_bijective P.val g).2 f).choose_spec

theorem lift_unique {P X Y : 𝒦} [IsKProjective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [IsQuasiIso g]
    (e : P ⟶ X) (h : e ≫ g = f) : e = lift f g :=
  by
  apply (hom_K_projective_bijective P.val g).1
  dsimp
  erw [lift_lifts]
  assumption

@[simp]
theorem lift_self {P X : 𝒦} [IsKProjective P.val] (g : P ⟶ X) [IsQuasiIso g] : lift g g = 𝟙 _ :=
  (lift_unique _ _ _ (by simp)).symm

@[simp]
theorem lift_comp {P X Y : 𝒦} [IsKProjective P.val] (f : P ⟶ X) (g : X ⟶ Y) [IsQuasiIso g] :
    lift (f ≫ g) g = f :=
  (lift_unique _ _ _ (by simp)).symm

@[simp, reassoc]
theorem lift_comp_lift_self {P X Y Z : 𝒦} [IsKProjective P.val] [IsKProjective X.val] (f : P ⟶ Y)
    (g : X ⟶ Y) [IsQuasiIso g] (k : Z ⟶ Y) [IsQuasiIso k] : lift f g ≫ lift g k = lift f k :=
  lift_unique _ _ _ (by simp)

@[simp, reassoc]
theorem lift_comp_lift_comp {P W X Y Z : 𝒦} [IsKProjective P.val] [IsKProjective X.val] (f : P ⟶ Y)
    (g : X ⟶ Y) [IsQuasiIso g] (h : Y ⟶ Z) (k : W ⟶ Z) [IsQuasiIso k] :
    lift f g ≫ lift (g ≫ h) k = lift (f ≫ h) k :=
  lift_unique _ _ _ (by simp)

@[simp]
theorem lift_neg {P X Y : 𝒦} [IsKProjective P.val] (f : P ⟶ Y) (g : X ⟶ Y) [IsQuasiIso g] :
    lift (-f) g = -lift f g :=
  (lift_unique _ _ _ (by simp)).symm

theorem lift_add {P X Y : 𝒦} [IsKProjective P.val] (f₁ f₂ : P ⟶ Y) (g : X ⟶ Y) [IsQuasiIso g] :
    lift (f₁ + f₂) g = lift f₁ g + lift f₂ g :=
  (lift_unique _ _ _ (by simp)).symm

instance isKProjectiveShift (X : 𝒦) [IsKProjective X.val] (m : ℤ) :
    IsKProjective ((CategoryTheory.shiftFunctor 𝒦 m).obj X).val :=
  HomotopyCategory.isKProjectiveShift X.val m

-- strange?
instance {X Y : 𝒦} (g : X ⟶ Y) [IsQuasiIso g] (m : ℤ) :
    IsQuasiIso ((CategoryTheory.shiftFunctor 𝒦 m).map g) :=
  HomotopyCategory.isQuasiIsoShift _ _ _ _

theorem shiftFunctor_map_lift {P X Y : 𝒦} [IsKProjective P.val] (f : P ⟶ Y) (g : X ⟶ Y)
    [IsQuasiIso g] (m : ℤ) :
    (CategoryTheory.shiftFunctor 𝒦 m).map (lift f g) =
      lift ((CategoryTheory.shiftFunctor 𝒦 m).map f) ((CategoryTheory.shiftFunctor 𝒦 m).map g) :=
  by
  apply lift_unique
  simp only [← CategoryTheory.Functor.map_comp, lift_lifts]

theorem lift_ext {P X Y : 𝒦} [IsKProjective P.val] (g : X ⟶ Y) [IsQuasiIso g] (a b : P ⟶ X)
    (h : a ≫ g = b ≫ g) : a = b :=
  (hom_K_projective_bijective P.val g).1 h

@[simps]
def replaceTriangle (T : triangle 𝒦) : triangle 𝒦
    where
  obj₁ := T.obj₁.replace
  obj₂ := T.obj₂.replace
  obj₃ := T.obj₃.replace
  mor₁ := lift (T.obj₁.π ≫ T.mor₁) T.obj₂.π
  mor₂ := lift (T.obj₂.π ≫ T.mor₂) T.obj₃.π
  mor₃ :=
    haveI h : is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧') := inferInstance
    @lift _ _ _ _ _ _ _ _ (T.obj₃.π ≫ T.mor₃) (T.obj₁.π⟦(1 : ℤ)⟧') h

-- What?
theorem distinguished_replaceTriangle (T : triangle 𝒦) (hT : T ∈ (dist_triang 𝒦)) :
    replaceTriangle T ∈ (dist_triang 𝒦) :=
  by
  let S := replace_triangle T
  change S ∈ _
  obtain ⟨Z, g, h, hW⟩ := pretriangulated.distinguished_cocone_triangle _ _ S.mor₁
  let W := triangle.mk (BoundedHomotopyCategory A) S.mor₁ g h
  change W ∈ _ at hW 
  have hWT : W.mor₁ ≫ T.obj₂.π = T.obj₁.π ≫ T.mor₁ := _
  obtain ⟨q, sq2, sq3⟩ :=
    pretriangulated.complete_distinguished_triangle_morphism _ _ hW hT T.obj₁.π T.obj₂.π hWT
  let r : W ⟶ T := ⟨T.obj₁.π, T.obj₂.π, q, hWT, sq2, sq3⟩
  let W' := triangle.mk (HomotopyCategory _ _) W.mor₁ W.mor₂ W.mor₃
  let T' := triangle.mk (HomotopyCategory _ _) T.mor₁ T.mor₂ T.mor₃
  let r' : W' ⟶ T' := ⟨T.obj₁.π, T.obj₂.π, q, hWT, sq2, sq3⟩
  have : is_quasi_iso r.hom₃ := is_quasi_iso_of_triangle W' T' hW hT r'
  have : is_K_projective W.obj₃.val :=
    by
    haveI : is_K_projective W'.obj₁ := show is_K_projective T.obj₁.replace.val by infer_instance
    haveI : is_K_projective W'.obj₂ := show is_K_projective T.obj₂.replace.val by infer_instance
    exact HomotopyCategory.isKProjectiveOfTriangle W' hW
  haveI : is_K_projective S.obj₁.val := show is_K_projective T.obj₁.replace.val by infer_instance
  haveI : is_K_projective S.obj₂.val := show is_K_projective T.obj₂.replace.val by infer_instance
  haveI : is_K_projective S.obj₃.val := show is_K_projective T.obj₃.replace.val by infer_instance
  apply mem_distinguished_of_iso _ hW
  refine' ⟨⟨𝟙 _, 𝟙 _, lift q T.obj₃.π, _, _, _⟩, ⟨𝟙 _, 𝟙 _, lift T.obj₃.π q, _, _, _⟩, _, _⟩
  · dsimp; rw [category.comp_id, category.id_comp]
  · dsimp [S, replace_triangle]
    rw [category.id_comp]
    apply lift_unique
    erw [category.assoc, lift_lifts]; exact sq2
  · dsimp [S, replace_triangle]
    rw [CategoryTheory.Functor.map_id, category.comp_id]
    have :
      is_quasi_iso
        ((CategoryTheory.shiftFunctor (BoundedHomotopyCategory A) (1 : ℤ)).map T.obj₁.π) :=
      by show is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧'); infer_instance
    -- strange.
    apply lift_ext (T.obj₁.π⟦(1 : ℤ)⟧')
    erw [category.assoc, lift_lifts, lift_lifts_assoc]
    exact sq3
    assumption
  · dsimp; rw [category.id_comp, category.comp_id]
  · dsimp [S, replace_triangle]
    rw [category.id_comp]
    apply lift_ext q
    erw [category.assoc, lift_lifts, lift_lifts, sq2]
    assumption
  · dsimp [S, replace_triangle]
    rw [CategoryTheory.Functor.map_id, category.comp_id]
    have :
      is_quasi_iso
        ((CategoryTheory.shiftFunctor (BoundedHomotopyCategory A) (1 : ℤ)).map T.obj₁.π) :=
      by show is_quasi_iso (T.obj₁.π⟦(1 : ℤ)⟧'); infer_instance
    -- strange.
    apply lift_ext (T.obj₁.π⟦(1 : ℤ)⟧')
    erw [category.assoc, lift_lifts, sq3, lift_lifts_assoc]
    assumption
  · ext <;> dsimp; rw [category.id_comp]; rw [category.id_comp]
    apply lift_ext q; erw [category.assoc, lift_lifts, lift_lifts, category.id_comp]
    assumption
  · ext <;> dsimp; rw [category.id_comp]; rw [category.id_comp]
    apply lift_ext T.obj₃.π; erw [category.assoc, lift_lifts, lift_lifts, category.id_comp]
    assumption
  · dsimp [W, S, replace_triangle]
    rw [lift_lifts]

@[simps]
def ext0 : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab
    where
  obj X := preadditiveYoneda.flip.obj (Opposite.op <| X.unop.replace)
  map X₁ X₂ f := preadditiveYoneda.flip.map (lift (X₂.unop.π ≫ f.unop) X₁.unop.π).op
  map_id' := by
    intro X
    ext Y e
    dsimp [preadditive_yoneda, preadditive_yoneda_obj]
    change _ ≫ e = e
    simp only [category.comp_id, id_apply]
    convert category.id_comp _
    symm
    apply lift_unique
    simp
  map_comp' := by
    intro X₁ X₂ X₃ f g
    ext Y e
    dsimp
    simp only [comp_apply, LinearMap.toAddMonoidHom_coe, preadditive_yoneda_obj_map_apply,
      Quiver.Hom.unop_op]
    change _ ≫ e = _ ≫ _ ≫ e
    conv_rhs => rw [← category.assoc]
    congr 1
    symm
    apply lift_unique
    simp

def ext (i : ℤ) : 𝒦ᵒᵖ ⥤ 𝒦 ⥤ Ab :=
  ext0 ⋙ (whiskeringLeft _ _ _).obj (shiftFunctor _ i)

-- why is this so slow?
-- DT: squeezing the simps made it very fast!
@[simps]
def replacementIso (P₁ P₂ X : 𝒦) [IsKProjective P₁.val] [IsKProjective P₂.val] (f₁ : P₁ ⟶ X)
    (f₂ : P₂ ⟶ X) [IsQuasiIso f₁] [IsQuasiIso f₂] : P₁ ≅ P₂
    where
  Hom := lift f₁ f₂
  inv := lift f₂ f₁
  hom_inv_id' :=
    by
    have : 𝟙 P₁ = lift f₁ f₁ := by apply lift_unique; simp only [category.id_comp]
    rw [this]
    apply lift_unique
    simp only [category.assoc, lift_lifts]
  inv_hom_id' :=
    by
    have : 𝟙 P₂ = lift f₂ f₂ := by apply lift_unique; simp only [category.id_comp]
    rw [this]
    apply lift_unique
    simp only [category.assoc, lift_lifts]

@[simps]
def extIso (i : ℤ) (P X Y : 𝒦) [IsKProjective P.val] (f : P ⟶ X) [IsQuasiIso f] :
    ((ext i).obj (Opposite.op X)).obj Y ≅ AddCommGroupCat.of (P ⟶ Y⟦i⟧) :=
  (preadditiveYoneda.obj (Y⟦i⟧)).mapIso (replacementIso P X.replace X f X.π).op

instance ext_additive (i : ℤ) (X : 𝒦) : Functor.Additive ((ext i).obj (Opposite.op X)) :=
  by
  refine' ⟨_⟩
  intro X Y f g
  ext h
  dsimp [Ext, preadditive_yoneda]
  rw [(CategoryTheory.shiftFunctor 𝒦 i).map_add, preadditive.comp_add]

instance ext_additive' (i : ℤ) (X : 𝒦) : Functor.Additive ((ext i).flip.obj X).rightOp :=
  by
  refine' ⟨_⟩
  intro X Y f g
  dsimp [Ext, preadditive_yoneda]
  rw [← op_add]
  congr 1
  ext h
  dsimp
  rw [← preadditive.add_comp]
  congr 1
  symm
  apply lift_unique
  simp only [preadditive.add_comp, lift_lifts, preadditive.comp_add]

def CategoryTheory.Adjunction.yonedaWhiskeringLeft {C D : Type _} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) : yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ≅ G ⋙ yoneda :=
  by
  fapply nat_iso.of_components
  · intro Y
    fapply nat_iso.of_components
    · intro X; exact (adj.hom_equiv (Opposite.unop X) Y).toIso
    · intro X₁ X₂ f; ext g; exact adj.hom_equiv_naturality_left f.unop g
  · intro Y₁ Y₂ f; ext X g; exact adj.hom_equiv_naturality_right g f

def CategoryTheory.Adjunction.preadditiveYonedaWhiskeringLeft {C D : Type _} [Category C]
    [Category D] [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [Functor.Additive G] :
    preadditiveYoneda ⋙ (whiskeringLeft _ _ _).obj F.op ≅ G ⋙ preadditiveYoneda :=
  by
  fapply nat_iso.of_components
  · intro Y
    fapply nat_iso.of_components
    · intro X
      refine'
        add_equiv_iso_AddCommGroup_iso.hom { adj.hom_equiv (Opposite.unop X) Y with map_add' := _ }
      intro f g; simp
    · intro X₁ X₂ f; ext g; exact adj.hom_equiv_naturality_left f.unop g
  · intro Y₁ Y₂ f; ext X g; exact adj.hom_equiv_naturality_right g f

end EnoughProjectives

instance shiftEquiv_symm_inverse_additive (i : ℤ) :
    (shiftEquiv (BoundedHomotopyCategory A) i).symm.inverse.Additive :=
  show (CategoryTheory.shiftFunctor (BoundedHomotopyCategory A) i).Additive by infer_instance

instance shiftEquiv_inverse_additive (i : ℤ) :
    (shiftEquiv (BoundedHomotopyCategory A) i).inverse.Additive :=
  show (CategoryTheory.shiftFunctor (BoundedHomotopyCategory A) (-i)).Additive by infer_instance

def homShiftRightIso (X : 𝒦) (i : ℤ) :
    CategoryTheory.shiftFunctor 𝒦 i ⋙ preadditiveYoneda.flip.obj (Opposite.op X) ≅
      preadditiveYoneda.flip.obj (Opposite.op (X⟦-i⟧)) :=
  haveI :=
    (iso_whisker_right
        (shift_equiv (BoundedHomotopyCategory A)
                  i).symm.toAdjunction.preadditiveYonedaWhiskeringLeft.symm
        ((evaluation _ _).obj <| Opposite.op X) :
      _)
  this

def homShiftLeftIso (X : 𝒦) (i : ℤ) :
    (CategoryTheory.shiftFunctor 𝒦 i).op ⋙ preadditiveYoneda.obj X ≅
      preadditiveYoneda.obj (X⟦-i⟧) :=
  haveI :=
    (shift_equiv (BoundedHomotopyCategory A) i).toAdjunction.preadditiveYonedaWhiskeringLeft.app X
  this

-- The LES for Ext in the second variable.
instance (i : ℤ) (X : 𝒦) [EnoughProjectives A] : homologicalFunctor ((ext i).obj (Opposite.op X)) :=
  by
  show homological_functor (CategoryTheory.shiftFunctor 𝒦 i ⋙ preadditive_yoneda.flip.obj _)
  let E := hom_shift_right_iso X.replace i
  exact homological_of_nat_iso _ _ E.symm

-- The LES for Ext in the first variable.
-- We need K-projective replacements of triangles for this.
instance (i : ℤ) (X : 𝒦) [EnoughProjectives A] : homologicalFunctor ((ext i).flip.obj X).rightOp :=
  by
  constructor
  intro T hT
  have :=
    homological_functor.cond (preadditive_yoneda.obj (X⟦i⟧)).rightOp (replace_triangle T)
      (distinguished_replace_triangle _ hT)
  exact this

instance lift_isIso [EnoughProjectives A] (X Y X' Y' : 𝒦) (f : X ⟶ Y) (πX : X' ⟶ X) (πY : Y' ⟶ Y)
    [HomotopyCategory.IsQuasiIso f] [HomotopyCategory.IsQuasiIso πX]
    [HomotopyCategory.IsQuasiIso πY] [HomotopyCategory.IsKProjective X'.val]
    [HomotopyCategory.IsKProjective Y'.val] : IsIso (lift (πX ≫ f) πY) :=
  by
  use lift πY (πX ≫ f)
  constructor
  · apply lift_ext (πX ≫ f); simp; infer_instance
  · apply lift_ext πY; simp; infer_instance

@[simp]
theorem inv_lift [EnoughProjectives A] (X Y X' Y' : 𝒦) (f : X ⟶ Y) (πX : X' ⟶ X) (πY : Y' ⟶ Y)
    [HomotopyCategory.IsQuasiIso f] [HomotopyCategory.IsQuasiIso πX]
    [HomotopyCategory.IsQuasiIso πY] [HomotopyCategory.IsKProjective X'.val]
    [HomotopyCategory.IsKProjective Y'.val] : inv (lift (πX ≫ f) πY) = lift πY (πX ≫ f) := by
  apply lift_unique; rw [is_iso.inv_comp_eq]; simp

instance isIso_ext_flip_obj_map_of_isQuasiIso [EnoughProjectives A] (i : ℤ) (X X' Y : 𝒦)
    (f : X ⟶ X') [HomotopyCategory.IsQuasiIso f] : IsIso (((ext i).flip.obj Y).map f.op) :=
  by
  let e := (preadditive_yoneda.obj (Y⟦i⟧)).map (lift (X.π ≫ f) X'.π).op
  change is_iso e
  apply functor.map_is_iso

end BoundedHomotopyCategory

variable [EnoughProjectives A]

def ext' (i : ℤ) : Aᵒᵖ ⥤ A ⥤ Ab :=
  (BoundedHomotopyCategory.single A 0).op ⋙
    (BoundedHomotopyCategory.single A 0 ⋙ (BoundedHomotopyCategory.ext i).flip).flip

