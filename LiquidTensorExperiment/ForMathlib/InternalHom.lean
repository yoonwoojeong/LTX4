import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.Tactic

#align_import for_mathlib.internal_hom

namespace CategoryTheory.Monoidal

open CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

class RightClosed (X : C) where
  isAdj : IsLeftAdjoint (tensorRight X)

attribute [instance 100] CategoryTheory.Monoidal.RightClosed.isAdj

variable (C)

class MonoidalClosedRight where
  closed : ∀ X : C, RightClosed X

attribute [instance 100] CategoryTheory.Monoidal.MonoidalClosedRight.closed

variable [MonoidalClosedRight.{v} C]

variable {C}

def internalHom (X Y : C) : C :=
  (rightAdjoint (tensorRight X)).obj Y

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
def internalHomEquiv (X Y Z : C) : (X ⊗ Y ⟶ Z) ≃ (X ⟶ internalHom Y Z) :=
  (Adjunction.ofLeftAdjoint (tensorRight Y)).homEquiv X Z

def internalHomPostcompose (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    internalHom X Y₁ ⟶ internalHom X Y₂ :=
  (rightAdjoint (tensorRight X)).map f

@[simp]
theorem internalHomPostcompose_id (X Y : C) : internalHomPostcompose X (𝟙 Y) = 𝟙 _ :=
  (rightAdjoint (tensorRight X)).map_id _

@[simp]
theorem internalHomPostcompose_comp (X : C) {Y₁ Y₂ Y₃ : C} (f₁ : Y₁ ⟶ Y₂) (f₂ : Y₂ ⟶ Y₃) :
    internalHomPostcompose X (f₁ ≫ f₂) =
      internalHomPostcompose X f₁ ≫ internalHomPostcompose X f₂ :=
  (rightAdjoint (tensorRight X)).map_comp _ _

def internalHomPrecompose {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : internalHom X₂ Y ⟶ internalHom X₁ Y :=
  internalHomEquiv _ _ _ <| tensorHom (𝟙 _) f ≫ (internalHomEquiv _ _ _).symm (𝟙 _)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem split_left {A₁ A₂ B₁ B₂ : C} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) : f ⊗ g = (f ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ g) :=
  by simp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem split_right {A₁ A₂ B₁ B₂ : C} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) : f ⊗ g = (𝟙 _ ⊗ g) ≫ (f ⊗ 𝟙 _) :=
  by simp

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem internalHomEquiv_tensor_right {X Y₁ Y₂ Z : C} (f : Y₁ ⟶ Y₂) (g : X ⊗ Y₂ ⟶ Z) :
    internalHomEquiv _ _ _ ((𝟙 _ ⊗ f) ≫ g) = internalHomEquiv _ _ _ g ≫ internalHomPrecompose f _ :=
  by
  apply_fun (CategoryTheory.Monoidal.internalHomEquiv _ _ _).symm
  simp
  dsimp [CategoryTheory.Monoidal.internalHomPrecompose, CategoryTheory.Monoidal.internalHomEquiv, internalHom]
  simp only [CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.Adjunction.homEquiv_counit, CategoryTheory.MonoidalCategory.tensorRight_map, tensor_id,
    CategoryTheory.Adjunction.homEquiv_naturality_right, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc, CategoryTheory.Adjunction.homEquiv_naturality_left_symm,
    CategoryTheory.Adjunction.homEquiv_naturality_right_symm]
  simp only [← tensor_right_map]
  rw [(adjunction.of_left_adjoint (tensor_right Y₁)).counit_naturality_assoc]
  rw [(adjunction.of_left_adjoint (tensor_right Y₁)).left_triangle_components_assoc]
  dsimp
  simp only [← category.assoc, ← tensor_comp, category.id_comp, category.comp_id]
  conv_rhs => rw [split_right _ f, category.assoc]
  rw [← tensor_right_map]
  simp only [functor.map_comp, category.assoc]
  rw [(adjunction.of_left_adjoint (tensor_right Y₂)).counit_naturality]
  erw [(adjunction.of_left_adjoint (tensor_right Y₂)).left_triangle_components_assoc]

@[simp]
theorem internalHomPrecompose_id (X Y : C) : internalHomPrecompose (𝟙 X) Y = 𝟙 _ := by
  dsimp [CategoryTheory.Monoidal.internalHomPrecompose, CategoryTheory.Monoidal.internalHomEquiv, internalHom]; simp; dsimp; simp

@[simp]
theorem internalHomPrecompose_comp {X₁ X₂ X₃ : C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (Y : C) :
    internalHomPrecompose (f₁ ≫ f₂) Y = internalHomPrecompose f₂ Y ≫ internalHomPrecompose f₁ Y :=
  by
  change _ = CategoryTheory.Monoidal.internalHomEquiv _ _ _ _ ≫ _
  rw [← CategoryTheory.Monoidal.internalHomEquiv_tensor_right, ← CategoryTheory.Category.assoc, ← tensor_comp, CategoryTheory.Category.id_comp]
  rfl

@[simp]
theorem internalHomPostcompose_comp_precompose {A₁ A₂ B₁ B₂ : C} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    internalHomPostcompose _ f ≫ internalHomPrecompose g _ =
      internalHomPrecompose g _ ≫ internalHomPostcompose _ f :=
  by
  apply_fun (CategoryTheory.Monoidal.internalHomEquiv _ _ _).symm
  dsimp [CategoryTheory.Monoidal.internalHomPrecompose, CategoryTheory.Monoidal.internalHomPostcompose, CategoryTheory.Monoidal.internalHomEquiv, internalHom]
  simp only [CategoryTheory.Adjunction.homEquiv_counit, CategoryTheory.MonoidalCategory.tensorRight_map, tensor_id,
    CategoryTheory.Adjunction.homEquiv_naturality_right, CategoryTheory.Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc,
    CategoryTheory.Adjunction.homEquiv_naturality_left_symm, adjunction.hom_equiv_naturality_right_symm]
  simp only [← tensor_right_map, adjunction.counit_naturality, adjunction.counit_naturality_assoc,
    functor.map_comp, adjunction.left_triangle_components, adjunction.right_triangle_components,
    adjunction.left_triangle_components_assoc, adjunction.right_triangle_components_assoc]
  dsimp
  simp only [← category.assoc, ← tensor_comp, category.id_comp, category.comp_id]
  rw [split_right _ g, category.assoc, ← tensor_right_map, adjunction.counit_naturality,
    category.assoc]

@[simps]
def internalHomFunctor : Cᵒᵖ ⥤ C ⥤ C
    where
  obj X :=
    { obj := fun Y => internalHom X.unop Y
      map := fun Y₁ Y₂ => internalHomPostcompose _ }
  map X₁ X₂ f := { app := fun Y => internalHomPrecompose f.unop _ }

end CategoryTheory.Monoidal

