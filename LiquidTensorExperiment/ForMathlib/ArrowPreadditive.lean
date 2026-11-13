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
import Mathlib.CategoryTheory.Arrow

#align_import for_mathlib.arrow_preadditive

-- TODO : generalize to comma categories?
-- TODO : generalize to comma categories?
namespace CategoryTheory

variable {A : Type _} [Category A] [Preadditive A]

attribute [local simp] preadditive.comp_nsmul preadditive.nsmul_comp preadditive.comp_zsmul
  preadditive.zsmul_comp

instance Arrow.hasZero (P Q : Arrow A) : Zero (P ⟶ Q) :=
  ⟨Arrow.homMk (show 0 ≫ Q.hom = P.hom ≫ 0 by simp)⟩

instance Arrow.hasAdd (P Q : Arrow A) : Add (P ⟶ Q) :=
  ⟨fun f g => Arrow.homMk (show (f.left + g.left) ≫ Q.hom = P.hom ≫ (f.right + g.right) by simp)⟩

instance Arrow.hasNeg (P Q : Arrow A) : Neg (P ⟶ Q) :=
  ⟨fun f => Arrow.homMk (show (-f.left) ≫ Q.hom = P.hom ≫ (-f.right) by simp)⟩

instance Arrow.hasSub (P Q : Arrow A) : Sub (P ⟶ Q) :=
  ⟨fun f g => Arrow.homMk (show (f.left - g.left) ≫ Q.hom = P.hom ≫ (f.right - g.right) by simp)⟩

instance Arrow.hasNsmul (P Q : Arrow A) : SMul ℕ (P ⟶ Q) :=
  ⟨fun n f => Arrow.homMk (show (n • f.left) ≫ Q.hom = P.hom ≫ (n • f.right) by simp)⟩

instance Arrow.hasZsmul (P Q : Arrow A) : SMul ℤ (P ⟶ Q) :=
  ⟨fun n f => Arrow.homMk (show (n • f.left) ≫ Q.hom = P.hom ≫ (n • f.right) by simp)⟩

@[simp]
theorem Arrow.hasAdd_left {P Q : Arrow A} (f g : P ⟶ Q) : (f + g).left = f.left + g.left :=
  rfl

@[simp]
theorem Arrow.hasAdd_right {P Q : Arrow A} (f g : P ⟶ Q) : (f + g).right = f.right + g.right :=
  rfl

@[simp]
theorem Arrow.hasNeg_left {P Q : Arrow A} (f : P ⟶ Q) : (-f).left = -f.left :=
  rfl

@[simp]
theorem Arrow.hasNeg_right {P Q : Arrow A} (f : P ⟶ Q) : (-f).right = -f.right :=
  rfl

@[simp]
theorem Arrow.hasSub_left {P Q : Arrow A} (f g : P ⟶ Q) : (f - g).left = f.left - g.left :=
  rfl

@[simp]
theorem Arrow.hasSub_right {P Q : Arrow A} (f g : P ⟶ Q) : (f - g).right = f.right - g.right :=
  rfl

instance Arrow.addCommGroup (P Q : Arrow A) : AddCommGroup (P ⟶ Q) :=
  { Arrow.hasAdd P Q, Arrow.hasZero P Q, Arrow.hasNeg P Q, Arrow.hasNsmul P Q,
    Arrow.hasZsmul P Q with
    add_assoc := fun f g h => by ext <;> apply add_assoc
    zero_add := fun f => by ext <;> apply zero_add
    add_zero := fun f => by ext <;> apply add_zero
    add_left_neg := fun f => by ext <;> apply add_left_neg
    add_comm := fun f g => by ext <;> apply add_comm }

instance Arrow.preadditive : Preadditive (Arrow A) :=
  ⟨inferInstance, by introv P; ext <;> apply preadditive.add_comp, by introv P;
    ext <;> apply preadditive.comp_add⟩

end CategoryTheory

