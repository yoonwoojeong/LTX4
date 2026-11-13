import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective

#align_import for_mathlib.Profinite.product

namespace Profinite

universe u

variable (X Y : Profinite.{u})

open CategoryTheory.Limits

open CategoryTheory

/-- An explicit cone for the product of two profinite sets. -/
@[simps]
def prodCone : Cone (pair X Y) :=
  Limits.BinaryFan.mk (⟨Prod.fst⟩ : Profinite.of (X × Y) ⟶ X)
    (⟨Prod.snd⟩ : Profinite.of (X × Y) ⟶ Y)

/-
{ X := Profinite.of (X × Y),
  π := discrete.nat_trans (λ i,
    match i with
    | ⟨walking_pair.left⟩ := ⟨prod.fst⟩
    | ⟨walking_pair.right⟩ := ⟨prod.snd⟩
    end) }
-/
/-
{ X := Profinite.of (X × Y),
  π :=
  { app := λ i,
  match i with
  | discrete.mk walking_pair.left := ⟨prod.fst⟩
  | discrete.mk walking_pair.right := ⟨prod.snd⟩
  end } } .
-/
/-- The explicit cone for the product of two profinite sets is a limit cone. -/
@[simps]
def isLimitProdCone : IsLimit (prodCone X Y)
    where
  lift S := { toFun := fun t => ⟨S.π.app ⟨WalkingPair.left⟩ t, S.π.app ⟨WalkingPair.right⟩ t⟩ }
  fac := by
    rintro S (_ | _)
    · ext; rfl
    · ext; rfl
  uniq := by
    rintro S m h
    ext x
    · specialize h ⟨CategoryTheory.Limits.WalkingPair.left⟩
      apply_fun fun e => e x at h 
      exact h
    · specialize h ⟨WalkingPair.right⟩
      apply_fun fun e => e x at h 
      exact h

/-- The isomorphism between the categorical product and the "usual" product. -/
@[simps Hom inv]
noncomputable def prodIso : X ⨯ Y ≅ Profinite.of (X × Y) :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitProdCone X Y)

end Profinite

