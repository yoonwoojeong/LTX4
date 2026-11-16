import LiquidTensorExperiment.ForMathlib.HomotopyCategoryPretriangulated
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import Mathlib.CategoryTheory.Abelian.Projective

#align_import for_mathlib.derived.defs

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

open HomologicalComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace HomotopyCategory

variable {ι : Type _} {c : ComplexShape ι}

local notation "𝒦" => HomotopyCategory A c

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-- Say `c` is a complex shape on an index type `ι`. An object of `homotopy_category A c`
is acyclic if the homology of this object is 0 at all indices `i : ι`. -/
class IsAcyclic (X : 𝒦) : Prop where
  cond : ∀ i, IsZero ((HomotopyCategory.homology'Functor _ _ i).obj X)

theorem isAcyclicOfIso {X Y : 𝒦} (e : X ≅ Y) [IsAcyclic X] : IsAcyclic Y :=
  by
  constructor
  intro i
  let e' : (homology'Functor A c i).obj X ≅ (homology'Functor A c i).obj Y := Functor.mapIso _ e
  apply CategoryTheory.Limits.isZero_of_iso_of_zero _ e'
  apply IsAcyclic.cond X i

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-- An object of `homotopy_category A c` is "K-projective" if the only map from
that object to any acyclic object is the zero map. -/
class IsKProjective (X : 𝒦) : Prop where
  cond : ∀ (Y : 𝒦) [IsAcyclic Y] (f : X ⟶ Y), f = 0

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-- A morphism in the homotopy category is a quasi-isomorphism if it
induces isomorphisms on all homology groups. -/
class IsQuasiIso {X Y : 𝒦} (f : X ⟶ Y) : Prop where
  cond : ∀ i, IsIso ((HomotopyCategory.homology'Functor _ _ i).map f)

end HomotopyCategory

namespace HomotopyCategory

local notation "𝒦" => HomotopyCategory A (ComplexShape.up ℤ)

local notation "HH" => HomotopyCategory.homology'Functor A (ComplexShape.up ℤ) 0

/-- An object `(Cⁱ)` of `homotopy_category A ℤ↑` is bounded_by `n : ℕ` if the all the objects
`Cⁱ` for `i ≥ n` in the complex are zero -/
def BoundedBy (X : 𝒦) (n : ℤ) : Prop :=
  ∀ i, n ≤ i → IsZero (X.as.pt i)

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
class IsBoundedAbove (X : 𝒦) : Prop where
  cond : ∃ a : ℤ, X.BoundedBy a

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
class IsUniformlyBoundedAbove {α : Type _} (X : α → 𝒦) : Prop where
  cond : ∃ n : ℤ, ∀ a, (X a).BoundedBy n

instance isBoundedAboveOfIsUniformlyBoundedAbove {α : Type _} (X : α → 𝒦)
    [IsUniformlyBoundedAbove X] (a) : IsBoundedAbove (X a) :=
  by
  obtain ⟨n, hn⟩ := IsUniformlyBoundedAbove.cond X
  exact ⟨⟨n, hn a⟩⟩

end HomotopyCategory

variable (A)

/-- The category `bounded_homotopy_category A` has objects the complexes indexed by `ℤ↑`
which are bounded above, i.e. the objects in the complex are equal to zero for sufficiently
large indices. Morphisms are homotopy classes of maps. -/
structure BoundedHomotopyCategory where
  val : HomotopyCategory A (ComplexShape.up ℤ)
  [bdd : HomotopyCategory.IsBoundedAbove val]

