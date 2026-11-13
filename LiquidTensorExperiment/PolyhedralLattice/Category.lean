import LiquidTensorExperiment.PolyhedralLattice.Basic
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels

#align_import polyhedral_lattice.category

/-!

# The category of polyhedral lattices

-/


universe u

open CategoryTheory

/-- The category of polyhedral lattices and bounded group homomorphisms. -/
def PolyhedralLatticeCat : Type (u + 1) :=
  Bundled PolyhedralLattice

instance : CoeSort PolyhedralLatticeCat (Type _) :=
  Bundled.hasCoeToSort

namespace PolyhedralLatticeCat

variable (Λ : PolyhedralLatticeCat)

instance : PolyhedralLattice Λ :=
  Λ.str

def toSemiNormedGroup : SemiNormedGroupCat :=
  SemiNormedGroupCat.of Λ

instance bundledHom : BundledHom @PolyhedralLatticeHom :=
  ⟨@PolyhedralLatticeHom.toFun, @PolyhedralLatticeHom.id, @PolyhedralLatticeHom.comp,
    @PolyhedralLatticeHom.coe_inj⟩

deriving instance LargeCategory, ConcreteCategory for PolyhedralLatticeCat

/-- Construct a bundled `PolyhedralLattice` from the underlying type and typeclass. -/
def of (Λ : Type u) [PolyhedralLattice Λ] : PolyhedralLatticeCat :=
  Bundled.of Λ

-- noncomputable
-- instance : has_zero PolyhedralLattice := ⟨of punit⟩
-- noncomputable
-- instance : inhabited PolyhedralLattice := ⟨0⟩
@[simp]
theorem coe_of (Λ : Type u) [PolyhedralLattice Λ] : (PolyhedralLatticeCat.of Λ : Type u) = Λ :=
  rfl

@[simp]
theorem coe_id (Λ : PolyhedralLatticeCat) : ⇑(𝟙 Λ) = id :=
  rfl

instance : Limits.HasZeroMorphisms.{u, u + 1} PolyhedralLatticeCat
    where
  comp_zero := by intros; ext; rfl
  zero_comp := by intro _ _ _ f; ext; exact f.map_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
def isoMk {Λ₁ Λ₂ : PolyhedralLatticeCat.{u}} (f : Λ₁ →+ Λ₂) (g : Λ₂ → Λ₁)
    (hf : ∀ l, «expr∥ ∥» (f l) = «expr∥ ∥» l) (hfg : g ∘ f = id) (hgf : f ∘ g = id) : Λ₁ ≅ Λ₂
    where
  hom := { f with strict' := fun l => le_of_eq (hf l) }
  inv :=
    {
      AddEquiv.symm
        { f with
          invFun := g
          left_inv := congr_fun hfg
          right_inv := congr_fun hgf } with
      strict' := fun l =>
        calc
          «expr∥ ∥» (g l) ≤ «expr∥ ∥» (f (g l)) := le_of_eq <| (hf _).symm
          _ = «expr∥ ∥» l := congr_arg norm <| congr_fun hgf l }
  hom_inv_id' := by ext x; exact congr_fun hfg x
  inv_hom_id' := by ext x; exact congr_fun hgf x

end PolyhedralLatticeCat

