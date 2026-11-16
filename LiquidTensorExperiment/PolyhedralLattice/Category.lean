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

instance : CoeSort PolyhedralLatticeCat (Type _) where
  coe X := X.α

namespace PolyhedralLatticeCat

variable (Λ : PolyhedralLatticeCat)

instance : PolyhedralLattice Λ :=
  Λ.str

def toSemiNormedGroup : SemiNormedGroupCat :=
  SemiNormedGroupCat.of Λ

-- Porting note: mathlib4's `BundledHom` also asks for `id_toFun` and `comp_toFun`, which
-- Lean 3 discharged automatically; here they hold by `rfl`.
instance bundledHom : BundledHom @PolyhedralLatticeHom where
  toFun _ _ f := f
  id _ := PolyhedralLatticeHom.id
  comp _ _ _ g f := g.comp f
  hom_ext _ _ _ _ h := PolyhedralLatticeHom.coe_inj h
  id_toFun _ := rfl
  comp_toFun _ _ _ _ _ := rfl

-- Porting note: Lean 3 used `attribute [derive [large_category, concrete_category]]`; the
-- instances it derived are written out (with the names Lean 3 gave them)
instance largeCategory : LargeCategory PolyhedralLatticeCat :=
  BundledHom.category @PolyhedralLatticeHom

instance concreteCategory : ConcreteCategory PolyhedralLatticeCat :=
  BundledHom.concreteCategory @PolyhedralLatticeHom

-- Porting note: in Lean 3 morphisms unfolded to `PolyhedralLatticeHom` and used its
-- coercion; in Lean 4 it is declared (as for mathlib's `MonCat`)
instance {Λ₁ Λ₂ : PolyhedralLatticeCat} : CoeFun (Λ₁ ⟶ Λ₂) fun _ => Λ₁ → Λ₂ where
  coe (f : PolyhedralLatticeHom Λ₁ Λ₂) := f

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
  -- Porting note: the `Zero` instance on morphisms is that of `PolyhedralLatticeHom`
  zero X Y := (inferInstance : Zero (PolyhedralLatticeHom X Y))
  comp_zero := by intros; ext; rfl
  zero_comp := by intro _ _ _ f; ext; exact f.map_zero

def isoMk {Λ₁ Λ₂ : PolyhedralLatticeCat.{u}} (f : Λ₁ →+ Λ₂) (g : Λ₂ → Λ₁)
    (hf : ∀ l, ‖f l‖ = ‖l‖) (hfg : g ∘ f = id) (hgf : f ∘ g = id) : Λ₁ ≅ Λ₂
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
          ‖g l‖ ≤ ‖(f (g l))‖ := le_of_eq <| (hf _).symm
          _ = ‖l‖ := congr_arg norm <| congr_fun hgf l }
  hom_inv_id := by ext x; exact congr_fun hfg x
  inv_hom_id := by ext x; exact congr_fun hgf x

end PolyhedralLatticeCat

