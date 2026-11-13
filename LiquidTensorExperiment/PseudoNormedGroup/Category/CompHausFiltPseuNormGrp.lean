import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective
import Mathlib.Logic.Equiv.Fin
import LiquidTensorExperiment.ForMathlib.CompHaus
import LiquidTensorExperiment.ForMathlib.Topology
import LiquidTensorExperiment.PseudoNormedGroup.WithTinv

#align_import pseudo_normed_group.category.CompHausFiltPseuNormGrp

/-!

# The category of profinitely filtered pseudo-normed groups.

The category of profinite pseudo-normed groups, and the category of
profinitely filtered pseudo-normed groups equipped with an action of T⁻¹.

-/


--import for_mathlib.concrete
universe u

open CategoryTheory

open scoped NNReal

attribute [local instance] typePow

noncomputable section

/-- The category of CompHaus-ly filtered pseudo-normed groups. -/
def CompHausFiltPseuNormGrp : Type (u + 1) :=
  Bundled ComphausFilteredPseudoNormedGroup

namespace CompHausFiltPseuNormGrp

-- Porting note: mathlib4's `BundledHom` also asks for `id_toFun` and `comp_toFun`, which
-- Lean 3 discharged automatically; here they hold by `rfl`.
def bundledHom : BundledHom @ComphausFilteredPseudoNormedGroupHom where
  toFun _ _ f := f
  id _ := ComphausFilteredPseudoNormedGroupHom.id
  comp _ _ _ g f := g.comp f
  hom_ext _ _ _ _ h := ComphausFilteredPseudoNormedGroupHom.coe_inj h
  id_toFun _ := rfl
  comp_toFun _ _ _ _ _ := rfl

attribute [local instance] bundledHom

-- Porting note: Lean 3 used `attribute [derive [large_category, concrete_category]]`; the
-- instances it derived are written out (with the names Lean 3 gave them)
instance largeCategory : LargeCategory CompHausFiltPseuNormGrp :=
  BundledHom.category @ComphausFilteredPseudoNormedGroupHom

instance concreteCategory : ConcreteCategory CompHausFiltPseuNormGrp :=
  BundledHom.concreteCategory @ComphausFilteredPseudoNormedGroupHom

instance : CoeSort CompHausFiltPseuNormGrp (Type _) where
  coe X := X.α

instance (M : CompHausFiltPseuNormGrp) : ComphausFilteredPseudoNormedGroup M :=
  M.str

/-- Construct a bundled `CompHausFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [ComphausFilteredPseudoNormedGroup M] : CompHausFiltPseuNormGrp :=
  Bundled.of M

@[simp]
theorem id_apply (M : CompHausFiltPseuNormGrp) (x : M) : (𝟙 M : M ⟶ M) x = x :=
  rfl

end CompHausFiltPseuNormGrp

