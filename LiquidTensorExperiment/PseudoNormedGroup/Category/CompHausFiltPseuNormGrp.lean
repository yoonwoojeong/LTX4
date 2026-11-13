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

def bundledHom : BundledHom @ComphausFilteredPseudoNormedGroupHom :=
  ⟨@ComphausFilteredPseudoNormedGroupHom.toFun, @ComphausFilteredPseudoNormedGroupHom.id,
    @ComphausFilteredPseudoNormedGroupHom.comp, @ComphausFilteredPseudoNormedGroupHom.coe_inj⟩

attribute [local instance] bundled_hom

deriving instance LargeCategory, ConcreteCategory for CompHausFiltPseuNormGrp

instance : CoeSort CompHausFiltPseuNormGrp (Type _) :=
  Bundled.hasCoeToSort

instance (M : CompHausFiltPseuNormGrp) : ComphausFilteredPseudoNormedGroup M :=
  M.str

/-- Construct a bundled `CompHausFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [ComphausFilteredPseudoNormedGroup M] : CompHausFiltPseuNormGrp :=
  Bundled.of M

@[simp]
theorem id_apply (M : CompHausFiltPseuNormGrp) (x : M) : (𝟙 M : M ⟶ M) x = x :=
  rfl

end CompHausFiltPseuNormGrp

