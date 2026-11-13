import LiquidTensorExperiment.PseudoNormedGroup.Category.StrictProFiltPseuNormGrp

#align_import pseudo_normed_group.category.CompHausFiltPseuNormGrpWithTinv

universe u

open CategoryTheory

open scoped NNReal

attribute [local instance] typePow

noncomputable section

/-- The category of profinitely filtered pseudo-normed groups with action of `T⁻¹`. -/
def CompHausFiltPseuNormGrpWithTinv (r : ℝ≥0) : Type (u + 1) :=
  Bundled (@ComphausFilteredPseudoNormedGroupWithTinv r)

namespace CompHausFiltPseuNormGrpWithTinv

variable (r' : ℝ≥0)

def bundledHom : BundledHom (@ComphausFilteredPseudoNormedGroupWithTinvHom r') :=
  ⟨@ComphausFilteredPseudoNormedGroupWithTinvHom.toFun r',
    @ComphausFilteredPseudoNormedGroupWithTinvHom.id r',
    @ComphausFilteredPseudoNormedGroupWithTinvHom.comp r',
    @ComphausFilteredPseudoNormedGroupWithTinvHom.coe_inj r'⟩

attribute [local instance] bundled_hom

/- ./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler λ α,
has_coe_to_sort[has_coe_to_sort] α (Sort*) -/
deriving instance
  «./././Mathport/Syntax/Translate/Command.lean:43:9: unsupported derive handler λ α,
  has_coe_to_sort[has_coe_to_sort] α (Sort*)», LargeCategory, ConcreteCategory for
  CompHausFiltPseuNormGrpWithTinv

end CompHausFiltPseuNormGrpWithTinv

