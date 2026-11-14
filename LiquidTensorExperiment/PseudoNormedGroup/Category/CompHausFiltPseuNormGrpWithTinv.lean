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

-- Porting note: mathlib4's `BundledHom` also asks for `id_toFun` and `comp_toFun`, which
-- Lean 3 discharged automatically; here they hold by `rfl`.
def bundledHom : BundledHom (@ComphausFilteredPseudoNormedGroupWithTinvHom r') where
  toFun _ _ f := f
  id _ := ComphausFilteredPseudoNormedGroupWithTinvHom.id
  comp _ _ _ g f := g.comp f
  hom_ext _ _ _ _ h := ComphausFilteredPseudoNormedGroupWithTinvHom.coe_inj h
  id_toFun _ := rfl
  comp_toFun _ _ _ _ _ := rfl

attribute [local instance] bundledHom

-- Porting note: Lean 3 used `attribute [derive [large_category, concrete_category]]`; the
-- instances it derived are written out (with the names Lean 3 gave them)
instance largeCategory (r : ℝ≥0) : LargeCategory (CompHausFiltPseuNormGrpWithTinv r) :=
  BundledHom.category (@ComphausFilteredPseudoNormedGroupWithTinvHom r)

instance concreteCategory (r : ℝ≥0) : ConcreteCategory (CompHausFiltPseuNormGrpWithTinv r) :=
  BundledHom.concreteCategory (@ComphausFilteredPseudoNormedGroupWithTinvHom r)

instance (r : ℝ≥0) : CoeSort (CompHausFiltPseuNormGrpWithTinv r) (Type _) where
  coe X := X.α

instance (r : ℝ≥0) (M : CompHausFiltPseuNormGrpWithTinv r) :
    ComphausFilteredPseudoNormedGroupWithTinv r M :=
  M.str

-- Porting note: in Lean 3 morphisms unfolded to the structure and used its coercion; in Lean 4
-- the coercion to functions is declared explicitly
instance {r : ℝ≥0} {A B : CompHausFiltPseuNormGrpWithTinv r} : CoeFun (A ⟶ B) fun _ => A → B where
  coe (f : ComphausFilteredPseudoNormedGroupWithTinvHom r A B) := f

end CompHausFiltPseuNormGrpWithTinv
