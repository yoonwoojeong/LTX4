import LiquidTensorExperiment.PseudoNormedGroup.Category.StrictCompHausFiltPseuNormGrp

#align_import pseudo_normed_group.category.ProFiltPseuNormGrp

universe u

open CategoryTheory

open scoped NNReal

noncomputable section

attribute [local instance] typePow

/-- The category of profinitely filtered pseudo-normed groups. -/
def ProFiltPseuNormGrp : Type (u + 1) :=
  Bundled ProfinitelyFilteredPseudoNormedGroup

namespace ProFiltPseuNormGrp

attribute [local instance] CompHausFiltPseuNormGrp.bundledHom

def bundledHom :
    BundledHom.ParentProjection
      @ProfinitelyFilteredPseudoNormedGroup.toComphausFilteredPseudoNormedGroup :=
  ⟨⟩

attribute [local instance] bundledHom

-- Porting note: Lean 3 used `attribute [derive [large_category, concrete_category]]`; the
-- instances it derived are written out (with the names Lean 3 gave them), as for mathlib's
-- `CommMonCat`
instance largeCategory : LargeCategory ProFiltPseuNormGrp := by
  dsimp only [ProFiltPseuNormGrp]; infer_instance

instance concreteCategory : ConcreteCategory ProFiltPseuNormGrp := by
  dsimp only [ProFiltPseuNormGrp]; infer_instance

instance : CoeSort ProFiltPseuNormGrp (Type _) where
  coe X := X.α

instance : HasForget₂ ProFiltPseuNormGrp CompHausFiltPseuNormGrp :=
  BundledHom.forget₂ _ _

@[simps]
def toCompHausFilt : ProFiltPseuNormGrp ⥤ CompHausFiltPseuNormGrp :=
  forget₂ _ _

/-- Construct a bundled `ProFiltPseuNormGrp` from the underlying type and typeclass. -/
def of (M : Type u) [ProfinitelyFilteredPseudoNormedGroup M] : ProFiltPseuNormGrp :=
  Bundled.of M

instance : Zero ProFiltPseuNormGrp :=
  ⟨of PUnit⟩

instance : Inhabited ProFiltPseuNormGrp :=
  ⟨0⟩

instance (M : ProFiltPseuNormGrp) : ProfinitelyFilteredPseudoNormedGroup M :=
  M.str

-- Porting note: in Lean 3 morphisms unfolded to `ComphausFilteredPseudoNormedGroupHom` and used
-- its coercion; in Lean 4 it is declared (as for mathlib's `MonCat`)
instance {A B : ProFiltPseuNormGrp.{u}} : CoeFun (A ⟶ B) fun _ => A → B where
  coe (f : ComphausFilteredPseudoNormedGroupHom A B) := f

@[simp]
theorem coe_of (V : Type u) [ProfinitelyFilteredPseudoNormedGroup V] :
    (ProFiltPseuNormGrp.of V : Type u) = V :=
  rfl

@[simp]
theorem coe_id (V : ProFiltPseuNormGrp) : ⇑(𝟙 V) = id :=
  rfl

@[simp]
theorem coe_comp {A B C : ProFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) : ⇑(f ≫ g) = g ∘ f :=
  rfl

@[simp]
theorem coe_comp_apply {A B C : ProFiltPseuNormGrp} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) :=
  rfl

open PseudoNormedGroup

section

variable (M : Type _) [ProfinitelyFilteredPseudoNormedGroup M] (c : ℝ≥0)

instance : T2Space (TopCat.of (filtration M c)) := by dsimp; infer_instance

instance : TotallyDisconnectedSpace (TopCat.of (filtration M c)) := by dsimp; infer_instance

instance : CompactSpace (TopCat.of (filtration M c)) := by dsimp; infer_instance

end

end ProFiltPseuNormGrp

