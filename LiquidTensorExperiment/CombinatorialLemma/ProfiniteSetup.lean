import LiquidTensorExperiment.Lbar.Functor
import LiquidTensorExperiment.CombinatorialLemma.Finite
import Mathlib.Algebra.Module.LinearMap
import LiquidTensorExperiment.PseudoNormedGroup.BoundedLimits
import LiquidTensorExperiment.ForMathlib.Profinite.DisjointUnion
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Compactum

#align_import combinatorial_lemma.profinite_setup

noncomputable section

open scoped NNReal BigOperators

universe u

section

variable (r : ℝ≥0) [Fact (0 < r)] (Λ : Type u) [PolyhedralLattice Λ]

open CategoryTheory

open CategoryTheory.Limits

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem polyhedral_exhaustive (M : Type _) [PseudoNormedGroup M]
    (e : ∀ x : M, ∃ c, x ∈ PseudoNormedGroup.filtration M c) (x : Λ →+ M) :
    ∃ c : ℝ≥0, x ∈ PseudoNormedGroup.filtration (Λ →+ M) c :=
  by
  obtain ⟨ι, hι, l, hl, h⟩ := PolyhedralLattice.polyhedral Λ
  skip
  let cs : ι → ℝ≥0 := fun i => (e (x (l i))).some
  let c := finset.univ.sup fun i => cs i / «expr∥ ∥₊» (l i)
  -- This should be easy, using the fact that (l i) ≠ 0.
  have hc : ∀ i, cs i ≤ c * «expr∥ ∥₊» (l i) :=
    by
    intro i; rw [← mul_inv_le_iff₀]
    · exact Finset.le_sup (Finset.mem_univ i)
    · rw [Ne.def, nnnorm_eq_zero]; exact h i
  use c
  rw [GeneratesNorm.addMonoidHom_mem_filtration_iff hl x]
  intro i
  apply PseudoNormedGroup.filtration_mono (hc i)
  apply (e (x (l i))).choose_spec

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
@[simps]
def polyhedralPostcompose {M N : ProFiltPseuNormGrpWithTinv₁ r} (f : M ⟶ N) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r (Λ →+ M) (Λ →+ N)
    where
  toFun x := f.toAddMonoidHom.comp x
  map_zero' := by simp only [AddMonoidHom.comp_zero]
  map_add' := by intros; ext; dsimp; erw [f.to_add_monoid_hom.map_add]; rfl
  strict' := by
    obtain ⟨ι, hι, l, hl, h⟩ := PolyhedralLattice.polyhedral Λ
    skip
    intro c x hx
    erw [GeneratesNorm.addMonoidHom_mem_filtration_iff hl] at hx ⊢
    intro i
    apply f.strict
    exact hx i
  continuous' c := by
    rw [PolyhedralLattice.AddMonoidHom.continuous_iff]
    intro l
    simp only
    have aux1 := PolyhedralLattice.AddMonoidHom.incl_continuous Λ r M c
    have aux2 := f.level_continuous (c * «expr∥ ∥₊» l)
    exact (aux2.comp (continuous_apply l)).comp aux1
  map_Tinv' x := by ext l; dsimp; erw [f.map_Tinv]; rfl

/-- the functor `M ↦ Hom(Λ, M), where both are considered as objects in
  `ProFiltPseuNormGrpWithTinv₁.{u} r` -/
@[simps]
def homFunctor : ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r
    where
  obj M :=
    { M := Λ →+ M
      str := inferInstance
      exhaustive' := by apply polyhedral_exhaustive; apply M.exhaustive r }
  map M N f := polyhedralPostcompose _ _ f
  map_id' M := by
    ext
    dsimp [polyhedralPostcompose]
    simp
  map_comp' M N L f g := by
    ext
    dsimp [polyhedralPostcompose]
    simp

@[simps]
def polyhedralPostcompose' {M N : PseuNormGrp₁} (f : M ⟶ N) :
    StrictPseudoNormedGroupHom (Λ →+ M) (Λ →+ N)
    where
  toFun x := f.toAddMonoidHom.comp x
  map_zero' := by simp only [AddMonoidHom.comp_zero]
  map_add' := by intros; ext; dsimp; erw [f.to_add_monoid_hom.map_add]; rfl
  strict' := by
    obtain ⟨ι, hι, l, hl, h⟩ := PolyhedralLattice.polyhedral Λ
    skip
    intro c x hx
    erw [GeneratesNorm.addMonoidHom_mem_filtration_iff hl] at hx ⊢
    intro i
    apply f.strict
    exact hx i

@[simps]
def homFunctor' : PseuNormGrp₁.{u} ⥤ PseuNormGrp₁.{u}
    where
  obj M :=
    { carrier := Λ →+ M
      exhaustive' := by apply polyhedral_exhaustive; apply M.exhaustive }
  map M N f := polyhedralPostcompose' _ f
  map_id' X := by ext; rfl
  map_comp' X Y Z f g := by ext; rfl

open CategoryTheory.Limits PseuNormGrp₁

variable {J : Type u} [SmallCategory J] (K : J ⥤ PseuNormGrp₁.{u})

def Ab.limitCone' {J : Type u} [SmallCategory J] (K : J ⥤ Ab.{u}) : LimitCone K :=
  ⟨Ab.explicitLimitCone.{u, u} _, Ab.explicitLimitConeIsLimit.{u, u} _⟩

attribute [simps] to_Ab Ab.limitCone'

abbrev homFunctor'ConeIsoHomToFunAuxToFunAuxValAux (Λ : Type u) {J : Type u} [PolyhedralLattice Λ]
    [SmallCategory J] (K : J ⥤ PseuNormGrp₁)
    (f : ↥(boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ toAb)))) (q : Λ) :
    ↥(Ab.limitCone' (K ⋙ toAb)).Cone.pt :=
  { val := fun j => (f.1.1 j).1 q
    property := by
      intro a b g
      have := f.1.2 g
      dsimp at this ⊢
      rw [← this]; rfl }

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
abbrev homFunctor'ConeIsoHomToFunAuxToFunAux (Λ : Type u) {J : Type u} [PolyhedralLattice Λ]
    [SmallCategory J] (K : J ⥤ PseuNormGrp₁)
    (f : ↥(boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ toAb)))) :
    Λ → ↥(boundedConePoint (Ab.limitCone' (K ⋙ toAb))) := fun q =>
  { val := homFunctor'ConeIsoHomToFunAuxToFunAuxValAux Λ _ f q
    property := by
      obtain ⟨c, hc⟩ := f.2
      use c * «expr∥ ∥₊» q
      intro j
      apply hc
      simp }

abbrev homFunctor'ConeIsoHomToFunAux (Λ : Type u) {J : Type u} [PolyhedralLattice Λ]
    [SmallCategory J] (K : J ⥤ PseuNormGrp₁) :
    ↥(boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ toAb))) →
      ↥((homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ toAb)))) :=
  fun f =>
  { toFun := homFunctor'ConeIsoHomToFunAuxToFunAux _ _ f
    map_zero' := by ext; simpa
    map_add' := fun x y => by ext; simpa }

def homFunctor'ConeIsoHom :
    boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ _)) ⟶
      (homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ _)))
    where
  toFun := homFunctor'ConeIsoHomToFunAux _ _
  map_zero' := by ext; simpa
  map_add' x y := by ext; simpa
  strict' := by
    intro c x hx
    obtain ⟨⟨d, hc⟩, rfl⟩ := hx
    intro e q hq
    dsimp [bounded_elements.filt_incl]
    delta homFunctor'ConeIsoHomToFunAuxToFunAux
    delta homFunctor'ConeIsoHomToFunAuxToFunAuxValAux
    refine' ⟨⟨_, _⟩, rfl⟩
    intro j
    apply hc _ hq

abbrev homFunctor'ConeIsoInvToFunAuxValAuxValAux (Λ : Type u) {J : Type u} [PolyhedralLattice Λ]
    [SmallCategory J] (K : J ⥤ PseuNormGrp₁)
    (f : ↥((homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ toAb))))) :
    ∀ j : J, (((K ⋙ homFunctor' Λ) ⋙ toAb) ⋙ forget Ab).obj j := fun j =>
  { toFun := fun q => (f.1 q).1.1 j
    map_zero' := by simpa
    map_add' := fun x y => by simpa }

abbrev homFunctor'ConeIsoInvToFunAuxValAux (Λ : Type u) {J : Type u} [PolyhedralLattice Λ]
    [SmallCategory J] (K : J ⥤ PseuNormGrp₁)
    (f : ↥((homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ toAb))))) :
    ↥(Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ toAb)).Cone.pt :=
  { val := homFunctor'ConeIsoInvToFunAuxValAuxValAux _ _ f
    property := by
      intro i j g
      ext q
      change Λ →+ _ at f 
      exact (f q).1.2 g }

abbrev homFunctor'ConeIsoInvToFunAux (Λ : Type u) {J : Type u} [PolyhedralLattice Λ]
    [SmallCategory J] (K : J ⥤ PseuNormGrp₁) :
    ↥((homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ toAb)))) →
      ↥(boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ toAb))) :=
  fun f =>
  { val := homFunctor'ConeIsoInvToFunAuxValAux _ _ f
    property :=
      by
      obtain ⟨c, hc⟩ :=
        ((homFunctor' Λ).obj (bounded_cone_point (Ab.limitCone' (K ⋙ to_Ab)))).exhaustive f
      use c
      intro j d q hq
      dsimp [Ab.explicitLimitCone]
      specialize hc hq
      obtain ⟨t, ht⟩ := hc
      rw [← ht]
      apply t.2 }

def homFunctor'ConeIsoInv :
    (homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ _))) ⟶
      boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ _))
    where
  toFun := homFunctor'ConeIsoInvToFunAux _ _
  map_zero' := by ext; simpa
  map_add' x y := by ext; simpa
  strict' := by
    intro c x hx
    dsimp
    refine' ⟨⟨_, _⟩, rfl⟩
    intro j d q hq
    dsimp [Ab.explicitLimitCone]
    specialize hx hq
    obtain ⟨t, ht⟩ := hx
    rw [← ht]
    apply t.2

def homFunctor'ConeIsoAux :
    boundedConePoint (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ _)) ≅
      (homFunctor' Λ).obj (boundedConePoint (Ab.limitCone' (K ⋙ _)))
    where
  Hom := homFunctor'ConeIsoHom _ _
  inv := homFunctor'ConeIsoInv _ _
  hom_inv_id' := by ext; rfl
  inv_hom_id' := by ext; rfl

def homFunctorConeIso :
    boundedCone (Ab.limitCone' ((K ⋙ homFunctor' Λ) ⋙ _)) ≅
      (homFunctor' Λ).mapCone (boundedCone (Ab.limitCone' (K ⋙ _))) :=
  Cones.ext (homFunctor'ConeIsoAux _ _) fun j => by ext; rfl

instance : PreservesLimits (homFunctor' Λ) :=
  by
  constructor; intro J hJ; constructor; intro K
  apply
    preserves_limit_of_preserves_limit_cone
      (PseuNormGrp₁.boundedConeIsLimit ⟨_, Ab.explicitLimitConeIsLimit.{u, u} _⟩)
  refine'
    is_limit.of_iso_limit
      (PseuNormGrp₁.boundedConeIsLimit ⟨_, Ab.explicitLimitConeIsLimit.{u, u} _⟩) _
  apply homFunctorConeIso

instance (c) : PreservesLimits (homFunctor'.{u} Λ ⋙ PseuNormGrp₁.level.obj c) :=
  @Limits.compPreservesLimits _ _ _ _ _ _ _ _ _ <|
    show PreservesLimits _ from PseuNormGrp₁.preservesLimitsLevelObj.{u, u} _

def ProFiltPseuNormGrpWithTinv₁.toPNG₁ : ProFiltPseuNormGrpWithTinv₁ r ⥤ PseuNormGrp₁
    where
  obj M :=
    { carrier := M
      exhaustive' := M.exhaustive r }
  map X Y f := { f.toAddMonoidHom with strict' := fun c x h => f.Strict h }

def dropProfiniteDropTinv :
    pFPNGT₁ToPFPNG₁ₑₗ r ⋙ ProFiltPseuNormGrp₁.toPNG₁ ≅ ProFiltPseuNormGrpWithTinv₁.toPNG₁ r :=
  (NatIso.ofComponents fun X => Iso.refl _) <| by tidy

instance : PreservesLimits (ProFiltPseuNormGrpWithTinv₁.toPNG₁ r) :=
  preservesLimitsOfNatIso (dropProfiniteDropTinv r)

def homFunctor'ForgetIso (c) :
    ProFiltPseuNormGrpWithTinv₁.toPNG₁ r ⋙ homFunctor' Λ ⋙ PseuNormGrp₁.level.obj c ≅
      homFunctor _ Λ ⋙ pFPNGT₁ToPFPNG₁ₑₗ r ⋙ ProFiltPseuNormGrp₁.level.obj c ⋙ forget _ :=
  (NatIso.ofComponents fun X => eqToIso rfl) <| by tidy

instance homFunctorLevelPreservesLimits (c) :
    PreservesLimits (homFunctor r Λ ⋙ pFPNGT₁ToPFPNG₁ₑₗ r ⋙ ProFiltPseuNormGrp₁.level.obj c) :=
  by
  apply preserves_limits_of_reflects_of_preserves _ (forget Profinite)
  apply preserves_limits_of_nat_iso (homFunctor'ForgetIso _ _ _)
  change
    preserves_limits
      (ProFiltPseuNormGrpWithTinv₁.toPNG₁ r ⋙ homFunctor' Λ ⋙ PseuNormGrp₁.level.obj c)
  apply limits.comp_preserves_limits

end

