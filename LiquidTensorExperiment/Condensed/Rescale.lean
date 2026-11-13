import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.Rescale.PseudoNormedGroup
import LiquidTensorExperiment.HacksAndTricks.AsyncI
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.Facts.Nnreal

#align_import condensed.rescale

noncomputable section

universe u

open scoped NNReal

open CategoryTheory

namespace ComphausFilteredPseudoNormedGroup

def ofRescaleOneStrict (M : Type _) [ComphausFilteredPseudoNormedGroup M] :
    StrictComphausFilteredPseudoNormedGroupHom (Rescale 1 M) M :=
  { Rescale.ofRescaleOneStrictPseudoNormedGroupHom M with
    Continuous' := fun c => ComphausFilteredPseudoNormedGroup.continuous_castLe (c * 1⁻¹) c }

def toRescaleOneStrict (M : Type _) [ComphausFilteredPseudoNormedGroup M] :
    StrictComphausFilteredPseudoNormedGroupHom M (Rescale 1 M) :=
  { Rescale.toRescaleOneStrictPseudoNormedGroupHom M with
    Continuous' := fun c =>
      haveI : Fact (c ≤ c * 1⁻¹) := ⟨le_of_eq (by rw [inv_one, mul_one])⟩
      ComphausFilteredPseudoNormedGroup.continuous_castLe c (c * 1⁻¹) }

def ofRescaleEqStrict (M : Type _) [ComphausFilteredPseudoNormedGroup M] (r r' : ℝ≥0) [Fact (0 < r)]
    [Fact (0 < r')] (hrr' : r = r') :
    StrictComphausFilteredPseudoNormedGroupHom (Rescale r M) (Rescale r' M) :=
  { Rescale.ofRescaleEqStrictPseudoNormedGroupHom r r' M hrr' with
    Continuous' := fun c =>
      haveI : Fact (c * r⁻¹ ≤ c * r'⁻¹) := ⟨le_of_eq (by rw [hrr'])⟩
      ComphausFilteredPseudoNormedGroup.continuous_castLe (c * r⁻¹) (c * r'⁻¹) }

def ofRescaleRescaleStrict (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] (M : Type _)
    [ComphausFilteredPseudoNormedGroup M] :
    StrictComphausFilteredPseudoNormedGroupHom (Rescale r (Rescale r' M)) (Rescale (r' * r) M) :=
  { Rescale.ofRescaleRescaleStrictPseudoNormedGroupHom r r' M with
    Continuous' := fun c =>
      haveI : Fact (c * r⁻¹ * r'⁻¹ ≤ c * (r' * r)⁻¹) := ⟨le_of_eq (by rw [mul_inv_rev, mul_assoc])⟩
      ComphausFilteredPseudoNormedGroup.continuous_castLe (c * r⁻¹ * r'⁻¹) _ }

def toRescaleRescaleStrict (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] (M : Type _)
    [ComphausFilteredPseudoNormedGroup M] :
    StrictComphausFilteredPseudoNormedGroupHom (Rescale (r' * r) M) (Rescale r (Rescale r' M)) :=
  { Rescale.toRescaleRescaleStrictPseudoNormedGroupHom r r' M with
    Continuous' := fun c =>
      haveI : Fact (c * (r' * r)⁻¹ ≤ c * r⁻¹ * r'⁻¹) := ⟨le_of_eq (by rw [mul_inv_rev, mul_assoc])⟩
      ComphausFilteredPseudoNormedGroup.continuous_castLe (c * (r' * r)⁻¹) _ }

end ComphausFilteredPseudoNormedGroup

namespace CompHausFiltPseuNormGrp

@[simps]
def rescale (r : ℝ≥0) : CompHausFiltPseuNormGrp ⥤ CompHausFiltPseuNormGrp
    where
  obj M := of (Rescale r M)
  map M₁ M₂ f := Rescale.mapComphausFilteredPseudoNormedGroupHom r f
  map_id' := by intros; ext; rfl
  map_comp' := by intros; ext; rfl

def rescaleIsoComponent (r : ℝ≥0) [Fact (0 < r)] (M : CompHausFiltPseuNormGrp) :
    (rescale r).obj M ≅ M
    where
  Hom :=
    ComphausFilteredPseudoNormedGroupHom.mk' (AddMonoidHom.id _)
      (by
        refine' ⟨r⁻¹, fun c => ⟨_, _⟩⟩
        · intro x hx
          refine' PseudoNormedGroup.filtration_mono _ hx
          rw [mul_comm]
        · convert @ComphausFilteredPseudoNormedGroup.continuous_castLe M _ _ _ _ using 1
          rw [mul_comm]; infer_instance)
  inv :=
    ComphausFilteredPseudoNormedGroupHom.mk' (AddMonoidHom.id _)
      (by
        have hr : r ≠ 0 := ne_of_gt (Fact.out _)
        refine' ⟨r, fun c => ⟨_, _⟩⟩
        · intro x hx
          dsimp; erw [Rescale.mem_filtration]
          refine' PseudoNormedGroup.filtration_mono _ hx
          rw [mul_comm, inv_mul_cancel_left₀ hr]
        · convert @ComphausFilteredPseudoNormedGroup.continuous_castLe M _ _ _ _ using 1
          rw [mul_comm, inv_mul_cancel_left₀ hr]; infer_instance)
  hom_inv_id' := by intros; ext; rfl
  inv_hom_id' := by intros; ext; rfl

def rescaleIso (r : ℝ≥0) [Fact (0 < r)] : rescale r ≅ 𝟭 _ :=
  NatIso.ofComponents (rescaleIsoComponent r) fun _ _ _ => rfl

-- instance (X : Profinite) (c : ℝ≥0) [fact (0 < c)] :
--   limits.preserves_limits (rescale c) :=
-- limits.preserves_limits_of_nat_iso (rescale_iso c).symm
instance rescalePreservesLimitsOfShapeDiscreteQuotient (X : Profinite.{u}) (c : ℝ≥0)
    [Fact (0 < c)] :
    Limits.PreservesLimitsOfShape.{u, u, u, u, u + 1, u + 1} (DiscreteQuotient.{u} ↥X)
      (rescale.{u, u} c) :=
  Limits.preservesLimitsOfShapeOfNatIso (rescaleIso c).symm

def rescale₁ (r : ℝ≥0) [Fact (0 < r)] (M : CompHausFiltPseuNormGrp)
    (exh : ∀ m : M, ∃ c, m ∈ PseudoNormedGroup.filtration M c) : CompHausFiltPseuNormGrp₁
    where
  M := Rescale r M
  exhaustive' m := by
    obtain ⟨c, hc⟩ := exh (rescale.of.symm m)
    simp only [Rescale.mem_filtration]
    refine' ⟨c * r, PseudoNormedGroup.filtration_mono _ hc⟩
    rw [mul_inv_cancel_right₀]; exact ne_of_gt (Fact.out _)

end CompHausFiltPseuNormGrp

namespace CompHausFiltPseuNormGrp₁

@[simps]
def rescale (r : ℝ≥0) [Fact (0 < r)] : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp₁
    where
  obj M :=
    { M := Rescale r M
      exhaustive' := fun m =>
        by
        obtain ⟨c, hc⟩ := M.exhaustive (rescale.of.symm m)
        simp only [Rescale.mem_filtration]
        refine' ⟨c * r, PseudoNormedGroup.filtration_mono _ hc⟩
        rw [mul_inv_cancel_right₀]; exact ne_of_gt (Fact.out _) }
  map M₁ M₂ f := Rescale.mapStrictComphausFilteredPseudoNormedGroupHom r f
  map_id' := by intros; ext; rfl
  map_comp' := by intros; ext; rfl

instance rescale.equivalence (r : ℝ≥0) [Fact (0 < r)] : IsEquivalence (rescale r) := by
  haveI : Fact (0 < r⁻¹) := ⟨nnreal.inv_pos.2 (Fact.elim inferInstance)⟩ <;>
      haveI : Fact (0 < r * r⁻¹) :=
        ⟨mul_pos (Fact.elim inferInstance) (Fact.elim inferInstance)⟩ <;>
    exact
      is_equivalence.mk (@Rescale r⁻¹ ⟨nnreal.inv_pos.2 (Fact.elim inferInstance)⟩)
        { Hom :=
            { app := fun M =>
                ((-- M ⟶ rescale 1 M ⟶ rescale (r * r⁻¹) M ⟶ rescale r⁻¹ (rescale r M)
                          ComphausFilteredPseudoNormedGroup.toRescaleRescaleStrict
                          r⁻¹ r M).comp
                      (ComphausFilteredPseudoNormedGroup.ofRescaleEqStrict M 1 (r * r⁻¹)
                        (Eq.symm (mul_inv_cancel (ne_of_gt (Fact.elim inferInstance)))))).comp
                  (ComphausFilteredPseudoNormedGroup.toRescaleOneStrict M)
              naturality' := fun M N f => rfl }
          inv :=
            { app := fun M =>
                (-- rescale r⁻¹ (rescale r M) ⟶ rescale (r * r⁻¹) M ⟶ rescale 1 M ⟶ M
                      ComphausFilteredPseudoNormedGroup.ofRescaleOneStrict
                      M).comp
                  ((ComphausFilteredPseudoNormedGroup.ofRescaleEqStrict M (r * r⁻¹) 1
                        (mul_inv_cancel (ne_of_gt (Fact.elim inferInstance)))).comp
                    (ComphausFilteredPseudoNormedGroup.ofRescaleRescaleStrict r⁻¹ r M))
              naturality' := fun M N f => rfl }
          hom_inv_id' := rfl
          inv_hom_id' := rfl }
        { Hom :=
            { app := fun M =>
                (-- rescale r (rescale r⁻¹ M) ⟶ rescale (r⁻¹ * r) M ⟶ rescale 1 M ⟶ M
                      ComphausFilteredPseudoNormedGroup.ofRescaleOneStrict
                      M).comp
                  ((ComphausFilteredPseudoNormedGroup.ofRescaleEqStrict M (r⁻¹ * r) 1
                        (inv_mul_cancel (ne_of_gt (Fact.elim inferInstance)))).comp
                    (ComphausFilteredPseudoNormedGroup.ofRescaleRescaleStrict r r⁻¹ M))
              naturality' := fun M N f => rfl }
          inv :=
            { app := fun M =>
                ((-- M ⟶ rescale 1 M ⟶ rescale (r⁻¹ * r) M ⟶ rescale r (rescale r⁻¹ M)
                          ComphausFilteredPseudoNormedGroup.toRescaleRescaleStrict
                          r r⁻¹ M).comp
                      (ComphausFilteredPseudoNormedGroup.ofRescaleEqStrict M 1 (r⁻¹ * r)
                        (Eq.symm (inv_mul_cancel (ne_of_gt (Fact.elim inferInstance)))))).comp
                  (ComphausFilteredPseudoNormedGroup.toRescaleOneStrict M)
              naturality' := fun M N f => rfl }
          hom_inv_id' := rfl
          inv_hom_id' := rfl }

instance rescalePreservesLimitsOfShapeDiscreteQuotient (X : Profinite.{u}) (c : ℝ≥0)
    [Fact (0 < c)] :
    Limits.PreservesLimitsOfShape.{u, u, u, u, u + 1, u + 1} (DiscreteQuotient.{u} ↥X)
      (rescale.{u, u} c) :=
  by
  let foo :=
    (CategoryTheory.Adjunction.isEquivalencePreservesLimits (Rescale c)).PreservesLimitsOfShape
  exact foo

-- not 100% sure why I need to define foo first
@[simps]
def rescaleEnlargingIso (r : ℝ≥0) [Fact (0 < r)] :
    rescale r ⋙ cHFPNG₁ToCHFPNGₑₗ ≅ cHFPNG₁ToCHFPNGₑₗ :=
  by
  refine' _ ≪≫ iso_whisker_left _ (CompHausFiltPseuNormGrp.rescaleIso r) ≪≫ functor.right_unitor _
  exact nat_iso.of_components (fun M => iso.refl _) fun _ _ _ => rfl

@[simps]
def rescaleToCondensedIso (r : ℝ≥0) [Fact (0 < r)] :
    rescale r ⋙ toCondensed ≅
      cHFPNG₁ToCHFPNGₑₗ ⋙ CompHausFiltPseuNormGrp.rescale r ⋙ CompHausFiltPseuNormGrp.toCondensed :=
  NatIso.ofComponents (fun M => Iso.refl _) fun _ _ _ => rfl

-- @[simps]
-- def strict_unscale (r : ℝ≥0) [fact (1 ≤ r)] :
--   rescale r ⟶ 𝟭 _ :=
-- { app := λ M, comphaus_filtered_pseudo_normed_group.strict_unscale M r,
--   naturality' := by { intros, ext, refl, } }
-- def Condensed_unscale (r : ℝ≥0) [fact (1 ≤ r)] :
--   rescale r ⋙ to_Condensed ⟶ to_Condensed :=
-- whisker_right (strict_unscale r) to_Condensed ≫ (functor.left_unitor _).hom
-- instance is_iso_strict_unscale (r : ℝ≥0) [fact (1 ≤ r)] (M) :
--   is_iso ((Condensed_unscale r).app M) :=
-- begin
--   admit
-- end
end CompHausFiltPseuNormGrp₁

namespace ComphausFilteredPseudoNormedGroupHom

def strictify (M₁ M₂ : Type _) [ComphausFilteredPseudoNormedGroup M₁]
    [ComphausFilteredPseudoNormedGroup M₂] (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂)
    (r : ℝ≥0) [Fact (0 < r)] (hf : f.BoundBy r) :
    StrictComphausFilteredPseudoNormedGroupHom (Rescale r M₁) M₂ :=
  StrictComphausFilteredPseudoNormedGroupHom.mk' f.toAddMonoidHom
    (by
      intro c
      refine' ⟨fun x hx => PseudoNormedGroup.filtration_mono _ (hf hx), f.continuous _ fun _ => rfl⟩
      have hr : r ≠ 0 := ne_of_gt (Fact.out _)
      rw [mul_left_comm, mul_inv_cancel hr, mul_one])

end ComphausFilteredPseudoNormedGroupHom

open CompHausFiltPseuNormGrp₁

def strictifyNatTrans {C : Type _} [Category C] {F G : C ⥤ CompHausFiltPseuNormGrp₁.{u}}
    (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) (c : ℝ≥0) [Fact (0 < c)]
    (h : ∀ X, (α.app X).BoundBy c) : F ⋙ CompHausFiltPseuNormGrp₁.rescale.{u, u} c ⟶ G
    where
  app X := ComphausFilteredPseudoNormedGroupHom.strictify _ _ (α.app X) c (h X)
  naturality' X Y f := by ext x; have := α.naturality f; apply_fun fun φ => φ.toFun x at this ;
    exact this

theorem strictifyNatTrans_enlarging {C : Type _} [Category C]
    {F G : C ⥤ CompHausFiltPseuNormGrp₁.{u}}
    (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) (c : ℝ≥0) [Fact (0 < c)]
    (h : ∀ X, (α.app X).BoundBy c) :
    whiskerRight (strictifyNatTrans α c h) cHFPNG₁ToCHFPNGₑₗ =
      (Functor.associator _ _ _).Hom ≫ whiskerLeft F (rescaleEnlargingIso c).Hom ≫ α :=
  by ext; rfl

@[simp]
theorem strictifyNatTrans_enlarging' {C : Type _} [Category C]
    {F G : C ⥤ CompHausFiltPseuNormGrp₁.{u}}
    (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ.{u}) (c : ℝ≥0) [Fact (0 < c)]
    (h : ∀ X, (α.app X).BoundBy c) :
    whiskerLeft F (rescaleEnlargingIso.{u, u} c).inv ≫
        (Functor.associator _ _ _).inv ≫ whiskerRight (strictifyNatTrans α c h) cHFPNG₁ToCHFPNGₑₗ =
      α :=
  by ext; rfl

-- move me
instance preadditiveCompHausFiltPseuNormGrp : Preadditive CompHausFiltPseuNormGrp.{u}
    where
  homGroup M N := by infer_instance
  add_comp := by intro X Y Z f₁ f₂ g; ext; exact g.map_add _ _
  comp_add := by intros; ext; rfl

section

variable {F G H : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁.{u}}

variable (α β : F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ)

variable (c cα cβ cαβ : ℝ≥0) [Fact (0 < c)] [Fact (0 < cα)] [Fact (0 < cβ)] [Fact (0 < cαβ)]

def nonstrictExtend (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ) (c : ℝ≥0) [Fact (0 < c)]
    (h : ∀ X, (α.app X).BoundBy c) :
    Profinite.extend.{u} F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ Profinite.extend.{u} G ⋙ cHFPNG₁ToCHFPNGₑₗ :=
  whiskerLeft (Profinite.extend F) (rescaleEnlargingIso.{u, u} c).inv ≫
    whiskerRight
      ((Profinite.extendCommutes _ _).Hom ≫ Profinite.extendNatTrans.{u} (strictifyNatTrans α c h))
      cHFPNG₁ToCHFPNGₑₗ

-- move me
attribute [reassoc] whisker_left_comp whisker_right_comp

theorem nonstrictExtend_whiskerLeft (h : ∀ X, (α.app X).BoundBy c) :
    whiskerLeft FintypeCat.toProfinite (nonstrictExtend.{u} α c h) =
      (Functor.associator _ _ _).inv ≫
        whiskerRight (Profinite.extendExtends.{u} F).Hom cHFPNG₁ToCHFPNGₑₗ.{u} ≫
          α ≫
            whiskerRight (Profinite.extendExtends.{u} G).inv cHFPNG₁ToCHFPNGₑₗ.{u} ≫
              (Functor.associator _ _ _).Hom :=
  by
  rw [nonstrictExtend, whisker_right_comp, whisker_left_comp, whisker_left_comp, ←
    whisker_right_left, ← whisker_right_left, Profinite.extendNatTrans_whiskerLeft,
    whisker_right_comp, whisker_right_comp, strictifyNatTrans_enlarging, ←
    CategoryTheory.whiskerRight_comp_assoc, Profinite.extendCommutes_comp_extendExtends]
  rfl

theorem nonstrictExtendBoundBy (h : ∀ X, (α.app X).BoundBy c) (X : Profinite.{u}) :
    ((nonstrictExtend α c h).app X).BoundBy c :=
  by
  conv =>
    congr
    skip
    rw [← one_mul c]
  -- can't get nth_rewrite to work
  refine' ComphausFilteredPseudoNormedGroupHom.BoundBy.comp (fun r m hm => _) _
  · rw [mul_comm]
    rwa [show r = r * c * c⁻¹ by
        rw [mul_assoc, mul_inv_cancel (ne_of_gt (Fact.elim inferInstance)), mul_one] <;>
          infer_instance] at
      hm 
  · rw [← one_mul (1 : ℝ≥0), whisker_right_comp]
    apply ComphausFilteredPseudoNormedGroupHom.BoundBy.comp
    · apply StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.boundByOne
    · apply StrictComphausFilteredPseudoNormedGroupHom.toChfpsngHom.boundByOne

theorem nonstrict_extend_ext'
    (α β : Profinite.extend.{u} F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ Profinite.extend G ⋙ cHFPNG₁ToCHFPNGₑₗ)
    (c : ℝ≥0) [Fact (0 < c)] (hα : ∀ X, (α.app X).BoundBy c) (hβ : ∀ X, (β.app X).BoundBy c)
    (h : whiskerLeft FintypeCat.toProfinite α = whiskerLeft FintypeCat.toProfinite β) : α = β :=
  by
  suffices strictifyNatTrans α c hα = strictifyNatTrans β c hβ by
    rw [← strictifyNatTrans_enlarging' α c hα, ← strictifyNatTrans_enlarging' β c hβ, this]
  rw [← cancel_epi (Profinite.extendCommutes F (CompHausFiltPseuNormGrp₁.rescale.{u, u} c)).inv]
  apply Profinite.extend_nat_trans_ext
  simp only [whisker_left_comp, cancel_epi]
  refine' ((whiskering_right _ _ _).obj cHFPNG₁ToCHFPNGₑₗ.{u}).map_injective _
  simp only [whiskering_right_obj_map, whisker_right_left, strictifyNatTrans_enlarging,
    whisker_left_comp, h]

-- move me
instance fact_max_pos : Fact (0 < max cα cβ) :=
  ⟨lt_max_iff.mpr (Or.inl <| Fact.out _)⟩

theorem nonstrictExtend_mono (c₁ c₂ : ℝ≥0) [Fact (0 < c₁)] [Fact (0 < c₂)]
    (h₁ : ∀ X, (α.app X).BoundBy c₁) (h₂ : ∀ X, (α.app X).BoundBy c₂) :
    nonstrictExtend α c₁ h₁ = nonstrictExtend α c₂ h₂ :=
  by
  refine' nonstrict_extend_ext' _ _ (max c₁ c₂) _ _ _
  · intro X; refine' (nonstrictExtendBoundBy _ _ _ _).Mono _ (le_max_left _ _)
  · intro X; refine' (nonstrictExtendBoundBy _ _ _ _).Mono _ (le_max_right _ _)
  · simp only [nonstrictExtend_whiskerLeft]

theorem nonstrict_extend_ext
    (α β : Profinite.extend.{u} F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ Profinite.extend G ⋙ cHFPNG₁ToCHFPNGₑₗ)
    (cα : ℝ≥0) [Fact (0 < cα)] (cβ : ℝ≥0) [Fact (0 < cβ)] (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, (β.app X).BoundBy cβ)
    (h : whiskerLeft FintypeCat.toProfinite α = whiskerLeft FintypeCat.toProfinite β) : α = β :=
  by
  refine' nonstrict_extend_ext' _ _ (max cα cβ) _ _ h
  · intro X; refine' (hα X).Mono _ (le_max_left _ _)
  · intro X; refine' (hβ X).Mono _ (le_max_right _ _)

-- move me
instance fact_add_pos (c₁ c₂ : ℝ≥0) [h₁ : Fact (0 < c₁)] [h₂ : Fact (0 < c₂)] :
    Fact (0 < c₁ + c₂) :=
  ⟨add_pos h₁.1 h₂.1⟩

theorem nonstrictExtend_map_add (hα : ∀ X, (α.app X).BoundBy cα) (hβ : ∀ X, (β.app X).BoundBy cβ)
    (hαβ : ∀ X, ((α + β).app X).BoundBy cαβ) :
    nonstrictExtend (α + β) cαβ hαβ = nonstrictExtend α cα hα + nonstrictExtend β cβ hβ :=
  by
  refine' nonstrict_extend_ext _ _ cαβ (cα + cβ) _ _ _
  · intro X; apply nonstrictExtendBoundBy
  · intro X
    simp only [nat_trans.app_add]
    exact (nonstrictExtendBoundBy _ _ _ X).add (nonstrictExtendBoundBy _ _ _ X)
  · ext S : 2
    simp only [whisker_left_app, nat_trans.app_add]
    simp only [← whisker_left_app, nonstrictExtend_whiskerLeft, nonstrictExtend_whiskerLeft,
      preadditive.add_comp, preadditive.comp_add, nat_trans.app_add, nat_trans.comp_app,
      category.id_comp, category.comp_id, functor.associator_hom_app, functor.associator_inv_app]

theorem nonstrictExtend_map_neg (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, ((-α).app X).BoundBy cβ) : nonstrictExtend (-α) cβ hβ = -nonstrictExtend α cα hα :=
  by
  refine' nonstrict_extend_ext _ _ cβ cα _ _ _
  · intro X; apply nonstrictExtendBoundBy
  · intro X; apply (nonstrictExtendBoundBy _ _ _ _).neg
  · ext S : 2
    simp only [whisker_left_app, nat_trans.app_neg]
    simp only [← whisker_left_app, nonstrictExtend_whiskerLeft, nonstrictExtend_whiskerLeft,
      preadditive.neg_comp, preadditive.comp_neg, nat_trans.app_neg, nat_trans.comp_app,
      category.id_comp, category.comp_id, functor.associator_hom_app, functor.associator_inv_app]

theorem nonstrictExtend_map_sub (hα : ∀ X, (α.app X).BoundBy cα) (hβ : ∀ X, (β.app X).BoundBy cβ)
    (hαβ : ∀ X, ((α - β).app X).BoundBy cαβ) :
    nonstrictExtend (α - β) cαβ hαβ = nonstrictExtend α cα hα - nonstrictExtend β cβ hβ :=
  by
  refine' nonstrict_extend_ext _ _ cαβ (cα + cβ) _ _ _
  · intro X; apply nonstrictExtendBoundBy
  · intro X
    simp only [nat_trans.app_sub]
    exact (nonstrictExtendBoundBy _ _ _ X).sub (nonstrictExtendBoundBy _ _ _ X)
  · ext S : 2
    simp only [whisker_left_app, nat_trans.app_sub]
    simp only [← whisker_left_app, nonstrictExtend_whiskerLeft, nonstrictExtend_whiskerLeft,
      preadditive.sub_comp, preadditive.comp_sub, nat_trans.app_sub, nat_trans.comp_app,
      category.id_comp, category.comp_id, functor.associator_hom_app, functor.associator_inv_app]

theorem nonstrictExtend_map_nsmul (n : ℕ) (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, ((n • α).app X).BoundBy cβ) :
    nonstrictExtend (n • α) cβ hβ = n • nonstrictExtend α cα hα :=
  by
  refine' nonstrict_extend_ext _ _ cβ (1 + n * cα) _ _ _
  · intro X; apply nonstrictExtendBoundBy
  · intro X
    simp only [nat_trans.app_nsmul]
    exact ((nonstrictExtendBoundBy _ _ _ _).nsmul _).Mono _ le_add_self
  · ext S : 2
    simp only [whisker_left_app, nat_trans.app_nsmul]
    simp only [← whisker_left_app, nonstrictExtend_whiskerLeft, nonstrictExtend_whiskerLeft,
      preadditive.nsmul_comp, preadditive.comp_nsmul, nat_trans.app_nsmul, nat_trans.comp_app,
      category.id_comp, category.comp_id, functor.associator_hom_app, functor.associator_inv_app]

theorem nonstrictExtend_comp (α : F ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ G ⋙ cHFPNG₁ToCHFPNGₑₗ)
    (β : G ⋙ cHFPNG₁ToCHFPNGₑₗ ⟶ H ⋙ cHFPNG₁ToCHFPNGₑₗ) (hα : ∀ X, (α.app X).BoundBy cα)
    (hβ : ∀ X, (β.app X).BoundBy cβ) (hαβ : ∀ X, ((α ≫ β).app X).BoundBy cαβ) :
    nonstrictExtend (α ≫ β) cαβ hαβ = nonstrictExtend α cα hα ≫ nonstrictExtend β cβ hβ :=
  by
  refine' nonstrict_extend_ext _ _ cαβ (cα * cβ) (nonstrictExtendBoundBy _ _ _) _ _
  · intro X
    rw [mul_comm]
    apply ComphausFilteredPseudoNormedGroupHom.BoundBy.comp
    · exact nonstrictExtendBoundBy α cα hα X
    · exact nonstrictExtendBoundBy β cβ hβ X
  ·
    simp only [nonstrictExtend_whiskerLeft, whisker_left_comp, category.assoc, ←
      iso_whisker_right_hom, ← iso_whisker_right_inv, iso.hom_inv_id_assoc, iso.inv_hom_id_assoc]

theorem nonstrictExtend_id (hα : ∀ X, (NatTrans.app (𝟙 (F ⋙ cHFPNG₁ToCHFPNGₑₗ.{u})) X).BoundBy cα) :
    nonstrictExtend (𝟙 _) cα hα = 𝟙 _ :=
  by
  refine' nonstrict_extend_ext _ _ cα 1 (nonstrictExtendBoundBy _ _ _) _ _
  · intro X; exact ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ _ _
  · simp only [nonstrictExtend_whiskerLeft, whisker_left_comp, category.assoc, ←
      iso_whisker_right_hom, ← iso_whisker_right_inv, category.id_comp, iso.hom_inv_id_assoc,
      iso.inv_hom_id_assoc, whisker_left_id']
    rfl

theorem nonstrictExtend_whiskerRight_enlarging (α : F ⟶ G) :
    (nonstrictExtend (whiskerRight α cHFPNG₁ToCHFPNGₑₗ) 1 fun X =>
        (ComphausFilteredPseudoNormedGroupHom.mkOfStrictStrict _ _).boundByOne) =
      whiskerRight (Profinite.extendNatTrans α) _ :=
  by
  refine'
    nonstrict_extend_ext _ _ 1 1 (nonstrictExtendBoundBy _ _ _)
      (fun X => (ComphausFilteredPseudoNormedGroupHom.mkOfStrictStrict _ _).boundByOne) _
  rw [nonstrictExtend_whiskerLeft, ← whisker_right_left, Profinite.extendNatTrans_whiskerLeft]
  rfl

end

