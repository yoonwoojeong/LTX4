import LiquidTensorExperiment.PseudoNormedGroup.Category.CompHausFiltPseuNormGrpWithTinv

#align_import pseudo_normed_group.category.ProFiltPseuNormGrpWithTinv

/-!

# The category of profinitely filtered pseudo-normed groups (and friends).

The category of profinite pseudo-normed groups, and the category of
profinitely filtered pseudo-normed groups equipped with an action of T⁻¹.

-/


universe u

open CategoryTheory

open scoped NNReal

attribute [local instance] typePow

noncomputable section

/-- The category of profinitely filtered pseudo-normed groups with action of `T⁻¹`. -/
def ProFiltPseuNormGrpWithTinv (r : ℝ≥0) : Type (u + 1) :=
  Bundled (@ProfinitelyFilteredPseudoNormedGroupWithTinv r)

namespace ProFiltPseuNormGrpWithTinv

variable (r' : ℝ≥0)

attribute [local instance] CompHausFiltPseuNormGrpWithTinv.bundledHom

def bundled_hom :
    BundledHom.ParentProjection
      (@ProfinitelyFilteredPseudoNormedGroupWithTinv.toComphausFilteredPseudoNormedGroupWithTinv
        r') :=
  ⟨⟩

attribute [local instance] bundled_hom

/-
instance bundled_hom : bundled_hom (@comphaus_filtered_pseudo_normed_group_with_Tinv_hom r') :=
⟨@comphaus_filtered_pseudo_normed_group_with_Tinv_hom.toFun r',
 @comphaus_filtered_pseudo_normed_group_with_Tinv_hom.id r',
 @comphaus_filtered_pseudo_normed_group_with_Tinv_hom.comp r',
 @comphaus_filtered_pseudo_normed_group_with_Tinv_hom.coe_inj r'⟩
-/
-- Porting note: Lean 3 used `attribute [derive [λ α, has_coe_to_sort α (Sort*), large_category,
-- concrete_category]]`; the instances it derived are written out (with the names Lean 3 gave
-- them)
instance largeCategory (r : ℝ≥0) : LargeCategory (ProFiltPseuNormGrpWithTinv r) := by
  dsimp only [ProFiltPseuNormGrpWithTinv]; infer_instance

instance concreteCategory (r : ℝ≥0) : ConcreteCategory (ProFiltPseuNormGrpWithTinv r) := by
  dsimp only [ProFiltPseuNormGrpWithTinv]; infer_instance

instance (r : ℝ≥0) : CoeSort (ProFiltPseuNormGrpWithTinv r) (Type _) where
  coe X := X.α

instance (r : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r) : ProfinitelyFilteredPseudoNormedGroupWithTinv r M :=
  M.str

-- Porting note: in Lean 3 morphisms unfolded to the structure and used its coercion; in Lean 4
-- the coercion to functions is declared explicitly
instance {r : ℝ≥0} {A B : ProFiltPseuNormGrpWithTinv r} : CoeFun (A ⟶ B) fun _ => A → B where
  coe (f : ComphausFilteredPseudoNormedGroupWithTinvHom r A B) := f

/-- Construct a bundled `ProFiltPseuNormGrpWithTinv` from the underlying type and typeclass. -/
def of (r' : ℝ≥0) (M : Type u) [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] :
    ProFiltPseuNormGrpWithTinv r' :=
  Bundled.of M

instance : Zero (ProFiltPseuNormGrpWithTinv r') :=
  ⟨{  α := PUnit
      str := PUnit.profinitelyFilteredPseudoNormedGroupWithTinv r' }⟩

instance : Inhabited (ProFiltPseuNormGrpWithTinv r') :=
  ⟨0⟩

@[simp]
theorem coe_of (V : Type u) [ProfinitelyFilteredPseudoNormedGroupWithTinv r' V] :
    (ProFiltPseuNormGrpWithTinv.of r' V : Type u) = V :=
  rfl

@[simp]
theorem of_coe (M : ProFiltPseuNormGrpWithTinv r') : of r' M = M := by cases M; rfl

@[simp]
theorem coe_id (V : ProFiltPseuNormGrpWithTinv r') : ⇑(𝟙 V) = id :=
  rfl

@[simp]
theorem coe_comp {A B C : ProFiltPseuNormGrpWithTinv r'} (f : A ⟶ B) (g : B ⟶ C) :
    ⇑(f ≫ g) = g ∘ f :=
  rfl

@[simp]
theorem coe_comp_apply {A B C : ProFiltPseuNormGrpWithTinv r'} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) :=
  rfl

open PseudoNormedGroup

section

variable (M : Type _) [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] (c : ℝ≥0)

instance : T2Space (TopCat.of (filtration M c)) := by dsimp; infer_instance

instance : TotallyDisconnectedSpace (TopCat.of (filtration M c)) := by dsimp; infer_instance

instance : CompactSpace (TopCat.of (filtration M c)) := by dsimp; infer_instance

end

-- @[simps] def Filtration (c : ℝ≥0) : ProFiltPseuNormGrp ⥤ Profinite :=
-- { obj := λ M, ⟨Top.of (filtration M c)⟩,
--   map := λ M₁ M₂ f, ⟨f.level c, f.level_continuous c⟩,
--   map_id' := by { intros, ext, refl },
--   map_comp' := by { intros, ext, refl } }
open PseudoNormedGroup ComphausFilteredPseudoNormedGroupWithTinvHom

open ProfinitelyFilteredPseudoNormedGroupWithTinv (tinv)

variable {r'}

variable {M M₁ M₂ : ProFiltPseuNormGrpWithTinv.{u} r'}

variable {f : M₁ ⟶ M₂}

-- Porting note: Lean 3's recursive `ext` is replaced by the explicit `ext` lemma of
-- `ComphausFilteredPseudoNormedGroupWithTinvHom` (here and in `pow`, `powPowX`, `powMul`), and
-- by `funext i j` for the nested function types
/-- The isomorphism induced by a bijective `comphaus_filtered_pseudo_normed_group_with_Tinv_hom`
whose inverse is strict. -/
def isoOfEquivOfStrict (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) : M₁ ≅ M₂
    where
  hom := f
  inv := invOfEquivOfStrict e he strict
  hom_inv_id := by
    apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
    intro x
    simp [ComphausFilteredPseudoNormedGroupWithTinvHom.invOfEquivOfStrict, he]
  inv_hom_id := by
    apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
    intro x
    simp [ComphausFilteredPseudoNormedGroupWithTinvHom.invOfEquivOfStrict, he]

@[simp]
theorem isoOfEquivOfStrict.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₁) :
    (isoOfEquivOfStrict e he strict).hom x = f x :=
  rfl

@[simp]
theorem IsoOfEquivOfStrictSymm.apply (e : M₁ ≃+ M₂) (he : ∀ x, f x = e x)
    (strict : ∀ ⦃c x⦄, x ∈ filtration M₂ c → e.symm x ∈ filtration M₁ c) (x : M₂) :
    (isoOfEquivOfStrict e he strict).symm.hom x = e.symm x :=
  rfl

def isoOfEquivOfStrict' (e : M₁ ≃+ M₂)
    (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
    (continuous' : ∀ c, Continuous (PseudoNormedGroup.level e (fun c x => (strict' c x).1) c))
    (map_Tinv' : ∀ x, e (tinv x) = tinv (e x)) : M₁ ≅ M₂ :=
  @isoOfEquivOfStrict r' M₁ M₂
    { e.toAddMonoidHom with
      toFun := e
      strict' := fun c x => (strict' c x).1
      continuous'
      map_Tinv' }
    e (fun _ => rfl) (by intro c x hx; rwa [strict', e.apply_symm_apply])

@[simp]
theorem isoOfEquivOfStrict'_hom_apply (e : M₁ ≃+ M₂)
    (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
    (continuous' : ∀ c, Continuous (PseudoNormedGroup.level e (fun c x => (strict' c x).1) c))
    (map_Tinv' : ∀ x, e (tinv x) = tinv (e x)) (x : M₁) :
    (isoOfEquivOfStrict' e strict' continuous' map_Tinv').hom x = e x :=
  rfl

@[simp]
theorem isoOfEquivOfStrict'_inv_apply (e : M₁ ≃+ M₂)
    (strict' : ∀ c x, x ∈ filtration M₁ c ↔ e x ∈ filtration M₂ c)
    (continuous' : ∀ c, Continuous (PseudoNormedGroup.level e (fun c x => (strict' c x).1) c))
    (map_Tinv' : ∀ x, e (tinv x) = tinv (e x)) (x : M₂) :
    (isoOfEquivOfStrict' e strict' continuous' map_Tinv').inv x = e.symm x :=
  rfl

variable (r')

@[simps]
def pow (n : ℕ) : ProFiltPseuNormGrpWithTinv.{u} r' ⥤ ProFiltPseuNormGrpWithTinv.{u} r'
    where
  obj M := of r' <| M ^ n
  map f := ProfinitelyFilteredPseudoNormedGroupWithTinv.piMap r' _ _ fun _ => f
  map_id M := by
    apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
    intro x
    rfl
  map_comp := by
    intros
    apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
    intro x
    rfl

@[simps]
def powPowXEquiv (N n : ℕ) : M ^ (N * n) ≃+ (M ^ N) ^ n :=
  {
    ((Equiv.curry _ _ _).symm.trans
        (((Equiv.prodComm _ _).trans finProdFinEquiv).arrowCongr
          (Equiv.refl
            _))).symm with
    toFun :=
      ((Equiv.curry _ _ _).symm.trans
          (((Equiv.prodComm _ _).trans finProdFinEquiv).arrowCongr (Equiv.refl _))).symm
    map_add' := fun x y => by
      funext i j
      rfl }

open ProfinitelyFilteredPseudoNormedGroup

open ComphausFilteredPseudoNormedGroup

@[simps]
def powPowX (N n : ℕ) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
    (pow r' N ⋙ pow r' n).obj M ≅ (pow r' (N * n)).obj M :=
  Iso.symm <|
    isoOfEquivOfStrict' (powPowXEquiv r' N n)
      (by
        intro c x
        dsimp
        constructor <;> intro h
        · intro i j; exact h (finProdFinEquiv (j, i))
        · intro ij
          have := h (finProdFinEquiv.symm ij).2 (finProdFinEquiv.symm ij).1
          dsimp [-finProdFinEquiv_symm_apply] at this 
          simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using this)
      (by
        intro c; dsimp
        rw [← (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun _ => M ^ N) c).comp_continuous_iff, ←
          (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun _ => M) c).symm.comp_continuous_iff']
        apply continuous_pi
        intro i
        rw [← (ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun _ => M) c).comp_continuous_iff]
        apply continuous_pi
        intro j
        have := @continuous_apply _ (fun _ => filtration M c) _ (finProdFinEquiv (j, i))
        dsimp [Function.comp] at this ⊢
        simpa only [Subtype.coe_eta])
      (by
        intros
        funext i j
        rfl)

@[simps hom inv]
def powMul (N n : ℕ) : pow r' (N * n) ≅ pow r' N ⋙ pow r' n :=
  NatIso.ofComponents (fun M => (powPowX r' N n M).symm)
    (by
      intro X Y f
      apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
      intro x
      funext i j
      rfl)

end ProFiltPseuNormGrpWithTinv

