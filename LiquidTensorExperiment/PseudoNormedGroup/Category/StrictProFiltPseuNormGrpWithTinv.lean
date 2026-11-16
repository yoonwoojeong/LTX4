import LiquidTensorExperiment.PseudoNormedGroup.Category.ProFiltPseuNormGrpWithTinv

#align_import pseudo_normed_group.category.strictProFiltPseuNormGrpWithTinv

universe u

open CategoryTheory

open scoped NNReal

attribute [local instance] typePow

noncomputable section

/-- `ProFiltPseuNormGrpWithTinv₁ r` is the bundled category of
`profinitely_filtered_pseudo_normed_group_with_Tinv r`s, with
(this is the `₁`) exhaustive filtrations and strict morphisms.
The objects are filtered abelian groups equipped with an
endomorphism `T⁻¹` with norm at most `r`; see the docstring
of `profinitely_filtered_pseudo_normed_group_with_Tinv` for
more details.
-/
structure ProFiltPseuNormGrpWithTinv₁ (r : ℝ≥0) : Type (u + 1) where
  M : Type u
  [str : ProfinitelyFilteredPseudoNormedGroupWithTinv r M]
  exhaustive' : ∀ m : M, ∃ c : ℝ≥0, m ∈ PseudoNormedGroup.filtration M c

namespace ProFiltPseuNormGrpWithTinv₁

variable (r : ℝ≥0)


instance : CoeSort (ProFiltPseuNormGrpWithTinv₁ r) (Type _) :=
  ⟨fun M => M.M⟩

instance (M : ProFiltPseuNormGrpWithTinv₁ r) : ProfinitelyFilteredPseudoNormedGroupWithTinv r M :=
  M.str

theorem exhaustive (M : ProFiltPseuNormGrpWithTinv₁ r) (m : M) :
    ∃ c : ℝ≥0, m ∈ PseudoNormedGroup.filtration M c :=
  M.exhaustive' m

instance : LargeCategory (ProFiltPseuNormGrpWithTinv₁.{u} r)
    where
  Hom A B := ComphausFilteredPseudoNormedGroupWithTinvHom r A B
  id A := ComphausFilteredPseudoNormedGroupWithTinvHom.id
  comp f g := g.comp f
  -- Porting note: Lean 3 proved the category laws automatically
  id_comp _ := ComphausFilteredPseudoNormedGroupWithTinvHom.ext fun _ => rfl
  comp_id _ := ComphausFilteredPseudoNormedGroupWithTinvHom.ext fun _ => rfl
  assoc _ _ _ := ComphausFilteredPseudoNormedGroupWithTinvHom.ext fun _ => rfl

-- Porting note: in Lean 3 morphisms unfolded to `ComphausFilteredPseudoNormedGroupWithTinvHom` and
-- used its coercion; in Lean 4 the coercion to functions is declared explicitly
instance {A B : ProFiltPseuNormGrpWithTinv₁.{u} r} : CoeFun (A ⟶ B) fun _ => A → B where
  coe (f : ComphausFilteredPseudoNormedGroupWithTinvHom r A B) := f

def pFPNGT₁ToPFPNGTₑₗ : ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ ProFiltPseuNormGrpWithTinv.{u} r
    where
  obj M := ProFiltPseuNormGrpWithTinv.of r M
  map f := f

instance : ConcreteCategory (ProFiltPseuNormGrpWithTinv₁.{u} r)
    where
  forget :=
    { obj := fun M => M
      map := fun f => f }
  -- Porting note: Lean 3 proved this field automatically
  forget_faithful := ⟨fun h => ComphausFilteredPseudoNormedGroupWithTinvHom.ext (congrFun h)⟩

/-- The "forget the action of T⁻¹" functor on
  profinitely filtered (exhaustive pseudo-)normed groups. -/
def _root_.pFPNGT₁ToPFPNG₁ₑₗ : ProFiltPseuNormGrpWithTinv₁.{u} r ⥤ ProFiltPseuNormGrp₁.{u}
    where
  obj M :=
    { M
      exhaustive' := M.exhaustive' }
  map f :=
    { toFun := f
      map_zero' := f.map_zero
      map_add' := f.map_add
      strict' := f.strict
      continuous' := f.continuous' }

/-- The forgetful functor which takes a profinitely filtered normed group with an action of T⁻¹,
then forgets the action and considered it as a `CompHaus`ly filtered normed group. -/
@[simps]
def _root_.pFPNGT₁ToCHFPNG₁ₑₗ (r' : ℝ≥0) :
    ProFiltPseuNormGrpWithTinv₁.{u} r' ⥤ CompHausFiltPseuNormGrp₁.{u} :=
  pFPNGT₁ToPFPNG₁ₑₗ r' ⋙ pFPNG₁ToCHFPNG₁ₑₗ

theorem coe_comp_apply {A B C : ProFiltPseuNormGrpWithTinv₁ r} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) :=
  rfl

open ProfinitelyFilteredPseudoNormedGroupWithTinv

def tinvLimitFunAux {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁ r)
    (x :
      Σ c : ℝ≥0,
        CompHausFiltPseuNormGrp₁.ConePointTypeFilt ((K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r) ⋙ pFPNG₁ToCHFPNG₁ₑₗ)
          c)
    (j : J) : PseudoNormedGroup.filtration (K.obj j) x.fst :=
  x.2 j

def tinvLimitFun' {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
    (c : ℝ≥0)
    (x :
      CompHausFiltPseuNormGrp₁.ConePointTypeFilt ((K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r) ⋙ pFPNG₁ToCHFPNG₁ₑₗ)
        c) :
    Σ c,
      CompHausFiltPseuNormGrp₁.ConePointTypeFilt ((K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r) ⋙ pFPNG₁ToCHFPNG₁ₑₗ)
        c :=
  ⟨r⁻¹ * c, fun j =>
    -- Porting note: the type and `r` of `tinv` are given explicitly
    ⟨tinv (r' := r) (M := (K.obj j).M) (tinvLimitFunAux r K ⟨c, x⟩ j : K.obj j),
      tinv_mem_filtration (r' := r) (M := (K.obj j).M) _ _ (tinvLimitFunAux r K ⟨c, x⟩ j).2⟩,
    by
    intro i j f
    -- Porting note: Lean 3's `ext1` is `Subtype.ext`
    apply Subtype.ext
    show (K.map f) (tinv (r' := r) (M := (K.obj i).M) _) = tinv (r' := r) (M := (K.obj j).M) _
    erw [(K.map f).map_tinv]
    congr 1
    exact congrArg Subtype.val (x.2 f)⟩

def tinvLimitFun {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
    (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt →
      (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt :=
  Quotient.map' (fun x => tinvLimitFun' r K x.1 x.2)
    (by
      rintro x y ⟨c, h₁, h₂, h⟩
      refine' ⟨r⁻¹ * c, mul_le_mul' le_rfl h₁, mul_le_mul' le_rfl h₂, _⟩
      ext j
      show tinv (tinvLimitFunAux r K x j : K.obj j) = tinv (tinvLimitFunAux r K y j : K.obj j)
      congr 1
      rw [Subtype.ext_iff, Function.funext_iff] at h 
      specialize h j; rwa [Subtype.ext_iff] at h )

open CompHausFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁.ConePointType

theorem tinvLimitFun_incl {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
    (c : ℝ≥0) (x) : tinvLimitFun r K (incl c x) = incl (r⁻¹ * c) (tinvLimitFun' r K c x).2 :=
  rfl

@[simps]
def tinvLimitAddMonoidHom {J : Type u} [SmallCategory J]
    (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
    (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt →+
      (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt
    where
  toFun := tinvLimitFun r K
  map_zero' := by
    apply Quotient.sound'
    dsimp only
    refine' ⟨0, _, le_rfl, _⟩ <;> dsimp only [tinvLimitFun']
    · rw [MulZeroClass.mul_zero]
    · ext j
      exact (tinv (r' := r) (M := (K.obj j).M)).map_zero
  map_add' := by
    rintro ⟨cx, x⟩ ⟨cy, y⟩
    show
      tinvLimitFun r K (incl cx x + incl cy y) =
        tinvLimitFun r K (incl cx x) + tinvLimitFun r K (incl cy y)
    simp only [incl_add_incl, tinvLimitFun_incl]
    -- Porting note: `simp` does not rewrite the right hand side sum (instance mismatch)
    erw [incl_add_incl]
    apply Quotient.sound'
    dsimp only
    refine' ⟨_, le_rfl, _, _⟩
    · exact (mul_add _ _ _).symm.le
    · ext j
      exact (tinv (r' := r) (M := (K.obj j).M)).map_add _ _

open PseudoNormedGroup ProFiltPseuNormGrp₁ CompHausFiltPseuNormGrp₁

theorem Tinv_limit_aux {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
    (c : ℝ≥0) (x : (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt)
    (hx : x ∈ filtration (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt c) :
    tinvLimitAddMonoidHom r K x ∈
      filtration (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt (r⁻¹ * c) :=
  by
  obtain ⟨x, rfl⟩ := hx
  dsimp only [tinvLimitAddMonoidHom_apply, tinvLimitFun_incl]
  exact ⟨_, rfl⟩

-- TODO: break up this proof into pieces.
def tinvLimit {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
    ComphausFilteredPseudoNormedGroupHom
      (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt
      (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBound (tinvLimitAddMonoidHom r K) r⁻¹
    (by
      intro c
      fconstructor
      · apply Tinv_limit_aux
      · let X := (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt
        let F : filtration X c → filtration X (r⁻¹ * c) := fun x =>
          ⟨tinvLimitAddMonoidHom r K x, Tinv_limit_aux _ _ _ _ x.2⟩
        change Continuous F
        let e := CompHausFiltPseuNormGrp₁.ConePointType.filtHomeo (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ)
        suffices Continuous (e (r⁻¹ * c) ∘ F ∘ (e c).symm) by
          -- Porting note: Lean 3's `simpa` replaced by the explicit `Homeomorph` lemmas
          exact (e c).symm.comp_continuous_iff'.mp ((e (r⁻¹ * c)).comp_continuous_iff.mp this)
        let I : ∀ j : J, ComphausFilteredPseudoNormedGroupHom (K.obj j).M (K.obj j).M := fun j =>
          tinv (r' := r) (M := (K.obj j).M)
        -- Porting note: the proof obligations of `G` are stated as separate `have`s
        have hG1 : ∀ (x : CompHausFiltPseuNormGrp₁.ConePointTypeFilt
              (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c) (j : J),
            I j (x j).1 ∈ filtration (K.obj j).M (r⁻¹ * c) := fun x j =>
          tinv_mem_filtration (r' := r) (M := (K.obj j).M) _ _ (x j).2
        have hG2 : ∀ (x : CompHausFiltPseuNormGrp₁.ConePointTypeFilt
              (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c) ⦃i j : J⦄ (e : i ⟶ j),
            StrictComphausFilteredPseudoNormedGroupHom.level
              ((K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ).map e)
              (⟨I i (x i).1, hG1 x i⟩ : filtration (K.obj i).M (r⁻¹ * c)) =
            (⟨I j (x j).1, hG1 x j⟩ : filtration (K.obj j).M (r⁻¹ * c)) := by
          intro x i j e
          have := congrArg Subtype.val (x.2 e)
          apply Subtype.ext
          change (K.map e) (I i (x i).1) = I j (x j).1
          rw [← this]
          exact (K.map e).map_tinv _
        let G :
          CompHausFiltPseuNormGrp₁.ConePointTypeFilt (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c →
            CompHausFiltPseuNormGrp₁.ConePointTypeFilt (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ) (r⁻¹ * c) :=
          fun x => ⟨fun j => ⟨I j (x j).1, hG1 x j⟩, hG2 x⟩
        have : Continuous G := by
          apply Continuous.subtype_mk
          apply continuous_pi
          intro i
          let G1 :
            CompHausFiltPseuNormGrp₁.ConePointTypeFilt (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c →
              filtration (K.obj i).M c :=
            fun x => x i
          let G2 : filtration (K.obj i).M c → filtration (K.obj i).M (r⁻¹ * c) := fun x =>
            ⟨I i x, tinv_mem_filtration (r' := r) (M := (K.obj i).M) _ _ x.2⟩
          change Continuous (G2 ∘ G1)
          apply Continuous.comp
          · apply ComphausFilteredPseudoNormedGroupHom.continuous; intro x; rfl
          · let G11 :
              CompHausFiltPseuNormGrp₁.ConePointTypeFilt (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ _ ⋙ pFPNG₁ToCHFPNG₁ₑₗ) c →
                ∀ j : J, filtration (K.obj j).M c :=
              fun x => x
            let G12 : (∀ j : J, filtration (K.obj j).M c) → filtration (K.obj i).M c := fun x => x i
            change Continuous (G12 ∘ G11)
            apply Continuous.comp
            apply continuous_apply
            apply continuous_subtype_val
        convert this
        ext : 1
        dsimp
        apply_fun (e (r⁻¹ * c)).symm
        simp
        ext; rfl)

instance {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
    ProfinitelyFilteredPseudoNormedGroupWithTinv r
      (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt :=
  {
    (inferInstance :
      ProfinitelyFilteredPseudoNormedGroup
        _) with
    tinv := tinvLimit r K
    tinv_mem_filtration := ComphausFilteredPseudoNormedGroupHom.mkOfBoundBoundBy _ _ _ }

def limitCone {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
    Limits.Cone K
    where
  pt :=
    { M := (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt
      exhaustive' := (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).pt.exhaustive }
  π :=
    { app := fun j =>
        { (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).π.app j with
          map_Tinv' := by
            -- Porting note: Lean 3's `simpa` after unfolding is replaced by an explicit argument
            intro y
            obtain ⟨c, x, rfl⟩ := ConePointType.incl_jointly_surjective y
            change
              ((ConePointType.incl (r⁻¹ * c) (tinvLimitFun' r K c x).2).preimage j).1 =
                tinv (r' := r) (M := (K.obj j).M) ((ConePointType.incl c x).preimage j).1
            rw [ConePointType.coe_incl_preimage_apply, ConePointType.coe_incl_preimage_apply]
            rfl }
      naturality := by
        intro i j e
        ext1 x
        have := (ProFiltPseuNormGrp₁.limitCone (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).π.naturality e
        apply_fun fun e => e x at this 
        exact this }

instance {J : Type u} [SmallCategory J] : CreatesLimitsOfShape J (pFPNGT₁ToPFPNG₁ₑₗ r)
    where
  CreatesLimit {K} :=
    { reflects := fun {C} hC =>
        { lift := fun S =>
            { hC.lift ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone S) with
              map_Tinv' := by
                intro x
                -- Porting note: Lean 3's `erw`/`rw` chain is replaced by an explicit argument
                have hfac : ∀ (j : J) (y : S.pt.M),
                    ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone C).π.app j
                        (hC.lift ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone S) y) =
                      ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone S).π.app j y := fun j y =>
                  congrArg (fun φ => φ y) (hC.fac ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone S) j)
                apply ProFiltPseuNormGrp₁.eq_of_π_eq _ hC
                intro j
                refine (hfac j _).trans
                  ((ComphausFilteredPseudoNormedGroupWithTinvHom.map_tinv (S.π.app j) x).trans ?_)
                refine Eq.trans ?_
                  (ComphausFilteredPseudoNormedGroupWithTinvHom.map_tinv (C.π.app j) _).symm
                exact congrArg (fun y => tinv (r' := r) (M := (K.obj j).M) y) (hfac j x).symm }
          fac := fun S j =>
            ComphausFilteredPseudoNormedGroupWithTinvHom.ext fun x =>
              congrArg (fun φ => φ x) (hC.fac ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone S) j)
          uniq := fun S m h =>
            ComphausFilteredPseudoNormedGroupWithTinvHom.ext fun x =>
              congrArg (fun φ => φ x)
                (hC.uniq ((pFPNGT₁ToPFPNG₁ₑₗ r).mapCone S) ((pFPNGT₁ToPFPNG₁ₑₗ r).map m)
                  fun j => StrictComphausFilteredPseudoNormedGroupHom.ext fun y =>
                    congrArg (fun φ => φ y) (h j)) }
      lifts := fun C hC =>
        { liftedCone := limitCone r K
          validLift :=
            (ProFiltPseuNormGrp₁.limitConeIsLimit (K ⋙ pFPNGT₁ToPFPNG₁ₑₗ r)).uniqueUpToIso hC } }

instance : CreatesLimits (pFPNGT₁ToPFPNG₁ₑₗ r) where
  CreatesLimitsOfShape := inferInstance

instance (r') : CreatesLimits (pFPNGT₁ToCHFPNG₁ₑₗ r') :=
  CategoryTheory.compCreatesLimits _ _

def limitConeIsLimit {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r) :
    Limits.IsLimit (limitCone r K) :=
  Limits.isLimitOfReflects (pFPNGT₁ToPFPNG₁ₑₗ r) (ProFiltPseuNormGrp₁.limitConeIsLimit _)

instance : Limits.HasLimits (ProFiltPseuNormGrpWithTinv₁.{u} r) :=
  hasLimits_of_hasLimits_createsLimits (pFPNGT₁ToPFPNG₁ₑₗ r)

theorem isLimit_ext {J : Type u} [SmallCategory J] (K : J ⥤ ProFiltPseuNormGrpWithTinv₁.{u} r)
    (C : Limits.Cone K) (hC : Limits.IsLimit C) (x y : C.pt) (h : ∀ j, C.π.app j x = C.π.app j y) :
    x = y :=
  ProFiltPseuNormGrp₁.isLimit_ext _ _ (Limits.isLimitOfPreserves (pFPNGT₁ToPFPNG₁ₑₗ r) hC) _ _ h

section ExplicitProducts

def product {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) :
    ProFiltPseuNormGrpWithTinv₁.{u} r where
  M := ∀ i, X i
  -- Why couldn't typeclass inference find this?
  str := ProfinitelyFilteredPseudoNormedGroupWithTinv.pi _ _
  exhaustive' := (ProFiltPseuNormGrp₁.product fun i => (pFPNGT₁ToPFPNG₁ₑₗ r).obj (X i)).exhaustive'

@[simps]
def product.π {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) (i) :
    product r X ⟶ X i :=
  { (ProFiltPseuNormGrp₁.product.π fun i => (pFPNGT₁ToPFPNG₁ₑₗ r).obj (X i)) i with
    map_Tinv' := fun x => rfl }

@[simps]
def product.lift {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
    (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (f : ∀ i, M ⟶ X i) : M ⟶ product r X :=
  {
    ProFiltPseuNormGrp₁.product.lift (fun i => (pFPNGT₁ToPFPNG₁ₑₗ r).obj (X i))
      ((pFPNGT₁ToPFPNG₁ₑₗ r).obj M) fun i => (pFPNGT₁ToPFPNG₁ₑₗ r).map (f i) with
    map_Tinv' := by
      intro x
      -- Porting note: Lean 3's recursive `ext` is replaced by `funext`
      funext i
      -- Porting note: both sides agree with `(f i).map_tinv` definitionally
      exact ComphausFilteredPseudoNormedGroupWithTinvHom.map_tinv (f i) x }

@[reassoc (attr := simp)]
theorem product.lift_π {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
    (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (f : ∀ i, M ⟶ X i) (i) :
    product.lift r X M f ≫ product.π r X i = f i := by
  -- Porting note: Lean 3's `ext; simpa` is replaced by the explicit `ext` lemma and `rfl`
  apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
  intro x
  rfl

theorem product.lift_unique {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
    (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (f : ∀ i, M ⟶ X i) (g : M ⟶ product r X)
    (hg : ∀ i, g ≫ product.π r X i = f i) : g = product.lift r X M f := by
  -- Porting note: Lean 3's recursive `ext` is replaced by the explicit `ext` lemmas
  apply ComphausFilteredPseudoNormedGroupWithTinvHom.ext
  intro x
  funext i
  exact congrArg (fun φ : M ⟶ X i => (φ : M → X i) x) (hg i)

theorem product.hom_ext {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r)
    (M : ProFiltPseuNormGrpWithTinv₁.{u} r) (g₁ g₂ : M ⟶ product r X)
    (h : ∀ i, g₁ ≫ product.π r X i = g₂ ≫ product.π r X i) : g₁ = g₂ :=
  by
  rw [product.lift_unique r X M _ g₁ fun i => rfl, product.lift_unique r X M _ g₂ fun i => rfl]
  simp [h]

def product.fan {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) :
    Limits.Fan X :=
  Limits.Fan.mk (product r X) fun b => product.π _ _ _

def product.isLimit {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrpWithTinv₁.{u} r) :
    Limits.IsLimit (product.fan r X)
    where
  lift M := product.lift _ _ _ fun i => M.π.app ⟨i⟩
  fac := by
    rintro S ⟨j⟩
    dsimp [product.fan]
    simp
  uniq := by
    intro S m hm
    apply product.hom_ext
    intro i
    dsimp [product.fan] at hm 
    simpa using hm ⟨i⟩

end ExplicitProducts

end ProFiltPseuNormGrpWithTinv₁

