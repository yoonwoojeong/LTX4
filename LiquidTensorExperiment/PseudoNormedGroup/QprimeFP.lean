import LiquidTensorExperiment.PseudoNormedGroup.FP2
import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.FreePfpng.Acyclic
import LiquidTensorExperiment.ForMathlib.Derived.ExtCoproducts
import LiquidTensorExperiment.ForMathlib.Derived.Example
import LiquidTensorExperiment.BreenDeligne.Eval2
import LiquidTensorExperiment.SystemOfComplexes.ShiftSubId
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitProducts
import LiquidTensorExperiment.Condensed.QprimeIsoms
import LiquidTensorExperiment.Condensed.ShortExact
import LiquidTensorExperiment.Condensed.BdSes
import LiquidTensorExperiment.Condensed.FilteredColimits

#align_import pseudo_normed_group.QprimeFP

noncomputable section

open scoped NNReal

universe u

open CategoryTheory CategoryTheory.Limits BreenDeligne

def ProFiltPseuNormGrpWithTinv₁.toCHFPNG {r'} (M : ProFiltPseuNormGrpWithTinv₁.{u} r') :
    CompHausFiltPseuNormGrp :=
  (pFPNGT₁ToCHFPNG₁ₑₗ r' ⋙ cHFPNG₁ToCHFPNGₑₗ).obj M

section Step1

variable (r' : ℝ≥0)

variable (BD : BreenDeligne.Data) (κ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c, BD.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

abbrev freeCond :=
  profiniteToCondensed.{u} ⋙ condensedSetToCondensedAb

def qprimeFPNat : ℝ≥0 ⥤ ChainComplex (Condensed.{u} Ab.{u + 1}) ℕ :=
  fPsystem r' BD ⟨M⟩ κ ⋙ (freeCond.{u}.mapFreeAb ⋙ FreeAb.eval _).mapHomologicalComplex _

def qprimeFPInt : ℝ≥0 ⥤ CochainComplex (Condensed.{u} Ab.{u + 1}) ℤ :=
  qprimeFPNat r' BD κ M ⋙ HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp

def qprimeFP : ℝ≥0 ⥤ BoundedHomotopyCategory (Condensed.{u} Ab.{u + 1}) :=
  qprimeFPNat r' BD κ M ⋙ ChainComplex.toBoundedHomotopyCategory

end Step1

section Step2

variable {r' : ℝ≥0}

variable (BD : BreenDeligne.Package) (κ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c, BD.data.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

def ProFiltPseuNormGrpWithTinv₁.toCondensed : Condensed.{u} Ab.{u + 1} :=
  (pFPNGT₁ToCHFPNG₁ₑₗ r' ⋙ cHFPNG₁ToCHFPNGₑₗ.{u} ⋙ CompHausFiltPseuNormGrp.toCondensed.{u}).obj M

-- move me
/-- `Tinv : M → M` as hom of condensed abelian groups -/
def ProFiltPseuNormGrpWithTinv₁.tinvCond : M.toCondensed ⟶ M.toCondensed :=
  CompHausFiltPseuNormGrp.toCondensed.{u}.map ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv

attribute [local instance] typePow

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

def qprimeFPInclAux'' (c : ℝ≥0) (n : ℕ) (M : ProFiltPseuNormGrpWithTinv.{u} r') (i : Fin n) :
    (filtrationPow r' c n).obj M ⟶ ((filtration r').obj c).obj M :=
  ((filtration r').obj c).map <| ProfinitelyFilteredPseudoNormedGroupWithTinv.piProj _ _ i

def qprimeFPInclAux' (c : ℝ≥0) (n : ℕ) (i : Fin n) (S : Profinite.{u}ᵒᵖ) :
    uliftFunctor.{u + 1, u}.obj
        (Opposite.unop.{u + 2} S ⟶ PseudoNormedGroup.filtrationObj.{u} (M ^ n) c) ⟶
      uliftFunctor.{u + 1, u}.obj
        ((CompHausFiltPseuNormGrp.of.{u} ↥((pFPNGT₁ToPFPNG₁ₑₗ.{u} r').obj M)).presheaf
          (Opposite.unop.{u + 2} S)) :=
  uliftFunctor.map fun f =>
    ⟨Subtype.val ∘ qprimeFPInclAux'' c n ⟨M⟩ i ∘ f, by
      refine' ⟨_, _, Continuous.comp _ _, rfl⟩ <;> apply ContinuousMap.continuous⟩

-- move me
instance : PreservesLimits condensedAbToCondensedSet.{u} :=
  Adjunction.rightAdjointPreservesLimits condensedAbCondensedSetAdjunction

-- move me
instance : PreservesLimits condensedSetToPresheaf :=
  Adjunction.rightAdjointPreservesLimits condensedSetPresheafAdjunction

universe v

theorem Ab.ulift_map_apply {A B : Ab.{u}} (f : A ⟶ B) :
    ⇑(Ab.ulift.{v}.map f) = uliftFunctor.map f := by ext; rfl

-- def QprimeFP_incl_aux_foo (c : ℝ≥0) (n : ℕ) :
--   (pseudo_normed_group.filtration_obj (M ^ n) c).to_Condensed ⟶
--   (Condensed_Ab_to_CondensedSet.obj (⨁ λ (i : ulift (fin n)), M.to_Condensed)) :=
-- begin
--   let x := biproduct.is_bilimit (λ (i : ulift (fin n)), M.to_Condensed),
--   let y := is_bilimit_of_preserves Condensed_Ab_to_presheaf x,
--   refine ⟨y.is_limit.lift ⟨_, ⟨λ i, ⟨_, _⟩, _⟩⟩⟩,
--   { refine QprimeFP_incl_aux' _ _ _ i.down, },
--   { intros S T f,
--     dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
--     rw [← ulift_functor.map_comp, Ab.ulift_map_apply, ← ulift_functor.map_comp],
--     congr' 1, },
--   { clear y x,
--     rintros ⟨i⟩ ⟨j⟩ ⟨⟨⟨⟩⟩⟩,
--     ext S : 2,
--     dsimp [QprimeFP_incl_aux', ProFiltPseuNormGrpWithTinv₁.to_Condensed],
--     simp only [discrete.functor_map_id, category.id_comp],
--     symmetry, apply category.comp_id, }
-- end
def qprimeFPInclAux (c : ℝ≥0) (n : ℕ) :
    (PseudoNormedGroup.filtrationObj (M ^ n) c).toCondensed ⟶
      condensedAbToCondensedSet.obj (⨁ fun i : Fin n => M.toCondensed) :=
  by
  let x := biproduct.isLimit fun i : Fin n => M.to_Condensed
  let y := CategoryTheory.Limits.isLimitOfPreserves (condensedAbToCondensedSet ⋙ condensedSetToPresheaf) x
  refine' ⟨y.lift ⟨_, ⟨fun i => ⟨_, _⟩, _⟩⟩⟩
  · refine' qprimeFPInclAux' _ _ _ i.as
  · intro S T f
    rcases i with ⟨⟨i⟩⟩
    dsimp [qprimeFPInclAux', ProFiltPseuNormGrpWithTinv₁.toCondensed]
    rw [← ulift_functor.map_comp, Ab.ulift_map_apply, ← ulift_functor.map_comp]
    congr 1
  · clear y x
    rintro ⟨i⟩ ⟨j⟩ ⟨⟨⟨⟩⟩⟩
    ext S : 2
    dsimp [qprimeFPInclAux', ProFiltPseuNormGrpWithTinv₁.toCondensed]
    simp only [Discrete.functor_map_id, Category.id_comp]
    symm; apply Category.comp_id

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes false

theorem lift_app {C 𝓐 ι : Type _} [Category C] [Category 𝓐] [Preadditive 𝓐] {F G : C ⥤ 𝓐}
    (f : ι → (F ⟶ G)) (x) (T) :
    (FreeAbelianGroup.lift f x).app T = FreeAbelianGroup.lift (fun i => (f i).app T) x :=
  by
  simp only [← NatTrans.appHom_apply, ← AddMonoidHom.comp_apply]
  congr 1; clear x; ext x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, FreeAbelianGroup.lift.of]

theorem mapFreeAb_comp_map {X Y Z : Type _} [Category X] [Category Y] [Category Z] (F : X ⥤ Y)
    (G : Y ⥤ Z) {α β : FreeAb X} (f : α ⟶ β) :
    (F ⋙ G).mapFreeAb.map f = G.mapFreeAb.map (F.mapFreeAb.map f) :=
  by
  dsimp only [Functor.mapFreeAb, Functor.comp_map]
  rw [← AddMonoidHom.comp_apply]; congr 1; clear f
  ext f
  simp only [FreeAbelianGroup.map_of_apply, Functor.comp_map, AddMonoidHom.coe_comp,
    Function.comp_apply]

open CategoryTheory.Preadditive

open scoped BigOperators

theorem Biproduct.desc_eq_sum {𝓐 ι : Type _} [Category 𝓐] [Abelian 𝓐] [Fintype ι] (M : ι → 𝓐)
    (X : 𝓐) (f : ∀ i, M i ⟶ X) : biproduct.desc f = ∑ i : ι, biproduct.π _ _ ≫ f i := by
  classical
  ext i
  simp only [biproduct.ι_desc, comp_sum]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · rw [biproduct.ι_π_assoc, dif_pos rfl, CategoryTheory.eqToHom_refl, Category.id_comp]
  · rintro j - hj; rw [biproduct.ι_π_ne_assoc, zero_comp]; exact hj.symm

instance groupOfSections (A : Condensed.{u} Ab.{u + 1}) (S : Profinite.{u}ᵒᵖ) :
    AddCommGroup (((condensedAbToCondensedSet ⋙ condensedSetToPresheaf).obj A).obj S) :=
  AddCommGroupCat.addCommGroupInstance
    ((@Sheaf.val Profinite Profinite.category proetaleTopology Ab AddCommGroupCat.largeCategory
          A).obj
      S)

instance groupOfHoms (X A : Type u) [AddCommGroup A] : AddCommGroup (X ⟶ A) :=
  @Pi.addCommGroup X _ _

instance uliftFunctorGroup (A : Type u) [AddCommGroup A] : AddCommGroup (uliftFunctor.obj A) :=
  ULift.addCommGroup

theorem QprimeFP_incl_aux3 {X A : Type u} [AddCommGroup A] {ι : Type _} (s : Finset ι) (n : ι → ℤ)
    (f : ι → (X ⟶ A)) :
    ∑ i in s, n i • uliftFunctor.{v}.map (f i) = uliftFunctor.map (∑ i in s, n i • f i) :=
  by
  let φ := AddMonoidHom.mk' (fun g : X ⟶ A => uliftFunctor.{v}.map g) _
  · show ∑ i in s, n i • φ (f i) = _; simp only [← φ.map_sum, ← φ.map_zsmul]; rfl
  intro g₁ g₂; rfl

instance groupOfSheafHoms (X) (A : Condensed.{u} Ab.{u + 1}) :
    AddCommGroup (X ⟶ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).obj A)
    where
  add f g :=
    ⟨fun S => f.app S + g.app S, by
      intro S T φ; show X.map φ ≫ f.app T + X.map φ ≫ g.app T = _
      simp only [NatTrans.naturality]; ext1 x; symm
      exact (A.val.map φ).map_add (f.app S x) (g.app S x)⟩
  add_assoc := by intros; ext : 2; apply add_assoc
  zero := ⟨fun S => 0, by intro S T φ; ext1 x; symm; exact (A.val.map φ).map_zero⟩
  zero_add := by intros; ext : 2; apply zero_add
  add_zero := by intros; ext : 2; apply add_zero
  nsmul n f :=
    ⟨fun S => n • f.app S, by
      intro S T φ; show n • X.map φ ≫ f.app T = _
      simp only [NatTrans.naturality]; ext1 x; symm
      exact (A.val.map φ).map_nsmul (f.app S x) n⟩
  nsmul_zero := by intros; ext : 2; apply AddCommGroup.nsmul_zero'
  nsmul_succ := by intros; ext : 2; apply AddCommGroup.nsmul_succ'
  neg f :=
    ⟨fun S => -f.app S, by
      intro S T φ; show -X.map φ ≫ f.app T = _
      simp only [NatTrans.naturality]; ext1 x; symm
      exact (A.val.map φ).map_neg (f.app S x)⟩
  sub f g :=
    ⟨fun S => f.app S - g.app S, by
      intro S T φ; show X.map φ ≫ f.app T - X.map φ ≫ g.app T = _
      simp only [NatTrans.naturality]; ext1 x; symm
      exact (A.val.map φ).map_sub (f.app S x) (g.app S x)⟩
  sub_eq_add_neg := by intros; ext : 2; apply sub_eq_add_neg
  zsmul n f :=
    ⟨fun S => n • f.app S, by
      intro S T φ; show n • X.map φ ≫ f.app T = _
      simp only [NatTrans.naturality]; ext1 x; symm
      exact (A.val.map φ).map_zsmul (f.app S x) n⟩
  zsmul_zero' := by intros; ext : 2; apply AddCommGroup.zsmul_zero'
  zsmul_succ' := by intros; ext : 2; apply AddCommGroup.zsmul_succ'
  zsmul_neg' := by intros; ext : 2; apply AddCommGroup.zsmul_neg'
  add_left_neg := by intros; ext : 2; apply add_left_neg
  add_comm := by intros; ext : 2; apply add_comm

theorem QprimeFP_incl_aux1 {A B : Condensed.{u} Ab.{u + 1}} {ι : Type _} {X}
    (f : X ⟶ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).obj A) (s : Finset ι) (n : ι → ℤ)
    (g : ι → (A ⟶ B)) :
    f ≫ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).map (∑ i in s, n i • g i) =
      ∑ i in s, n i • f ≫ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).map (g i) :=
  by
  let φ :=
    AddMonoidHom.mk'
      (fun g : A ⟶ B => f ≫ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).map g) _
  · show φ _ = _; simp only [φ.map_sum, φ.map_zsmul]; rfl
  intro g₁ g₂; rfl

theorem QprimeFP_incl_aux2 {A : Condensed.{u} Ab.{u + 1}} {ι : Type _} {X} (s : Finset ι)
    (n : ι → ℤ) (f : ι → (X ⟶ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).obj A)) (S) :
    (∑ i in s, n i • f i).app S = ∑ i in s, n i • (f i).app S :=
  by
  let φ :=
    AddMonoidHom.mk'
      (fun g : X ⟶ (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).obj A => NatTrans.app g S)
      _
  · show φ _ = _; simp only [φ.map_sum, φ.map_zsmul]; rfl
  intro g₁ g₂; rfl

-- move me
-- lemma _root_.comphaus_filtered_pseudo_normed_group_hom.coe_to_add_monoid_hom
--   {M N : Type*} [comphaus_filtered_pseudo_normed_group M] [comphaus_filtered_pseudo_normed_group N]
--   (f : comphaus_filtered_pseudo_normed_group_hom M N) :
--   ⇑f.to_add_monoid_hom = f := rfl
@[simps]
def CompHausFiltPseuNormGrp.presheafIncl (A : CompHausFiltPseuNormGrp.{u}) (S : Profinite.{u}) :
    CompHausFiltPseuNormGrp.Presheaf A S →+ S → A :=
  AddMonoidHom.mk' Subtype.val fun _ _ => rfl

def qprimeFPIncl (c : ℝ≥0) :
    (qprimeFPInt r' BD.data κ M).obj c ⟶ (BD.eval' freeCond').obj M.toCondensed :=
  (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).map
    { f := fun n => condensedSetToCondensedAb.map <| qprimeFPInclAux _ _ _
      comm' := by
        rintro _ n (rfl : _ = _)
        rw [Package.evalFunctor_obj_d]
        dsimp only [UniversalMap.evalPow]
        dsimp only [qprimeFPNat, FPsystem, Functor.comp_obj, Functor.mapHomologicalComplex_obj_d]
        rw [ChainComplex.of_d]
        delta freeCond freeCond'
        rw [Functor.comp_map, mapFreeAb_comp_map, lift_app]
        dsimp only [FreeAb.eval, Functor.mapFreeAb, FPsystem.d, UniversalMap.evalFP2]
        simp only [CategoryTheory.whiskerRight_app, FreeAbelianGroup.lift_map, Function.comp.left_id,
          NatTrans.app_sum, map_sum, BasicUniversalMap.evalPow_app, NatTrans.app_zsmul,
          BasicUniversalMap.evalFP2, map_zsmul]
        dsimp only [FreeAb.ofFunctor]
        simp only [FreeAbelianGroup.lift.of, Function.comp_apply]
        rw [FreeAbelianGroup.lift_eq_sum, comp_sum, sum_comp, ← Finset.sum_coe_sort]
        apply Finset.sum_congr rfl
        rintro t -
        rw [comp_zsmul, zsmul_comp]; refine' congr_arg₂ _ rfl _
        rw [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
        congr 1
        ext1
        let x n := biproduct.isLimit fun i : Fin (BD.data.X n) => M.to_Condensed
        let y n := CategoryTheory.Limits.isLimitOfPreserves (condensedAbToCondensedSet ⋙ condensedSetToPresheaf) (x n)
        apply (y _).hom_ext; rintro ⟨j⟩
        rw [← condensedSetToPresheaf_map, ← condensedSetToPresheaf_map, Functor.map_comp, ←
          Functor.comp_map, Category.assoc, Functor.map_comp, Category.assoc]
        erw [← Functor.map_comp, biproduct.matrix_π]
        dsimp only [qprimeFPInclAux, condensedSetToPresheaf_map]
        rw [(y _).fac]
        simp only [Biproduct.desc_eq_sum, comp_zsmul, Category.comp_id]
        rw [QprimeFP_incl_aux1]
        have help :
          ∀ n i,
            ((condensedAbToCondensedSet ⋙ condensedSetToPresheaf).mapCone
                      (biproduct.bicone fun i : Fin (BD.data.X n) => M.to_Condensed).toCone).π.app
                ⟨i⟩ =
              (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).map
                (biproduct.π (fun i : Fin (BD.data.X n) => M.to_Condensed) i) :=
          by intros; rfl
        simp only [← help, (y _).fac]; clear help
        dsimp only [BasicUniversalMap.evalFP, profiniteToCondensed_map_val,
          BasicUniversalMap.evalPng₀]
        ext S : 2
        erw [QprimeFP_incl_aux2]
        dsimp only [NatTrans.comp_app, CategoryTheory.whiskerRight_app, qprimeFPInclAux']
        rw [← ulift_functor.map_comp, types_comp, QprimeFP_incl_aux3]
        congr 1
        dsimp only [Function.comp, yoneda_map_app, yoneda_obj_obj, ChainComplex.of_x,
          Profinite.coe_comp_apply, ContinuousMap.coe_mk, qprimeFPInclAux'']
        ext f s; clear y x
        dsimp only [Subtype.coe_mk, filtration_obj_map_apply, AddMonoidHom.mk'_apply,
          ComphausFilteredPseudoNormedGroupWithTinvHom.level, PseudoNormedGroup.level,
          ProfinitelyFilteredPseudoNormedGroupWithTinv.piProj,
          ComphausFilteredPseudoNormedGroupWithTinvHom.coe_mk, Pi.evalAddMonoidHom_apply,
          BreenDeligne.BasicUniversalMap.evalPng₀, BreenDeligne.BasicUniversalMap.evalPng,
          ComphausFilteredPseudoNormedGroup.piLift, ComphausFilteredPseudoNormedGroupHom.coe_mk,
          AddMonoidHom.mkToPi_apply]
        simp only [← ComphausFilteredPseudoNormedGroupHom.toAddMonoidHomHom_apply,
          AddMonoidHom.map_sum]
        rw [Fintype.sum_apply, ← AddMonoidHom.eval_apply_apply, AddMonoidHom.map_sum, ←
          CompHausFiltPseuNormGrp.presheafIncl_apply, AddMonoidHom.map_sum, Fintype.sum_apply]
        --rw [← equiv.ulift.{u+1 0}.sum_comp],
        refine' Finset.sum_congr rfl _
        intro t ht; rfl }

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

def qprimeFPSigmaProj :
    (∐ fun k => (qprimeFPInt r' BD.data κ M).obj (ι k)) ⟶ (BD.eval' freeCond').obj M.toCondensed :=
  Sigma.desc fun n => qprimeFPIncl BD κ M _

instance qprimeFP.uniformlyBounded :
    BoundedHomotopyCategory.UniformlyBounded fun k => (qprimeFP r' BD.data κ M).obj (ι k) := by
  use 1; intro k; apply ChainComplex.boundedByOne

end Step2

section Step3

open BoundedHomotopyCategory

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

variable {C : Type _} [Category C] [Preadditive C]

variable (A B : ℝ≥0 ⥤ C)

variable [HasCoproduct fun k : ULift ℕ => A.obj (ι k)]

variable [HasCoproduct fun k : ULift ℕ => B.obj (ι k)]

def sigmaShiftCone (c : cofan fun k => A.obj (ι k)) : cofan fun k => A.obj (ι k)
    where
  pt := c.pt
  ι :=
    Discrete.natTrans fun ⟨(j : ULift ℕ)⟩ =>
      A.map (homOfLE <| hι <| (by cases j; apply Nat.le_succ : j ≤ ⟨j.down + 1⟩)) ≫
        c.ι.app ⟨⟨j.down + 1⟩⟩

def sigmaShift' (c : cofan fun k => A.obj (ι k)) (hc : IsColimit c) :
    c.pt ⟶ (sigmaShiftCone ι hι A c).pt :=
  hc.desc _

def sigmaShift : (∐ fun k => A.obj (ι k)) ⟶ ∐ fun k => A.obj (ι k) :=
  sigmaShift' _ hι _ _ (colimit.isColimit _)

def qprimeFP.shiftSubId : (∐ fun k => A.obj (ι k)) ⟶ ∐ fun k => A.obj (ι k) :=
  sigmaShift _ hι _ - 𝟙 _

variable {A B}

def sigmaMap (f : A ⟶ B) : (∐ fun k => A.obj (ι k)) ⟶ ∐ fun k => B.obj (ι k) :=
  Sigma.desc fun k => f.app _ ≫ Sigma.ι _ k

end Step3

section Step4

variable {r' : ℝ≥0}

variable (BD : BreenDeligne.Package) (κ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c, BD.data.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

open Opposite CategoryTheory.Preadditive

open scoped Classical

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

def coproductEvalIso {α : Type (u + 1)}
    (X : α → HomologicalComplex (Condensed.{u} Ab.{u + 1}) (ComplexShape.up ℤ)) (n : ℤ)
    (T : ExtrDisc.{u}) :
    ((∐ X).pt n).val.obj (op T.val) ≅
      AddCommGroupCat.of (DirectSum α fun a => ((X a).pt n).val.obj (op T.val)) :=
  by
  refine'
    CategoryTheory.preservesColimitIso
        (HomologicalComplex.eval (Condensed.{u} Ab.{u + 1}) (ComplexShape.up ℤ) n ⋙
          Condensed.evaluation Ab.{u + 1} T.val)
        _ ≪≫
      _
  refine'
    _ ≪≫
      (colimit.isColimit <|
            Discrete.functor fun a => ((X a).pt n).val.obj (op T.val)).coconePointUniqueUpToIso
        (AddCommGroupCat.isColimitDirectSumCofan.{u + 1, u + 1} fun a =>
          ((X a).pt n).val.obj (op T.val))
  refine' HasColimit.isoOfNatIso (Discrete.natIso _)
  intro i; exact iso.refl _

theorem sigma_ι_coproductEvalIso {α : Type (u + 1)}
    (X : α → HomologicalComplex (Condensed.{u} Ab.{u + 1}) (ComplexShape.up ℤ)) (n : ℤ)
    (T : ExtrDisc.{u}) (a : α) :
    ((Sigma.ι X a : X a ⟶ _).f n).val.app (op T.val) ≫ (coproductEvalIso _ _ _).hom =
      DirectSum.of (fun a => ((X a).pt n).val.obj (op T.val)) a :=
  by
  dsimp only [coproductEvalIso]
  erw [(CategoryTheory.Limits.isColimitOfPreserves
        (HomologicalComplex.eval.{u + 1, u + 2, 0} (Condensed.{u, u + 1, u + 2} Ab.{u + 1})
            (ComplexShape.up.{0} ℤ) n ⋙
          Condensed.evaluation.{u + 2, u + 1, u} Ab.{u + 1} T.val)
        _).fac_assoc]
  dsimp
  erw [colimit.ι_desc_assoc]
  dsimp; simpa only [Category.id_comp, colimit.comp_coconePointUniqueUpToIso_hom]

-- Move this!
instance condensedSetToCondensedAbPreservesColimits :
    PreservesColimits condensedSetToCondensedAb.{u} :=
  Adjunction.leftAdjointPreservesColimits condensedAbCondensedSetAdjunction

section SesSetup

attribute [local instance] typePow

def condensedProdValIso {α : Type (u + 1)} (X : α → CondensedSet.{u}) :
    (∏ X).val ≅ ∏ fun i => (X i).val :=
  preservesLimitIso condensedSetToPresheaf _ ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso fun p => Iso.refl _)

@[simp, reassoc]
theorem condensedProdValIso_spec {α : Type (u + 1)} (X : α → CondensedSet.{u}) (i : α) :
    (condensedProdValIso X).hom ≫ Pi.π _ i = (Pi.π X i : ∏ X ⟶ X i).val :=
  by
  dsimp [condensedProdValIso]
  simp only [Category.assoc]
  erw [limit.lift_π]
  dsimp
  erw [limit.lift_π_assoc]
  erw [Category.comp_id]
  rfl

@[simp, reassoc]
theorem condensedProdValIso_spec' {α : Type (u + 1)} (X : α → CondensedSet.{u}) (i : α) :
    (condensedProdValIso X).inv ≫ (Pi.π X i : ∏ X ⟶ X i).val = Pi.π _ _ := by rw [Iso.inv_comp_eq];
  rw [condensedProdValIso_spec]

def functorProdEvalIso {α : Type (u + 1)} (X : α → Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) (T) :
    (∏ X).obj T ≅ ∏ fun i => (X i).obj T :=
  preservesLimitIso ((evaluation _ _).obj T) _ ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso fun p => Iso.refl _)

@[simp, reassoc]
theorem functorProdEvalIso_spec {α : Type (u + 1)} (X : α → Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) (T)
    (i : α) : (functorProdEvalIso X T).hom ≫ Pi.π _ i = (Pi.π X i : ∏ X ⟶ X i).app _ :=
  by
  dsimp [functorProdEvalIso]
  simp only [Category.assoc]
  erw [limit.lift_π]
  dsimp
  erw [limit.lift_π_assoc]
  erw [Category.comp_id]
  rfl

@[simp, reassoc]
theorem functorProdEvalIso_spec' {α : Type (u + 1)} (X : α → Profinite.{u}ᵒᵖ ⥤ Type (u + 1)) (T)
    (i : α) : (functorProdEvalIso X T).inv ≫ (Pi.π X i : ∏ X ⟶ X i).app _ = Pi.π _ i := by
  rw [Iso.inv_comp_eq]; rw [functorProdEvalIso_spec]

def filtrationPowIsoAux (j : ℕ) (r : ℝ≥0) :
    (ProFiltPseuNormGrp₁.level.obj r).obj
        (∏ fun i : ULift.{u} (Fin j) => (pFPNGT₁ToPFPNG₁ₑₗ _).obj M) ≅
      ∏ fun i : ULift.{u} (Fin j) => PseudoNormedGroup.filtrationObj M r :=
  preservesLimitIso (ProFiltPseuNormGrp₁.level.obj r) _ ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso fun q => Iso.refl _)

@[simp, reassoc]
theorem filtrationPowIsoAux_spec (j : ℕ) (r : ℝ≥0) (i) :
    (filtrationPowIsoAux M j r).hom ≫
        Pi.π (fun i : ULift.{u} (Fin j) => PseudoNormedGroup.filtrationObj M r) i =
      (ProFiltPseuNormGrp₁.level.obj r).map (Pi.π _ i) :=
  by
  dsimp [filtrationPowIsoAux]
  simp only [Category.assoc]
  erw [limit.lift_π]
  dsimp
  erw [limit.lift_π_assoc]
  erw [Category.comp_id]
  rfl

@[simp, reassoc]
theorem filtrationPowIsoAux_spec' (j : ℕ) (r : ℝ≥0) (i) :
    (filtrationPowIsoAux M j r).inv ≫ (ProFiltPseuNormGrp₁.level.obj r).map (Pi.π _ i) = Pi.π _ i :=
  by rw [Iso.inv_comp_eq]; rw [filtrationPowIsoAux_spec]

def ProFiltPseuNormGrp₁.productFan {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) :
    Fan X :=
  Fan.mk (ProFiltPseuNormGrp₁.product X) fun i => ProFiltPseuNormGrp₁.product.π _ _

def ProFiltPseuNormGrp₁.isLimitProductFan {α : Type u} [Fintype α]
    (X : α → ProFiltPseuNormGrp₁.{u}) : IsLimit (ProFiltPseuNormGrp₁.productFan X)
    where
  lift S := ProFiltPseuNormGrp₁.product.lift _ _ fun i => S.π.app ⟨i⟩
  fac := by
    rintro S ⟨j⟩
    dsimp
    erw [ProFiltPseuNormGrp₁.product.lift_π]
  uniq := by
    intro S m hm
    apply ProFiltPseuNormGrp₁.product.hom_ext
    rintro j
    erw [hm ⟨j⟩]
    erw [ProFiltPseuNormGrp₁.product.lift_π]

def ProFiltPseuNormGrp₁.productPowIso {α : Type u} [Fintype α] (X : α → ProFiltPseuNormGrp₁.{u}) :
    ∏ X ≅ ProFiltPseuNormGrp₁.product X :=
  (limit.isLimit _).conePointUniqueUpToIso (ProFiltPseuNormGrp₁.isLimitProductFan _)

@[simp, reassoc]
theorem ProFiltPseuNormGrp₁.productPowIso_spec {α : Type u} [Fintype α]
    (X : α → ProFiltPseuNormGrp₁.{u}) (i) :
    (ProFiltPseuNormGrp₁.productPowIso X).hom ≫ ProFiltPseuNormGrp₁.product.π _ _ = Pi.π _ i :=
  by
  erw [ProFiltPseuNormGrp₁.product.lift_π]
  rfl

@[simp, reassoc]
theorem ProFiltPseuNormGrp₁.productPowIso_spec' {α : Type u} [Fintype α]
    (X : α → ProFiltPseuNormGrp₁.{u}) (i) :
    (ProFiltPseuNormGrp₁.productPowIso X).inv ≫ Pi.π _ i = ProFiltPseuNormGrp₁.product.π _ _ := by
  rw [Iso.inv_comp_eq]; rw [ProFiltPseuNormGrp₁.productPowIso_spec]

def filtrationPowProj (j : ℕ) (r : ℝ≥0) (i : Fin j) :
    PseudoNormedGroup.filtrationObj.{u} (↥M ^ j) r ⟶ PseudoNormedGroup.filtrationObj.{u} M r
    where
  toFun t := ⟨t.1 i, t.2 _⟩
  continuous_toFun :=
    by
    let e := ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun i : Fin j => M) r
    let t := _; change Continuous t
    suffices Continuous (t ∘ e.symm) by simpa using this
    convert continuous_apply i
    ext; rfl

def filtrationPowIsoAux'₀ (j : ℕ) (r : ℝ≥0) :
    PseudoNormedGroup.filtrationObj.{u} (↥M ^ j) r ≅
      (ProFiltPseuNormGrp₁.level.{u}.obj r).obj
        (ProFiltPseuNormGrp₁.product.{u} fun i : ULift.{u, 0} (Fin j) =>
          (pFPNGT₁ToPFPNG₁ₑₗ.{u} r').obj M)
    where
  -- This can't be the best way to do this, but at this point I'm quite annoyed.
  hom :=
    { toFun := fun q =>
        ⟨fun i => q.1 i.down, by
          intro i
          apply q.2⟩
      continuous_toFun :=
        by
        rw [(ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun i : ULift.{u} (Fin j) => M)
                r).Inducing.continuous_iff]
        apply continuous_pi
        intro i; dsimp
        let e := ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun i : Fin j => M) r
        let t := _; change Continuous t
        suffices Continuous (t ∘ e.symm) by simpa using this
        convert continuous_apply i.down
        ext; rfl }
  inv :=
    { toFun := fun q =>
        ⟨fun i => q.1 ⟨i⟩, by
          intro i
          apply q.2⟩
      continuous_toFun :=
        by
        let e₁ := ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun i : Fin j => M) r
        let e₂ :=
          ComphausFilteredPseudoNormedGroup.filtrationPiHomeo (fun i : ULift.{u} (Fin j) => M) r
        let t := _; change Continuous t
        suffices Continuous (e₁ ∘ t ∘ e₂.symm) by simpa using this
        apply continuous_pi
        intro i; convert continuous_apply (ULift.up i)
        ext; rfl }
  hom_inv_id := by ext; rfl
  inv_hom_id := by ext _ ⟨⟩; rfl

@[simp, reassoc]
theorem filtrationPowIsoAux'₀_spec (j : ℕ) (r : ℝ≥0) (i) :
    (filtrationPowIsoAux'₀ M j r).hom ≫
        ((ProFiltPseuNormGrp₁.level.obj r).map <| ProFiltPseuNormGrp₁.product.π _ i) =
      filtrationPowProj M j r i.down :=
  by ext; rfl

@[simp, reassoc]
theorem filtrationPowIsoAux'₀_spec' (j : ℕ) (r : ℝ≥0) (i : ULift.{u} (Fin j)) :
    (filtrationPowIsoAux'₀ M j r).inv ≫ filtrationPowProj M j r i.down =
      ((ProFiltPseuNormGrp₁.level.obj r).map <| ProFiltPseuNormGrp₁.product.π _ i) :=
  by cases i; ext _ ⟨k⟩; rfl

def filtrationPowIsoAux' (j : ℕ) (r : ℝ≥0) :
    PseudoNormedGroup.filtrationObj.{u} (↥M ^ j) r ≅
      (ProFiltPseuNormGrp₁.level.obj r).obj
        (∏ fun i : ULift.{u} (Fin j) => (pFPNGT₁ToPFPNG₁ₑₗ _).obj M) :=
  filtrationPowIsoAux'₀ _ _ _ ≪≫
    (ProFiltPseuNormGrp₁.level.obj r).mapIso (ProFiltPseuNormGrp₁.productPowIso _).symm

@[simp, reassoc]
theorem filtrationPowIsoAux'_spec (j : ℕ) (r : ℝ≥0) (i) :
    (filtrationPowIsoAux' M j r).hom ≫ (ProFiltPseuNormGrp₁.level.obj r).map (Pi.π _ i) =
      filtrationPowProj _ _ _ i.down :=
  by
  dsimp [filtrationPowIsoAux']
  simp only [Category.assoc]
  simp only [← Functor.map_comp, ProFiltPseuNormGrp₁.productPowIso_spec']
  simp

@[simp, reassoc]
theorem filtrationPowIsoAux'_spec' (j : ℕ) (r : ℝ≥0) (i : ULift.{u} (Fin j)) :
    (filtrationPowIsoAux' M j r).inv ≫ filtrationPowProj _ _ _ i.down =
      (ProFiltPseuNormGrp₁.level.obj r).map (Pi.π _ i) :=
  by rw [Iso.inv_comp_eq]; rw [filtrationPowIsoAux'_spec]

def filtrationPowIso (j : ℕ) (r : ℝ≥0) :
    PseudoNormedGroup.filtrationObj.{u} (M ^ j) r ≅
      ∏ fun i : ULift.{u} (Fin j) => PseudoNormedGroup.filtrationObj M r :=
  filtrationPowIsoAux' _ _ _ ≪≫ filtrationPowIsoAux _ _ _

@[simp, reassoc]
theorem filtrationPowIso_spec (j : ℕ) (r : ℝ≥0) (i : ULift.{u} (Fin j)) :
    (filtrationPowIso M j r).hom ≫ Pi.π _ i = filtrationPowProj _ _ _ i.down :=
  by
  dsimp [filtrationPowIso]
  simp

@[simp, reassoc]
theorem filtrationPowIso_spec' (j : ℕ) (r : ℝ≥0) (i : ULift.{u} (Fin j)) :
    (filtrationPowIso M j r).inv ≫ filtrationPowProj _ _ _ i.down = Pi.π _ i := by
  rw [Iso.inv_comp_eq]; rw [filtrationPowIso_spec]

def profinitePowFiltrationIsoComponent (j : ℕ) (r : ℝ≥0) (T : Profinite.{u}) :
    ULift.{u + 1} (T ⟶ PseudoNormedGroup.filtrationObj.{u} (↥M ^ j) r) ≅
      ∏ fun i : ULift.{u + 1} (Fin j) =>
        ULift.{u + 1}
          (T ⟶ (ProFiltPseuNormGrp₁.level.{u}.obj r).obj ((pFPNGT₁ToPFPNG₁ₑₗ.{u} r').obj M)) :=
  uliftFunctor.mapIso ((yoneda.flip.obj (op T)).mapIso <| filtrationPowIso _ _ _) ≪≫
    { hom := Pi.lift fun i f => ULift.up <| ULift.down f ≫ Pi.π _ (ULift.up i.down)
      inv := fun t =>
        ULift.up <|
          Pi.lift fun i =>
            let q :=
              Pi.π
                (fun i : ULift.{u + 1, 0} (Fin j) =>
                  ULift.{u + 1, u}
                    (T ⟶
                      (ProFiltPseuNormGrp₁.level.{u}.obj r).obj ((pFPNGT₁ToPFPNG₁ₑₗ.{u} r').obj M)))
                (ULift.up <| ULift.down i) t
            q.down
      hom_inv_id := by
        ext ⟨t⟩ : 2; dsimp
        apply limit.hom_ext; rintro ⟨⟨q⟩⟩
        simp
      inv_hom_id := by
        apply limit.hom_ext; rintro ⟨⟨q⟩⟩
        simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, Category.id_comp]
        ext t
        dsimp
        rw [← comp_apply, limit.lift_π]
        rfl }

@[simp, reassoc]
theorem profinitePowFiltrationIsoComponent_spec (j : ℕ) (r : ℝ≥0) (T : Profinite.{u})
    (i : ULift.{u + 1} (Fin j)) :
    (profinitePowFiltrationIsoComponent M j r T).hom ≫ Pi.π _ i =
      uliftFunctor.map ((yoneda.flip.obj (op T)).map <| filtrationPowProj _ _ _ i.down) :=
  by
  dsimp [profinitePowFiltrationIsoComponent]
  simp
  ext ⟨t⟩ : 2
  dsimp
  simp

@[simp, reassoc]
theorem profinitePowFiltrationIsoComponent_spec' (j : ℕ) (r : ℝ≥0) (T : Profinite.{u})
    (i : ULift.{u + 1} (Fin j)) :
    (profinitePowFiltrationIsoComponent M j r T).inv ≫
        uliftFunctor.map ((yoneda.flip.obj (op T)).map <| filtrationPowProj _ _ _ i.down) =
      Pi.π _ i :=
  by rw [Iso.inv_comp_eq]; rw [profinitePowFiltrationIsoComponent_spec]

def profinitePowFiltrationIso (j : ℕ) (r : ℝ≥0) :
    (PseudoNormedGroup.filtrationObj.{u} (↥M ^ j) r).toCondensed ≅
      ∏ fun k : ULift.{u + 1, 0} (Fin j) =>
        ((ProFiltPseuNormGrp₁.level.obj r).obj ((pFPNGT₁ToPFPNG₁ₑₗ _).obj M)).toCondensed :=
  by
  refine' Sheaf.Iso.mk _ _ _
  refine' _ ≪≫ (condensedProdValIso _).symm
  refine' NatIso.ofComponents _ _
  · intro T
    refine' _ ≪≫ (functorProdEvalIso _ _).symm
    refine' profinitePowFiltrationIsoComponent _ _ _ _
  · intro X Y f; dsimp
    apply (CategoryTheory.Limits.isLimitOfPreserves ((evaluation _ _).obj Y) (limit.isLimit _)).hom_ext
    rintro ⟨i⟩; swap; infer_instance
    dsimp; simp only [Category.assoc]
    erw [functorProdEvalIso_spec', NatTrans.naturality, functorProdEvalIso_spec'_assoc,
      profinitePowFiltrationIsoComponent_spec, profinitePowFiltrationIsoComponent_spec_assoc]
    ext; rfl

@[simp, reassoc]
theorem profinitePowFiltrationIso_spec (j : ℕ) (r : ℝ≥0) (i : ULift.{u + 1} (Fin j)) :
    (profinitePowFiltrationIso M j r).hom ≫ Pi.π _ i =
      profiniteToCondensed.map (filtrationPowProj _ _ _ i.down) :=
  by
  dsimp [profinitePowFiltrationIso, Sheaf.Iso.mk]
  ext1; dsimp
  simp only [Category.assoc]
  rw [condensedProdValIso_spec']
  ext T : 2
  dsimp
  simp only [Category.assoc]
  rw [functorProdEvalIso_spec']
  erw [profinitePowFiltrationIsoComponent_spec]
  rfl

@[simp, reassoc]
theorem profinitePowFiltrationIso_spec' (j : ℕ) (r : ℝ≥0) (i : ULift.{u + 1} (Fin j)) :
    (profinitePowFiltrationIso M j r).inv ≫
        profiniteToCondensed.map (filtrationPowProj _ _ _ i.down) =
      Pi.π _ i :=
  by rw [Iso.inv_comp_eq]; rw [profinitePowFiltrationIso_spec]

def combine (hι : Monotone ι) (n : ℕ) : ℕ →o ℝ≥0
    where
  toFun t := κ (ι <| ULift.up t) n
  monotone' := by
    intro a b h
    apply Fact.out (Monotone (Function.swap κ n))
    apply hι
    exact h

def isoOnTheLeftZero₀ :
    (∐ fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt 0 ≅
      ∐ fun k : ULift.{u + 1, 0} ℕ => ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt 0 :=
  by
  refine' CategoryTheory.preservesColimitIso (HomologicalComplex.eval _ _ 0) _ ≪≫ _
  refine' HasColimit.isoOfNatIso (Discrete.natIso fun i => iso.refl _)

@[simp, reassoc]
theorem isoOnTheLeftZero₀_spec' (i : ULift.{u + 1} ℕ) :
    Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt 0) i ≫
        (isoOnTheLeftZero₀ BD κ M ι).inv =
      (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) i).f 0 :=
  by
  dsimp [isoOnTheLeftZero₀]
  erw [colimit.ι_desc_assoc]; dsimp; simp only [Category.id_comp]
  erw [colimit.ι_desc]; rfl

@[simp, reassoc]
theorem isoOnTheLeftZero₀_spec (i : ULift.{u + 1} ℕ) :
    (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) i).f 0 ≫
        (isoOnTheLeftZero₀ BD κ M ι).hom =
      Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt 0) i :=
  by rw [← Iso.eq_comp_inv]; rw [isoOnTheLeftZero₀_spec']

def isoOnTheLeftZero :
    (∐ fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt 0 ≅
      ∐ fun i : AsSmall.{u + 1, 0, 0} ℕ =>
        condensedSetToCondensedAb.{u}.obj
          (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt 0)) =>
            (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι 0)).obj i) :=
  by
  refine' isoOnTheLeftZero₀ BD κ M _ ≪≫ _
  refine' Sigma.mapIso _
  rintro ⟨j⟩
  dsimp [qprimeFPInt, qprimeFPNat, FreeAb.eval, Functor.mapFreeAb, FPsystem, FPsystem.X]
  refine' CondensedSet_to_Condensed_Ab.map_iso _
  refine' profinitePowFiltrationIso M (BD.data.X 0) (κ (ι ⟨j⟩) 0)

--≪≫ _,
@[simp, reassoc]
theorem isoOnTheLeftZero_spec' (k : ℕ) :
    Sigma.ι
          (fun i : AsSmall.{u + 1, 0, 0} ℕ =>
            condensedSetToCondensedAb.{u}.obj
              (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt 0)) =>
                (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι 0)).obj i))
          ⟨k⟩ ≫
        (isoOnTheLeftZero _ _ _ _ _).inv =
      condensedSetToCondensedAb.map (profinitePowFiltrationIso M (BD.data.pt 0) (κ (ι ⟨k⟩) 0)).inv ≫
        (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f
          0 :=
  by
  dsimp [isoOnTheLeftZero]
  erw [colimit.ι_desc_assoc]; dsimp
  rw [Category.assoc]
  slice_lhs 2 3 => rw [isoOnTheLeftZero₀_spec']

@[simp, reassoc]
theorem isoOnTheLeftZero_spec (k : ℕ) :
    condensedSetToCondensedAb.map (profinitePowFiltrationIso M (BD.data.pt 0) (κ (ι ⟨k⟩) 0)).inv ≫
        (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f
            0 ≫
          (isoOnTheLeftZero _ _ _ _ _).hom =
      Sigma.ι
        (fun i : AsSmall.{u + 1, 0, 0} ℕ =>
          condensedSetToCondensedAb.{u}.obj
            (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt 0)) =>
              (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι 0)).obj i))
        ⟨k⟩ :=
  by rw [← Category.assoc, ← Iso.eq_comp_inv, isoOnTheLeftZero_spec']

@[simp, reassoc]
theorem isoOnTheLeftZero_spec_alt (k : ℕ) :
    (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f 0 ≫
        (isoOnTheLeftZero _ _ _ _ _).hom =
      condensedSetToCondensedAb.map (profinitePowFiltrationIso M (BD.data.pt 0) (κ (ι ⟨k⟩) 0)).hom ≫
        Sigma.ι
          (fun i : AsSmall.{u + 1, 0, 0} ℕ =>
            condensedSetToCondensedAb.{u}.obj
              (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt 0)) =>
                (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι 0)).obj i))
          ⟨k⟩ :=
  by rw [← Functor.mapIso_hom, ← Iso.inv_comp_eq, Functor.mapIso_inv, isoOnTheLeftZero_spec]

def PseudoNormedGroup.mapFiltration (M : Type _) [ProfinitelyFilteredPseudoNormedGroup M]
    (a b : ℝ≥0) (h : a ≤ b) :
    PseudoNormedGroup.filtrationObj M a ⟶ PseudoNormedGroup.filtrationObj M b
    where
  toFun := PseudoNormedGroup.castLe' h
  continuous_toFun := by
    haveI : Fact (a ≤ b) := ⟨h⟩
    apply ComphausFilteredPseudoNormedGroup.continuous_castLe

theorem pow_filtration_hom_ext {T : Profinite.{u}} (j : ℕ) (r : ℝ≥0)
    (f g : T ⟶ PseudoNormedGroup.filtrationObj (M ^ j) r)
    (h : ∀ k, f ≫ filtrationPowProj M j r k = g ≫ filtrationPowProj M j r k) : f = g :=
  by
  ext t x
  specialize h x
  apply_fun fun e => (e t).1 at h 
  exact h

theorem iso_on_the_left_zero_conj_aux (j : ℕ) :
    ((profinitePowFiltrationIso.{u} M (BD.data.pt 0) (κ (ι { down := j }) 0)).hom ≫
          (Condensed.asNatDiagramPow.{u} M.toCHFPNG (combine.{u} κ ι hι 0) (BD.data.pt 0)).map
            (AsSmall.up.{0, 0, u + 1}.map (homOfLE.{0} (Nat.le_succ _)))) ≫
        (profinitePowFiltrationIso.{u} M (BD.data.pt 0) (κ (ι { down := j + 1 }) 0)).inv =
      profiniteToCondensed.map
        (PseudoNormedGroup.mapFiltration _ _ _
          (Fact.out (Monotone (Function.swap κ 0)) (hι <| by exact_mod_cast j.le_succ))) :=
  by
  rw [Iso.comp_inv_eq]
  apply limit.hom_ext; rintro ⟨k⟩
  dsimp [Condensed.asNatDiagramPow, pow_functor]; simp only [Category.assoc]
  erw [profinitePowFiltrationIso_spec]
  simp only [lim_map_π, Discrete.natTrans_app]
  erw [profinitePowFiltrationIso_spec_assoc]
  dsimp [Condensed.asNatDiagram, CategoryTheory.Limits.restrictDiagram, CompHausFiltPseuNormGrp.levelCondensedDiagram,
    CompHausFiltPseuNormGrp.levelCondensedDiagram']
  rw [← Profinite_to_Condensed.map_comp]
  have h : κ (ι ⟨j⟩) 0 ≤ κ (ι ⟨j + 1⟩) 0 :=
    by
    apply Fact.out (Monotone (Function.swap κ 0))
    apply hι
    exact_mod_cast j.le_succ
  change _ ≫ Profinite_to_Condensed.map (PseudoNormedGroup.mapFiltration M _ _ h) = _
  rw [← Profinite_to_Condensed.map_comp]
  congr 1

theorem isoOnTheLeftZero_conj :
    (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ M)).f 0 =
      (isoOnTheLeftZero _ _ _ _ hι).hom ≫
        (Condensed.coproductToCoproduct
              (Condensed.asNatDiagramPow M.toCHFPNG (combine κ ι hι 0) _ ⋙ _) -
            𝟙 _) ≫
          (isoOnTheLeftZero _ _ _ _ hι).inv :=
  by
  dsimp [qprimeFP.shiftSubId]
  simp only [comp_sub, sub_comp, Category.id_comp, Iso.hom_inv_id, Category.assoc]
  congr 1
  apply (CategoryTheory.Limits.isColimitOfPreserves (HomologicalComplex.eval _ _ _) (colimit.isColimit _)).hom_ext
  swap; infer_instance
  rintro ⟨⟨j⟩⟩; dsimp
  erw [← HomologicalComplex.comp_f, colimit.ι_desc]
  dsimp [sigmaShiftCone]
  rw [isoOnTheLeftZero_spec_alt_assoc]
  erw [colimit.ι_desc_assoc]; dsimp
  simp only [Category.assoc]
  slice_rhs 3 4 => erw [isoOnTheLeftZero_spec']
  simp only [← Category.assoc]
  congr 1
  dsimp [condensedSetToCondensedAb]
  simp only [← Functor.map_comp]
  dsimp [qprimeFPInt, qprimeFPNat, FreeAb.eval, Functor.mapFreeAb, FPsystem, FPsystem.X,
    FreeAb.ofFunctor]
  rw [FreeAbelianGroup.lift.of]; dsimp
  congr 1
  ext S : 2
  dsimp
  simp only [← Functor.map_comp]; congr 1
  simp only [← NatTrans.comp_app, ← Sheaf.Hom.comp_val]
  rw [iso_on_the_left_zero_conj_aux]
  ext; rfl

def isoOnTheLeftNeg₀ (q : ℕ) :
    (∐ fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt -[q+1] ≅
      ∐ fun k : ULift.{u + 1, 0} ℕ => ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt -[q+1] :=
  by
  refine' CategoryTheory.preservesColimitIso (HomologicalComplex.eval _ _ _) _ ≪≫ _
  refine' HasColimit.isoOfNatIso (Discrete.natIso fun i => iso.refl _)

@[simp, reassoc]
theorem isoOnTheLeftNeg₀_spec' (q : ℕ) (i : ULift.{u + 1} ℕ) :
    Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt -[q+1])
          i ≫
        (isoOnTheLeftNeg₀ BD κ M ι q).inv =
      (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) i).f
        -[q+1] :=
  by
  dsimp [isoOnTheLeftNeg₀]
  erw [colimit.ι_desc_assoc]; dsimp; simp only [Category.id_comp]
  erw [colimit.ι_desc]; rfl

@[simp, reassoc]
theorem isoOnTheLeftNeg₀_spec (q : ℕ) (i : ULift.{u + 1} ℕ) :
    (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) i).f
          -[q+1] ≫
        (isoOnTheLeftNeg₀ BD κ M ι q).hom =
      Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt -[q+1])
        i :=
  by rw [← Iso.eq_comp_inv]; rw [isoOnTheLeftNeg₀_spec']

def isoOnTheLeftNeg (q : ℕ) :
    (∐ fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt -[q+1] ≅
      ∐ fun i : AsSmall.{u + 1, 0, 0} ℕ =>
        condensedSetToCondensedAb.{u}.obj
          (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt (q + 1))) =>
            (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι (q + 1))).obj i) :=
  by
  refine' isoOnTheLeftNeg₀ BD κ M _ q ≪≫ _
  refine' Sigma.mapIso _
  rintro ⟨j⟩
  dsimp [qprimeFPInt, qprimeFPNat, FreeAb.eval, Functor.mapFreeAb, FPsystem, FPsystem.X]
  refine' CondensedSet_to_Condensed_Ab.map_iso _
  refine' profinitePowFiltrationIso M (BD.data.X (q + 1)) (κ (ι ⟨j⟩) (q + 1))

@[simp, reassoc]
theorem isoOnTheLeftNeg_spec' (q : ℕ) (k : ℕ) :
    Sigma.ι
          (fun i : AsSmall.{u + 1, 0, 0} ℕ =>
            condensedSetToCondensedAb.{u}.obj
              (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt (q + 1))) =>
                (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι (q + 1))).obj i))
          ⟨k⟩ ≫
        (isoOnTheLeftNeg _ _ _ _ _ q).inv =
      condensedSetToCondensedAb.map
          (profinitePowFiltrationIso M (BD.data.pt (q + 1)) (κ (ι ⟨k⟩) (q + 1))).inv ≫
        (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f
          -[q+1] :=
  by
  dsimp [isoOnTheLeftNeg]
  erw [colimit.ι_desc_assoc]; dsimp
  rw [Category.assoc]
  slice_lhs 2 3 => rw [isoOnTheLeftNeg₀_spec']

@[simp, reassoc]
theorem isoOnTheLeftNeg_spec (q : ℕ) (k : ℕ) :
    condensedSetToCondensedAb.map
          (profinitePowFiltrationIso M (BD.data.pt (q + 1)) (κ (ι ⟨k⟩) (q + 1))).inv ≫
        (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f
            -[q+1] ≫
          (isoOnTheLeftNeg _ _ _ _ _ q).hom =
      Sigma.ι
        (fun i : AsSmall.{u + 1, 0, 0} ℕ =>
          condensedSetToCondensedAb.{u}.obj
            (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt (q + 1))) =>
              (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι (q + 1))).obj i))
        ⟨k⟩ :=
  by rw [← Category.assoc, ← Iso.eq_comp_inv, isoOnTheLeftNeg_spec']

@[simp, reassoc]
theorem isoOnTheLeftNeg_spec_alt (q : ℕ) (k : ℕ) :
    (Sigma.ι (fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)) ⟨k⟩).f
          -[q+1] ≫
        (isoOnTheLeftNeg _ _ _ _ _ q).hom =
      condensedSetToCondensedAb.map
          (profinitePowFiltrationIso M (BD.data.pt (q + 1)) (κ (ι ⟨k⟩) (q + 1))).hom ≫
        Sigma.ι
          (fun i : AsSmall.{u + 1, 0, 0} ℕ =>
            condensedSetToCondensedAb.{u}.obj
              (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt (q + 1))) =>
                (Condensed.asNatDiagram.{u} M.toCHFPNG (combine.{u} κ ι hι (q + 1))).obj i))
          ⟨k⟩ :=
  by rw [← Functor.mapIso_hom, ← Iso.inv_comp_eq, Functor.mapIso_inv, isoOnTheLeftNeg_spec]

theorem iso_on_the_left_neg_conj_aux (q : ℕ) (j : ℕ) :
    ((profinitePowFiltrationIso.{u} M (BD.data.pt (q + 1)) (κ (ι { down := j }) (q + 1))).hom ≫
          (Condensed.asNatDiagramPow.{u} M.toCHFPNG (combine.{u} κ ι hι (q + 1))
                (BD.data.pt (q + 1))).map
            (AsSmall.up.{0, 0, u + 1}.map (homOfLE.{0} (Nat.le_succ _)))) ≫
        (profinitePowFiltrationIso.{u} M (BD.data.pt (q + 1))
            (κ (ι { down := j + 1 }) (q + 1))).inv =
      profiniteToCondensed.map
        (PseudoNormedGroup.mapFiltration _ _ _
          (Fact.out (Monotone (Function.swap κ (q + 1))) (hι <| by exact_mod_cast j.le_succ))) :=
  by
  rw [Iso.comp_inv_eq]
  apply limit.hom_ext; rintro ⟨k⟩
  dsimp [Condensed.asNatDiagramPow, pow_functor]; simp only [Category.assoc]
  erw [profinitePowFiltrationIso_spec]
  simp only [lim_map_π, Discrete.natTrans_app]
  erw [profinitePowFiltrationIso_spec_assoc]
  dsimp [Condensed.asNatDiagram, CategoryTheory.Limits.restrictDiagram, CompHausFiltPseuNormGrp.levelCondensedDiagram,
    CompHausFiltPseuNormGrp.levelCondensedDiagram']
  rw [← Profinite_to_Condensed.map_comp]
  have h : κ (ι ⟨j⟩) (q + 1) ≤ κ (ι ⟨j + 1⟩) (q + 1) :=
    by
    apply Fact.out (Monotone (Function.swap κ (q + 1)))
    apply hι
    exact_mod_cast j.le_succ
  change _ ≫ Profinite_to_Condensed.map (PseudoNormedGroup.mapFiltration M _ _ h) = _
  rw [← Profinite_to_Condensed.map_comp]
  congr 1

theorem isoOnTheLeftNeg_conj (q : ℕ) :
    (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ M)).f -[q+1] =
      (isoOnTheLeftNeg _ _ _ _ hι _).hom ≫
        (Condensed.coproductToCoproduct
              (Condensed.asNatDiagramPow M.toCHFPNG (combine κ ι hι (q + 1)) _ ⋙ _) -
            𝟙 _) ≫
          (isoOnTheLeftNeg _ _ _ _ hι _).inv :=
  by
  dsimp [qprimeFP.shiftSubId]
  simp only [comp_sub, sub_comp, Category.id_comp, Iso.hom_inv_id, Category.assoc]
  congr 1
  apply (CategoryTheory.Limits.isColimitOfPreserves (HomologicalComplex.eval _ _ _) (colimit.isColimit _)).hom_ext
  swap; infer_instance
  rintro ⟨⟨j⟩⟩; dsimp
  erw [← HomologicalComplex.comp_f, colimit.ι_desc]
  dsimp [sigmaShiftCone]
  rw [isoOnTheLeftNeg_spec_alt_assoc]
  erw [colimit.ι_desc_assoc]; dsimp
  simp only [Category.assoc]
  slice_rhs 3 4 => erw [isoOnTheLeftNeg_spec']
  simp only [← Category.assoc]
  congr 1
  dsimp [condensedSetToCondensedAb]
  simp only [← Functor.map_comp]
  dsimp [qprimeFPInt, qprimeFPNat, FreeAb.eval, Functor.mapFreeAb, FPsystem, FPsystem.X,
    FreeAb.ofFunctor]
  rw [FreeAbelianGroup.lift.of]; dsimp
  congr 1
  ext S : 2
  dsimp
  simp only [← Functor.map_comp]; congr 1
  simp only [← NatTrans.comp_app, ← Sheaf.Hom.comp_val]
  rw [iso_on_the_left_neg_conj_aux]
  ext; rfl

def productIsoBiproduct {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A] {α : Type (u + 1)}
    [Fintype α] (X : α → A) : ∏ X ≅ biproduct X :=
  (limit.isLimit _).conePointUniqueUpToIso (biproduct.isLimit _)

@[simp, reassoc]
theorem productIsoBiproduct_spec' {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    {α : Type (u + 1)} [Fintype α] (X : α → A) (t) :
    (productIsoBiproduct X).inv ≫ Pi.π _ t = biproduct.π _ t := by erw [limit.lift_π]; rfl

@[simp, reassoc]
theorem productIsoBiproduct_spec {A : Type (u + 2)} [Category.{u + 1} A] [Abelian A]
    {α : Type (u + 1)} [Fintype α] (X : α → A) (t) :
    (productIsoBiproduct X).hom ≫ biproduct.π _ t = Pi.π _ t := by
  rw [← Iso.eq_inv_comp, productIsoBiproduct_spec']

def condensedProductIsoBiproduct (q : ℕ) :
    condensedAbToCondensedSet.{u}.obj (∏ fun i : ULift.{u + 1, 0} (Fin q) => M.toCondensed) ≅
      condensedAbToCondensedSet.{u}.obj (⨁ fun i : Fin q => M.toCondensed) :=
  condensedAbToCondensedSet.mapIso <|
    { hom := biproduct.lift fun i => Pi.π _ ⟨i⟩
      inv := Pi.lift fun i => biproduct.π _ i.down
      hom_inv_id := by apply limit.hom_ext; rintro ⟨⟨j⟩⟩; dsimp; simp
      inv_hom_id := by apply biproduct.hom_ext; rintro ⟨j⟩; dsimp; simp }

--(limit.is_limit _).cone_point_unique_up_to_iso (biproduct.is_limit _)
@[simp, reassoc]
theorem condensedProductIsoBiproduct_spec' (q : ℕ) (i : ULift.{u + 1} (Fin q)) :
    (condensedProductIsoBiproduct M q).inv ≫ condensedAbToCondensedSet.map (Pi.π _ i) =
      condensedAbToCondensedSet.map (biproduct.π _ i.down) :=
  by
  dsimp only [condensedProductIsoBiproduct, Functor.mapIso_inv, Functor.mapIso_hom]
  rw [← Condensed_Ab_to_CondensedSet.map_comp]
  erw [limit.lift_π]
  rfl

@[simp, reassoc]
theorem condensedProductIsoBiproduct_spec (q : ℕ) (i : ULift.{u + 1} (Fin q)) :
    (condensedProductIsoBiproduct M q).hom ≫ condensedAbToCondensedSet.map (biproduct.π _ i.down) =
      condensedAbToCondensedSet.map (Pi.π _ i) :=
  by rw [← Iso.eq_inv_comp]; rw [condensedProductIsoBiproduct_spec']

def condensedProductIsoProduct (q : ℕ) :
    condensedAbToCondensedSet.{u}.obj (∏ fun i : ULift.{u + 1, 0} (Fin q) => M.toCondensed) ≅
      ∏ fun i : ULift.{u + 1} (Fin q) => condensedAbToCondensedSet.obj M.toCondensed :=
  preservesLimitIso condensedAbToCondensedSet _ ≪≫
    HasLimit.isoOfNatIso (Discrete.natIso fun i => Iso.refl _)

@[simp, reassoc]
theorem condensedProductIsoProduct_spec (q : ℕ) (i : ULift.{u + 1} (Fin q)) :
    (condensedProductIsoProduct M q).hom ≫ Pi.π _ i = condensedAbToCondensedSet.map (Pi.π _ i) :=
  by
  dsimp [condensedProductIsoProduct]; simp only [Category.assoc]
  erw [limit.lift_π]
  dsimp
  erw [Category.comp_id, limit.lift_π]; rfl

@[simp, reassoc]
theorem condensedProductIsoProduct_spec' (q : ℕ) (i : ULift.{u + 1} (Fin q)) :
    (condensedProductIsoProduct M q).inv ≫ condensedAbToCondensedSet.map (Pi.π _ i) = Pi.π _ i := by
  rw [Iso.inv_comp_eq]; rw [condensedProductIsoProduct_spec]

def isoOnTheRightZero :
    condensedSetToCondensedAb.{u}.obj
        (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt 0)) =>
          (Condensed.asNatCocone.{u} M.toCHFPNG (combine.{u} κ ι hι 0)).pt) ≅
      ((BD.eval' freeCond'.{u}).obj M.toCondensed).pt 0 :=
  by
  refine' CondensedSet_to_Condensed_Ab.map_iso _
  dsimp
  refine' _ ≪≫ condensedProductIsoBiproduct _ _
  refine' (condensedProductIsoProduct _ _).symm

-- Why is this thing tagged with simp in the first place!?
attribute [-simp] forget_map_eq_coe

@[simp, reassoc]
theorem isoOnTheRightZero_spec' (i : ULift.{u + 1} (Fin (BD.data.pt 0))) :
    (isoOnTheRightZero BD κ M ι hι).inv ≫ condensedSetToCondensedAb.map (Pi.π _ i) =
      condensedSetToCondensedAb.map (condensedAbToCondensedSet.map <| biproduct.π _ i.down) :=
  by
  dsimp [isoOnTheRightZero]; simp only [← Functor.map_comp]; congr 1; ext S : 2
  dsimp; simp_rw [← Functor.map_comp, ← NatTrans.comp_app, ← Sheaf.Hom.comp_val, Category.assoc]
  erw [condensedProductIsoProduct_spec]
  erw [condensedProductIsoBiproduct_spec']
  rfl

@[simp, reassoc]
theorem isoOnTheRightZero_spec (i : ULift.{u + 1} (Fin (BD.data.pt 0))) :
    (isoOnTheRightZero BD κ M ι hι).hom ≫
        condensedSetToCondensedAb.map (condensedAbToCondensedSet.map <| biproduct.π _ i.down) =
      condensedSetToCondensedAb.map (Pi.π _ i) :=
  by rw [← Iso.eq_inv_comp]; rw [isoOnTheRightZero_spec']

theorem isoOnTheRightZero_conj :
    (qprimeFPSigmaProj BD κ M ι).f 0 =
      (isoOnTheLeftZero _ _ _ _ hι).hom ≫
        Condensed.coproductPresentationWithPow condensedSetToCondensedAb M.toCHFPNG
            (combine _ _ _ _) _ ≫
          (isoOnTheRightZero _ _ _ _ _).hom :=
  by
  dsimp [qprimeFPSigmaProj]
  apply
    (CategoryTheory.Limits.isColimitOfPreserves (HomologicalComplex.eval _ _ 0)
        (colimit.isColimit
          (Discrete.functor fun k : ULift.{u + 1, 0} ℕ =>
            (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)))).hom_ext
  rintro ⟨⟨i⟩⟩; dsimp; rw [← HomologicalComplex.comp_f, colimit.ι_desc]; dsimp
  slice_rhs 1 2 => erw [isoOnTheLeftZero_spec_alt BD κ M ι hι i]
  dsimp [Condensed.coproductPresentationWithPow, -condensedSetToCondensedAb_map]
  simp only [Category.assoc, colimit.ι_desc]
  dsimp [-condensedSetToCondensedAb_map]
  dsimp [qprimeFPIncl, -condensedSetToCondensedAb_map, isoOnTheRightZero]
  simp only [← Functor.map_comp]; congr 1
  simp_rw [← Category.assoc]; rw [← Iso.comp_inv_eq, Iso.eq_comp_inv]
  apply limit.hom_ext; rintro ⟨j⟩
  simp only [Category.assoc, lim_map_π]
  erw [condensedProductIsoProduct_spec]
  erw [condensedProductIsoBiproduct_spec']
  erw [profinitePowFiltrationIso_spec_assoc]
  ext S : 3
  dsimp [qprimeFPInclAux]
  rw [← CategoryTheory.whiskerRight_app, ← NatTrans.comp_app]
  have :=
    (CategoryTheory.Limits.isLimitOfPreserves (condensedAbToCondensedSet.{u} ⋙ condensedSetToPresheaf.{u})
        (biproduct.isLimit fun i : Fin (BD.data.X 0) => M.to_Condensed)).fac
  dsimp at this ; erw [this _ ⟨j.down⟩]
  ext; rfl

def isoOnTheRightNeg (q : ℕ) :
    condensedSetToCondensedAb.{u}.obj
        (∏ fun j : ULift.{u + 1, 0} (Fin (BD.data.pt (q + 1))) =>
          (Condensed.asNatCocone.{u} M.toCHFPNG (combine.{u} κ ι hι (q + 1))).pt) ≅
      ((BD.eval' freeCond'.{u}).obj M.toCondensed).pt -[q+1] :=
  by
  refine' CondensedSet_to_Condensed_Ab.map_iso _
  dsimp
  refine' _ ≪≫ condensedProductIsoBiproduct _ _
  refine' (condensedProductIsoProduct _ _).symm

@[simp, reassoc]
theorem isoOnTheRightNeg_spec' (q : ℕ) (i : ULift.{u + 1} (Fin (BD.data.pt (q + 1)))) :
    (isoOnTheRightNeg BD κ M ι hι q).inv ≫ condensedSetToCondensedAb.map (Pi.π _ i) =
      condensedSetToCondensedAb.map (condensedAbToCondensedSet.map <| biproduct.π _ i.down) :=
  by
  dsimp [isoOnTheRightNeg]; simp only [← Functor.map_comp]; congr 1; ext S : 2
  dsimp; simp_rw [← Functor.map_comp, ← NatTrans.comp_app, ← Sheaf.Hom.comp_val, Category.assoc]
  erw [condensedProductIsoProduct_spec]
  erw [condensedProductIsoBiproduct_spec']
  rfl

@[simp, reassoc]
theorem isoOnTheRightNeg_spec (q : ℕ) (i : ULift.{u + 1} (Fin (BD.data.pt (q + 1)))) :
    (isoOnTheRightNeg BD κ M ι hι q).hom ≫
        condensedSetToCondensedAb.map (condensedAbToCondensedSet.map <| biproduct.π _ i.down) =
      condensedSetToCondensedAb.map (Pi.π _ i) :=
  by rw [← Iso.eq_inv_comp]; rw [isoOnTheRightNeg_spec']

theorem isoOnTheRightNeg_conj (q : ℕ) :
    (qprimeFPSigmaProj BD κ M ι).f -[q+1] =
      (isoOnTheLeftNeg _ _ _ _ hι q).hom ≫
        Condensed.coproductPresentationWithPow condensedSetToCondensedAb M.toCHFPNG
            (combine _ _ _ _) _ ≫
          (isoOnTheRightNeg _ _ _ _ _ _).hom :=
  by
  dsimp [qprimeFPSigmaProj]
  apply
    (CategoryTheory.Limits.isColimitOfPreserves (HomologicalComplex.eval _ _ -[q+1])
        (colimit.isColimit
          (Discrete.functor fun k : ULift.{u + 1, 0} ℕ =>
            (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)))).hom_ext
  rintro ⟨⟨i⟩⟩; dsimp; rw [← HomologicalComplex.comp_f, colimit.ι_desc]; dsimp
  slice_rhs 1 2 => erw [isoOnTheLeftNeg_spec_alt BD κ M ι hι q i]
  dsimp [Condensed.coproductPresentationWithPow, -condensedSetToCondensedAb_map]
  simp only [Category.assoc, colimit.ι_desc]
  dsimp [-condensedSetToCondensedAb_map]
  dsimp [qprimeFPIncl, -condensedSetToCondensedAb_map, isoOnTheRightNeg]
  simp only [← Functor.map_comp]; congr 1
  simp_rw [← Category.assoc]; rw [← Iso.comp_inv_eq, Iso.eq_comp_inv]
  apply limit.hom_ext; rintro ⟨j⟩
  simp only [Category.assoc, lim_map_π]
  erw [condensedProductIsoProduct_spec]
  erw [condensedProductIsoBiproduct_spec']
  erw [profinitePowFiltrationIso_spec_assoc]
  ext S : 3
  dsimp [qprimeFPInclAux]
  rw [← CategoryTheory.whiskerRight_app, ← NatTrans.comp_app]
  erw [(CategoryTheory.Limits.isLimitOfPreserves (condensedAbToCondensedSet.{u} ⋙ condensedSetToPresheaf.{u})
          (biproduct.isLimit fun i : Fin (BD.data.X (q + 1)) => M.to_Condensed)).fac
      _ ⟨j.down⟩]
  ext; rfl

end SesSetup

theorem qprimeFP.mono (n : ℤ) :
    Mono ((qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ M)).f n) :=
  by
  rcases n with ((_ | q) | q)
  · erw [isoOnTheLeftZero_conj]
    apply (config := { instances := false }) mono_comp; infer_instance
    apply (config := { instances := false }) mono_comp; swap; infer_instance
    apply Condensed.mono_coproductToCoproduct
  · apply mono_of_isZero_object
    let e :
      (∐ fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt
          (Int.ofNat q.succ) ≅
        ∐ fun k : ULift.{u + 1} ℕ =>
          ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt (Int.ofNat q.succ) :=
      CategoryTheory.preservesColimitIso (HomologicalComplex.eval _ _ _) _ ≪≫
        HasColimit.isoOfNatIso (Discrete.natIso fun p => iso.refl _)
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ e.symm
    apply CategoryTheory.isZero_colimit; intro j
    exact is_zero_zero _
  · erw [isoOnTheLeftNeg_conj]
    apply (config := { instances := false }) mono_comp; infer_instance
    apply (config := { instances := false }) mono_comp; swap; infer_instance
    apply Condensed.mono_coproductToCoproduct

/-
  rw Condensed.mono_iff_ExtrDisc, intros T,
  let Q := QprimeFP_int r' BD.data κ M,
  let e : ((∐ λ (k : ulift.{u+1 0} ℕ), Q.obj (ι k)).X n).val.obj
    (op T.val) ≅ _ := coproduct_eval_iso _ _ _,
  let φ : ulift.{u+1} ℕ → Ab.{u+1} := λ k, ((Q.obj (ι k)).X n).val.obj (op T.val),
  let D := AddCommGroup.direct_sum_cofan.{u+1 u+1} φ,
  let hD := AddCommGroup.is_colimit_direct_sum_cofan.{u+1 u+1} φ,
  let g : D.X ⟶ D.X := sigma_shift'.{u u+2 u+1} _ hι (Q ⋙ (homological_complex.eval
    (Condensed.{u} Ab.{u+1}) (complex_shape.up ℤ) n) ⋙ Condensed.evaluation _ T.val) D hD,
  let f := _, change mono f,
  have hf : f = e.hom ≫ (g - 𝟙 _) ≫ e.inv,
  { rw [← category.assoc, iso.eq_comp_inv],
    dsimp [f, QprimeFP.shift_sub_id],
    change (_ - _) ≫ _ = _,
    simp only [comp_sub, sub_comp, category.id_comp, category.comp_id, Sheaf.hom.id_val,
      nat_trans.id_app], congr' 1,
    refine ((is_colimit_of_preserves (homological_complex.eval.{u+1 u+2 0}
      (Condensed.{u u+1 u+2} Ab.{u+1}) (complex_shape.up.{0} ℤ) n ⋙
      Condensed.evaluation.{u+2 u+1 u} Ab.{u+1} T.val) (colimit.is_colimit _))).hom_ext (λ j, _),
    dsimp [sigma_shift],
    slice_lhs 1 2
    { erw [← nat_trans.comp_app, ← Sheaf.hom.comp_val, ← homological_complex.comp_f,
        colimit.ι_desc] },
    slice_rhs 1 2
    { erw sigma_ι_coproduct_eval_iso },
    dsimp [sigma_shift_cone],
    rw category.assoc,
    slice_lhs 2 3
    { erw sigma_ι_coproduct_eval_iso },
    erw hD.fac, refl },
  suffices : mono (g - 𝟙 _),
  { rw hf,
    apply_with mono_comp { instances := ff },
    apply_instance,
    apply_with mono_comp { instances := ff },
    exact this,
    apply_instance },
  rw [AddCommGroup.mono_iff_injective, injective_iff_map_eq_zero],
  intros x hx,
  erw [sub_eq_zero, id_apply] at hx,
  ext ⟨i⟩,
  classical,
  induction i with i IH,
  { rw ← hx,
    dsimp [g, sigma_shift', sigma_shift_cone, hD, AddCommGroup.is_colimit_direct_sum_cofan,
      AddCommGroup.direct_sum_desc, discrete.nat_trans, direct_sum.to_add_monoid],
    rw [dfinsupp.sum_add_hom_apply, dfinsupp.sum_apply],
    apply finset.sum_eq_zero,
    rintro ⟨j⟩ -,
    convert dif_neg _,
    rw [finset.mem_singleton],
    intro H, rw ulift.ext_iff at H, revert H, apply nat.no_confusion, },
  { rw ← hx,
    classical,
    dsimp [g, sigma_shift', sigma_shift_cone, hD, AddCommGroup.is_colimit_direct_sum_cofan,
      AddCommGroup.direct_sum_desc, discrete.nat_trans, direct_sum.to_add_monoid],
    rw [dfinsupp.sum_add_hom_apply, dfinsupp.sum_apply],
    rw dfinsupp.zero_apply at IH,
    convert finset.sum_eq_single (ulift.up $ i) _ _,
    { rw [IH, add_monoid_hom.map_zero, dfinsupp.zero_apply], },
    { rintro ⟨j⟩ - hj, convert dif_neg _, rw [finset.mem_singleton],
      intro H, apply hj, rw ulift.ext_iff at H ⊢, change i+1 = j+1 at H,
      change j = i, linarith only [H] },
    { intro, rw [IH, add_monoid_hom.map_zero, dfinsupp.zero_apply], }, },
  recover, all_goals { classical; apply_instance }
  -/
theorem qprimeFPSigmaProj_eq_0 (n : ℕ) : (qprimeFPSigmaProj BD κ M ι).f (n + 1 : ℤ) = 0 := by
  apply IsZero.eq_of_tgt; apply is_zero_zero

-- move me
theorem AddCommGroupCat.eq_of_isZero (A : AddCommGroupCat) (hA : IsZero A) (x y : A) : x = y := by
  rw [← Ab.pt_apply' x, ← Ab.pt_apply' y]; congr 1; apply hA.eq_of_tgt

attribute [simps] condensedAbToPresheaf

theorem qprimeFP.epi (hι : Monotone ι)
    (hκι : ∀ (r : ℝ≥0) (q), ∃ n : ℕ, r ≤ (combine.{u} κ ι hι q) n) (n : ℤ) :
    Epi ((qprimeFPSigmaProj BD κ M ι).f n) :=
  by
  rcases n with ((_ | q) | q)
  · erw [isoOnTheRightZero_conj]
    swap; assumption
    apply (config := { instances := false }) epi_comp; infer_instance
    apply (config := { instances := false }) epi_comp; swap; infer_instance
    rw [Condensed.coproductPresentationWithPow_eq]
    apply (config := { instances := false }) epi_comp; swap; infer_instance
    swap; · intro r; apply hκι
    exact
      Condensed.epi_coproductToColimit
        (Condensed.asNatDiagramPow.{u} M.to_CHFPNG (combine.{u} κ ι hι 0) (BD.data.X 0) ⋙
          condensedSetToCondensedAb.{u})
  · apply epi_of_isZero
    exact is_zero_zero _
  · erw [isoOnTheRightNeg_conj]; swap; assumption
    apply (config := { instances := false }) epi_comp; infer_instance
    apply (config := { instances := false }) epi_comp; swap; infer_instance
    rw [Condensed.coproductPresentationWithPow_eq]
    apply (config := { instances := false }) epi_comp; swap; infer_instance
    swap; · intro r; apply hκι
    exact
      Condensed.epi_coproductToColimit
        (Condensed.asNatDiagramPow.{u} M.to_CHFPNG (combine.{u} κ ι hι (q + 1))
            (BD.data.X (q + 1)) ⋙
          condensedSetToCondensedAb.{u})

/-
  rw is_epi_iff_forall_surjective,
  intros S,
  rcases n with ((_|n)|n),
  swap,
  { intro f,
    refine ⟨0, _⟩, apply AddCommGroup.eq_of_is_zero,
    rw [← evaluation_obj_obj, ← Condensed_Ab_to_presheaf_obj],
    apply functor.map_is_zero, apply functor.map_is_zero, exact is_zero_zero _, },
  { admit },
  { admit },
  -/
theorem qprimeFP.exact (n : ℤ) (hκι : ∀ (r : ℝ≥0) (q), ∃ n : ℕ, r ≤ (combine.{u} κ ι hι q) n) :
    Exact ((qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ M)).f n)
      ((qprimeFPSigmaProj BD κ M ι).f n) :=
  by
  rcases n with ((_ | q) | q)
  · erw [isoOnTheLeftZero_conj]
    erw [isoOnTheRightZero_conj]; swap; assumption
    rw [← Category.assoc]
    apply CategoryTheory.exact_comp_inv_hom_comp
    rw [exact_iso_comp]; rw [exact_comp_iso]
    apply (Condensed.shortExact_sequence_with_pow _ _ _ _ _).exact
    intro r; apply hκι
  · apply CategoryTheory.Limits.exact_of_isZero
    let e :
      (∐ fun k : ULift.{u + 1, 0} ℕ => (qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt
          (Int.ofNat q.succ) ≅
        ∐ fun k : ULift.{u + 1} ℕ =>
          ((qprimeFPInt.{u} r' BD.data κ M).obj (ι k)).pt (Int.ofNat q.succ) :=
      CategoryTheory.preservesColimitIso (HomologicalComplex.eval _ _ _) _ ≪≫
        HasColimit.isoOfNatIso (Discrete.natIso fun p => iso.refl _)
    apply CategoryTheory.Limits.isZero_of_iso_of_zero _ e.symm
    apply CategoryTheory.isZero_colimit; intro j
    exact is_zero_zero _
  · erw [isoOnTheLeftNeg_conj]
    erw [isoOnTheRightNeg_conj]; swap; assumption
    rw [← Category.assoc]
    apply CategoryTheory.exact_comp_inv_hom_comp
    rw [exact_iso_comp]; rw [exact_comp_iso]
    apply (Condensed.shortExact_sequence_with_pow _ _ _ _ _).exact
    intro r; apply hκι

theorem qprimeFP.shortExact (hκι : ∀ (r : ℝ≥0) (q), ∃ n : ℕ, r ≤ (combine.{u} κ ι hι q) n) (n : ℤ) :
    ShortExact ((qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD.data κ M)).f n)
      ((qprimeFPSigmaProj BD κ M ι).f n) :=
  by
  apply (config := { instances := false }) ShortExact.mk
  · apply qprimeFP.mono
  · apply qprimeFP.epi; assumption
  · apply qprimeFP.exact; assumption

end Step4

section Step5

variable {r' : ℝ≥0} [Fact (0 < r')] [Fact (r' ≤ 1)]

variable (BD : BreenDeligne.Data)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

def qprimeFPNat.tinv [∀ c n, Fact (κ c n ≤ r' * κ₂ c n)] :
    qprimeFPNat r' BD κ M ⟶ qprimeFPNat r' BD κ₂ M :=
  whiskerRight (fPsystem.tinv.{u} r' BD ⟨M⟩ _ _) _

def qprimeFPInt.tinv [∀ c n, Fact (κ c n ≤ r' * κ₂ c n)] :
    qprimeFPInt r' BD κ M ⟶ qprimeFPInt r' BD κ₂ M :=
  whiskerRight (qprimeFPNat.tinv _ _ _ _)
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp)

def qprimeFP.tinv [∀ c n, Fact (κ c n ≤ r' * κ₂ c n)] : qprimeFP r' BD κ M ⟶ qprimeFP r' BD κ₂ M :=
  whiskerRight (qprimeFPNat.tinv _ _ _ _) ChainComplex.toBoundedHomotopyCategory

/-- The natural inclusion map -/
def qprimeFPNat.ι [∀ c n, Fact (κ c n ≤ κ₂ c n)] : qprimeFPNat r' BD κ M ⟶ qprimeFPNat r' BD κ₂ M :=
  whiskerRight (fPsystem.res r' BD ⟨M⟩ _ _) _

/-- The natural inclusion map -/
def qprimeFPInt.ι [∀ c n, Fact (κ c n ≤ κ₂ c n)] : qprimeFPInt r' BD κ M ⟶ qprimeFPInt r' BD κ₂ M :=
  whiskerRight (qprimeFPNat.ι _ _ _ _)
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp)

/-- The natural inclusion map -/
def qprimeFP.ι [∀ c n, Fact (κ c n ≤ κ₂ c n)] : qprimeFP r' BD κ M ⟶ qprimeFP r' BD κ₂ M :=
  whiskerRight (qprimeFPNat.ι _ _ _ _) ChainComplex.toBoundedHomotopyCategory

open CategoryTheory.Preadditive

theorem commsqShiftSubIdTinv [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ r' * κ c n)] :
    Commsq (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD κ₂ M))
      (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.tinv BD κ₂ κ M))
      (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.tinv BD κ₂ κ M))
      (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD κ M)) :=
  Commsq.ofEq
    (by
      delta qprimeFP.shiftSubId
      rw [sub_comp, comp_sub, Category.id_comp, Category.comp_id]
      refine' congr_arg₂ _ _ rfl
      apply colimit.hom_ext; rintro ⟨⟨j⟩⟩
      dsimp [sigmaShift, sigmaShift', sigmaShiftCone, sigmaMap]
      rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc]
      dsimp [sigmaShiftCone]
      simp only [Category.assoc, colimit.ι_desc]
      dsimp [sigmaShiftCone]
      simp only [sigmaShift, sigmaShift', sigmaShiftCone, sigmaMap, colimit.ι_desc_assoc,
        colimit.ι_desc, Cofan.mk_ι_app, Category.assoc, NatTrans.naturality_assoc,
        Discrete.natTrans_app])

theorem commsqShiftSubIdι [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ κ c n)] :
    Commsq (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD κ₂ M))
      (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.ι BD κ₂ κ M))
      (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.ι BD κ₂ κ M))
      (qprimeFP.shiftSubId ι hι (qprimeFPInt r' BD κ M)) :=
  Commsq.ofEq
    (by
      delta qprimeFP.shiftSubId
      rw [sub_comp, comp_sub, Category.id_comp, Category.comp_id]
      refine' congr_arg₂ _ _ rfl
      apply colimit.hom_ext; rintro ⟨⟨j⟩⟩
      dsimp [sigmaShift, sigmaShift', sigmaShiftCone]
      simp only [sigmaShiftCone, sigmaMap, colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app,
        Category.assoc, NatTrans.naturality_assoc, Discrete.natTrans_app, colimit.cocone_ι])

end Step5

section Step6

variable {r' : ℝ≥0} [Fact (0 < r')] [Fact (r' ≤ 1)]

variable (BD : BreenDeligne.Package)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.data.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.data.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

open CategoryTheory.Preadditive

-- lemma commsq_sigma_proj_Tinv' (j) (n : ℕ) [fact (κ₂ (ι j) n ≤ r' * κ (ι j) n)] :
-- QprimeFP_incl_aux M (κ₂ (ι j) n) (BD.data.X n) ≫
--     Condensed_Ab_to_CondensedSet.map (biproduct.map (λ (i : ulift (fin (BD.data.X n))), M.Tinv_cond)) =
--   Profinite_to_Condensed.map
--       ((FiltrationPow.Tinv r' (κ₂ (ι j) n) (κ (ι j) n) (BD.data.X n)).app ⟨M⟩) ≫
--     QprimeFP_incl_aux M (κ (ι j) n) (BD.data.X n) :=
-- by admit
theorem commsqSigmaProjTinv [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ r' * κ c n)] :
    Commsq (qprimeFPSigmaProj BD κ₂ M ι)
      (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.tinv BD.data κ₂ κ M))
      ((BD.eval' freeCond').map M.tinvCond) (qprimeFPSigmaProj BD κ M ι) :=
  Commsq.ofEq
    (by
      apply colimit.hom_ext; rintro ⟨j⟩
      simp only [qprimeFPSigmaProj, sigmaMap, colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app,
        Category.assoc, NatTrans.naturality_assoc]
      dsimp only [qprimeFPIncl, qprimeFPInt.tinv, CategoryTheory.whiskerRight_app, Package.eval',
        Functor.comp_map]
      rw [← Functor.map_comp, ← Functor.map_comp]
      refine' congr_arg _ _
      ext n : 2
      dsimp only [HomologicalComplex.comp_f, Data.evalFunctor, Functor.comp_obj,
        Functor.flip_obj_map, HomologicalComplex.functorEval_map_app_f,
        Data.evalFunctor'_obj_x_map, Functor.comp_map, qprimeFPNat.tinv, CategoryTheory.whiskerRight_app,
        Functor.mapHomologicalComplex_map_f]
      rw [mapFreeAb_comp_map]
      dsimp only [FreeAb.eval, Functor.mapFreeAb, FPsystem.Tinv, fP2.tinv_app, FreeAb.ofFunctor]
      simp only [FreeAbelianGroup.lift_map, Function.comp, Function.comp.left_id]
      rw [FreeAbelianGroup.lift.of]
      simp only [← Functor.map_comp]
      congr 1
      ext1
      let x := biproduct.isLimit fun i : Fin (BD.data.X n) => M.to_Condensed
      let y := CategoryTheory.Limits.isLimitOfPreserves (condensedAbToCondensedSet ⋙ condensedSetToPresheaf) x
      apply y.hom_ext; rintro ⟨k⟩
      simp only [Sheaf.Hom.comp_val, Category.assoc, qprimeFPInclAux, y.fac]
      rw [← condensedSetToPresheaf_map, ← Functor.comp_map]
      simp only [Functor.mapCone_π_app, Bicone.toCone_π_app, biproduct.bicone_π]
      rw [← Functor.map_comp, biproduct.map_π, Functor.map_comp]
      have :
        ((condensedAbToCondensedSet ⋙ condensedSetToPresheaf).mapCone
                  (biproduct.bicone fun i : Fin (BD.data.X n) => M.to_Condensed).toCone).π.app
            ⟨k⟩ =
          (condensedAbToCondensedSet ⋙ condensedSetToPresheaf).map
            (biproduct.π (fun j : Fin (BD.data.X n) => M.to_Condensed) k) :=
        rfl
      rw [← this, ← Category.assoc, y.fac]; clear this y x
      ext S : 2
      dsimp only [NatTrans.comp_app, qprimeFPInclAux', Functor.comp_map,
        condensedAbToCondensedSet_map, condensedSetToPresheaf_map, profiniteToCondensed_map_val,
        CategoryTheory.whiskerRight_app, ProFiltPseuNormGrpWithTinv₁.tinvCond, forget_map_eq_coe, yoneda_map_app,
        CompHausFiltPseuNormGrp.toCondensed_map, Ab.ulift_map_apply]
      simp only [← ulift_functor.map_comp]
      rfl)

theorem commsqSigmaProjι [∀ (c : ℝ≥0) (n : ℕ), Fact (κ₂ c n ≤ κ c n)] :
    Commsq (qprimeFPSigmaProj BD κ₂ M ι)
      (sigmaMap (fun k : ULift ℕ => ι k) (qprimeFPInt.ι BD.data κ₂ κ M)) (𝟙 _)
      (qprimeFPSigmaProj BD κ M ι) :=
  Commsq.ofEq
    (by
      simp only [Category.comp_id]
      apply colimit.hom_ext; intro j
      simp only [qprimeFPSigmaProj, sigmaMap, colimit.ι_desc_assoc, colimit.ι_desc, Cofan.mk_ι_app,
        Category.assoc, NatTrans.naturality_assoc]
      dsimp only [qprimeFPIncl, qprimeFPInt.ι, CategoryTheory.whiskerRight_app, Package.eval', Functor.comp_map]
      rw [← Functor.map_comp]
      refine' congr_arg _ _
      ext n : 2
      dsimp only [HomologicalComplex.comp_f, Data.evalFunctor, Functor.comp_obj,
        Functor.flip_obj_map, HomologicalComplex.functorEval_map_app_f,
        Data.evalFunctor'_obj_x_map, Functor.comp_map, qprimeFPNat.ι, CategoryTheory.whiskerRight_app,
        Functor.mapHomologicalComplex_map_f]
      rw [mapFreeAb_comp_map]
      dsimp only [FreeAb.eval, Functor.mapFreeAb, FPsystem.res, fP2.res_app, FreeAb.ofFunctor]
      simp only [FreeAbelianGroup.lift_map, Function.comp, Function.comp.left_id]
      rw [FreeAbelianGroup.lift.of, ← Functor.map_comp]
      refine' congr_arg _ _
      ext1
      let x := biproduct.isLimit fun i : Fin (BD.data.X n) => M.to_Condensed
      let y := CategoryTheory.Limits.isLimitOfPreserves (condensedAbToCondensedSet ⋙ condensedSetToPresheaf) x
      apply y.hom_ext; intro k
      simp only [Sheaf.Hom.comp_val, Category.assoc, qprimeFPInclAux, y.fac]
      rw [← condensedSetToPresheaf_map, ← Functor.comp_map]
      ext S : 2
      dsimp only [NatTrans.comp_app, qprimeFPInclAux', Functor.comp_map,
        condensedAbToCondensedSet_map, condensedSetToPresheaf_map, profiniteToCondensed_map_val,
        CategoryTheory.whiskerRight_app, forget_map_eq_coe, yoneda_map_app,
        CompHausFiltPseuNormGrp.toCondensed_map, Ab.ulift_map_apply]
      simp only [← ulift_functor.map_comp]
      rfl)

end Step6

