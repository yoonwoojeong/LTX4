import LiquidTensorExperiment.Thm95.DoubleComplex
import LiquidTensorExperiment.PseudoNormedGroup.Homotopy
import LiquidTensorExperiment.Rescale.FiltrationPow

#align_import thm95.row_iso

/-!
# A complex canonically isomorphic to `row 1` of the double complex

We have
```
lemma double_complex.row_one :
  (double_complex BD κ r r' V Λ M N).row 1 =
  BD.system κ r V r' (Hom ((cosimplicial Λ N).obj (mk 0)) M) := rfl
```

We want to "rewrite" this row in such a way that it is the target
of the homotopies that will be constructed formally from `BD.homotopy`.

Concretely, we want:
```
(((data.mul N).obj BD.data).system (rescale_constants κ N) r V r').obj (op (Hom Λ M)) ≅
  (thm95.double_complex BD.data κ r r' V Λ M N).row 1
```

This means that we need to multiply `BD` by `N`,
and then take the system associated with `rescale N (Hom Λ M)`.

We need the following isomorphisms

* `BD.system M^N = (BD.mul N).system M`
* `Hom (rescale N (Λ^N)) M = (rescale N (Hom Λ M)^N` (2 steps?)
* `(cosimplicial Λ N).obj (mk 0) = rescale N (Λ^N)`

-/


universe u v

noncomputable section

open scoped NNReal BigOperators Kronecker

attribute [local instance] typePow

attribute [local reducible] cLCFPTinv₂ cLCFPTinv₂.res BreenDeligne.UniversalMap.evalCLCFPTinv₂

-- move this
namespace CategoryTheory

namespace Arrow

variable {C : Type _} [Category C] {X Y Z X' Y' Z' : C}

variable (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')

theorem mk_comp_congr (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by cases hf; cases hg; rfl

end Arrow

end CategoryTheory

open CategoryTheory

section Rescale

variable {BD : BreenDeligne.Data}

variable (κ : ℕ → ℝ≥0)

variable [BD.Suitable κ]

variable (r : ℝ≥0) (V : SemiNormedGroupCat.{v}) [NormedWithAut r V] [Fact (0 < r)]

variable {r' : ℝ≥0} [Fact (0 < r')] [Fact (r' ≤ 1)] (c : ℝ≥0)

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

-- move this
instance rescaleConstantsSuitable (N : ℝ≥0) : BD.Suitable (rescaleConstants κ N) := by
  delta rescaleConstants; infer_instance

variable (BD)

open BreenDeligne Opposite

open ProFiltPseuNormGrpWithTinv (of)

section

def filtrationPowRescaleIso (n : ℕ) (N : ℝ≥0) :
    ((filtration r').obj c).obj ((ProFiltPseuNormGrpWithTinv.pow r' n).obj (of r' (Rescale N M))) ≅
      ((filtration r').obj (c * N⁻¹)).obj ((ProFiltPseuNormGrpWithTinv.pow r' n).obj M) :=
  Iso.refl _

def complexRescaleIso (N : ℝ≥0) :
    (BD.complex (rescaleConstants κ N) r V r' c).obj (op M) ≅
      (BD.complex κ r V r' c).obj (op <| of r' <| Rescale N M) :=
  HomologicalComplex.Hom.isoOfComponents
    (by
      intro i
      refine' cLCTinv.mapIso r V _ _ _ _ _ _ _ _
      ·
        refine'
          (filtrationPowRescaleIso _ _ _ _ ≪≫ filtrationCastEq r' _ _ (mul_assoc c (κ i) N⁻¹) _).op
      ·
        refine'
          (filtrationPowRescaleIso _ _ _ _ ≪≫
              filtrationCastEq _ (r' * (c * κ i) * N⁻¹) (r' * (c * (κ i * N⁻¹)))
                (by simp only [mul_assoc]) _).op
      · rfl
      · rfl)
    (by
      intro i j hij
      apply Arrow.mk_injective
      dsimp only [Data.complex_obj_d, UniversalMap.evalCLCFPTinv, UniversalMap.evalCLCFPTinv₂,
        _root_.id, SemiNormedGroupCat.equalizer.mapNat_app, cLCTinv.mapIso_hom, cLCTinv.map,
        unop_op, filtrationCastEq, Iso.op_hom]
      simp only [SemiNormedGroupCat.equalizer.map_comp_map, UniversalMap.evalCLCFP_rescale, ←
        cLCFP.res_def', NatIso.app_hom, Functor.mapIso_hom, filtration_map_app,
        filtrationPowRescaleIso, Iso.refl_trans]
      apply SemiNormedGroupCat.equalizer.map_congr
      · have :=
          @UniversalMap.res_comp_evalCLCFP V r' (c * (κ i * N⁻¹)) (c * κ i * N⁻¹)
            (c * (κ j * N⁻¹)) (c * κ j * N⁻¹) (BD.X j) (BD.X i) (BD.d j i) ⟨(mul_assoc _ _ _).le⟩ _
            _ ⟨(mul_assoc _ _ _).le⟩
        replace := NatTrans.congr_app this.symm (op M)
        replace := congr_arg arrow.mk this
        refine' (this.trans _).symm
        apply Arrow.mk_comp_congr; · rfl; · rw [UniversalMap.evalCLCFP_rescale]
      · have :=
          @UniversalMap.res_comp_evalCLCFP V r' (r' * (c * (κ i * N⁻¹))) (r' * (c * κ i) * N⁻¹)
            (r' * (c * (κ j * N⁻¹))) (r' * (c * κ j) * N⁻¹) (BD.X j) (BD.X i) (BD.d j i)
            ⟨le_of_eq <| by simp only [mul_assoc]⟩ _ _ ⟨le_of_eq <| by simp only [mul_assoc]⟩
        replace := NatTrans.congr_app this.symm (op M)
        replace := congr_arg arrow.mk this
        refine' (this.trans _).symm
        apply Arrow.mk_comp_congr; · rfl; · rw [UniversalMap.evalCLCFP_rescale]
      any_goals rfl)

noncomputable def systemRescaleIso (N : ℝ≥0) :
    (BD.system (rescaleConstants κ N) r V r').obj (op M) ≅
      (BD.system κ r V r').obj (op <| of r' <| Rescale N M) :=
  NatIso.ofComponents (fun c => complexRescaleIso BD κ r V c.unop _ _)
    (by
      intro c₁ c₂ h
      ext i : 2
      apply Arrow.mk_injective
      erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp only [Data.system_obj, cLCFPTinv₂.res, complexRescaleIso,
        HomologicalComplex.Hom.isoOfComponents, cLCTinv.mapIso_hom, cLCTinv.mapNat_app]
      simp only [cLCTinv.map_comp_map]
      rfl)

end

end Rescale

namespace Thm95

open BreenDeligne PolyhedralLattice Opposite

variable (BD : BreenDeligne.Data) (κ : ℕ → ℝ≥0) [BD.Suitable κ]

variable (r : ℝ≥0) (V : SemiNormedGroupCat.{v}) [NormedWithAut r V] [Fact (0 < r)]

variable {r' : ℝ≥0} [Fact (0 < r')] [Fact (r < r')] [Fact (r' ≤ 1)] (c : ℝ≥0)

section

variable {m n : ℕ} (ϕ : UniversalMap m n) (g : BasicUniversalMap m n)

variable (c₁ c₂ : ℝ≥0) (N : ℕ) [Fact (0 < N)]

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

theorem evalFP_hMul [g.Suitable c₂ c₁] :
    (cLC V).map (filtrationPow.mulIso.{u, u} r' c₁ M N n).hom.op ≫
        (cLC V).map
          ((BasicUniversalMap.evalFP r' c₂ c₁ g).app
              (ProFiltPseuNormGrpWithTinv.of r' (M ^ N))).op =
      (cLC V).map ((BasicUniversalMap.evalFP r' c₂ c₁ ((BasicUniversalMap.mul N) g)).app M).op ≫
        (cLC V).map (filtrationPow.mulIso.{u, u} r' c₂ M N m).hom.op :=
  by
  simp only [← (cLC V).map_comp, ← op_comp]; congr 2
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  exact BasicUniversalMap.mulIso_evalFP r' c₁ c₂ g N M

theorem evalCLCFP_hMul [ϕ.Suitable c₂ c₁] {_ : (UniversalMap.mul N ϕ).Suitable c₂ c₁} :
    ((UniversalMap.mul N ϕ).evalCLCFP V r' c₁ c₂).app (op M) ≫
        (cLC V).map (filtrationPow.mulIso.{u, u} r' c₂ M N m).op.hom =
      (cLC V).map (filtrationPow.mulIso.{u, u} r' c₁ M N n).op.hom ≫
        ((ϕ.evalCLCFP V r' c₁ c₂).app (op (ProFiltPseuNormGrpWithTinv.of r' (M ^ N))) : _) :=
  by
  dsimp only [UniversalMap.evalCLCFP, CategoryTheory.whiskerRight_app]
  simp only [UniversalMap.evalLCFP_eq_evalLCFP', UniversalMap.evalLCFP', ←
    NatTrans.appHom_apply, ← Functor.mapAddHom_apply, AddMonoidHom.map_sum,
    AddMonoidHom.map_zsmul]
  rw [Preadditive.sum_comp, Preadditive.comp_sum]
  symm; have hN : 0 < N := Fact.out _
  apply Finset.sum_bij fun g hg => BasicUniversalMap.mul N g
  · intro g hg; rw [UniversalMap.mem_support_hMul N hN]; refine' ⟨g, hg, rfl⟩
  · intro g hg
    simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, UniversalMap.coeff_hMul N hN]
    congr 1
    have : g.suitable c₂ c₁ := UniversalMap.suitable_of_mem_support _ _ _ _ hg; skip
    rw [← BasicUniversalMap.evalLCFP_eq_evalLCFP' _ _ _ _ g this, ←
      BasicUniversalMap.evalLCFP_eq_evalLCFP']
    swap; · apply BasicUniversalMap.hMul_suitable
    dsimp only [BasicUniversalMap.evalLCFP, NatTrans.appHom_apply, Functor.mapAddHom_apply,
      CategoryTheory.whiskerRight_app, NatTrans.op_app, unop_op]
    simp only [← Functor.comp_map]
    apply eval_FP_mul
  · intro g₁ g₂ hg₁ hg₂ H; exact BasicUniversalMap.hMul_injective N hN H
  · intro g; rw [UniversalMap.mem_support_hMul N hN]; rintro ⟨g', h1, h2⟩; exact ⟨g', h1, h2⟩

def mulComplexIso (c : ℝ≥0) :
    (((Data.mul N).obj BD).complex κ r V r' c).obj (op M) ≅
      (BD.complex κ r V r' c).obj (op (ProFiltPseuNormGrpWithTinv.of r' <| M ^ N)) :=
  HomologicalComplex.Hom.isoOfComponents
    (by
      intro i
      refine' cLCTinv.mapIso r V _ _ _ _ _ _ _ _
      · exact (filtrationPow.mulIso.{u, u} r' (c * κ i) M N (BD.X i)).op
      · exact (filtrationPow.mulIso.{u, u} r' (r' * (c * κ i)) M N (BD.X i)).op
      · rfl
      · rfl)
    (by
      intro i j hij
      apply Arrow.mk_injective
      dsimp only [Data.complex_obj_d, UniversalMap.evalCLCFPTinv, UniversalMap.evalCLCFPTinv₂,
        _root_.id, SemiNormedGroupCat.equalizer.mapNat_app, cLCTinv.mapIso_hom, cLCTinv.map,
        Data.mul_obj_d]
      simp only [SemiNormedGroupCat.equalizer.map_comp_map]
      apply SemiNormedGroupCat.equalizer.map_congr
      · rw [eval_CLCFP_mul]
      · rw [eval_CLCFP_mul]
      all_goals rfl)

end

def mulSystemIso (N : ℕ) [Fact (0 < N)] (M : ProFiltPseuNormGrpWithTinv.{u} r') :
    (((Data.mul N).obj BD).system κ r V r').obj (op M) ≅
      (BD.system κ r V r').obj (op (ProFiltPseuNormGrpWithTinv.of r' <| M ^ N)) :=
  NatIso.ofComponents (fun c => mulComplexIso BD κ r V N M c.unop)
    (by
      intro c₁ c₂ hc
      ext i : 2
      apply Arrow.mk_injective
      erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      dsimp only [Data.system_obj, cLCFPTinv₂.res, Thm95.mulComplexIso,
        HomologicalComplex.Hom.isoOfComponents, cLCTinv.mapIso_hom, cLCTinv.mapNat_app]
      simp only [cLCTinv.map_comp_map]
      rfl)

def mulRescaleIsoRowOne (N : ℕ) [Fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
    (Λ : PolyhedralLatticeCat.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
    (((Data.mul N).obj BD).system (rescaleConstants κ N') r V r').obj (op (hom Λ M)) ≅
      (Thm95.doubleComplex BD κ r r' V Λ M N).row 1 :=
  mulSystemIso _ _ r V N _ ≪≫
    systemRescaleIso _ κ r V _ _ ≪≫
      ((BD.system κ r V r').mapIso <|
        (PolyhedralLatticeCat.homCosimplicialZeroIso Λ N r' M N' h).op)

theorem mulRescaleIsoRowOne_strict (N : ℕ) [Fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
    (Λ : PolyhedralLatticeCat.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0) (i : ℕ)
    (x : (((Data.mul N).obj BD).system (rescaleConstants κ N') r V r').obj (op (hom Λ M)) c i) :
    ‖((mulRescaleIsoRowOne BD κ r V N N' h Λ M).hom x)‖ = ‖x‖ :=
  by
  apply NormedAddGroupHom.norm_eq_of_isometry
  refine' Isometry.comp (Isometry.comp _ _) _
  · apply Data.system_mapIso_isometry
  · dsimp only; apply cLCTinv.mapIso_isometry
  · apply cLCTinv.mapIso_isometry

theorem quux (N : ℕ) [Fact (0 < N)] (M : ProFiltPseuNormGrpWithTinv.{u} r') (c₁ c₂ : ℝ≥0) (i : ℕ)
    [(UniversalMap.sum i N).Suitable c₂ c₁]
    {_ : ((Finset.univ : Finset (Fin N)).Sum (BasicUniversalMap.proj i)).Suitable c₂ c₁} :
    (UniversalMap.evalCLCFP V r' c₁ c₂ (UniversalMap.sum i N)).app (op M) =
      (cLC V).map
        ((BasicUniversalMap.evalFP r' c₂ c₁
                ((Finset.univ : Finset (Fin N)).Sum (BasicUniversalMap.proj i))).app
            M).op :=
  by dsimp only [UniversalMap.sum]; rw [UniversalMap.evalCLCFP_of]; rfl

theorem bar (N : ℕ) [Fact (0 < N)] (Λ : PolyhedralLatticeCat.{u})
    (M : ProFiltPseuNormGrpWithTinv.{u} r') (c₁ c₂ : ℝ≥0) (hc : c₁ * N⁻¹ = c₂) (n : ℕ)
    {_ : ((Finset.univ : Finset (Fin N)).Sum (BasicUniversalMap.proj n)).Suitable c₂ c₁} :
    (filtrationPowRescaleIso c₁ (ProFiltPseuNormGrpWithTinv.of r' (hom Λ M ^ N)) n N ≪≫
            ((filtration r').mapIso (eqToIso hc)).app
              ((ProFiltPseuNormGrpWithTinv.pow r' n).obj
                (ProFiltPseuNormGrpWithTinv.of r' (hom Λ M ^ N)))).inv ≫
        ((filtration r').obj c₁).map ((ProFiltPseuNormGrpWithTinv.pow r' n).map (Λ.homSum N r' M)) =
      (filtrationPow.mulIso.{u, u} r' c₂ (hom.{u, u} Λ M) N n).hom ≫
        (BasicUniversalMap.evalFP.{u} r' c₂ c₁ (Finset.univ.Sum (BasicUniversalMap.proj n))).app
          (hom.{u, u} Λ M) :=
  by
  dsimp only [filtrationPowRescaleIso]; rw [Iso.refl_trans]
  dsimp only [filtrationPow.mulIso_hom, NatIso.app_inv, Functor.mapIso_inv, pow_obj,
    ProFiltPseuNormGrpWithTinv.coe_of, filtration_map_app]
  ext x i : 3
  erw [comp_apply, comp_apply]
  dsimp only [filtration_obj_map_apply, powPowX_hom_apply, ContinuousMap.coe_mk,
    ComphausFilteredPseudoNormedGroupWithTinvHom.level_coe, Subtype.coe_mk, Filtration.castLe_apply,
    PseudoNormedGroup.coe_castLe, BasicUniversalMap.evalFP, BasicUniversalMap.evalPng₀,
    ProFiltPseuNormGrpWithTinv.pow_map, ProfinitelyFilteredPseudoNormedGroupWithTinv.piMap_to_fun]
  rw [← ComphausFilteredPseudoNormedGroupHom.coe_toAddMonoidHom, ←
    ComphausFilteredPseudoNormedGroupHom.toAddMonoidHomHom_apply]
  simp only [PolyhedralLatticeCat.homSum_apply, AddMonoidHom.map_sum, AddMonoidHom.finset_sum_apply,
    Finset.sum_apply]
  apply Fintype.sum_congr
  intro j
  simp only [ComphausFilteredPseudoNormedGroupHom.coe_toAddMonoidHom,
    ComphausFilteredPseudoNormedGroupHom.toAddMonoidHomHom_apply,
    BasicUniversalMap.evalPng_apply, ProFiltPseuNormGrpWithTinv.powPowX_hom_to_fun,
    ProFiltPseuNormGrpWithTinv.powPowXEquiv_symm_apply, Equiv.invFun_as_coe, Equiv.symm_symm,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.arrowCongr_apply, Function.comp,
    Equiv.refl_apply, Equiv.curry_symm_apply, Function.uncurry, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  rw [← fin_prod_fin_equiv.sum_comp]; swap; · infer_instance
  simp only [BasicUniversalMap.proj, Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.punitProd_symm_apply, Matrix.kronecker, Matrix.one_apply,
    BasicUniversalMap.projAux, Equiv.symm_apply_apply, boole_mul, ← ite_and, @eq_comm _ i,
    boole_mul, Matrix.kroneckerMap, Subtype.val_eq_coe]
  simp_rw [ite_smul, one_smul, zero_smul]
  convert (Finset.sum_ite_eq' Finset.univ (j, i) fun p => x.val p.2 p.1).symm using 2
  · simp only [Finset.mem_univ, if_true, Subtype.val_eq_coe]
  · ext ⟨a, b⟩
    split_ifs
    any_goals rfl
    all_goals rw [← Prod.mk.inj_iff, Prod.mk.eta] at h ; tauto

theorem foo (N : ℕ) [Fact (0 < N)] (Λ : PolyhedralLatticeCat.{u})
    (M : ProFiltPseuNormGrpWithTinv.{u} r') (c₁ c₂ : ℝ≥0) (hc : c₁ * N⁻¹ = c₂) (i : ℕ)
    [H : UniversalMap.Suitable c₂ c₁ (UniversalMap.sum i N)] :
    (cLC V).map ((filtrationPow r' c₁ i).op.map (Λ.homSum N r' M).op) ≫
        (cLC V).map
          (filtrationPowRescaleIso c₁ (ProFiltPseuNormGrpWithTinv.of r' (hom Λ M ^ N)) i N ≪≫
                filtrationCastEq r' (c₁ * N⁻¹) c₂ hc
                  ((ProFiltPseuNormGrpWithTinv.pow r' i).obj
                    (ProFiltPseuNormGrpWithTinv.of r' (hom Λ M ^ N)))).op.inv =
      (UniversalMap.evalCLCFP V r' c₁ c₂ (UniversalMap.sum i N)).app (op (hom Λ M)) ≫
        (cLC V).map (filtrationPow.mulIso.{u, u} r' c₂ (hom Λ M) N i).op.hom :=
  by
  rw [← (cLC V).map_comp]
  dsimp only [filtrationPow, CategoryTheory.Functor.op_map, CategoryTheory.Functor.comp_map,
    filtrationCastEq, Quiver.Hom.unop_op]
  rw [Iso.op_inv, quux, ← (cLC V).map_comp, Iso.op_hom, ← op_comp, ← op_comp]
  swap; · exact @BasicUniversalMap.suitable_of_suitable_of _ _ _ _ _ H
  congr 2
  apply bar

theorem rowMap_eq_sum_comp (N : ℕ) [Fact (0 < N)] (N' : ℝ≥0) (h : N' = N)
    [∀ i : ℕ, UniversalMap.Suitable (rescaleConstants κ N' i) (κ i) ((BD.Sum N).f i)]
    (Λ : PolyhedralLatticeCat.{u}) (M : ProFiltPseuNormGrpWithTinv.{u} r') :
    (Thm95.doubleComplex BD κ r r' V Λ M N).rowMap 0 1 =
      (Iso.refl ((BD.system κ r V r').obj (op (hom Λ M)))).inv ≫
        (bDSystemMap (BD.Sum N) κ (rescaleConstants κ N') r V).app (op (hom Λ M)) ≫
          (Thm95.mulRescaleIsoRowOne BD κ r V N N' h Λ M).hom :=
  by
  subst h
  dsimp only [Iso.refl_inv]
  erw [Category.id_comp]
  rw [← Iso.comp_inv_eq]
  rw [Thm95.doubleComplex.rowMap_zero_one]
  dsimp only [Thm95.mulRescaleIsoRowOne, Iso.trans_inv, NatTrans.comp_app, Functor.mapIso_inv]
  simp only [← Category.assoc, ← (BD.system κ r V r').map_comp, ← NatTrans.comp_app, Iso.op_inv, ←
    op_comp, PolyhedralLatticeCat.cechAugmentationMap_eq_homSum]
  rw [Iso.comp_inv_eq]
  ext c i : 4
  apply Arrow.mk_injective
  erw [NatTrans.comp_app, NatTrans.comp_app, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [BD_system_map_app_app, BD_map_app_f, Data.sum_f, Data.system_map, Data.complex,
    Data.complex₂_map_f, Thm95.mulSystemIso, systemRescaleIso, complexRescaleIso, Thm95.mulComplexIso]
  erw [NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.Hom.isoOfComponents_inv_f]
  dsimp only [cLCFPTinv₂, UniversalMap.evalCLCFPTinv₂, cLCTinv.mapIso_hom, cLCTinv.mapIso_inv,
    cLCTinv.f_map, _root_.id, cLCTinv.map, SemiNormedGroupCat.equalizer.mapNat_app, unop_op]
  rw [SemiNormedGroupCat.equalizer.map_comp_map, SemiNormedGroupCat.equalizer.map_comp_map]
  apply SemiNormedGroupCat.equalizer.map_congr
  · rw [foo]; rfl
  · rw [foo]; rfl
  all_goals rfl

end Thm95

