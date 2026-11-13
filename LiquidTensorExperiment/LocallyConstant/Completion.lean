import Mathlib.Topology.ContinuousFunction.Compact
import LiquidTensorExperiment.ForMathlib.SemiNormedGroup
import LiquidTensorExperiment.LocallyConstant.CompletionAux
import LiquidTensorExperiment.FreePfpng.Main
import LiquidTensorExperiment.Prop819

#align_import locally_constant.completion

noncomputable section

universe u

open CategoryTheory Opposite ProFiltPseuNormGrp₁

open Function (Surjective)

open scoped NNReal

variable (S : Profinite.{u})

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

variable (V' : Type u) [NormedAddCommGroup V'] [CompleteSpace V']

def lCC : Profinite.{u}ᵒᵖ ⥤ Ab.{u} :=
  SemiNormedGroupCat.lCC.obj V ⋙ forget₂ _ _

attribute [local instance] LocallyConstant.seminormedAddCommGroup LocallyConstant.pseudoMetricSpace

open UniformSpace

theorem ContinuousMap.bddAbove_range_norm (f : C(S, V')) :
    BddAbove (Set.range fun s : ↥S => ‖f s‖) :=
  (isCompact_range <| continuous_norm.comp f.continuous).BddAbove

def Condensed.ofTopAbMapNormedGroupHom {S T : Profinite.{u}ᵒᵖ} (f : S ⟶ T) :
    NormedAddGroupHom C(_, V') C(_, V')
    where
  toFun := (Condensed.OfTopAb.presheaf.{u} V').map f
  map_add' _ _ := AddMonoidHom.map_add _ _ _
  bound' := by
    refine' ⟨1, fun g => _⟩
    rw [one_mul, ContinuousMap.norm_eq_iSup_norm]
    cases isEmpty_or_nonempty.{u + 1} (unop T : Profinite)
    · simp only [Real.ciSup_empty]; apply norm_nonneg
    apply ciSup_le
    intro s
    rw [ContinuousMap.norm_eq_iSup_norm]
    exact le_ciSup (ContinuousMap.bddAbove_range_norm _ _ _) (f.unop s)

theorem Condensed.of_top_ab_map_continuous {S T : Profinite.{u}ᵒᵖ} (f : S ⟶ T) :
    @Continuous C(_, V') C(_, V') _ _ ((Condensed.OfTopAb.presheaf.{u} V').map f) :=
  (Condensed.ofTopAbMapNormedGroupHom V' f).continuous

theorem LocallyConstant.toContinuousMap_isometry :
    Isometry (LocallyConstant.toContinuousMap : LocallyConstant S V' → C(S, V')) :=
  by
  intro f g
  simp only [edist_dist, dist_eq_norm, ContinuousMap.norm_eq_iSup_norm, LocallyConstant.norm_def,
    LocallyConstant.toContinuousMap_eq_coe, ContinuousMap.coe_sub,
    LocallyConstant.coe_continuousMap, Pi.sub_apply]
  rfl

theorem LocallyConstant.toContinuousMap_uniformInducing :
    UniformInducing (LocallyConstant.toContinuousMap : LocallyConstant S V' → C(S, V')) :=
  (LocallyConstant.toContinuousMap_isometry S V').UniformInducing

theorem LocallyConstant.toContinuousMap_uniformContinuous :
    UniformContinuous (LocallyConstant.toContinuousMap : LocallyConstant S V' → C(S, V')) :=
  (LocallyConstant.toContinuousMap_uniformInducing S V').UniformContinuous

theorem LocallyConstant.toContinuousMap_denseRange :
    DenseRange (LocallyConstant.toContinuousMap : LocallyConstant S V' → C(S, V')) :=
  LocallyConstant.Density.loc_const_dense _

def LocallyConstant.pkg : AbstractCompletion (LocallyConstant S V')
    where
  Space := C(S, V')
  coe := LocallyConstant.toContinuousMap
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  UniformInducing := LocallyConstant.toContinuousMap_uniformInducing S V'
  dense := LocallyConstant.toContinuousMap_denseRange S V'

def lCCIsoCondOfTopAbEquiv : Completion (LocallyConstant S V') ≃ C(S, V') :=
  (@Completion.cPkg (LocallyConstant S V') _).compareEquiv (LocallyConstant.pkg S V')

def lCCIsoCondOfTopAbAddEquiv : Completion (LocallyConstant S V') ≃+ C(S, V') :=
  {
    lCCIsoCondOfTopAbEquiv S
      V' with
    toFun := Completion.extension LocallyConstant.toContinuousMap
    map_add' := by
      intro f g
      apply Completion.induction_on₂ f g
      · apply isClosed_eq
        · exact completion.continuous_extension.comp continuous_add
        ·
          exact
            (completion.continuous_extension.comp continuous_fst).add
              (completion.continuous_extension.comp continuous_snd)
      · clear f g; intro f g
        rw [← Completion.coe_add, Completion.extension_coe, Completion.extension_coe,
          Completion.extension_coe]
        · rfl
        all_goals apply LocallyConstant.toContinuousMap_uniformContinuous }

theorem LCC_iso_Cond_of_top_ab_natural {S T : Profinite.{u}} (f : S ⟶ T) :
    lCCIsoCondOfTopAbAddEquiv S V' ∘ Completion.map (LocallyConstant.comap f) =
      (Condensed.OfTopAb.presheaf.{u} V').map f.op ∘ lCCIsoCondOfTopAbAddEquiv T V' :=
  by
  dsimp [lCCIsoCondOfTopAbAddEquiv]
  apply Completion.ext
  · refine' completion.continuous_extension.comp Completion.continuous_map
  · refine' (Condensed.of_top_ab_map_continuous _ _).comp Completion.continuous_extension
  intro g
  ext s
  simp only [Function.comp_apply]
  rw [Completion.map_coe, Completion.extension_coe, Completion.extension_coe,
    LocallyConstant.toContinuousMap_eq_coe, LocallyConstant.coe_continuousMap,
    LocallyConstant.toContinuousMap_eq_coe, LocallyConstant.coe_comap]
  · rfl
  · exact f.continuous
  · apply LocallyConstant.toContinuousMap_uniformContinuous
  · apply LocallyConstant.toContinuousMap_uniformContinuous
  · exact (LocallyConstant.comapHom f f.2).UniformContinuous

def lCCIsoCondOfTopAb : lCC.{u} V ≅ Condensed.OfTopAb.presheaf.{u} V :=
  NatIso.ofComponents
    (fun S => AddEquiv.toAddCommGroupCatIso <| lCCIsoCondOfTopAbAddEquiv (unop S) V)
    (by
      intro S T f
      ext1 φ
      have := LCC_iso_Cond_of_top_ab_natural V f.unop
      convert congr_fun this φ using 1
      clear this
      delta lCC SemiNormedGroupCat.lCC
      simp only [AddEquiv.to_AddCommGroup_iso_hom, CategoryTheory.comp_apply,
        AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_eq_iff_eq, Functor.comp_map, curry_obj_obj_map,
        uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
        SemiNormedGroupCat.locallyConstant_obj_map, SemiNormedGroupCat.completion_map]
      erw [Category.id_comp]
      rfl)

def condensedLCC : Condensed.{u} Ab.{u + 1}
    where
  val := lCC.{u} V ⋙ Ab.ulift.{u + 1}
  cond := by
    let e := lCCIsoCondOfTopAb V
    let e' := CategoryTheory.isoWhiskerRight e Ab.ulift.{u + 1}
    apply presheaf.isSheaf_of_iso proetaleTopology.{u} e'
    exact (Condensed.ofTopAb _).2

def condensedLCCIsoOfTopAb : condensedLCC V ≅ Condensed.ofTopAb V :=
  Sheaf.Iso.mk _ _ <| isoWhiskerRight (lCCIsoCondOfTopAb _) _

