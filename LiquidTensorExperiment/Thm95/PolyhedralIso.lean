import LiquidTensorExperiment.PolyhedralLattice.Cosimplicial
import LiquidTensorExperiment.PolyhedralLattice.Hom
import LiquidTensorExperiment.SystemOfComplexes.Rescale
import LiquidTensorExperiment.Rescale.Tinv
import LiquidTensorExperiment.PseudoNormedGroup.SumHom

#align_import thm95.polyhedral_iso

universe u

noncomputable section

open scoped NNReal

attribute [local instance] typePow

open CategoryTheory

namespace PolyhedralLatticeCat

open SimplexCategory

open PolyhedralLattice (Conerve.l Conerve.Obj)

variable (Λ : PolyhedralLatticeCat.{u}) (N : ℕ) [Fact (0 < N)]

variable (r' : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv.{u} r')

-- TODO: we probably want some efficient constructor for these isomorphisms,
-- because the default has a lot of redundancy in the proof obligations
theorem augmentation_eq_diagonal :
    cosimplicialAugmentationMap Λ N ≫ (CechConerve.objZeroIso _).hom = diagonalEmbedding Λ N := by
  rw [← Iso.eq_comp_inv]; rfl

def homRescaleHom [Fact (0 < r')] :
    PolyhedralLattice.hom (Rescale N Λ) M ≃+
      (ProFiltPseuNormGrpWithTinv.of r' <| Rescale N (PolyhedralLattice.hom Λ M)) :=
  AddEquiv.refl _

theorem homRescaleHom_symm_apply [Fact (0 < r')] (x) : (homRescaleHom Λ N r' M).symm x = x :=
  rfl

theorem hom_rescale_hom_strict [Fact (0 < r')] (c : ℝ≥0)
    (f : PolyhedralLattice.hom (Rescale (↑N) Λ) M) :
    f ∈ PseudoNormedGroup.filtration (PolyhedralLattice.hom (Rescale (↑N) Λ) M) c ↔
      f ∈
        PseudoNormedGroup.filtration
          (ProFiltPseuNormGrpWithTinv.of r' (Rescale (↑N) (PolyhedralLattice.hom Λ M))) c :=
  by
  constructor
  · intro hf c' l hl
    rw [mul_assoc]
    refine' hf _
    simp only [SeminormedAddCommGroup.mem_filtration_iff]
    erw [Rescale.nnnorm_def, mul_comm, div_eq_mul_inv]
    refine' mul_le_mul' _ le_rfl
    exact hl
  · intro hf c' l hl
    apply PseudoNormedGroup.filtration_mono (le_of_eq _)
    convert hf _
    · exact ↑N * c'
    · simp only [SeminormedAddCommGroup.mem_filtration_iff] at hl ⊢
      erw [Rescale.nnnorm_def, div_eq_mul_inv] at hl 
      rwa [← inv_inv (N : ℝ≥0), ← NNReal.mul_le_iff_le_inv, mul_comm]
      apply ne_of_gt
      rw [nnreal.inv_pos]
      have hN : 0 < N := Fact.out _
      exact_mod_cast hN
    · rw [mul_assoc, inv_mul_cancel_left₀]
      have hN : 0 < N := Fact.out _
      exact_mod_cast hN.ne'

section

open ProfinitelyFilteredPseudoNormedGroup PolyhedralLattice ComphausFilteredPseudoNormedGroup

theorem homRescaleHom_ctu [Fact (0 < r')] (c : ℝ≥0) :
    Continuous
      (PseudoNormedGroup.level (homRescaleHom Λ N r' M)
        (fun c f => (hom_rescale_hom_strict Λ N r' M c f).1) c) :=
  by
  refine' (AddMonoidHom.continuous_iff _ _ _ _ _).mpr _
  intro l
  haveI : Fact (c * (nnnorm l * N⁻¹) ≤ c * N⁻¹ * nnnorm l) :=
    ⟨by rw [mul_comm (nnnorm _), mul_assoc]⟩
  have aux1 := AddMonoidHom.incl_continuous (Rescale N Λ) r' M c
  have aux2 := (continuous_apply (Rescale.of l)).comp aux1
  exact (ComphausFilteredPseudoNormedGroup.embedding_castLe (c * (nnnorm l * N⁻¹)) (c * N⁻¹ * nnnorm l)).continuous_iff.mp aux2

end

def homRescaleIso [Fact (0 < r')] :
    PolyhedralLattice.hom (Rescale N Λ) M ≅
      ProFiltPseuNormGrpWithTinv.of r' <| Rescale N (PolyhedralLattice.hom Λ M) :=
  @ProFiltPseuNormGrpWithTinv.isoOfEquivOfStrict' _ (PolyhedralLattice.hom (Rescale N Λ) M)
    (ProFiltPseuNormGrpWithTinv.of r' (Rescale N (PolyhedralLattice.hom Λ M)))
    (homRescaleHom Λ N r' M) (fun c f => hom_rescale_hom_strict Λ N r' M c f)
    (homRescaleHom_ctu Λ N r' M) fun x => rfl

@[simps (config := { fullyApplied := false }) apply symm_apply]
def homFinsuppEquiv [Fact (0 < r')] :
    PolyhedralLattice.hom (Fin N →₀ Λ) M ≃+
      (ProFiltPseuNormGrpWithTinv.of r' <| PolyhedralLattice.hom Λ M ^ N)
    where
  toFun (f : (Fin N →₀ Λ) →+ M) i :=
    { toFun := fun l => f (Finsupp.single i l)
      map_zero' := by rw [Finsupp.single_zero, f.map_zero]
      map_add' := fun l₁ l₂ => by rw [Finsupp.single_add, f.map_add] }
  map_add' f g := by ext i l; simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_mk, Pi.add_apply]
  invFun := fun f : (Λ →+ M) ^ N =>
    { toFun := fun x => x.Sum fun i l => f i l
      map_zero' := by rw [Finsupp.sum_zero_index]
      map_add' := fun x y => by
        simp only [Finsupp.sum_add_index', map_zero, eq_self_iff_true, imp_true_iff, map_add,
          forall₃_true_iff] }
  left_inv f := by
    ext i l; dsimp only
    simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_mk, AddMonoidHom.toFun_eq_coe,
      Finsupp.singleAddHom_apply, Function.comp_apply, AddMonoidHom.map_zero,
      Finsupp.sum_single_index]
    erw [Finsupp.sum_single_index]
    rw [Finsupp.single_zero, AddMonoidHom.map_zero]
  right_inv f := by
    ext i l; dsimp only
    simp only [AddMonoidHom.toFun_eq_coe, AddMonoidHom.coe_mk, Finsupp.sum_single_index,
      AddMonoidHom.map_zero]

section

open ProfinitelyFilteredPseudoNormedGroup PolyhedralLattice PseudoNormedGroup
  ComphausFilteredPseudoNormedGroup

theorem homFinsuppEquiv_strict [Fact (0 < r')] (c : ℝ≥0)
    (f : PolyhedralLattice.hom (Fin N →₀ Λ) M) :
    f ∈ filtration (PolyhedralLattice.hom (Fin N →₀ Λ) M) c ↔
      (Λ.homFinsuppEquiv N r' M) f ∈
        filtration (ProFiltPseuNormGrpWithTinv.of r' (PolyhedralLattice.hom Λ M ^ N)) c :=
  by
  constructor
  · intro hf i c' l hl
    refine' hf _
    rw [SeminormedAddCommGroup.mem_filtration_iff, Finsupp.nnnorm_def, Finsupp.sum_single_index]
    · exact hl
    · exact nnnorm_zero
  · intro hf c' l hl
    let g := (Λ.Hom_finsupp_equiv N r' M) f
    have hg : (Λ.Hom_finsupp_equiv N r' M).symm g = f := AddEquiv.symm_apply_apply _ _
    rw [SeminormedAddCommGroup.mem_filtration_iff, Finsupp.nnnorm_def, Finsupp.sum_fintype] at hl 
    swap; · intro; exact nnnorm_zero
    rw [← hg, Hom_finsupp_equiv_symm_apply, AddMonoidHom.coe_mk, Finsupp.sum_fintype]
    swap; · intro; exact AddMonoidHom.map_zero _
    apply filtration_mono (mul_le_mul' le_rfl hl)
    rw [Finset.mul_sum]
    apply sum_mem_filtration
    rintro i hi
    apply hf _
    exact (SeminormedAddCommGroup.mem_filtration_iff _ _).mpr rfl.le

theorem homFinsuppEquiv_ctu [Fact (0 < r')] (c : ℝ≥0) :
    Continuous
      (level (Λ.homFinsuppEquiv N r' M) (fun c x => (homFinsuppEquiv_strict Λ N r' M c x).1) c) :=
  by
  rw [continuous_induced_rng]
  rw [continuous_pi_iff]
  intro i
  dsimp only [Function.comp]
  rw [AddMonoidHom.continuous_iff]
  intro l
  haveI : Fact (c * ‖Finsupp.single i l‖₊ ≤ c * ‖l‖₊) :=
    ⟨mul_le_mul' le_rfl <| le_of_eq _⟩
  · have aux1 := AddMonoidHom.incl_continuous (Fin N →₀ Λ) r' M c
    have aux2 := (continuous_apply (Finsupp.single i l)).comp aux1
    rwa [(ComphausFilteredPseudoNormedGroup.embedding_castLe (c * ‖Finsupp.single i l‖₊)
          (c * ‖l‖₊)).continuous_iff] at
      aux2 
  · rw [Finsupp.nnnorm_def, Finsupp.sum_single_index]; exact nnnorm_zero

end

@[simps]
def homFinsuppIso [Fact (0 < r')] :
    PolyhedralLattice.hom (Fin N →₀ Λ) M ≅
      ProFiltPseuNormGrpWithTinv.of r' <| PolyhedralLattice.hom Λ M ^ N :=
  ProFiltPseuNormGrpWithTinv.isoOfEquivOfStrict' (homFinsuppEquiv _ _ _ _)
    (homFinsuppEquiv_strict Λ N r' M) (homFinsuppEquiv_ctu Λ N r' M) (by intro; ext1; rfl)

open Opposite

section

variable [Fact (0 < r')] (N' : ℝ≥0)

def homCosimplicialZeroIso' :
    (hom M).obj (op <| of <| Rescale N (of (Fin N →₀ Λ))) ≅
      (hom M).obj (op <| (Λ.cosimplicial N).obj (mk 0)) :=
  (hom M).mapIso <| (CechConerve.objZeroIso _).op

def homCosimplicialZeroIsoAux (h : N' = N) :
    ProFiltPseuNormGrpWithTinv.of r' (Rescale N (PolyhedralLattice.hom Λ M)) ≅
      (ProFiltPseuNormGrpWithTinv.rescale r' N').obj (PolyhedralLattice.hom Λ M) :=
  by rw [h]; exact iso.refl _

@[simp]
theorem homCosimplicialZeroIsoAux_rfl : homCosimplicialZeroIsoAux Λ N r' M N rfl = Iso.refl _ :=
  rfl

def homCosimplicialZeroIso (h : N' = N) :
    PolyhedralLattice.hom ((Λ.cosimplicial N).obj (SimplexCategory.mk 0)) M ≅
      ProFiltPseuNormGrpWithTinv.of r' (Rescale N' (PolyhedralLattice.hom Λ M ^ N)) :=
  (homCosimplicialZeroIso' Λ N r' M).symm ≪≫-- jmc is not very proud of this
      (iso.refl _ : _) ≪≫
      homRescaleIso (of (Fin N →₀ Λ)) N r' M ≪≫
        homCosimplicialZeroIsoAux _ _ _ _ _ h ≪≫
          (ProFiltPseuNormGrpWithTinv.rescale r' N').mapIso (homFinsuppIso Λ N r' M)

end

variable [Fact (0 < r')] [Fact (r' ≤ 1)]

open scoped BigOperators

def unrescale (N : ℝ≥0) (M : Type _) [ProfinitelyFilteredPseudoNormedGroup M] :
    ComphausFilteredPseudoNormedGroupHom (Rescale N M) M :=
  ComphausFilteredPseudoNormedGroupHom.mkOfBound (AddMonoidHom.id _) N⁻¹
    (by
      intro c
      refine' ⟨fun x hx => _, _⟩
      · rwa [mul_comm]
      · haveI : Fact (c * N⁻¹ ≤ N⁻¹ * c) := ⟨(mul_comm _ _).le⟩
        exact ComphausFilteredPseudoNormedGroup.continuous_castLe (c * N⁻¹) (N⁻¹ * c))

def rescaleProj (N : ℕ) (M : Type _) [ProfinitelyFilteredPseudoNormedGroup M] (i : Fin N) :
    ComphausFilteredPseudoNormedGroupHom (Rescale N (M ^ N)) M :=
  (ComphausFilteredPseudoNormedGroup.piProj i).comp (unrescale N _)

theorem rescaleProjBoundBy (N : ℕ) (M : Type _) [ProfinitelyFilteredPseudoNormedGroup M]
    (i : Fin N) : (rescaleProj N M i).BoundBy N⁻¹ := by intro c x hx;
  rw [Rescale.mem_filtration, mul_comm] at hx ; exact hx i

def homSum :
    ProFiltPseuNormGrpWithTinv.of r' (Rescale N ((Λ →+ M) ^ N)) ⟶
      ProFiltPseuNormGrpWithTinv.of r' (Λ →+ M) :=
  ProfinitelyFilteredPseudoNormedGroupWithTinv.sumHom (Λ →+ M) N

theorem homSum_apply (x) : homSum Λ N r' M x = ∑ i, x i :=
  ProfinitelyFilteredPseudoNormedGroupWithTinv.sumHom_apply _ _ _

theorem finsupp_sum_diagonalEmbedding (f : (Λ →+ M) ^ N) (l : Λ) :
    (Finsupp.sum ((Λ.diagonalEmbedding N) l) fun i => f i) =
      (show Λ → M from show Λ →+ M from Λ.homSum N r' M f) l :=
  by
  simp only [AddMonoidHom.coe_mk, Hom_sum_apply]
  rw [Finsupp.sum_fintype, AddMonoidHom.finset_sum_apply, Fintype.sum_congr]
  · intro i
    dsimp only [PolyhedralLatticeCat.diagonalEmbedding, PolyhedralLatticeHom.coe_mk, Finsupp.singleAddHom_apply,
      Rescale.of, Equiv.coe_refl, id]
    simp only [Finset.sum_apply', Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  · intro i; exact (f i).map_zero

end PolyhedralLatticeCat

