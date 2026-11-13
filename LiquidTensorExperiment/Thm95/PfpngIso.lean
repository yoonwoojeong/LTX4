import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.Rescale.PseudoNormedGroup

#align_import thm95.pfpng_iso

open scoped NNReal

attribute [local instance] typePow

noncomputable section

open CategoryTheory

namespace ProFiltPseuNormGrpWithTinv

variable (r' : ℝ≥0) [Fact (0 < r')]

variable (c : ℝ≥0) (m n : ℕ)

variable (M : ProFiltPseuNormGrpWithTinv r')

local notation "ρ" => Rescale

/-
Useful facts that we already have:

* `Pow_mul (r') (N n : ℕ) : Pow r' (N * n) ≅ Pow r' N ⋙ Pow r' n`
* `iso_of_equiv_of_strict'` for constructing isos in `ProFiltPseuNormGrpWithTinv r'`
-/
open ComphausFilteredPseudoNormedGroup

@[simps (config := { fullyApplied := false })]
def powMulCommObjEquiv (X : ProFiltPseuNormGrpWithTinv r') : X ^ (m * n) ≃+ X ^ (n * m) :=
  (LinearEquiv.funCongrLeft ℤ X <|
      calc
        Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
        _ ≃ Fin m × Fin n := (Equiv.prodComm _ _)
        _ ≃ Fin (m * n) := finProdFinEquiv).toAddEquiv

theorem powMulCommObjEquiv_strict (X : ProFiltPseuNormGrpWithTinv r') (c : ℝ≥0)
    (x : (X : Type _) ^ (m * n)) :
    x ∈ PseudoNormedGroup.filtration (↥(of r' (↥X ^ (m * n)))) c ↔
      (powMulCommObjEquiv r' m n X) x ∈ PseudoNormedGroup.filtration (↥X ^ (n * m)) c :=
  by
  intros
  simp only [Pow_mul_comm_obj_equiv_apply, LinearEquiv.trans_apply, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.funCongrLeft_apply, LinearEquiv.funCongrLeft_comp]
  erw [PseudoNormedGroup.mem_filtration_pi]
  -- TODO arrange so that `simp` can achieve this
  erw [PseudoNormedGroup.mem_filtration_pi]
  fconstructor
  · intro h i
    apply h
  · intro h i
    simpa [-finProdFinEquiv_symm_apply] using h (finProdFinEquiv (fin_prod_fin_equiv.symm i).symm)

theorem powMulCommObjEquiv_ctu (X : ProFiltPseuNormGrpWithTinv r') (c : ℝ≥0) :
    Continuous
      (PseudoNormedGroup.level (⇑(powMulCommObjEquiv r' m n X))
        (fun c x => (powMulCommObjEquiv_strict r' _ _ X c x).mp) c) :=
  by
  rw [← (filtration_pi_homeo _ c).comp_continuous_iff, ←
    (filtration_pi_homeo _ c).symm.comp_continuous_iff']
  apply continuous_pi
  intro i
  dsimp [-finProdFinEquiv_symm_apply]
  convert continuous_apply (finProdFinEquiv (fin_prod_fin_equiv.symm i).symm) using 1
  ext x
  rw [Subtype.coe_mk]

@[simps (config := { fullyApplied := false })]
def powMulCommObj (X : ProFiltPseuNormGrpWithTinv r') : of r' (X ^ (m * n)) ≅ of r' (X ^ (n * m)) :=
  isoOfEquivOfStrict' (powMulCommObjEquiv r' _ _ X) (powMulCommObjEquiv_strict r' _ _ X)
    (powMulCommObjEquiv_ctu r' _ _ X) (by intros; ext; rfl)

def powMulComm : pow r' (m * n) ≅ pow r' (n * m) :=
  NatIso.ofComponents (fun X => powMulCommObj r' _ _ X)
    (by
      intro X Y f; ext x i
      -- This is just a terminal simp, which I've exploded for the sake of speed.
      simp only [Pow_mul_comm_obj_hom_to_fun,
        ProFiltPseuNormGrpWithTinv.isoOfEquivOfStrict'_hom_apply,
        ProFiltPseuNormGrpWithTinv.pow_map, LinearEquiv.trans_apply,
        ProFiltPseuNormGrpWithTinv.coe_comp_apply, LinearMap.funLeft_apply,
        LinearEquiv.coe_toAddEquiv, id.def, Equiv.prodComm_apply, LinearEquiv.funCongrLeft_apply,
        LinearEquiv.funCongrLeft_comp, ProfinitelyFilteredPseudoNormedGroupWithTinv.piMap_to_fun])

def powComm : pow r' m ⋙ pow r' n ≅ pow r' n ⋙ pow r' m :=
  calc
    pow r' m ⋙ pow r' n ≅ pow r' (m * n) := (powMul r' m n).symm
    _ ≅ pow r' (n * m) := (powMulComm r' m n)
    _ ≅ pow r' n ⋙ pow r' m := powMul r' n m

@[simps]
def powRescaleAux (c : ℝ≥0) (m : ℕ) (X : ProFiltPseuNormGrpWithTinv r') :
    ρ c (X ^ m) ≃+ ρ c X ^ m :=
  AddEquiv.refl _

theorem powRescaleAux_ctu (X : ProFiltPseuNormGrpWithTinv r') (c' : ℝ≥0) :
    Continuous (PseudoNormedGroup.level (⇑(powRescaleAux r' c m X)) (fun _ _ => id) c') :=
  by
  erw [← (filtration_pi_homeo _ _).comp_continuous_iff, ←
    (filtration_pi_homeo _ _).symm.comp_continuous_iff']
  apply continuous_pi
  intro i
  dsimp
  convert continuous_apply i
  ext
  rw [Subtype.coe_mk]

def powRescale : pow r' m ⋙ rescale r' c ≅ rescale r' c ⋙ pow r' m :=
  NatIso.ofComponents
    (fun X => by
      dsimp
      fapply iso_of_equiv_of_strict'
      apply Pow_rescale_aux
      · intro c' x
        erw [PseudoNormedGroup.mem_filtration_pi]
      -- err, why does that close the goal?
      · apply Pow_rescale_aux_ctu
      · intro x; ext i; rfl)
    (by
      intro X Y f; ext x i
      dsimp
      rfl)

/-- A very specific isomorphism -/
def powRescalePowIso : pow r' m ⋙ rescale r' c ⋙ pow r' n ≅ pow r' n ⋙ pow r' m ⋙ rescale r' c :=
  calc
    pow r' m ⋙ rescale r' c ⋙ pow r' n ≅ pow r' m ⋙ pow r' n ⋙ rescale r' c :=
      isoWhiskerLeft (pow r' m) (powRescale r' c n).symm
    _ ≅ (pow r' m ⋙ pow r' n) ⋙ rescale r' c := (Functor.associator _ _ _).symm
    _ ≅ (pow r' n ⋙ pow r' m) ⋙ rescale r' c := (isoWhiskerRight (powComm r' m n) _)
    _ ≅ pow r' n ⋙ pow r' m ⋙ rescale r' c := Functor.associator _ _ _

end ProFiltPseuNormGrpWithTinv

