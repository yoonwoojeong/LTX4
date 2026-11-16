import LiquidTensorExperiment.BreenDeligne.Constants
import LiquidTensorExperiment.SystemOfComplexes.Completion
import LiquidTensorExperiment.Thm95.Homotopy
import LiquidTensorExperiment.Thm95.ColExact
import LiquidTensorExperiment.Thm95.RowIso
import LiquidTensorExperiment.CombinatorialLemma.Profinite

#align_import thm95.default

noncomputable section

universe u v

open scoped NNReal

-- enable the notation `ℝ≥0` for the nonnegative real numbers.
open PolyhedralLattice Opposite

open thm95.UniversalConstants SystemOfDoubleComplexes CategoryTheory BreenDeligne

open ProFiltPseuNormGrpWithTinv (of)

section

variable (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r' < 1)]

variable (BD : Package)

variable (V : SemiNormedGroupCat.{v}) [NormedWithAut r V]

variable (κ κ' : ℕ → ℝ≥0) [BD.data.VerySuitable r r' κ]

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

variable (m : ℕ)

variable (Λ : PolyhedralLatticeCat.{u})

def Thm95.IH (m : ℕ) : Prop :=
  ∀ Λ : PolyhedralLatticeCat.{u},
    ((BD.data.system κ r V r').obj (op <| Hom Λ M)).IsWeakBoundedExact (k κ' m) (K r r' BD κ' m) m
      (c₀ r r' BD κ κ' m Λ)

theorem nSCRowExact (IH : ∀ m' < m, Thm95.IH r r' BD V κ κ' M m') (h0m : 0 < m) (i : ℕ)
    (hi : i ≤ m + 1) :
    ((Thm95.doubleComplex BD.data κ r r' V Λ M (n r r' BD κ' m)).row i).IsWeakBoundedExact (k₁ κ' m)
      (k₁ r r' BD κ' m) (m - 1) (c₀ r r' BD κ κ' m Λ) :=
  by
  haveI h0m_ : Fact (0 < m) := ⟨h0m⟩
  have hm' : m - 1 < m := Nat.pred_lt h0m.ne'
  rcases i with (i | i | i)
  · rw [Thm95.doubleComplex.row_zero]
    refine' (IH (m - 1) hm' Λ).of_le BD.data.systemAdmissible _ _ le_rfl _
    pick_goal 3
    · apply c₀_mono
    all_goals infer_instance
  · rw [Thm95.doubleComplex.row_one]
    refine' (IH (m - 1) hm' _).of_le BD.data.systemAdmissible _ _ le_rfl _
    pick_goal 3
    · apply c₀_pred_le; exact h0m
    all_goals infer_instance
  · rw [Thm95.doubleComplex.row]
    apply SystemOfComplexes.rescaleIsWeakBoundedExact
    refine' (IH (m - 1) hm' _).of_le BD.data.systemAdmissible _ _ le_rfl _
    pick_goal 3
    · apply c₀_pred_le_of_le; exact hi
    all_goals infer_instance

variable [Package.Adept BD κ κ']

def nSCHtpy :
    NormedSpectralHomotopy ((Thm95.doubleComplex BD.data κ r r' V Λ M (n r r' BD κ' m)).rowMap 0 1)
      m (k' κ' m) (ε r r' BD κ' m) (c₀ r r' BD κ κ' m Λ) (h r r' BD κ' m) :=
  (nSHAux BD r r' V κ κ' m Λ (op (hom Λ M))).of_iso _ _ _ (Iso.refl _)
    (Thm95.mulRescaleIsoRowOne BD.data κ r V _ _ (by norm_cast) Λ M) (fun _ _ _ => rfl)
    (Thm95.mulRescaleIsoRowOne_strict BD.data κ r V _ _ (by norm_cast) Λ M)
    (by apply Thm95.rowMap_eq_sum_comp)

def nSC (IH : ∀ m' < m, Thm95.IH r r' BD V κ κ' M m')
    [PseudoNormedGroup.Splittable (Λ →+ M) (n r r' BD κ' m) (Lem98.d Λ (n r r' BD κ' m))] :
    NormedSpectralConditions (Thm95.doubleComplex BD.data κ r r' V Λ M (n r r' BD κ' m)) m (k₁ κ' m)
      (k₁ r r' BD κ' m) (k' κ' m) (ε r r' BD κ' m) (c₀ r r' BD κ κ' m Λ) (h r r' BD κ' m)
    where
  rowExact := nSCRowExact _ _ _ _ _ _ _ _ _ IH
  colExact := by
    let N := N r r' BD κ' m
    haveI : Fact (r < 1) := ⟨(Fact.out _ : r < r').trans (Fact.out _ : r' < 1)⟩
    intro j hj
    refine'
      Thm95.colExact BD.data κ r r' V Λ M N j (Lem98.d Λ N) (k₁_sqrt κ' m) m _ _ (k₁ κ' m)
        (K₁ r r' BD κ' m) (le_of_eq _) _ _ (c₀ r r' BD κ κ' m Λ) ⟨le_rfl⟩ inferInstance ⟨le_rfl⟩
    · apply c₀_spec; assumption'
    · ext; delta k₁_sqrt; dsimp; simp only [Real.mul_self_sqrt, NNReal.zero_le_coe]
    · apply K₁_spec
  htpy := nSCHtpy r r' BD V κ κ' M m Λ
  Admissible := Thm95.doubleComplexAdmissible _

/-- A variant of Theorem 9.5 in [Analytic] using weak bounded exactness. -/
theorem thm95' :
    ∀ (Λ : PolyhedralLatticeCat.{u}) (S : Type u) [Fintype S] (V : SemiNormedGroupCat.{v})
      [NormedWithAut r V],
      ((BD.data.system κ r V r').obj (op <| Hom Λ (Lbar r' S))).IsWeakBoundedExact (k κ' m)
        (K r r' BD κ' m) m (c₀ r r' BD κ κ' m Λ) :=
  by
  apply Nat.strong_induction_on m <;> clear m
  intro m IH Λ S _S_fin V _V_r
  haveI :
    PseudoNormedGroup.Splittable (Λ →+ of r' (Lbar r' S)) (N r r' BD κ' m)
      (Lem98.d Λ (N r r' BD κ' m)) :=
    lem98Finite Λ S (N r r' BD κ' m)
  let cond := nSC.{u} r r' BD V κ κ' (of r' <| Lbar r' S) m Λ _
  swap
  · intro m' hm' Λ
    apply IH; assumption
  exact SystemOfDoubleComplexes.normedSpectral cond

/-- A variant of Theorem 9.5 in [Analytic] using weak bounded exactness. -/
theorem thm95'.profinite :
    ∀ (Λ : PolyhedralLatticeCat.{u}) (S : Profinite.{u}) (V : SemiNormedGroupCat.{v})
      [NormedWithAut r V],
      ((BD.data.system κ r V r').obj
            (op <| Hom Λ ((Lbar.functor.{u, u} r').obj S))).IsWeakBoundedExact
        (k κ' m) (K r r' BD κ' m) m (c₀ r r' BD κ κ' m Λ) :=
  by
  apply Nat.strong_induction_on m <;> clear m
  intro m IH Λ S V _V_r
  haveI :
    PseudoNormedGroup.Splittable (Λ →+ of r' ((Lbar.functor.{u, u} r').obj S)) (N r r' BD κ' m)
      (Lem98.d Λ (N r r' BD κ' m)) :=
    Lem98.main r' Λ S (N r r' BD κ' m)
  let cond := nSC.{u} r r' BD V κ κ' (of r' <| (Lbar.functor.{u, u} r').obj S) m Λ _
  swap
  · intro m' hm' Λ
    apply IH; assumption
  exact SystemOfDoubleComplexes.normedSpectral cond

/-- Theorem 9.5 in [Analytic] -/
theorem thm95 (Λ : PolyhedralLatticeCat.{u}) (S : Type u) [Fintype S] (V : SemiNormedGroupCat.{v})
    [NormedWithAut r V] :
    ((BD.data.system κ r V r').obj (op <| hom Λ (Lbar r' S))).IsBoundedExact (k κ' m ^ 2)
      (k r r' BD κ' m + 1) m (c₀ r r' BD κ κ' m Λ) :=
  by
  refine'
    SystemOfComplexes.IsWeakBoundedExact.strongOfComplete _ (thm95' r r' BD κ κ' m Λ S V) _ 1
      zero_lt_one
  apply Data.systemAdmissible

/-- Theorem 9.5 in [Analytic] -/
theorem thm95.profinite (Λ : PolyhedralLatticeCat.{u}) (S : Profinite.{u})
    (V : SemiNormedGroupCat.{v}) [NormedWithAut r V] :
    ((BD.data.system κ r V r').obj (op <| hom Λ ((Lbar.functor.{u, u} r').obj S))).IsBoundedExact
      (k κ' m ^ 2) (k r r' BD κ' m + 1) m (c₀ r r' BD κ κ' m Λ) :=
  by
  refine'
    SystemOfComplexes.IsWeakBoundedExact.strongOfComplete _ (thm95'.profinite r r' BD κ κ' m Λ S V)
      _ 1 zero_lt_one
  apply Data.systemAdmissible

/-- Theorem 9.5 in [Analytic] -/
theorem Thm94.explicit (S : Profinite.{0}) (V : SemiNormedGroupCat.{v}) [NormedWithAut r V] :
    ((BD.data.system κ r V r').obj (op <| ⟨(Lbar.functor.{0, 0} r').obj S⟩)).IsBoundedExact
      (k κ' m ^ 2) (k r r' BD κ' m + 1) m (c₀ r r' BD κ κ' m ⟨ℤ⟩) :=
  by
  refine'
    (thm95.profinite r r' BD κ κ' m ⟨ℤ⟩ S V).of_iso
      ((BD.data.system κ r V r').mapIso (HomZ_iso ⟨(Lbar.functor.{0, 0} r').obj S⟩).symm.op) _
  intro c n
  rw [← SystemOfComplexes.apply_hom_eq_hom_apply]
  apply SemiNormedGroupCat.iso_isometry_of_normNoninc <;>
    apply BreenDeligne.Data.complex.map_normNoninc

end

/- ===
Once we have determined the final shape of the statement,
we can update the proof `thm95' → first_target`, and then delete the theorem below.
Now I just want flexibility in changing `thm95`
and not be troubled with fixing the proof of the implication.
=== -/
/-- Theorem 9.5 in [Analytic] -/
theorem thm95'' (BD : Package) (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')]
    [Fact (r' < 1)] (κ : ℕ → ℝ≥0) [BD.data.VerySuitable r r' κ] [∀ i : ℕ, Fact (0 < κ i)] :
    ∀ m : ℕ,
      ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)),
        ∀ (Λ : Type u) [PolyhedralLattice Λ],
          ∃ c₀ : ℝ≥0,
            ∀ (S : Type u) [Fintype S],
              ∀ (V : SemiNormedGroupCat.{v}) [NormedWithAut r V],
                SystemOfComplexes.IsWeakBoundedExact
                  ((BD.data.system κ r V r').obj (op <| Hom Λ (Lbar r' S))) k K m c₀ :=
  by
  intro m
  let κ' := package.κ' BD κ
  haveI _inst_κ' : Package.Adept BD κ κ' := package.κ'_adept BD κ
  refine' ⟨k κ' m, K r r' BD κ' m, inferInstance, fun Λ _inst_Λ => _⟩
  refine' ⟨c₀ r r' BD κ κ' m (@PolyhedralLatticeCat.of Λ _inst_Λ), fun S _inst_S V _inst_V => _⟩
  apply thm95'

/-- Theorem 9.5 in [Analytic] -/
theorem thm95''.profinite (BD : Package) (r r' : ℝ≥0) [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')]
    [Fact (r' < 1)] (κ : ℕ → ℝ≥0) [BD.data.VerySuitable r r' κ] [∀ i : ℕ, Fact (0 < κ i)] :
    ∀ m : ℕ,
      ∃ (k K : ℝ≥0) (hk : Fact (1 ≤ k)),
        ∀ (Λ : Type u) [PolyhedralLattice Λ],
          ∃ c₀ : ℝ≥0,
            ∀ S : Profinite.{u},
              ∀ (V : SemiNormedGroupCat.{v}) [NormedWithAut r V],
                SystemOfComplexes.IsWeakBoundedExact
                  ((BD.data.system κ r V r').obj (op <| Hom Λ ((Lbar.functor.{u, u} r').obj S))) k K
                  m c₀ :=
  by
  intro m
  let κ' := package.κ' BD κ
  haveI _inst_κ' : Package.Adept BD κ κ' := package.κ'_adept BD κ
  refine' ⟨k κ' m, K r r' BD κ' m, inferInstance, fun Λ _inst_Λ => _⟩
  refine' ⟨c₀ r r' BD κ κ' m (@PolyhedralLatticeCat.of Λ _inst_Λ), fun S _inst_S V _inst_V => _⟩
  apply thm95'.profinite

