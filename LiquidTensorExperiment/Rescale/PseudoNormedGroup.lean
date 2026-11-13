import LiquidTensorExperiment.PseudoNormedGroup.Category.Default
import LiquidTensorExperiment.Rescale.Basic

#align_import rescale.pseudo_normed_group

noncomputable section

open scoped NNReal

namespace Rescale

open PseudoNormedGroup

variable (r r' : ℝ≥0) (M : Type _)

section PseudoNormedGroup

variable [PseudoNormedGroup M]

instance : PseudoNormedGroup (Rescale r M)
    where
  filtration c := show Set M from filtration M (c * r⁻¹)
  filtration_mono c₁ c₂ h := filtration_mono (mul_le_mul' h le_rfl)
  zero_mem_filtration c := @zero_mem_filtration M _ _
  neg_mem_filtration c := @neg_mem_filtration M _ _
  add_mem_filtration c₁ c₂ := by simp only [add_mul]; apply add_mem_filtration

theorem mem_filtration (x : Rescale r M) (c : ℝ≥0) :
    x ∈ filtration (Rescale r M) c ↔ of.symm x ∈ filtration M (c * r⁻¹) :=
  Iff.rfl

theorem mem_filtration' (x : Rescale r M) (c : ℝ≥0) [Fact (0 < r)] :
    of x ∈ filtration (Rescale r M) c ↔ x ∈ filtration M (c * r⁻¹) :=
  Iff.rfl

def toRescaleOneStrictPseudoNormedGroupHom : StrictPseudoNormedGroupHom M (Rescale 1 M)
    where
  toFun := Rescale.of
  map_zero' := rfl
  map_add' _ _ := rfl
  strict' c x hx := by rwa [mem_filtration', inv_one, mul_one]

def ofRescaleOneStrictPseudoNormedGroupHom : StrictPseudoNormedGroupHom (Rescale 1 M) M
    where
  toFun := Rescale.of.symm
  map_zero' := rfl
  map_add' _ _ := rfl
  strict' c x hx := by rwa [mem_filtration, inv_one, mul_one] at hx 

-- def of_to_rescale_one_comp_eq_id [fact (0 < r)] [fact (0 < r')] :
--   (of_rescale_one_strict_pseudo_normed_group_hom M).comp
--   (to_rescale_one_strict_pseudo_normed_group_hom M) =
--   strict_pseudo_normed_group_hom.id (rescale 1 M) :=
-- rfl
-- def to_of_rescale_one_comp_eq_id [fact (0 < r)] [fact (0 < r')] :
--   (to_rescale_one_strict_pseudo_normed_group_hom M).comp
--   (of_rescale_one_strict_pseudo_normed_group_hom M) =
--   strict_pseudo_normed_group_hom.id M :=
-- rfl
def ofRescaleEqStrictPseudoNormedGroupHom [Fact (0 < r)] [Fact (0 < r')] (h : r = r') :
    StrictPseudoNormedGroupHom (Rescale r M) (Rescale r' M)
    where
  toFun m := Rescale.of (Rescale.of.symm m)
  map_zero' := rfl
  map_add' _ _ := rfl
  strict' c x hx := by rwa [mem_filtration', ← h, ← mem_filtration r M]

def ofRescaleRescaleStrictPseudoNormedGroupHom [Fact (0 < r)] [Fact (0 < r')] :
    StrictPseudoNormedGroupHom (Rescale r (Rescale r' M)) (Rescale (r' * r) M)
    where
  toFun m := Rescale.of (Rescale.of.symm (Rescale.of.symm m))
  map_zero' := rfl
  map_add' _ _ := rfl
  strict' c x hx := by rwa [mem_filtration', mul_inv_rev, ← mul_assoc]

def toRescaleRescaleStrictPseudoNormedGroupHom [Fact (0 < r)] [Fact (0 < r')] :
    StrictPseudoNormedGroupHom (Rescale (r' * r) M) (Rescale r (Rescale r' M))
    where
  toFun m := Rescale.of (Rescale.of (Rescale.of.symm m))
  map_zero' := rfl
  map_add' _ _ := rfl
  strict' c x hx := by
    rwa [mem_filtration' r (Rescale r' M), mem_filtration', mul_assoc, ← mul_inv_rev, ←
      mem_filtration (r' * r) M]

-- def of_to_rescale_rescale_comp_eq_id [fact (0 < r)] [fact (0 < r')] :
--   (of_rescale_rescale_strict_pseudo_normed_group_hom r r' M).comp
--   (to_rescale_rescale_strict_pseudo_normed_group_hom r r' M) =
--   strict_pseudo_normed_group_hom.id (rescale r (rescale r' M)) :=
-- rfl
-- def to_of_rescale_rescale_comp_eq_id' [fact (0 < r)] [fact (0 < r')] :
--   (to_rescale_rescale_strict_pseudo_normed_group_hom r r' M).comp
--   (of_rescale_rescale_strict_pseudo_normed_group_hom r r' M) =
--   strict_pseudo_normed_group_hom.id (rescale (r' * r) M) :=
-- rfl
end PseudoNormedGroup

--Should we change name to this section? But one for the comphaus_fil.. and one for the
--profinitely_filt.. seems a lot
section ProfinitelyFilteredPseudoNormedGroup

open ComphausFilteredPseudoNormedGroup ProfinitelyFilteredPseudoNormedGroup

instance [ComphausFilteredPseudoNormedGroup M] : ComphausFilteredPseudoNormedGroup (Rescale r M)
    where
  topology := by delta Rescale; infer_instance
  t2 := by delta Rescale; infer_instance
  compact := by delta Rescale; infer_instance
  continuous_add' := by
    intro c₁ c₂
    haveI : Fact ((c₁ + c₂) * r⁻¹ ≤ c₁ * r⁻¹ + c₂ * r⁻¹) := ⟨(add_mul _ _ _).le⟩
    rw [(embedding_cast_le ((c₁ + c₂) * r⁻¹) (c₁ * r⁻¹ + c₂ * r⁻¹)).continuous_iff]
    exact continuous_add' (c₁ * r⁻¹) (c₂ * r⁻¹)
  continuous_neg' c := continuous_neg' _
  continuous_castLe c₁ c₂ h := continuous_cast_le _ _

instance [ProfinitelyFilteredPseudoNormedGroup M] :
    ProfinitelyFilteredPseudoNormedGroup (Rescale r M) where

@[simps]
def mapComphausFilteredPseudoNormedGroupHom {M₁ M₂ : Type _} [ComphausFilteredPseudoNormedGroup M₁]
    [ComphausFilteredPseudoNormedGroup M₂] (N : ℝ≥0)
    (f : ComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    ComphausFilteredPseudoNormedGroupHom (Rescale N M₁) (Rescale N M₂)
    where
  toFun := Rescale.of ∘ f ∘ Rescale.of.symm
  map_zero' := f.map_zero
  map_add' x y := f.map_add x y
  bound' := by
    obtain ⟨C, hC⟩ := f.bound
    refine' ⟨C, fun c x hx => _⟩
    rw [Rescale.mem_filtration] at hx ⊢
    simp only [Function.comp_apply, Equiv.symm_apply_apply, mul_assoc]
    exact hC hx
  continuous' c₁ c₂ f₀ hf₀ := f.Continuous f₀ hf₀

@[simps]
def mapStrictComphausFilteredPseudoNormedGroupHom {M₁ M₂ : Type _}
    [ComphausFilteredPseudoNormedGroup M₁] [ComphausFilteredPseudoNormedGroup M₂] (N : ℝ≥0)
    (f : StrictComphausFilteredPseudoNormedGroupHom M₁ M₂) :
    StrictComphausFilteredPseudoNormedGroupHom (Rescale N M₁) (Rescale N M₂)
    where
  toFun := Rescale.of ∘ f ∘ Rescale.of.symm
  map_zero' := f.map_zero
  map_add' x y := f.map_add x y
  strict' c x hx := by
    rw [Rescale.mem_filtration] at hx ⊢
    simp only [Function.comp_apply, Equiv.symm_apply_apply, mul_assoc]
    exact f.strict hx
  continuous' c := f.continuous' _

end ProfinitelyFilteredPseudoNormedGroup

section ProfinitelyFilteredPseudoNormedGroupWithTinv

open ProfinitelyFilteredPseudoNormedGroupWithTinv

open ProfinitelyFilteredPseudoNormedGroup

variable [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M]

@[simps]
def tinv' : Rescale r M →+ Rescale r M
    where
  toFun x := of <| tinv <| of.symm x
  map_zero' := by delta Rescale; exact Tinv.map_zero
  map_add' := by delta Rescale; exact Tinv.map_add

theorem tinv'_mem_filtration (c : ℝ≥0) (x : Rescale r M) (hx : x ∈ filtration (Rescale r M) c) :
    (tinv' r r' M) x ∈ filtration (Rescale r M) (r'⁻¹ * c) := by
  simpa only [mem_filtration, Tinv'_apply, Equiv.symm_apply_apply, mul_assoc] using
    Tinv_mem_filtration _ _ hx

variable [Fact (0 < r')]

@[simps]
def tinv : ComphausFilteredPseudoNormedGroupHom (Rescale r M) (Rescale r M) :=
  ComphausFilteredPseudoNormedGroupHom.mk' (tinv' r r' M)
    (by
      refine' ⟨r'⁻¹, fun c => ⟨Tinv'_mem_filtration r r' M c, _⟩⟩
      haveI : Fact (c * r⁻¹ ≤ r' * (r'⁻¹ * c * r⁻¹)) :=
        ⟨by rw [mul_assoc, mul_inv_cancel_left₀ ‹Fact (0 < r')›.1.Ne.symm]⟩
      apply Tinv₀_continuous)

instance : ProfinitelyFilteredPseudoNormedGroupWithTinv r' (Rescale r M) :=
  {
    Rescale.profinitelyFilteredPseudoNormedGroup r
      M with
    tinv := Rescale.tinv r r' M
    tinv_mem_filtration := tinv'_mem_filtration r r' M }

@[simps]
def mapComphausFilteredPseudoNormedGroupWithTinvHom {M₁ M₂ : Type _}
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M₁]
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M₂] (N : ℝ≥0)
    (f : ComphausFilteredPseudoNormedGroupWithTinvHom r' M₁ M₂) :
    ComphausFilteredPseudoNormedGroupWithTinvHom r' (Rescale N M₁) (Rescale N M₂) :=
  {
    mapComphausFilteredPseudoNormedGroupHom N
      f.toComphausFilteredPseudoNormedGroupHom with
    toFun := Rescale.of ∘ f ∘ Rescale.of.symm
    strict' := fun c x hx => by
      rw [Rescale.mem_filtration] at hx ⊢
      simp only [Function.comp_apply, Equiv.symm_apply_apply, mul_assoc]
      exact f.strict hx
    map_Tinv' := f.map_tinv
    continuous' := fun c => f.continuous' (c * N⁻¹) }

end ProfinitelyFilteredPseudoNormedGroupWithTinv

end Rescale

namespace ProFiltPseuNormGrpWithTinv

variable (r' : ℝ≥0) [Fact (0 < r')]

@[simps]
def rescale (N : ℝ≥0) : ProFiltPseuNormGrpWithTinv r' ⥤ ProFiltPseuNormGrpWithTinv r'
    where
  obj M := of r' <| Rescale N M
  map M₁ M₂ f := Rescale.mapComphausFilteredPseudoNormedGroupWithTinvHom _ _ f

end ProFiltPseuNormGrpWithTinv

namespace ProFiltPseuNormGrpWithTinv₁

variable (r' : ℝ≥0) [Fact (0 < r')]

@[simps]
def rescale (N : ℝ≥0) [Fact (0 < N)] :
    ProFiltPseuNormGrpWithTinv₁ r' ⥤ ProFiltPseuNormGrpWithTinv₁ r'
    where
  obj M :=
    { M := Rescale N M
      exhaustive' := fun x =>
        by
        obtain ⟨c, hc⟩ := M.exhaustive r' (rescale.of.symm x)
        refine' ⟨c * N, _⟩
        rw [Rescale.mem_filtration]
        rwa [mul_inv_cancel_right₀]
        exact (Fact.out _ : 0 < N).ne' }
  map M₁ M₂ f := Rescale.mapComphausFilteredPseudoNormedGroupWithTinvHom _ _ f

@[simps]
def rescaleOut (N : ℝ≥0) [Fact (1 ≤ N)] : rescale r' N ⟶ 𝟭 _
    where app M :=
    { toFun := (Rescale.of.symm : Rescale N M → M)
      map_zero' := rfl
      map_add' := fun x y => rfl
      strict' := fun c x hx => PseudoNormedGroup.filtration_mono (Fact.out _) hx
      continuous' := fun c => ComphausFilteredPseudoNormedGroup.continuous_castLe (c * N⁻¹) c
      map_Tinv' := fun x => rfl }

end ProFiltPseuNormGrpWithTinv₁

