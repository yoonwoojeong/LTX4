import LiquidTensorExperiment.PolyhedralLattice.PseudoNormedGroup
import LiquidTensorExperiment.PolyhedralLattice.Int
import LiquidTensorExperiment.PolyhedralLattice.Category
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import PolyhedralLattice.hom

/-!

# Category-theoretic Hom(Λ, M)

If Λ is a polyhedral lattice then Hom(Λ, -) is a functor from profinitely filtered
pseudo-normed groups equipped with T⁻¹ to itself. Furthermore, if Λ = ℤ then this
functor is isomorphic to the identity functor.

-/


noncomputable section

universe u

open scoped NNReal

-- enable the notation `ℝ≥0` for the nonnegative real numbers.
open ProFiltPseuNormGrpWithTinv (of)

/-- The additive group homomorphisms `Λ →+ M` as an object of `ProFiltPseuNormGrpWithTinv r'`. -/
def PolyhedralLattice.hom {r' : ℝ≥0} [Fact (0 < r')] (Λ M : Type _) [PolyhedralLattice Λ]
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] : ProFiltPseuNormGrpWithTinv r' :=
  of r' (Λ →+ M)

namespace PolyhedralLatticeCat

open Opposite PseudoNormedGroup PolyhedralLattice ProfinitelyFilteredPseudoNormedGroup
  ComphausFilteredPseudoNormedGroup

open CategoryTheory

variable {r' : ℝ≥0} [Fact (0 < r')]

/-- Like `polyhedral_lattice.Hom` but functorial in the first entry.
Unfortunately, this means that the entries are now swapped.
So `(PolyhedralLattice.Hom M).obj (op Λ) = Λ →+ M`. -/
@[simps]
def hom (M : ProFiltPseuNormGrpWithTinv r') : PolyhedralLatticeCatᵒᵖ ⥤ ProFiltPseuNormGrpWithTinv r'
    where
  obj Λ := hom Λ.unop M
  map Λ₁ Λ₂ f :=
    { toFun := fun g => g.comp f.unop.toAddMonoidHom
      map_zero' := AddMonoidHom.zero_comp _
      map_add' := fun g₁ g₂ => AddMonoidHom.add_comp _ _ _
      strict' := fun c g hg c' l hl => hg ((f.unop.strict_nnnorm _).trans hl)
      continuous' := fun c => by
        rw [AddMonoidHom.continuous_iff]
        intro l
        haveI : Fact (‖f.unop l‖₊ ≤ ‖l‖₊) := ⟨f.unop.strict_nnnorm l⟩
        have aux :=
          (continuous_apply (f.unop l)).comp (AddMonoidHom.incl_continuous Λ₁.unop r' M c)
        rwa [(ComphausFilteredPseudoNormedGroup.embedding_castLe (c * ‖f.unop l‖₊) (c * ‖l‖₊)).continuous_iff] at
          aux 
      map_Tinv' := fun g => by ext l; rfl }
  map_id Λ := by ext; rfl
  map_comp := by intros; ext; rfl

end PolyhedralLatticeCat

namespace PolyhedralLattice

/-!
In the remainder of the file, we show that `Hom(ℤ, M)` is isomorphic to `M`.
-/


open PseudoNormedGroup ComphausFilteredPseudoNormedGroupWithTinvHom

variable {r' : ℝ≥0} [Fact (0 < r')]

variable (M : ProFiltPseuNormGrpWithTinv.{u} r')

/-- `HomZ_map` as an equiv. -/
@[simps]
def homZMapEquiv : hom ℤ M ≃+ M where
  toFun := AddMonoidHom.eval 1
  invFun := (smulAddHom ℤ M).flip
  map_add' := AddMonoidHom.map_add _
  left_inv f := by ext; exact one_smul _ _
  right_inv x := one_smul _ _

theorem homZMapEquiv_strict (c : ℝ≥0) (f : hom ℤ M) :
    f ∈ filtration (hom ℤ M) c ↔ (homZMapEquiv M) f ∈ filtration M c :=
  by
  constructor
  · intro hf; simpa only [mul_one] using hf Int.one_mem_filtration
  · intro hx c₁ n hn
    rw [SeminormedAddCommGroup.mem_filtration_iff] at hn 
    have aux := PseudoNormedGroup.int_smul_mem_filtration n _ c hx
    rw [NNReal.coe_natAbs] at aux 
    rw [← (HomZ_map_equiv M).symm_apply_apply f, HomZ_map_equiv_symm_apply, AddMonoidHom.flip_apply,
      smulAddHom_apply, mul_comm]
    exact PseudoNormedGroup.filtration_mono (mul_le_mul_right' hn c) aux

theorem homZMapEquiv_ctu (c : ℝ≥0) :
    Continuous (level (homZMapEquiv M) (fun c x => (homZMapEquiv_strict M c x).1) c) :=
  by
  haveI : Fact (c * ‖1 : ℤ‖₊ ≤ c) := ⟨by rw [nnnorm_one, mul_one]⟩
  have aux := AddMonoidHom.incl_continuous ℤ r' M c
  have aux2 := (continuous_apply 1).comp aux
  rwa [(ComphausFilteredPseudoNormedGroup.embedding_castLe (c * ‖1 : ℤ‖₊)
        c).continuous_iff] at
    aux2 

/-- The isomorphism `Hom ℤ M ≅ M` for `M` a `profinitely_filtered_pseudo_normed_group_with_Tinv`. -/
noncomputable def homZIso : hom ℤ M ≅ M :=
  ProFiltPseuNormGrpWithTinv.isoOfEquivOfStrict' (homZMapEquiv M) (homZMapEquiv_strict M)
    (homZMapEquiv_ctu M) fun x => by
    simp only [AddMonoidHom.eval_apply_apply, HomZ_map_equiv_apply]; rfl

end PolyhedralLattice

#lint

