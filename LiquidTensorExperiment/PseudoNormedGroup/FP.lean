import LiquidTensorExperiment.PseudoNormedGroup.BreenDeligne
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Kernels

#align_import pseudo_normed_group.FP

/-!

# Constructions on the filtration on a profinitely filtered pseudo-normed group

## Main definitions

- `FiltrationPow r' c n`: the functor sending a profinitely filtered `M` to `M_c^n`.
- `φ.eval_FP r' c₁ c₂`: The map M_c₁^m → M_c₂^n induced by a (c₁, c₂)-suitable φ.

-/


open scoped Classical NNReal BigOperators Kronecker

noncomputable section

attribute [local instance] typePow

universe u

@[simps]
def PseudoNormedGroup.filtrationObj (M) [ProfinitelyFilteredPseudoNormedGroup M] (c) : Profinite :=
  Profinite.of (PseudoNormedGroup.filtration M c)

open ProfinitelyFilteredPseudoNormedGroup CategoryTheory ComphausFilteredPseudoNormedGroup

namespace filtration

variable (M : Type u) [ProfinitelyFilteredPseudoNormedGroup M]

@[simps]
def castLe (c₁ c₂ : ℝ≥0) [h : Fact (c₁ ≤ c₂)] :
    PseudoNormedGroup.filtrationObj.{u} M c₁ ⟶ PseudoNormedGroup.filtrationObj.{u} M c₂
    where
  toFun := PseudoNormedGroup.castLe
  continuous_toFun := continuous_castLe c₁ c₂

theorem castLe_refl (c : ℝ≥0) : castLe M c c = 𝟙 _ := by ext; rfl

theorem castLe_comp (c₁ c₂ c₃ : ℝ≥0) [h₁ : Fact (c₁ ≤ c₂)] [h₂ : Fact (c₂ ≤ c₃)] :
    castLe M c₁ c₂ ≫ castLe M c₂ c₃ = @castLe M _ c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ := by ext; rfl

end filtration

@[simps (config := { fullyApplied := false }) obj_obj obj_map_apply map_app]
def filtration (r' : ℝ≥0) : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv.{u} r' ⥤ Profinite.{u}
    where
  obj c :=
    { obj := fun M => PseudoNormedGroup.filtrationObj M c
      map := fun M N f => ⟨f.level c, f.level_continuous c⟩
      map_id' := by intros; ext; rfl
      map_comp' := by intros; ext; rfl }
  map c₁ c₂ h := { app := fun M => @Filtration.castLe _ _ c₁ c₂ ⟨leOfHom h⟩ }
  map_id' := by intros; ext; rfl
  map_comp' := by intros; ext; rfl

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup

open ProfinitelyFilteredPseudoNormedGroupWithTinv

/-- The functor that sends `A` to `A^n` -/
@[simps obj map]
def pow (n : ℕ) : Profinite ⥤ Profinite
    where
  obj A := of (A ^ n)
  map A B f :=
    { toFun := fun x j => f (x j)
      continuous_toFun := continuous_pi fun j => f.2.comp (continuous_apply j) }

@[simps]
def powPowX (N n : ℕ) (X) : (pow N ⋙ pow n).obj X ≅ (pow (N * n)).obj X :=
  Profinite.isoOfHomeo
    { toEquiv :=
        (Equiv.curry _ _ _).symm.trans
          (((Equiv.prodComm _ _).trans finProdFinEquiv).arrowCongr (Equiv.refl X))
      continuous_toFun := by
        apply continuous_pi
        intro ij
        let k := ((Equiv.prodComm _ _).trans finProdFinEquiv).symm ij
        convert
          (@continuous_apply _ (fun i => X) _ k.2).comp (@continuous_apply _ (fun i => X ^ N) _ k.1)
      continuous_invFun := by
        apply continuous_pi
        intro i
        refine' continuous_pi _
        intro j
        exact continuous_apply _ }

@[simps hom inv]
def powMul (N n : ℕ) : pow (N * n) ≅ pow N ⋙ pow n :=
  NatIso.ofComponents (fun X => (powPowX N n X).symm)
    (by
      intro X Y f
      ext x i j
      rfl)

@[simps]
def ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv₀Hom {r' : ℝ≥0} (M : Type _)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] (c c₂ : ℝ≥0) [Fact (c ≤ r' * c₂)] :
    filtrationObj M c ⟶ filtrationObj M c₂ :=
  ⟨Tinv₀ c c₂, Tinv₀_continuous _ _⟩

open ProfinitelyFilteredPseudoNormedGroupWithTinv

namespace filtration

@[simps]
def res (r' c₁ c₂ : ℝ≥0) [h : Fact (c₁ ≤ c₂)] : (filtration r').obj c₁ ⟶ (filtration r').obj c₂ :=
  (filtration r').map (homOfLE h.1)

theorem res_refl (r' c : ℝ≥0) : res r' c c = 𝟙 _ := by ext; rfl

theorem res_comp (r' c₁ c₂ c₃ : ℝ≥0) [h₁ : Fact (c₁ ≤ c₂)] [h₂ : Fact (c₂ ≤ c₃)] :
    res r' c₁ c₂ ≫ res r' c₂ c₃ = @res r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ := by ext; rfl

@[simps]
def tinv₀ {r' : ℝ≥0} (c c₂ : ℝ≥0) [Fact (c ≤ r' * c₂)] :
    (filtration.{u} r').obj c ⟶ (filtration r').obj c₂
    where
  app M := tinv₀Hom M c c₂
  naturality' M₁ M₂ f := by ext x; exact (f.map_Tinv _).symm

theorem tinv₀_comp_res {r' : ℝ≥0} (c₁ c₂ c₃ c₄ : ℝ≥0) [Fact (c₁ ≤ r' * c₂)] [Fact (c₃ ≤ r' * c₄)]
    [Fact (c₂ ≤ c₄)] [Fact (c₁ ≤ c₃)] : tinv₀ c₁ c₂ ≫ res r' c₂ c₄ = res r' c₁ c₃ ≫ tinv₀ c₃ c₄ :=
  rfl

def piIso (r' c : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r') (N : ℕ) :
    Profinite.of (filtration (M ^ N) c) ≅ Profinite.of (filtration M c ^ N) :=
  Profinite.isoOfHomeo <| filtrationPiHomeo _ _

end filtration

/-- `FiltrationPow r' c n` is the functor sending a profinitely filtered `M` to `M_c^n`. -/
@[simps (config := { fullyApplied := false }) obj map]
def filtrationPow (r' : ℝ≥0) (c : ℝ≥0) (n : ℕ) : ProFiltPseuNormGrpWithTinv r' ⥤ Profinite :=
  ProFiltPseuNormGrpWithTinv.pow r' n ⋙ (filtration r').obj c

namespace filtrationPow

@[simps]
def castLe (r' c₁ c₂ : ℝ≥0) [Fact (c₁ ≤ c₂)] (n : ℕ) :
    filtrationPow.{u} r' c₁ n ⟶ filtrationPow r' c₂ n
    where
  app M := Filtration.castLe _ c₁ c₂
  naturality' M N f := by ext; rfl

theorem castLe_refl (r' c : ℝ≥0) (n : ℕ) : castLe r' c c n = 𝟙 _ := by ext; rfl

theorem castLe_comp (r' c₁ c₂ c₃ : ℝ≥0) [h₁ : Fact (c₁ ≤ c₂)] [h₂ : Fact (c₂ ≤ c₃)] (n : ℕ) :
    castLe r' c₁ c₂ n ≫ castLe r' c₂ c₃ n = @castLe r' c₁ c₃ ⟨le_trans h₁.1 h₂.1⟩ n := by ext; rfl

@[simps]
def tinv (r' : ℝ≥0) (c c₂) [Fact (c ≤ r' * c₂)] (n) :
    filtrationPow r' c n ⟶ filtrationPow r' c₂ n :=
  whiskerLeft _ (filtration.tinv₀ c c₂)

theorem tinv_app (r' : ℝ≥0) (c c₂) [Fact (c ≤ r' * c₂)] (n M) :
    (tinv r' c c₂ n).app M = tinv₀Hom _ c c₂ :=
  rfl

theorem castLe_vcomp_tinv (r' c₁ c₂ c₃ : ℝ≥0) [Fact (c₁ ≤ c₂)] [Fact (c₂ ≤ c₃)]
    [Fact (c₁ ≤ r' * c₂)] [Fact (c₂ ≤ r' * c₃)] (n : ℕ) :
    castLe r' c₁ c₂ n ≫ tinv r' c₂ c₃ n = tinv r' c₁ c₂ n ≫ castLe r' c₂ c₃ n := by ext; rfl

@[simps hom inv]
def mulIso (r' c : ℝ≥0) (M : ProFiltPseuNormGrpWithTinv r') (N n : ℕ) :
    (filtrationPow r' c n).obj (ProFiltPseuNormGrpWithTinv.of r' (↥M ^ N)) ≅
      (filtrationPow r' c (N * n)).obj M :=
  ((filtration r').obj c).mapIso <| (ProFiltPseuNormGrpWithTinv.powMul r' N n).symm.app _

end filtrationPow

namespace BreenDeligne

namespace BasicUniversalMap

variable (r' c c₁ c₂ c₃ c₄ : ℝ≥0) {l m n : ℕ} (ϕ : BasicUniversalMap m n)

open filtrationPow ComphausFilteredPseudoNormedGroupWithTinvHom

@[simps]
def evalFP [ϕ.Suitable c₁ c₂] : filtrationPow.{u} r' c₁ m ⟶ filtrationPow r' c₂ n
    where
  app M :=
    { toFun := ϕ.evalPng₀ M c₁ c₂
      continuous_toFun := ϕ.evalPng₀_continuous M c₁ c₂ }
  naturality' M₁ M₂ f := by
    ext1 x
    change
      ϕ.eval_png₀ M₂ c₁ c₂ ((filtrationPow r' c₁ m).map f x) =
        (filtrationPow r' c₂ n).map f (ϕ.eval_png₀ M₁ c₁ c₂ x)
    ext j
    dsimp only [filtrationPow_map, filtration_obj_map_apply, basic_universal_map.eval_png₀_coe,
      ComphausFilteredPseudoNormedGroupWithTinvHom.level_coe, comp_to_fun, coe_to_add_monoid_hom]
    simp only [basic_universal_map.eval_png_apply, pi_map_to_fun, f.map_sum, f.map_zsmul]

theorem evalFP_comp (g : BasicUniversalMap m n) (f : BasicUniversalMap l m) [hg : g.Suitable c₂ c₃]
    [hf : f.Suitable c₁ c₂] [(BasicUniversalMap.comp g f).Suitable c₁ c₃] :
    (BasicUniversalMap.comp g f).evalFP r' c₁ c₃ = f.evalFP r' c₁ c₂ ≫ g.evalFP r' c₂ c₃ := by ext;
  dsimp; rw [eval_png_comp]; rfl

theorem castLe_comp_evalFP [Fact (c₁ ≤ c₂)] [ϕ.Suitable c₂ c₄] [ϕ.Suitable c₁ c₃] [Fact (c₃ ≤ c₄)] :
    castLe r' c₁ c₂ m ≫ ϕ.evalFP r' c₂ c₄ = ϕ.evalFP r' c₁ c₃ ≫ castLe r' c₃ c₄ n := by ext; rfl

open filtrationPow

theorem tinv_comp_evalFP (r' c₁ c₂ c₃ c₄ : ℝ≥0) [Fact (c₁ ≤ r' * c₂)] [Fact (c₃ ≤ r' * c₄)]
    [ϕ.Suitable c₁ c₃] [ϕ.Suitable c₂ c₄] :
    tinv r' c₁ c₂ m ≫ ϕ.evalFP r' c₂ c₄ = ϕ.evalFP r' c₁ c₃ ≫ tinv r' c₃ c₄ n :=
  by
  ext M x : 3
  change
    ϕ.eval_png₀ M c₂ c₄ ((Tinv r' c₁ c₂ m).app M x) =
      (Tinv r' c₃ c₄ n).app M (ϕ.eval_png₀ M c₁ c₃ x)
  ext j
  dsimp
  simp only [eval_png_apply, ComphausFilteredPseudoNormedGroupHom.map_sum,
    ComphausFilteredPseudoNormedGroupHom.map_zsmul, pi_Tinv_apply]

theorem mulIso_evalFP (N : ℕ) [ϕ.Suitable c₂ c₁] (M) :
    (filtrationPow.mulIso.{u, u} r' c₂ M N m).inv ≫
        (BasicUniversalMap.evalFP r' c₂ c₁ ϕ).app (ProFiltPseuNormGrpWithTinv.of r' (M ^ N)) =
      (BasicUniversalMap.evalFP r' c₂ c₁ ((BasicUniversalMap.mul N) ϕ)).app M ≫
        (filtrationPow.mulIso.{u, u} r' c₁ M N n).inv :=
  by
  ext x i j
  dsimp [mul]
  simp only [eval_png_apply, Equiv.symm_apply_apply, Matrix.submatrix_apply, Matrix.kronecker]
  rw [← fin_prod_fin_equiv.sum_comp, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_comm]
  simp only [Equiv.symm_apply_apply, Matrix.one_apply, boole_mul, ite_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.kroneckerMap, Matrix.kronecker_apply]
  convert Finset.sum_apply j (Finset.univ : Finset (Fin m)) _ using 1

end BasicUniversalMap

end BreenDeligne

