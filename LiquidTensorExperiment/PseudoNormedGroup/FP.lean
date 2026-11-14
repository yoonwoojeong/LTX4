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
def PseudoNormedGroup.filtrationObj (M) [ProfinitelyFilteredPseudoNormedGroup M] (c : ℝ≥0) : Profinite :=
  Profinite.of (PseudoNormedGroup.filtration M c)

open ProfinitelyFilteredPseudoNormedGroup CategoryTheory ComphausFilteredPseudoNormedGroup

namespace Filtration

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

end Filtration

@[simps (config := { fullyApplied := false }) obj_obj obj_map_apply map_app]
def filtration (r' : ℝ≥0) : ℝ≥0 ⥤ ProFiltPseuNormGrpWithTinv.{u} r' ⥤ Profinite.{u}
    where
  obj c :=
    { obj := fun M => PseudoNormedGroup.filtrationObj M c
      map := fun f => ⟨ComphausFilteredPseudoNormedGroupWithTinvHom.level f c,
        ComphausFilteredPseudoNormedGroupWithTinvHom.level_continuous f c⟩
      map_id := by
        intros
        apply ContinuousMap.ext
        intro x
        rfl
      map_comp := by
        intros
        apply ContinuousMap.ext
        intro x
        rfl }
  map {c₁ c₂} h := { app := fun M => @Filtration.castLe M _ c₁ c₂ ⟨leOfHom h⟩ }
  -- Porting note: Lean 3's recursive `ext` replaced by explicit `NatTrans.ext`/`ContinuousMap.ext`
  map_id := by
    intros
    apply NatTrans.ext
    funext M
    apply ContinuousMap.ext
    intro x
    rfl
  map_comp := by
    intros
    apply NatTrans.ext
    funext M
    apply ContinuousMap.ext
    intro x
    rfl

open SemiNormedGroupCat Opposite Profinite PseudoNormedGroup CategoryTheory BreenDeligne

open ProfinitelyFilteredPseudoNormedGroup

open ProfinitelyFilteredPseudoNormedGroupWithTinv

-- Porting note: Lean 4's instance search does not see through `A ^ n = Fin n → A`, so the
-- topological instances on powers are registered explicitly.
instance instCompactSpaceTypePow {n : ℕ} {α : Type _} [TopologicalSpace α] [CompactSpace α] :
    CompactSpace (α ^ n) :=
  Pi.compactSpace

instance instT2SpaceTypePow {n : ℕ} {α : Type _} [TopologicalSpace α] [T2Space α] :
    T2Space (α ^ n) :=
  Pi.t2Space

instance instTotallyDisconnectedSpaceTypePow {n : ℕ} {α : Type _} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (α ^ n) :=
  Pi.totallyDisconnectedSpace

/-- The functor that sends `A` to `A^n` -/
@[simps obj map]
def pow (n : ℕ) : Profinite ⥤ Profinite
    where
  obj A := of (A ^ n)
  map f :=
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
      -- Porting note: the inverse of `powPowX` is not definitionally computable (it comes from
      -- `asIso`), so we cancel the isomorphisms instead of closing the goal by `rfl`
      change _ ≫ (powPowX N n Y).inv = (powPowX N n X).inv ≫ _
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      apply ContinuousMap.ext
      intro x
      rfl)

@[simps]
def ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv₀Hom {r' : ℝ≥0} (M : Type _)
    [ProfinitelyFilteredPseudoNormedGroupWithTinv r' M] (c c₂ : ℝ≥0) [Fact (c ≤ r' * c₂)] :
    filtrationObj M c ⟶ filtrationObj M c₂ :=
  ⟨tinv₀ c c₂, tinv₀_continuous _ _⟩

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
  naturality M₁ M₂ f := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (ComphausFilteredPseudoNormedGroupWithTinvHom.map_tinv f _).symm

theorem tinv₀_comp_res {r' : ℝ≥0} (c₁ c₂ c₃ c₄ : ℝ≥0) [Fact (c₁ ≤ r' * c₂)] [Fact (c₃ ≤ r' * c₄)]
    [Fact (c₂ ≤ c₄)] [Fact (c₁ ≤ c₃)] : tinv₀ c₁ c₂ ≫ res r' c₂ c₄ = res r' c₁ c₃ ≫ tinv₀ c₃ c₄ := by
  apply NatTrans.ext
  funext M
  apply ContinuousMap.ext
  intro x
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
  naturality M N f := by ext; rfl

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
  naturality M₁ M₂ f := by
    -- Porting note: Lean 3's recursive `ext1`/`ext` replaced by explicit ext lemmas, and the
    -- `dsimp only`/`simp only` chain replaced by `show` plus `simp only`
    apply ContinuousMap.ext
    intro x
    change
      ϕ.evalPng₀ M₂ c₁ c₂ ((filtrationPow r' c₁ m).map f x) =
        (filtrationPow r' c₂ n).map f (ϕ.evalPng₀ M₁ c₁ c₂ x)
    apply Subtype.ext
    funext j
    show BreenDeligne.BasicUniversalMap.evalPng (M₂ : Type _) ϕ (fun a => f (x.1 a)) j =
      f (BreenDeligne.BasicUniversalMap.evalPng (M₁ : Type _) ϕ x.1 j)
    rw [BreenDeligne.BasicUniversalMap.evalPng_apply, BreenDeligne.BasicUniversalMap.evalPng_apply]
    simp only [_root_.map_sum, _root_.map_zsmul]

theorem evalFP_comp (g : BasicUniversalMap m n) (f : BasicUniversalMap l m) [hg : g.Suitable c₂ c₃]
    [hf : f.Suitable c₁ c₂] [(BasicUniversalMap.comp g f).Suitable c₁ c₃] :
    (BasicUniversalMap.comp g f).evalFP r' c₁ c₃ = f.evalFP r' c₁ c₂ ≫ g.evalFP r' c₂ c₃ := by
  -- Porting note: Lean 3's recursive `ext` replaced by explicit ext lemmas
  apply NatTrans.ext
  funext M
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  show BreenDeligne.BasicUniversalMap.evalPng (M : Type _) (BasicUniversalMap.comp g f) x.1 =
    BreenDeligne.BasicUniversalMap.evalPng (M : Type _) g
      (BreenDeligne.BasicUniversalMap.evalPng (M : Type _) f x.1)
  rw [BreenDeligne.BasicUniversalMap.evalPng_comp]
  rfl

theorem castLe_comp_evalFP [Fact (c₁ ≤ c₂)] [ϕ.Suitable c₂ c₄] [ϕ.Suitable c₁ c₃] [Fact (c₃ ≤ c₄)] :
    castLe r' c₁ c₂ m ≫ ϕ.evalFP r' c₂ c₄ = ϕ.evalFP r' c₁ c₃ ≫ castLe r' c₃ c₄ n := by
  apply NatTrans.ext
  funext M
  apply ContinuousMap.ext
  intro x
  rfl

open filtrationPow

theorem tinv_comp_evalFP (r' c₁ c₂ c₃ c₄ : ℝ≥0) [Fact (c₁ ≤ r' * c₂)] [Fact (c₃ ≤ r' * c₄)]
    [ϕ.Suitable c₁ c₃] [ϕ.Suitable c₂ c₄] :
    tinv r' c₁ c₂ m ≫ ϕ.evalFP r' c₂ c₄ = ϕ.evalFP r' c₁ c₃ ≫ tinv r' c₃ c₄ n := by
  apply NatTrans.ext
  funext M
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  show BreenDeligne.BasicUniversalMap.evalPng (M : Type _) ϕ
      (ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv (r' := r') x.1) j =
    ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv (r' := r')
      (BreenDeligne.BasicUniversalMap.evalPng (M : Type _) ϕ x.1 j)
  rw [BreenDeligne.BasicUniversalMap.evalPng_apply, BreenDeligne.BasicUniversalMap.evalPng_apply]
  show ∑ i : Fin m, ϕ j i • ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv (r' := r') (x.1 i) =
    ProfinitelyFilteredPseudoNormedGroupWithTinv.tinv (r' := r') (∑ i : Fin m, ϕ j i • x.1 i)
  simp only [ComphausFilteredPseudoNormedGroupHom.map_sum,
    ComphausFilteredPseudoNormedGroupHom.map_zsmul]

-- Porting note: `mulIso` has only one universe parameter in Lean 4, and `M` needs its type
-- ascription to elaborate `M ^ N`
theorem mulIso_evalFP (N : ℕ) [ϕ.Suitable c₂ c₁] (M : ProFiltPseuNormGrpWithTinv r') :
    (filtrationPow.mulIso.{u} r' c₂ M N m).inv ≫
        (BasicUniversalMap.evalFP r' c₂ c₁ ϕ).app (ProFiltPseuNormGrpWithTinv.of r' (M ^ N)) =
      (BasicUniversalMap.evalFP r' c₂ c₁ ((BasicUniversalMap.mul N) ϕ)).app M ≫
        (filtrationPow.mulIso.{u} r' c₁ M N n).inv := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext i j
  show BreenDeligne.BasicUniversalMap.evalPng ((M : Type _) ^ N) ϕ
      (fun a b => x.1 (finProdFinEquiv (b, a))) i j =
    BreenDeligne.BasicUniversalMap.evalPng (M : Type _) (BreenDeligne.BasicUniversalMap.mul N ϕ)
      x.1 (finProdFinEquiv (j, i))
  rw [BreenDeligne.BasicUniversalMap.evalPng_apply, BreenDeligne.BasicUniversalMap.evalPng_apply]
  dsimp only
  rw [← finProdFinEquiv.sum_comp, ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  simp only [BreenDeligne.BasicUniversalMap.hMul_apply, Matrix.reindexLinearEquiv_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.one_apply,
    Matrix.kronecker_apply, boole_mul, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Finset.sum_apply]
  rfl

end BasicUniversalMap

end BreenDeligne

