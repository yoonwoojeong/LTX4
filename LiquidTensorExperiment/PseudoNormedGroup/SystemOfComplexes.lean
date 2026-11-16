import LiquidTensorExperiment.SystemOfComplexes.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Tinv
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import pseudo_normed_group.system_of_complexes

/-!

# The system of complexes in Theorem 9.4 of `analytic.pdf`

Theorem 9.4 is about a system of complexes built from Breen-Deligne data,
a seminormed group `V` with `T⁻¹` (scaling by `r`) and a (certain explicit) profinitely filtered
pseudo-normed group `M` with `T⁻¹` (scaling by `r'`). We do not specialise to Scholze's
`𝓜-bar_r'(S)` in this file, but allow general profinitely filtered `M`. This file
contains the construction of the system of complexes from this data.

## Main definitions

Let `BD = (n₁ ⟶ n₂ ⟶ …)` be Breen-Deligne data, `κ` a sequence of non-negative reals which are
suitable for `BD`, and say `r,c≥0` and `V` is a normed group with `T⁻¹` scaling by `r`.

- `BD.complex κ r V r' c`: the functor taking a profinitely filtered pseudo-normed group `M`
  to the cochain complex `V-hat(M_{≤c}^n₁)^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^n₂)^{T⁻¹} ⟶ …`
  induced by the data.

- `BD.system κ r V r'`: the functor sending a profinitely filtered pseudo-normed group `M`
  to the system of complexes whose component at `c`
  is `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …`

-/


open scoped Classical NNReal

noncomputable section

open Opposite PseudoNormedGroup CategoryTheory CategoryTheory.Limits BreenDeligne

universe u

namespace BreenDeligne

namespace Data

section

variable (BD : BreenDeligne.Data) (κ : ℕ → ℝ≥0)

variable (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

variable (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)]

variable (M : ProFiltPseuNormGrpWithTinv.{u} r') (c : ℝ≥0)

/-- The object for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex₂X (a b : ℕ → ℝ≥0) [∀ i, Fact (b i ≤ r' * a i)] (i : ℕ) :
    (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroupCat :=
  cLCFPTinv₂ r V r' (a i) (b i) (BD.X i)

/-- The object for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complexX (i : ℕ) : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SemiNormedGroupCat :=
  complex₂X BD r V r' (fun i => c * κ i) (fun i => r' * (c * κ i)) i

variable [BD.Suitable κ]

/-- The differential for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex₂D (a b : ℕ → ℝ≥0) [∀ i, Fact (b i ≤ r' * a i)] [BD.Suitable a] [BD.Suitable b]
    (i j : ℕ) : BD.complex₂X r V r' a b i ⟶ BD.complex₂X r V r' a b j :=
  (BD.d j i).evalCLCFPTinv₂ r V r' _ _ _ _

/-- The differential for the complex of seminormed groups
`V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complexD (i j : ℕ) : BD.complexX κ r V r' c i ⟶ BD.complexX κ r V r' c j :=
  (BD.d j i).evalCLCFPTinv r V r' (c * κ i) (c * κ j)

theorem complexD_comp_d (i j k : ℕ) : BD.complexD κ r V r' c i j ≫ BD.complexD κ r V r' c j k = 0 :=
  by
  simp only [BreenDeligne.Data.complexD, ← UniversalMap.evalCLCFPTinv_comp, BD.d_comp_d,
    UniversalMap.evalCLCFPTinv_zero]

end

section

open HomologicalComplex

variable (BD : BreenDeligne.Data) (κ : ℕ → ℝ≥0) [BD.Suitable κ]

variable (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

variable (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)] (c : ℝ≥0)

/-- The complex of seminormed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
@[simps]
def complex₂ (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)] (r' : ℝ≥0)
    [Fact (0 < r')] [Fact (r' ≤ 1)] (a b : ℕ → ℝ≥0) [∀ i, Fact (b i ≤ r' * a i)] [BD.Suitable a]
    [BD.Suitable b] : (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ
    where
  obj M :=
    { X := fun i => (BD.complex₂X r V r' a b i).obj M
      d := fun i j => (BD.complex₂D r V r' a b i j).app M
      d_comp_d' := fun i j k _ _ => by
        rw [← NatTrans.comp_app]
        simp only [complex₂D, ← UniversalMap.evalCLCFPTinv₂_comp, BD.d_comp_d,
          UniversalMap.evalCLCFPTinv₂_zero]
        rfl
      shape := fun i j hij =>
        by
        simp only [complex₂D, ← UniversalMap.evalCLCFPTinv₂_comp, BD.shape _ _ hij,
          UniversalMap.evalCLCFPTinv₂_zero]
        rfl }
  map f :=
    { f := fun i => ((cLCFPTinv₂ r V r' (a i) (b i) (BD.X i)).map f : _)
      comm' := fun i j _ => NatTrans.naturality (BD.complex₂D r V r' a b i j) f }
  map_id M := by
    -- Porting note: Lean 3 `ext` was recursive
    apply HomologicalComplex.Hom.ext
    funext i
    exact CategoryTheory.Functor.map_id (cLCFPTinv₂ r V r' (a i) (b i) (BD.X i)) M
  map_comp f g := by
    -- Porting note: Lean 3 `ext` was recursive
    apply HomologicalComplex.Hom.ext
    funext i
    exact CategoryTheory.Functor.map_comp (cLCFPTinv₂ r V r' (a i) (b i) (BD.X i)) f g

/-- The complex of seminormed groups `V-hat(M_{≤c})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^2)^{T⁻¹} ⟶ …` -/
def complex (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)] (r' : ℝ≥0)
    [Fact (0 < r')] [Fact (r' ≤ 1)] (c : ℝ≥0) :
    (ProFiltPseuNormGrpWithTinv.{u} r')ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ :=
  BD.complex₂ r V r' (fun i => c * κ i) fun i => r' * (c * κ i)

namespace complex

theorem map_normNoninc {M₁ M₂} (f : M₁ ⟶ M₂) (n : ℕ) :
    (((BD.complex κ r V r' c).map f).f n).NormNoninc :=
  cLCFPTinv.map_normNoninc r V r' (c * κ n) (BD.X n) f

end complex

theorem complex_obj_d (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)] (c : ℝ≥0) (i j : ℕ) (M) :
    ((BD.complex κ r V r' c).obj M).d i j = ((BD.d j i).evalCLCFPTinv r V r' (c * κ i) (c * κ j)).app M :=
  rfl

theorem comm_sq_app {C D} [Category C] [Category D] {X₁ X₂ Y₁ Y₂ : C ⥤ D} {f₁ : X₁ ⟶ Y₁}
    {f₂ : X₂ ⟶ Y₂} {φ : X₁ ⟶ X₂} {ψ : Y₁ ⟶ Y₂} (hf : f₁ ≫ ψ = φ ≫ f₂) (c : C) :
    f₁.app c ≫ ψ.app c = φ.app c ≫ f₂.app c := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, hf]

/-- The system of complexes
`V-hat(M_{≤c}^{n₁})^{T⁻¹} ⟶ V-hat(M_{≤c_1c}^{n₂})^{T⁻¹} ⟶ ...`
occurring in Theorems 9.4 and 9.5 of [Analytic], as a functor in `M`. -/
@[simps obj map]
def system (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)] (r' : ℝ≥0)
    [Fact (0 < r')] [Fact (r' ≤ 1)] : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ SystemOfComplexes :=
  Functor.flip
    ({ obj := fun c => BD.complex κ r V r' (unop c)
       map := fun {c₂ c₁} h =>
        { app := fun M => by
            haveI : Fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h.unop.down.down⟩
            refine'
              { f := fun i =>
                  (cLCFPTinv₂.res r V r' (unop c₂ * κ i) (r' * (unop c₂ * κ i)) (unop c₁ * κ i)
                    (r' * (unop c₁ * κ i)) (BD.X i)).app M
                comm' := _ }
            · intro i j _
              have key := UniversalMap.res_comp_evalCLCFPTinv₂ r V r' (unop c₂ * κ i)
                  (r' * (unop c₂ * κ i)) (unop c₁ * κ i) (r' * (unop c₁ * κ i))
                  (unop c₂ * κ j) (r' * (unop c₂ * κ j)) (unop c₁ * κ j)
                  (r' * (unop c₁ * κ j)) (BD.d j i)
              dsimp only [complex, complex₂_obj_d, complex₂_obj_X, complex₂D, complex₂X]
              have key2 := comm_sq_app key M
              exact key2
          naturality := fun M N f => by
            -- Porting note: Lean 3 `ext` was recursive
            haveI : Fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h.unop.down.down⟩
            dsimp only
            apply HomologicalComplex.Hom.ext
            funext i
            dsimp only [HomologicalComplex.comp_f, complex, complex₂_map_f, complex₂_obj_X, complex₂X]
            have h := NatTrans.naturality
              (cLCFPTinv₂.res r V r' (unop c₂ * κ i) (r' * (unop c₂ * κ i)) (unop c₁ * κ i)
                (r' * (unop c₁ * κ i)) (BD.X i)) f
            exact h }
       map_id := by
        intro c
        -- Porting note: Lean 3 `ext` was recursive
        apply NatTrans.ext
        funext M
        dsimp only
        apply HomologicalComplex.Hom.ext
        funext i
        dsimp only [HomologicalComplex.id_f, NatTrans.id_app, complex, complex₂_map_f, complex₂_obj_X,
          complex₂X]
        have h := NatTrans.congr_app
          (cLCFPTinv₂.res_refl r V r' (unop c * κ i) (r' * (unop c * κ i)) (BD.X i)) M
        exact h
       map_comp := by
        intro c₃ c₂ c₁ h h'
        haveI H' : Fact ((unop c₁ : ℝ≥0) ≤ (unop c₂ : ℝ≥0)) := ⟨h'.unop.down.down⟩
        haveI H : Fact ((unop c₂ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := ⟨h.unop.down.down⟩
        haveI : Fact ((unop c₁ : ℝ≥0) ≤ (unop c₃ : ℝ≥0)) := ⟨H'.out.trans H.out⟩
        -- Porting note: Lean 3 `ext` was recursive
        apply NatTrans.ext
        funext M
        dsimp only
        apply HomologicalComplex.Hom.ext
        funext i
        dsimp only [HomologicalComplex.comp_f, NatTrans.comp_app, complex, complex₂_map_f,
          complex₂_obj_X, complex₂X]
        symm
        have h := NatTrans.congr_app (cLCFPTinv₂.res_comp_res r V r' (unop c₃ * κ i)
          (r' * (unop c₃ * κ i)) (unop c₂ * κ i) (r' * (unop c₂ * κ i)) (unop c₁ * κ i)
          (r' * (unop c₁ * κ i)) (BD.X i)) M
        exact h } :
      ℝ≥0ᵒᵖ ⥤ (ProFiltPseuNormGrpWithTinv r')ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ)

-- move this
instance fact_unop_op {c₁ c₂ : ℝ≥0} [Fact (c₂ ≤ c₁)] : Fact (unop (op c₂) ≤ unop (op c₁)) := by
  dsimp; apply_assumption

theorem system_res_def (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)] {M} {c₁ c₂ : ℝ≥0} {i : ℕ} [h : Fact (c₂ ≤ c₁)] :
    @SystemOfComplexes.res ((BD.system κ r V r').obj M) c₁ c₂ i _ =
      (cLCFPTinv.res r V r' (c₁ * κ i) (c₂ * κ i) (BD.X i)).app M :=
  rfl

theorem system_obj_d (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]
    (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)] {M} (c : ℝ≥0) (i j : ℕ) :
    @SystemOfComplexes.d ((BD.system κ r V r').obj M) c i j =
      ((BD.d j i).evalCLCFPTinv r V r' (c * κ i) (c * κ j)).app M :=
  rfl

-- Porting note: the types `α` and `β` of `Isometry` are given explicitly, since otherwise
-- instance search fails on `(forget SemiNormedGroupCat).obj _`.
theorem system_mapIso_isometry {M₁ M₂ : (ProFiltPseuNormGrpWithTinv r')ᵒᵖ} (f : M₁ ≅ M₂) (i : ℕ) :
    Isometry (α := ↥((((BD.system κ r V r').obj M₁).obj (op c)).X i))
      (β := ↥((((BD.system κ r V r').obj M₂).obj (op c)).X i))
      ((((BD.system κ r V r').mapIso f).hom.app (op c)).f i) :=
  by
  simp only [← Iso.app_hom, ← HomologicalComplex.Hom.isoApp_hom]
  apply SemiNormedGroupCat.iso_isometry_of_normNoninc <;> apply complex.map_normNoninc

instance system.separatedSpace (c : ℝ≥0) (i : ℕ) (M) :
    SeparatedSpace (((BD.system κ r V r').obj M) c i) :=
  cLCFPTinv₂.separatedSpace _ _ _ _ _ _ _

instance system.completeSpace (c : ℝ≥0) (i : ℕ) (M) :
    CompleteSpace (((BD.system κ r V r').obj M) c i) :=
  cLCFPTinv₂.completeSpace _ _ _ _ _ _ _

end

section

variable (BD : BreenDeligne.Data)

variable (r : ℝ≥0) (V : SemiNormedGroupCat) [NormedWithAut r V] [Fact (0 < r)]

variable (r' : ℝ≥0) [Fact (0 < r')] [Fact (r' ≤ 1)]

variable (κ : ℕ → ℝ≥0) [BD.VerySuitable r r' κ]

variable {r V r' κ}

theorem systemAdmissible {M} : ((BD.system κ r V r').obj M).Admissible :=
  { d_norm_noninc' := fun c i j hij =>
      haveI : UniversalMap.VerySuitable (BD.d j i) r r' (unop (op c) * κ j) (unop (op c) * κ i) :=
        by dsimp only [unop_op]; infer_instance
      UniversalMap.evalCLCFPTinv_normNoninc _ _ _ _ _ _ _
    res_normNoninc := fun c₁ c₂ i h => cLCFPTinv.res_normNoninc _ _ _ _ _ _ _ }

end

end Data

end BreenDeligne

#lint

