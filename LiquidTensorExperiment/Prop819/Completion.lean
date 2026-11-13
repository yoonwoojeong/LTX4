import Mathlib.Algebra.Homology.Additive
import LiquidTensorExperiment.LocallyConstant.Vhat
import LiquidTensorExperiment.NormedGroup.ControlledExactness
import LiquidTensorExperiment.Prop819.StrictComplexIso

#align_import prop819.completion

noncomputable section

universe u

variable (C D : CochainComplex SemiNormedGroupCat.{u} ℕ)

open SemiNormedGroupCat

/-- The completed cochain complex associated to C. -/
abbrev cmpl :=
  (completion.mapHomologicalComplex _).obj C

open scoped NNReal

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem cmpl_exact_of_exact (ε : ℝ≥0) (hε : 0 < ε)
    (cond :
      ∀ (n : ℕ) (f : C.pt (n + 1)) (hf : C.d (n + 1) (n + 2) f = 0),
        ∃ g : C.pt n, C.d _ _ g = f ∧ «expr∥ ∥₊» g ≤ «expr∥ ∥₊» f)
    (n : ℕ) (f : (cmpl C).pt (n + 1)) (hf : (cmpl C).d _ (n + 2) f = 0) :
    ∃ g : (cmpl C).pt n, (cmpl C).d _ _ g = f ∧ «expr∥ ∥₊» g ≤ (1 + ε) * «expr∥ ∥₊» f :=
  by
  have :=
    @controlled_exactness (C.X (n + 1)) (C.X n) (C.X (n + 2)) _ _ _ (C.d _ _) 1 zero_lt_one 1
      (C.d _ _) _ _ ε hε f _
  · rcases this with ⟨g, hg1, hg2⟩
    exact ⟨g, hg1, hg2⟩
  · intro g hg
    erw [AddMonoidHom.mem_ker] at hg 
    specialize cond _ g hg
    rcases cond with ⟨g', h1, h2⟩
    refine' ⟨g', h1, _⟩
    simpa
  · rintro g ⟨g, rfl⟩
    specialize cond (n + 1) (C.d (n + 1) (n + 2) g) _
    · change (C.d (n + 1) (n + 2) ≫ C.d (n + 2) (n + 3)) g = 0
      simp
    rcases cond with ⟨g', h1, h2⟩
    refine' ⟨g', h1, _⟩
    dsimp
    simp
    exact h2
  · erw [AddMonoidHom.mem_ker]
    exact hf

theorem injective_of_strictIso (F : StrictIso C D)
    (cond : ∀ (f : C.pt 0) (hf : C.d 0 1 f = 0), f = 0) (f : D.pt 0) (hf : D.d 0 1 f = 0) : f = 0 :=
  by
  let FF := (HomologicalComplex.eval _ _ 0).mapIso F.iso
  have : f = (FF.inv ≫ FF.hom) f := by rw [FF.inv_hom_id]; simp
  rw [this]
  change FF.hom (FF.inv f) = 0
  rw [← show FF.hom 0 = 0 by simp]
  congr 1
  apply cond
  change (F.iso.inv.f 0 ≫ C.d 0 1) f = 0
  erw [F.iso.inv.comm]
  change (F.iso.inv.f 1) _ = 0
  erw [hf]
  simp

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem exact_of_strictIso (F : StrictIso C D) (ε : ℝ≥0) (hε : 0 < ε)
    (cond :
      ∀ (n : ℕ) (f : C.pt (n + 1)) (hf : C.d _ (n + 2) f = 0),
        ∃ g : C.pt n, C.d _ _ g = f ∧ «expr∥ ∥₊» g ≤ (1 + ε) * «expr∥ ∥₊» f)
    (n : ℕ) (f : D.pt (n + 1)) (hf : D.d _ (n + 2) f = 0) :
    ∃ g : D.pt n, D.d _ _ g = f ∧ «expr∥ ∥₊» g ≤ (1 + ε) * «expr∥ ∥₊» f :=
  by
  specialize cond n (((HomologicalComplex.eval _ _ (n + 1)).mapIso F.iso).inv f) _
  · dsimp [HomologicalComplex.eval]
    change (F.iso.inv.f (n + 1) ≫ C.d (n + 1) (n + 2)) f = 0
    rw [F.iso.inv.comm]
    simp [hf]
  rcases cond with ⟨g, h1, h2⟩
  refine' ⟨((HomologicalComplex.eval _ _ n).mapIso F.iso).Hom g, _, _⟩
  · dsimp [HomologicalComplex.eval] at *
    change (F.iso.hom.f _ ≫ D.d _ _) _ = _
    rw [F.iso.hom.comm]
    simp [h1]
    let FF := (HomologicalComplex.eval _ _ (n + 1)).mapIso F.iso
    change (FF.inv ≫ FF.hom) f = f
    rw [FF.inv_hom_id]
    rfl
  · rw [SemiNormedGroupCat.strictIso_inv] at h2 
    rwa [SemiNormedGroupCat.strictIso_hom]

