import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.Limits
import LiquidTensorExperiment.ForMathlib.IsIsoNeg
import LiquidTensorExperiment.ForMathlib.HomologyIso
import LiquidTensorExperiment.ForMathlib.SemiNormedGroup
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Pt
import LiquidTensorExperiment.SystemOfComplexes.Basic

#align_import system_of_complexes.shift_sub_id

noncomputable section

universe u

open scoped NNReal

open CategoryTheory CategoryTheory.Limits Opposite

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem CategoryTheory.Homology.π_eq_zero {A B C : Ab.{u}} {f : A ⟶ B} {g : B ⟶ C} (w : f ≫ g = 0)
    (x) (h : ∃ a : A, f a = (kernelSubobject g).arrow x) : homology'.π f g w x = 0 :=
  by
  rcases h with ⟨a, ha⟩
  rw [Ab.apply_eq_pt_comp _ a, Ab.apply_eq_pt_comp _ x, ← image_subobject_arrow_comp f, ←
    imageToKernel_arrow _ _ w, ← category.assoc, ← category.assoc] at ha 
  have : (Ab.pt a ≫ factor_thru_image_subobject f) ≫ imageToKernel f g w = Ab.pt x :=
    by
    rw [← cancel_mono (kernel_subobject g).arrow]
    let e : ℤ ≃+ ULift.{u} ℤ := add_equiv.ulift.symm
    have he : Function.Surjective e.to_add_monoid_hom := e.surjective
    refine' (AddMonoidHom.cancel_right he).mp _
    ext; exact ha
  rw [Ab.apply_eq_pt_comp, ← this, category.assoc, homology'.condition, comp_zero]
  rfl

-- move me, generalize
instance ULift.preorder : Preorder (ULift.{u} ℕ) :=
  Preorder.lift ULift.down

section

variable (C : ℝ≥0ᵒᵖ ⥤ Ab.{u}) (i : ℕ) (f : ULift.{u} ℕ → ℝ≥0)

def ShiftSubId.shift (hf : Monotone f) :
    (∏ fun x => C.obj (op <| f x)) ⟶ ∏ fun x => C.obj (op <| f x) :=
  Pi.lift fun x => Pi.π _ ⟨x.down + 1⟩ ≫ C.map (homOfLE <| hf <| by apply Nat.le_succ).op

def shiftSubId (hf : Monotone f) : (∏ fun x => C.obj (op <| f x)) ⟶ ∏ fun x => C.obj (op <| f x) :=
  ShiftSubId.shift C f hf - 𝟙 _

end

namespace SystemOfComplexes

variable (C : SystemOfComplexes.{u}) (i : ℕ) (f : ULift.{u} ℕ → ℝ≥0)

def toAbH : ℝ≥0ᵒᵖ ⥤ Ab :=
  C.toAb ⋙ homology'Functor _ _ i

variable [∀ c i, CompleteSpace (C c i)] [∀ c i, SeparatedSpace (C c i)]

theorem shift_eq_zero (hf : Monotone f) {k K c₀ : ℝ≥0} [Fact (1 ≤ k)]
    (hC : C.IsBoundedExact k K i c₀) (hc₀ : ∀ j, c₀ ≤ f j) (hk : ∀ j, k * f j ≤ f (j + 1)) :
    ShiftSubId.shift (C.toAbH i) f hf = 0 :=
  by
  apply CategoryTheory.Limits.limit.hom_ext; intro j
  rw [zero_comp, ShiftSubId.shift, to_AbH, limit.lift_π, fan.mk_π_app, functor.comp_map,
    homology'Functor_map]
  convert comp_zero using 2
  apply homology'.ext
  rw [comp_zero, homology'.π_map]
  apply AddCommGroupCat.ext; intro x
  let d := HomologicalComplex.dFrom (C.to_Ab.obj (op (f (j.1 + 1)))) i
  let x' : C (f (j.1 + 1)) i := (kernel_subobject d).arrow x
  have aux : Fact (c₀ ≤ f j.1) := ⟨hc₀ _⟩
  haveI : Fact (k * f j.1 ≤ f (j.1 + 1)) := ⟨hk _⟩
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC (f j.1) aux i le_rfl (res x')
  have hdx' : C.d i (i + 1) x' = 0 :=
    by
    show ((kernel_subobject d).arrow ≫ (C.to_Ab.obj (op (f (j.1 + 1)))).d i (i + 1)) x = 0
    suffices (kernel_subobject d).arrow ≫ (C.to_Ab.obj (op (f (j.1 + 1)))).d i (i + 1) = 0 by
      rw [this]; rfl
    rw [← (C.to_Ab.obj (op (f (j.1 + 1)))).dFrom_comp_xNextIso, ← category.assoc,
      kernel_subobject_arrow_comp, zero_comp]
    dsimp; rfl
  rw [res_res, d_res, hdx', map_zero, norm_zero, MulZeroClass.mul_zero, ← coe_nnnorm, ←
    NNReal.coe_zero, NNReal.coe_le_coe, le_zero_iff, nnnorm_eq_zero, sub_eq_zero] at hy 
  apply CategoryTheory.Homology.π_eq_zero
  cases i
  · refine' ⟨0, _⟩
    rw [d_eq_zero] at hy ; swap; · decide
    rw [kernel_subobject_map_arrow_apply, HomologicalComplex.Hom.sqFrom_left,
      HomologicalComplex.dTo_eq_zero, AddCommGroupCat.zero_apply]
    · exact hy.symm; · rw [CochainComplex.prev_nat_zero]; dsimp; decide
  · refine' ⟨((C.to_Ab.obj (op (f j.1))).xPrevIso _).inv y, _⟩
    · dsimp; rfl
    rw [← comp_apply, ← comp_apply, HomologicalComplex.xPrevIso_comp_dTo,
      kernel_subobject_map_arrow]
    exact hy.symm

theorem shiftSubId_isIso (hf : Monotone f) {k K c₀ : ℝ≥0} [Fact (1 ≤ k)]
    (hC : C.IsBoundedExact k K i c₀) (hc₀ : ∀ j, c₀ ≤ f j) (hk : ∀ j, k * f j ≤ f (j + 1)) :
    IsIso (shiftSubId (C.toAbH i) f hf) :=
  by
  rw [shiftSubId, shift_eq_zero C i f hf hC hc₀ hk, zero_sub, isIso_neg_iff]
  infer_instance

end SystemOfComplexes

