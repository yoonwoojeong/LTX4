import Mathlib.CategoryTheory.Limits.ConcreteCategory

#align_import for_mathlib.concrete_equalizer

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

attribute [local instance] concrete_category.hasCoeToFun concrete_category.hasCoeToSort

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]

section Equalizer

theorem Concrete.equalizer_ext {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g]
    [PreservesLimit (parallelPair f g) (forget C)] (x y : equalizer f g)
    (h : equalizer.ι f g x = equalizer.ι f g y) : x = y :=
  by
  apply Concrete.limit_ext
  rintro (a | a)
  · apply h
  · rw [← limit.w (CategoryTheory.Limits.parallelPair f g) WalkingParallelPairHom.right, comp_apply, comp_apply, h]

def Concrete.equalizerEquivAux {X Y : C} (f g : X ⟶ Y) :
    (parallelPair f g ⋙ forget C).sections ≃ { x : X // f x = g x }
    where
  toFun x :=
    ⟨x.1 WalkingParallelPair.zero,
      by
      have h1 := x.2 CategoryTheory.Limits.WalkingParallelPairHom.left
      have h2 := x.2 CategoryTheory.Limits.WalkingParallelPairHom.right
      dsimp at h1 h2 
      erw [h1, h2]⟩
  invFun x :=
    { val := fun j =>
        match j with
        | WalkingParallelPair.zero => x.1
        | WalkingParallelPair.one => f x.1
      property := by
        dsimp [CategoryTheory.Functor.sections]
        rintro (a | a) (b | b) (f | f)
        · simp
        · rfl
        · exact x.2.symm
        · simp }
  left_inv := by
    rintro ⟨x, hx⟩
    ext (a | a)
    · rfl
    · change _ = x _
      rw [← hx CategoryTheory.Limits.WalkingParallelPairHom.left]
      rfl
  right_inv := by rintro ⟨_, _⟩; ext; rfl

noncomputable def Concrete.equalizerEquiv {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g]
    [PreservesLimit (parallelPair f g) (forget C)] : ↥(equalizer f g) ≃ { x // f x = g x } :=
  let h1 := limit.isLimit (parallelPair f g)
  let h2 := isLimitOfPreserves (forget C) h1
  let E := h2.conePointUniqueUpToIso (Types.limitConeIsLimit.{_, v} _)
  E.toEquiv.trans <| Concrete.equalizerEquivAux _ _

@[simp]
theorem Concrete.equalizerEquiv_apply {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g]
    [PreservesLimit (parallelPair f g) (forget C)] (x : equalizer f g) :
    (Concrete.equalizerEquiv f g x : X) = equalizer.ι f g x :=
  rfl

end Equalizer

end CategoryTheory.Limits

