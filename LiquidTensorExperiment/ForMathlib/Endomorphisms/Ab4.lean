import LiquidTensorExperiment.ForMathlib.Endomorphisms.Basic
import LiquidTensorExperiment.ForMathlib.Ab4
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

#align_import for_mathlib.endomorphisms.ab4

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace Endomorphisms

variable (𝓐 : Type u) [Category.{v} 𝓐] [Abelian 𝓐] [HasCoproducts.{v} 𝓐] [AB4 𝓐]
  [HasProductsOfShape (ULift.{v} ℕ) 𝓐]

instance : AB4 (Endomorphisms 𝓐) := by
  constructor; intro α X Y f hf
  let t := _; change mono t
  suffices mono ((Endomorphisms.forget _).map t) by
    refine' (Endomorphisms.forget _).mono_of_mono_map this
  let e₁ :
    (Endomorphisms.forget 𝓐).obj (∐ fun a : α => X a) ≅
      ∐ fun a : α => (Endomorphisms.forget _).obj (X a) :=
    CategoryTheory.preservesColimitIso _ _ ≪≫ HasColimit.isoOfNatIso (Discrete.natIso fun _ => iso.refl _)
  let e₂ : (Endomorphisms.forget 𝓐).obj (∐ Y) ≅ ∐ fun a => (Endomorphisms.forget _).obj (Y a) :=
    CategoryTheory.preservesColimitIso _ _ ≪≫ HasColimit.isoOfNatIso (Discrete.natIso fun _ => iso.refl _)
  have : (Endomorphisms.forget _).map t = e₁.hom ≫ _ ≫ e₂.inv
  rotate_left 2
  · apply sigma.desc
    intro a
    refine' _ ≫ sigma.ι _ a
    refine' (Endomorphisms.forget _).map (f a)
  · dsimp [e₁, e₂, t]
    apply (CategoryTheory.Limits.isColimitOfPreserves (Endomorphisms.forget 𝓐) (colimit.isColimit _)).hom_ext
    intro j
    dsimp
    simp only [Category.assoc]
    erw [(CategoryTheory.Limits.isColimitOfPreserves (Endomorphisms.forget 𝓐) (colimit.isColimit _)).fac_assoc]
    rw [← comp_f, colimit.ι_desc]; dsimp; simp; dsimp; simp; infer_instance
  rw [this]
  apply (config := { instances := false }) mono_comp; infer_instance
  apply (config := { instances := false }) mono_comp; swap; infer_instance
  apply AB4.cond; intro a; infer_instance

end Endomorphisms

end CategoryTheory

