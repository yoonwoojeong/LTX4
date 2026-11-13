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
  suffices mono ((endomorphisms.forget _).map t) by
    refine' (endomorphisms.forget _).mono_of_mono_map this
  let e₁ :
    (endomorphisms.forget 𝓐).obj (∐ fun a : α => X a) ≅
      ∐ fun a : α => (endomorphisms.forget _).obj (X a) :=
    preserves_colimit_iso _ _ ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  let e₂ : (endomorphisms.forget 𝓐).obj (∐ Y) ≅ ∐ fun a => (endomorphisms.forget _).obj (Y a) :=
    preserves_colimit_iso _ _ ≪≫ has_colimit.iso_of_nat_iso (discrete.nat_iso fun _ => iso.refl _)
  have : (endomorphisms.forget _).map t = e₁.hom ≫ _ ≫ e₂.inv
  rotate_left 2
  · apply sigma.desc
    intro a
    refine' _ ≫ sigma.ι _ a
    refine' (endomorphisms.forget _).map (f a)
  · dsimp [e₁, e₂, t]
    apply (is_colimit_of_preserves (endomorphisms.forget 𝓐) (colimit.is_colimit _)).hom_ext
    intro j
    dsimp
    simp only [category.assoc]
    erw [(is_colimit_of_preserves (endomorphisms.forget 𝓐) (colimit.is_colimit _)).fac_assoc]
    rw [← comp_f, colimit.ι_desc]; dsimp; simp; dsimp; simp; infer_instance
  rw [this]
  apply (config := { instances := false }) mono_comp; infer_instance
  apply (config := { instances := false }) mono_comp; swap; infer_instance
  apply AB4.cond; intro a; infer_instance

end Endomorphisms

end CategoryTheory

