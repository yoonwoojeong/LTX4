import LiquidTensorExperiment.ForMathlib.Derived.LesFacts

#align_import for_mathlib.Ext_quasi_iso

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace BoundedHomotopyCategory

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]

theorem ext_map_isIso_of_quasi_iso (A₁ A₂ B : BoundedHomotopyCategory 𝓐) (f : A₁ ⟶ A₂)
    [HomotopyCategory.IsQuasiIso f] (i : ℤ) : IsIso <| ((ext i).map f.op).app B :=
  by
  let e := replacement_iso A₁.replace A₂.replace A₂ (A₁.π ≫ f) A₂.π
  let e' := (preadditive_yoneda.obj (B⟦i⟧)).mapIso e.op
  show is_iso e'.hom
  infer_instance

end BoundedHomotopyCategory

