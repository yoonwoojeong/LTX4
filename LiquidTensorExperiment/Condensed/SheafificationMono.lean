import LiquidTensorExperiment.Condensed.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Evaluation
import LiquidTensorExperiment.ForMathlib.SheafificationMono

#align_import condensed.sheafification_mono

open CategoryTheory

open CategoryTheory.GrothendieckTopology

open Opposite

universe u

variable (F : Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) (G : Condensed.{u} Ab.{u + 1})

variable (η : F ⟶ G.val)

theorem condensed_ab_sheafifyLift_mono_of_exists :
    (∀ (B : Profinite.{u}) (t : F.obj (op B)),
        η.app (op B) t = 0 →
          ∃ (α : Type u) (_ : Fintype α) (X : α → Profinite.{u}) (π : ∀ a : α, X a ⟶ B) (surj :
            ∀ b : B, ∃ (a : α) (x : X a), π a x = b), ∀ a : α, F.map (π a).op t = 0) →
      Mono (proetaleTopology.sheafifyLift η G.cond) :=
  by
  intro h
  apply sheafify_lift_mono_of_exists_cover
  intro B t ht
  specialize h B t ht
  obtain ⟨α, hα, X, π, surj, h⟩ := h
  skip
  let W : proetale_topology.cover B := ⟨sieve.generate (presieve.of_arrows X π), _⟩
  use W
  rintro ⟨Z, f, ⟨A, g, hg, ⟨a⟩, rfl⟩⟩
  dsimp; simp [h a]
  use presieve.of_arrows X π, α, hα, X, π, surj
  apply sieve.le_generate

theorem presheaf_to_condensed_ab_map_mono_of_exists
    (h :
      ∀ (B : Profinite.{u}) (t : F.obj (op B)),
        η.app (op B) t = 0 →
          ∃ (α : Type u) (_ : Fintype α) (X : α → Profinite.{u}) (π : ∀ a : α, X a ⟶ B) (surj :
            ∀ b : B, ∃ (a : α) (x : X a), π a x = b), ∀ a : α, F.map (π a).op t = 0) :
    Mono (((sheafificationAdjunction proetaleTopology Ab.{u + 1}).homEquiv _ G).symm η) :=
  by
  apply (Sheaf_to_presheaf proetaleTopology Ab.{u + 1}).mono_of_mono_map
  dsimp [sheafification_adjunction]
  apply condensed_ab_sheafifyLift_mono_of_exists
  exact h

