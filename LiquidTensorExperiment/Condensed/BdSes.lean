import LiquidTensorExperiment.Condensed.FilteredColimitsCommuteWithFiniteLimits
import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.Condensed.ShortExact
import LiquidTensorExperiment.Condensed.BdSesAux
import LiquidTensorExperiment.ForMathlib.NnrealToNatColimit
import LiquidTensorExperiment.ForMathlib.PowFunctor

#align_import condensed.bd_ses

open CategoryTheory

open CategoryTheory.Limits

namespace Condensed

open scoped NNReal

open Opposite

noncomputable section

universe u

variable (F : CondensedSet.{u} ⥤ Condensed.{u} Ab.{u + 1}) [PreservesFilteredColimits F]
  (A : CompHausFiltPseuNormGrp.{u}) (ι : ℕ →o ℝ≥0) (hι : ∀ r : ℝ≥0, ∃ n : ℕ, r ≤ ι n)

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

def asNatDiagram : AsSmall.{u + 1} ℕ ⥤ CondensedSet.{u} :=
  restrictDiagram ι A.levelCondensedDiagram'

@[simp, reassoc]
theorem ι_colimitIsoCondensedObj (i) :
    colimit.ι _ i ≫ A.colimitIsoCondensedObj.hom = A.levelCondensedDiagramCocone.ι.app _ :=
  by
  dsimp [CompHausFiltPseuNormGrp.colimitIsoCondensedObj]
  erw [colimit.ι_desc_assoc]
  apply CondensedSet_to_presheaf.map_injective
  dsimp [CompHausFiltPseuNormGrp.colimitIsoCondensedObjAuxNatIso]
  ext S : 2; dsimp
  erw [(isColimitOfPreserves.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2}
        ((CategoryTheory.evaluation.{u, u + 1, u + 1, u + 2} Profinite.{u}ᵒᵖ (Type (u + 1))).obj S)
        (colimit.isColimit.{u + 1, u + 1, u + 1, u + 2}
          (A.level_Condensed_diagram' ⋙
            sheafToPresheaf.{u, u + 1, u + 1, u + 2} proetaleTopology.{u}
              (Type (u + 1))))).fac_assoc]
  erw [colimit.ι_desc_assoc]
  rfl

def isColimitLevelCondensedDiagramCocone : IsColimit A.levelCondensedDiagramCocone
    where
  desc S := A.colimitIsoCondensedObj.inv ≫ colimit.desc _ S
  fac := by
    intro S j; rw [← Category.assoc]
    let t := _; change t ≫ _ = _
    have ht : t = colimit.ι _ _ := by dsimp [t]; rw [Iso.comp_inv_eq, ι_colimit_iso_Condensed_obj]
    simp [ht]
  uniq := by
    intro S m hm
    rw [Iso.eq_inv_comp]
    apply colimit.hom_ext; intro j
    specialize hm j
    simpa

def asNatCocone : Cocone (asNatDiagram A ι) :=
  restrictCocone ι A.levelCondensedDiagramCocone

def isColimitAsNatCocone : IsColimit (asNatCocone A ι) :=
  isColimitRestrictCocone ι hι _ (isColimitLevelCondensedDiagramCocone _)

/-- The map `∐ F(A_≤(n * c)) ⟶ F(A)`-/
def coproductPresentation :
    (∐ fun i : AsSmall.{u + 1} ℕ => F.obj ((asNatDiagram A ι).obj i)) ⟶
      F.obj (asNatCocone A ι).pt :=
  Sigma.desc fun i => F.map ((asNatCocone A ι).ι.app i)

def presentationPointIsomorphism : F.obj (asNatCocone A ι).pt ≅ colimit (asNatDiagram A ι ⋙ F) :=
  (isColimitOfPreserves F (isColimitAsNatCocone A ι hι)).coconePointUniqueUpToIso
    (colimit.isColimit _)

theorem coproductPresentation_eq :
    coproductPresentation F A ι ≫ (presentationPointIsomorphism F A ι hι).hom =
      coproductToColimit (asNatDiagram A ι ⋙ F) :=
  by
  apply colimit.hom_ext; intro j
  erw [colimit.ι_desc]
  erw [colimit.ι_desc_assoc]
  dsimp
  erw [(CategoryTheory.Limits.isColimitOfPreserves F (Condensed.isColimitAsNatCocone A ι hι)).fac]
  rfl

theorem coproduct_to_colimit_shortExact_sequence (hι : ∀ r : ℝ≥0, ∃ n, r ≤ ι n) :
    ShortExact (coproductToCoproduct (asNatDiagram A ι ⋙ F) - 𝟙 _) (coproductPresentation F A ι) :=
  { Mono := inferInstance
    Epi := by
      have := Condensed.coproductPresentation_eq F A ι hι
      rw [← Iso.eq_comp_inv] at this ; rw [this]
      apply (config := { instances := false }) epi_comp
      infer_instance
      infer_instance
    exact := by
      have := Condensed.coproductPresentation_eq F A ι hι
      rw [← Iso.eq_comp_inv] at this ; rw [this]
      rw [exact_comp_iso]
      exact (Condensed.shortExact_sequence_aux (Condensed.asNatDiagram A ι ⋙ F)).exact }

variable (n : ℕ)

/-- The map `(∐ i, F((A_≤ i * c)^n)) ⟶ F(A^n)`. -/
def coproductPresentationWithPow :
    (∐ fun i : AsSmall.{u + 1} ℕ =>
        F.obj (∏ fun j : ULift.{u + 1} (Fin n) => (asNatDiagram A ι).obj i)) ⟶
      F.obj (∏ fun j : ULift.{u + 1} (Fin n) => (asNatCocone A ι).pt) :=
  Sigma.desc fun i => F.map (Pi.map fun j => (asNatCocone A ι).ι.app i)

def asNatDiagramPow : AsSmall.{u + 1} ℕ ⥤ CondensedSet.{u} :=
  asNatDiagram A ι ⋙ powFunctor _ (ULift.{u + 1} (Fin n))

def asNatCoconePow : Cocone (asNatDiagramPow A ι n) :=
  (powFunctor _ (ULift.{u + 1} (Fin n))).mapCocone (asNatCocone A ι)

def isColimitAsNatCoconePow : IsColimit (asNatCoconePow A ι n) :=
  isColimitOfPreserves _ (isColimitAsNatCocone _ _ hι)

def presentationPointIsomorphismWithPow :
    F.obj (∏ fun j : ULift.{u + 1} (Fin n) => (asNatCocone A ι).pt) ≅
      colimit (asNatDiagramPow A ι n ⋙ F) :=
  (isColimitOfPreserves F (isColimitAsNatCoconePow A ι hι n)).coconePointUniqueUpToIso
    (colimit.isColimit _)

theorem coproductPresentationWithPow_eq :
    coproductPresentationWithPow F A ι n =
      coproductToColimit (asNatDiagramPow A ι n ⋙ F) ≫
        (presentationPointIsomorphismWithPow F A ι hι n).inv :=
  by
  apply colimit.hom_ext; intro j
  erw [colimit.ι_desc]
  erw [colimit.ι_desc_assoc]
  dsimp
  erw [colimit.ι_desc]
  rfl

/-- This is the short exact sequence of condensed abelian groups of the form
`0 → ∐ i, F((A_{c * i})^n) → ∐ i, F((A_{c * i})^n) → F(A^n) → 0`.
-/
theorem shortExact_sequence_with_pow (hι : ∀ r : ℝ≥0, ∃ n, r ≤ ι n) :
    ShortExact (coproductToCoproduct (asNatDiagramPow A ι n ⋙ F) - 𝟙 _)
      (coproductPresentationWithPow F A ι n) :=
  { Mono := inferInstance
    Epi := by
      rw [Condensed.coproductPresentationWithPow_eq]
      apply epi_comp
      apply hι
    exact := by
      rw [Condensed.coproductPresentationWithPow_eq]
      rw [exact_comp_iso]
      exact (Condensed.shortExact_sequence_aux _).exact
      apply hι }

end Condensed

