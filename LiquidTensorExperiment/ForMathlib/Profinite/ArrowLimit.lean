import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.Topology.Category.Profinite.AsLimit
import LiquidTensorExperiment.ForMathlib.Profinite.CompatDiscreteQuotient
import LiquidTensorExperiment.ForMathlib.Cech.Split

#align_import for_mathlib.Profinite.arrow_limit

noncomputable section

open CategoryTheory

universe u

namespace Profinite

variable (F : Arrow Profinite.{u}) (surj : Function.Surjective F.Hom)

open DiscreteQuotient

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def fintypeArrowDiagram : DiscreteQuotient F.left ⥤ Arrow FintypeCat.{u}
    where
  obj S :=
    { left := FintypeCat.of S
      right := FintypeCat.of <| S.make F.Hom surj
      Hom := DiscreteQuotient.map (S.makeLeComap _ _) }
  map S T f :=
    { left := ofLE <| leOfHom f
      right := ofLE <| make_right_mono F.Hom surj S T <| leOfHom f }

/-- A diagram of arrows construction from discrete quotients of F.left. -/
@[simps]
def arrowDiagram : DiscreteQuotient F.left ⥤ Arrow Profinite.{u} :=
  fintypeArrowDiagram F surj ⋙ FintypeCat.toProfinite.mapArrow

/-- The left diagram associated to arrow_diagram. -/
abbrev leftArrowDiagram : DiscreteQuotient F.left ⥤ Profinite.{u} :=
  arrowDiagram F surj ⋙ Arrow.leftFunc

/-- The right diagram associated to arrow_diagram. -/
abbrev rightArrowDiagram : DiscreteQuotient F.left ⥤ Profinite.{u} :=
  arrowDiagram F surj ⋙ Arrow.rightFunc

theorem arrowDiagram_surjective (S : DiscreteQuotient F.left) :
    Function.Surjective ((arrowDiagram F surj).obj S).Hom :=
  by
  rintro ⟨x⟩
  obtain ⟨x, rfl⟩ := surj x
  exact ⟨S.proj x, rfl⟩

instance (S : DiscreteQuotient F.left) : Arrow.Split ((arrowDiagram F surj).obj S)
    where
  σ :=
    ⟨fun x => Classical.choose (arrowDiagram_surjective F surj S x), continuous_of_discreteTopology⟩
  is_splitting' := by
    ext x
    erw [Classical.choose_spec (arrow_diagram_surjective F surj S x)]
    rfl

/-- A cone which is a limit expressing an arrow as a limit. -/
@[simps]
def arrowCone : Limits.Cone (arrowDiagram F surj)
    where
  pt := F
  π :=
    {
      app := fun S =>
        { left := ⟨S.proj, S.proj_continuous⟩
          right := ⟨(S.make _ surj).proj, (S.make _ surj).proj_continuous⟩ } }

/-- A helper definition used for `arrow_limit_cone`. -/
def arrowDiagramSndPreserves : Limits.PreservesLimit (arrowDiagram F surj ⋙ Comma.snd _ _) (𝟭 _) :=
  by
  have h := limits.id_preserves_limits.preserves_limits_of_shape
  have hh := h.preserves_limit
  exact hh

/-- the limit cone assocciated to arrow_diagram -/
@[simps]
def arrowLimitCone : Limits.LimitCone (arrowDiagram F surj)
    where
  Cone :=
    @Comma.coneOfPreserves _ _ _ _ _ _ _ _ _ _ _ (arrowDiagramSndPreserves _ _) (limitCone _) _
      (limitConeIsLimit _)
  IsLimit :=
    @Comma.coneOfPreservesIsLimit _ _ _ _ _ _ _ _ _ _ _ (arrowDiagramSndPreserves _ _) _
      (limitConeIsLimit _) _ _

/-- lifing arrow_cone gives an isomorphism on the left -/
instance arrow_isIso_lift_left :
    IsIso ((arrowLimitCone F surj).IsLimit.lift (arrowCone F surj)).left :=
  Profinite.isIso_asLimitCone_lift _

/-- lifing arrow_cone gives an isomorphism on the right -/
instance arrow_isIso_lift_right :
    IsIso ((arrowLimitCone F surj).IsLimit.lift (arrowCone F surj)).right :=
  isIso_of_bijective _
    (by
      constructor
      · intro x y h
        apply discrete_quotient.eq_of_proj_eq
        intro S
        apply_fun Subtype.val at h 
        let T : DiscreteQuotient F.left := S.comap F.hom.continuous
        let R : DiscreteQuotient F.right := T.make F.hom surj
        have hR : R ≤ S := by
          apply DiscreteQuotient.make_right_le
          tauto
        apply_fun fun e => e T at h 
        have := discrete_quotient.of_le_proj_apply hR
        rw [← this, ← this]
        congr 1
      · intro x
        cases' x with x hx
        dsimp at x hx 
        let Us : ∀ I : DiscreteQuotient F.right, I := fun I =>
          of_le (make_right_le _ _ _ _ (by tauto)) (x <| I.comap F.hom.continuous)
        rcases DiscreteQuotient.exists_of_compat Us _ with ⟨y, hy⟩
        · refine' ⟨y, _⟩
          ext I : 2
          dsimp at *
          let J : DiscreteQuotient F.right := I.make F.hom surj
          let II : DiscreteQuotient F.left := J.comap F.hom.continuous ⊓ I
          have h1 : II ≤ I := inf_le_right
          have h2 : II ≤ J.comap F.hom.continuous := inf_le_left
          rw [← hx (hom_of_le h1)]
          dsimp [comma.cone_of_preserves_is_limit, limit_cone_is_limit, CompHaus.limitConeIsLimit,
            TopCat.limitConeIsLimit]
          rw [hy]
          dsimp [Us]
          rw [← hx (hom_of_le h2)]
          rw [← of_le_comp_apply]
        · intro A B h
          dsimp [Us]
          have := comap_mono F.hom.continuous h
          rw [← hx (hom_of_le this)]
          rw [← of_le_comp_apply, ← of_le_comp_apply])

@[simps]
def leftArrowCone : Limits.Cone (leftArrowDiagram F surj) :=
  Functor.mapCone _ (arrowCone F surj)

@[simps]
def rightArrowCone : Limits.Cone (rightArrowDiagram F surj) :=
  Functor.mapCone _ (arrowCone F surj)

instance leftArrowCone_lift_isIso :
    IsIso <| (limitConeIsLimit <| leftArrowDiagram F surj).lift (leftArrowCone F surj) :=
  Profinite.arrow_isIso_lift_left _ _

instance rightArrowCone_lift_isIso :
    IsIso <| (limitConeIsLimit <| rightArrowDiagram F surj).lift (rightArrowCone F surj) :=
  Profinite.arrow_isIso_lift_right _ _

@[simps]
def leftArrowConeIso : leftArrowCone F surj ≅ limitCone <| leftArrowDiagram F surj :=
  Limits.Cones.ext (asIso <| (limitConeIsLimit <| leftArrowDiagram F surj).lift _) fun _ => rfl

@[simps]
def rightArrowConeIso : rightArrowCone F surj ≅ limitCone <| rightArrowDiagram F surj :=
  Limits.Cones.ext (asIso <| (limitConeIsLimit <| rightArrowDiagram F surj).lift _) fun _ => rfl

/-- The isomorphism of cones showing that arrow_cone is a limit cone. -/
@[simps]
def arrowConeIso : arrowCone F surj ≅ (arrowLimitCone F surj).Cone :=
  haveI :=
    arrow.is_iso_of_iso_left_of_is_iso_right
      ((arrow_limit_cone F surj).IsLimit.lift (arrow_cone F surj))
  limits.cones.ext (as_iso <| (arrow_limit_cone F surj).IsLimit.lift (arrow_cone F surj)) fun _ =>
    rfl

/-- arrow_cone is a limit cone. -/
@[simps]
def isLimitArrowCone : Limits.IsLimit (arrowCone F surj) :=
  Limits.IsLimit.ofIsoLimit (arrowLimitCone F surj).IsLimit (arrowConeIso F surj).symm

@[simps]
def isLimitLeftArrowCone : Limits.IsLimit (leftArrowCone F surj) :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit <| leftArrowDiagram F surj)
    (leftArrowConeIso _ _).symm

@[simps]
def isLimitRightArrowCone : Limits.IsLimit (rightArrowCone F surj) :=
  Limits.IsLimit.ofIsoLimit (limitConeIsLimit <| rightArrowDiagram F surj)
    (rightArrowConeIso _ _).symm

open Opposite

open scoped Simplicial

@[simps]
def cechConeDiagram (n : ℕ) : DiscreteQuotient F.left ⥤ Profinite.{u} :=
  arrowDiagram F surj ⋙ SimplicialObject.cechNerve ⋙ (evaluation _ _).obj (op [n])

def cechConeDiagramProj (n : ℕ) (S : DiscreteQuotient F.left) (i : Fin (n + 1)) :
    (cechConeDiagram F surj n).obj S ⟶ Profinite.of S :=
  Limits.WidePullback.π _ i

def cechConeDiagramInclusion (n : ℕ) (S : DiscreteQuotient F.left) :
    (cechConeDiagram F surj n).obj S → Fin (n + 1) → S := fun a i =>
  cechConeDiagramProj F surj n S i a

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem cechConeDiagramInclusion_injective (n : ℕ) (S : DiscreteQuotient F.left) :
    Function.Injective (cechConeDiagramInclusion F surj n S) :=
  by
  intro a b h
  dsimp [Cech_cone_diagram] at a b 
  haveI : Limits.PreservesLimitsOfSize.{0, 0} (forget Profinite.{u}) :=
    Limits.preservesLimitsOfSizeShrink.{0, u, 0, u, u, u, u + 1, u + 1}
      (forget.{u + 1, u, u} Profinite.{u})
  apply CategoryTheory.Limits.Concrete.widePullback_ext'
  rintro j
  apply_fun fun e => e j at h 
  exact h

instance cechConeDiagramFintype (n : ℕ) (S : DiscreteQuotient F.left) :
    Fintype ((cechConeDiagram F surj n).obj S) :=
  Fintype.ofInjective (cechConeDiagramInclusion F surj n S)
    (cechConeDiagramInclusion_injective F surj n S)

@[simps]
def cechCone (n : ℕ) : Limits.Cone (cechConeDiagram F surj n) :=
  Functor.mapCone _ (arrowCone F surj)

@[simps]
def swapConeRight (n : ℕ) (S : Limits.Cone (cechConeDiagram F surj n)) :
    Limits.Cone (rightArrowDiagram F surj)
    where
  pt := S.pt
  π :=
    { app := fun T => S.π.app T ≫ Limits.WidePullback.base _
      naturality' := by
        intro X Y f
        dsimp
        simp [← S.w f] }

@[simps]
def swapConeLeft (n : ℕ) (i : Fin (n + 1)) (S : Limits.Cone (cechConeDiagram F surj n)) :
    Limits.Cone (leftArrowDiagram F surj)
    where
  pt := S.pt
  π :=
    { app := fun T => S.π.app T ≫ Limits.WidePullback.π _ i
      naturality' := by
        intro X Y f
        dsimp
        simp [← S.w f] }

@[simps]
def cechConeIsLimit (n : ℕ) : Limits.IsLimit (cechCone F surj n)
    where
  lift S :=
    Limits.WidePullback.lift ((isLimitRightArrowCone F surj).lift <| swapConeRight _ _ _ _)
      (fun i => (isLimitLeftArrowCone F surj).lift <| swapConeLeft _ _ _ i _)
      (by
        intro i
        apply (is_limit_right_arrow_cone F surj).hom_ext
        intro T
        simp
        have :
          (arrow_cone F surj).pt.Hom ≫ (right_arrow_cone F surj).π.app T =
            (left_arrow_cone F surj).π.app T ≫
              (whisker_left (arrow_diagram F surj) arrow.left_to_right).app T :=
          by rfl
        erw [this, ← category.assoc,
          (is_limit_left_arrow_cone F surj).fac (swap_cone_left F surj n i S) T]
        simp)
  fac := by
    intro S T
    apply limits.wide_pullback.hom_ext
    · intro i
      dsimp
      simp
      have := (is_limit_left_arrow_cone F surj).fac
      erw [this]
      rfl
    · dsimp
      simp
      erw [(is_limit_right_arrow_cone F surj).fac]
      rfl
  uniq := by
    intro S f h
    apply limits.wide_pullback.hom_ext
    · dsimp; simp
      intro i
      apply (is_limit_left_arrow_cone F surj).hom_ext
      intro T
      simp
      erw [← h T, category.assoc, limits.wide_pullback.lift_π]
      rfl
    · dsimp; simp
      apply (is_limit_right_arrow_cone F surj).hom_ext
      intro T
      simp
      erw [← h T, category.assoc, limits.wide_pullback.lift_base]
      rfl

end Profinite

