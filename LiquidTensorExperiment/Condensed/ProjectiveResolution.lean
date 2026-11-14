import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.Condensed.Extr.Equivalence
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi

#align_import condensed.complex

universe u

open CategoryTheory

/-

S extr. disc.
A cond ab group.

A ↦ Hom_{CondSet}(S,A) = A(S) commutes with limits and colimits.

A(-) commutes with finite products, in Ab, finite products = finite coproducts.

Z[S] is projective.

A -> B epi, Hom(Z[S],A) -> Hom(Z[S],B) -- A(S) -> B(S) WTS: surjective.

1. If S is extr. disc. and A -> B is an epi of cond ab, then A(S) -> B(S) surjective.
  B -> B/A

-/
noncomputable section

def CondensedAb.free (S : CondensedSet) : Condensed Ab :=
  condensedSetToCondensedAb.obj <| S

local notation "ℤ[" S "]" => CondensedAb.free S.toCondensed

def Condensed.forgetAb (S : Condensed Ab) : CondensedSet :=
  condensedAbToCondensedSet.obj S

def Quiver.Hom.forgetAb {S T : Condensed Ab} (e : S ⟶ T) : S.forgetAb ⟶ T.forgetAb :=
  condensedAbToCondensedSet.map e

namespace CondensedAb

def toFree (S : CondensedSet) : S ⟶ condensedAbToCondensedSet.obj (free S) :=
  condensedAbCondensedSetAdjunction.homEquiv _ _ <| 𝟙 _

def freeLift {S : CondensedSet} {A : Condensed Ab} (e : S ⟶ A.forgetAb) : free S ⟶ A :=
  (condensedAbCondensedSetAdjunction.homEquiv _ _).symm e

@[simp]
theorem toFree_freeLift {S : CondensedSet} {A : Condensed Ab} (e : S ⟶ A.forgetAb) :
    toFree S ≫ (freeLift e).forgetAb = e :=
  by
  dsimp only [Condensed.forgetAb, to_free, free_lift, Quiver.Hom.forgetAb]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit, Category.assoc,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Condensed_Ab_CondensedSet_adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components, Category.comp_id]

theorem freeLift_unique {S : CondensedSet} {A : Condensed Ab} (e : S ⟶ A.forgetAb) (f : free S ⟶ A)
    (h : toFree S ≫ f.forgetAb = e) : f = freeLift e :=
  by
  apply_fun Condensed_Ab_CondensedSet_adjunction.hom_equiv _ _
  dsimp [free_lift]
  rw [Equiv.apply_symm_apply]
  exact h

@[ext]
theorem free_hom_ext {S : CondensedSet} {A : Condensed Ab} (f g : free S ⟶ A)
    (h : toFree S ≫ f.forgetAb = toFree S ≫ g.forgetAb) : f = g := by
  rw [free_lift_unique _ f rfl, free_lift_unique _ g rfl, h]

end CondensedAb

@[simps]
def homEquivEvaluation (S : Profinite.{u}) (A : Condensed Ab) :
    (ℤ[S] ⟶ A) ≃ (condensedAbToCondensedSet ⋙ CondensedSet.evaluation S).obj A :=
  (condensedAbCondensedSetAdjunction.homEquiv S.toCondensed A).trans <|
    (equivOfFullyFaithful <| sheafToPresheaf.{u} _ _).trans <| yoneda'Equiv _ _

theorem homEquivEvaluation_apply_eq_app_id (S : Profinite.{u}) (A : Condensed Ab) (f : ℤ[S] ⟶ A) :
    homEquivEvaluation S A f =
      (CondensedAb.toFree _ ≫ condensedAbToCondensedSet.map f).val.app _ ⟨𝟙 _⟩ :=
  rfl

theorem exists_homEquivEvaluation_symm_app_eq (S : Profinite.{u}) (A : Condensed Ab)
    (f : A.val.obj (Opposite.op S)) :
    ∃ t : ℤ[S].val.obj (Opposite.op S), ((homEquivEvaluation S A).symm f).val.app _ t = f :=
  by
  -- This proof can probably be made simpler using some adjunction voodoo...
  use(homEquivEvaluation _ _) (𝟙 _)
  dsimp [homEquivEvaluation, Adjunction.whiskerRight]
  simp_rw [← comp_apply, ← NatTrans.comp_app]
  erw [Category.comp_id, proetale_topology.toSheafify_sheafifyLift]
  dsimp [Functor.preimage, Full.preimage, yoneda'_equiv]
  simp only [comp_apply, AddCommGroupCat.free_map_coe, Category.id_comp, Category.comp_id]
  dsimp [Functor.rightUnitor, AddCommGroupCat.adj, Applicative.toFunctor]
  erw [Equiv.apply_symm_apply]
  simp only [op_id, CategoryTheory.Functor.map_id, id_apply, one_mul, MonoidHom.toFun_eq_coe,
    FreeGroup.lift.of, types_id_apply]

attribute [local instance] Limits.HasZeroObject.zero'

open CategoryTheory.Limits

open Opposite

-- sanity check
example (S : Profinite.{u}) : PreservesZeroObjects (Condensed.evaluation Ab.{u + 1} S) :=
  inferInstance

instance (S : Profinite.{u}) [Projective S] : Projective ℤ[S]
    where Factors A B f g hg := by
    rw [CategoryTheory.Limits.epi_iff_isZero_cokernel] at hg 
    -- this follows from the fact that evaluation preserves colimits.
    let e : (cokernel g).val.obj (op S) ≅ cokernel (g.val.app (op S)) :=
      by
      refine'
        (CategoryTheory.Limits.isColimitOfPreserves (Condensed.evaluation Ab S)
                (colimit.isColimit _)).coconePointUniqueUpToIso
            (colimit.isColimit _) ≪≫
          HasColimit.isoOfNatIso _
      refine' NatIso.ofComponents _ _
      · rintro (a | b); exact eq_to_iso rfl; exact eq_to_iso rfl
      rintro (a | b) (c | d) (e | e)
      all_goals dsimp
      all_goals simp; try rfl
    replace hg := CategoryTheory.Limits.isZero_of_preserves (Condensed.evaluation Ab.{u + 1} S) hg
    dsimp [Condensed.evaluation] at hg 
    replace hg := CategoryTheory.Limits.isZero_of_iso_of_zero hg e
    rw [← CategoryTheory.Limits.epi_iff_isZero_cokernel] at hg 
    replace hg : Function.Surjective (g.val.app (op S)) :=
      by
      skip
      apply AddCommGroupCat.surjective_of_epi
    let f₁ := homEquivEvaluation _ _ f
    dsimp at f₁ 
    obtain ⟨f', h⟩ := hg f₁
    use(homEquivEvaluation _ _).symm f'
    apply_fun homEquivEvaluation _ _
    change _ = f₁
    rw [← h, homEquivEvaluation_apply, Sheaf.Hom.comp_val, NatTrans.comp_app]
    erw [← comp_apply, ← comp_apply, Category.id_comp, ← NatTrans.comp_app, ← NatTrans.comp_app]
    dsimp [homEquivEvaluation]
    simp_rw [← Category.assoc, ← NatTrans.comp_app]
    rw [proetale_topology.toSheafify_sheafifyLift]
    rw [Adjunction.homEquiv_counit]
    dsimp
    simp only [Category.assoc, Adjunction.whiskerRight_counit_app_app]
    simp_rw [comp_apply]
    congr 1
    dsimp [Functor.preimage, yoneda'_equiv, Full.preimage, AddCommGroupCat.adj, CategoryTheory.uliftFunctor]
    change (FreeAbelianGroup.lift id) (_ <$> FreeAbelianGroup.of _) = _
    simp

theorem isZero_iff_forall_zero {A : Condensed.{u} Ab.{u + 1}} :
    IsZero A ↔ ∀ S : ExtrDisc, IsZero (A.val.obj (op S.val)) :=
  by
  constructor
  · intro h S
    apply CategoryTheory.Limits.isZero_of_preserves (Condensed.evaluation Ab.{u + 1} S.val)
    assumption
  · intro h
    let FF :=
      (Sheaf_to_presheaf _ _ : Condensed.{u} Ab.{u + 1} ⥤ _) ⋙
        (CategoryTheory.whiskeringLeft _ _ _).obj ExtrDisc_to_Profinite.op
    haveI : creates_colimits FF := by apply condensedToExtrDiscPresheafCreatesColimits
    suffices A ≅ ⊥_ _ by apply CategoryTheory.Limits.isZero_of_iso_of_zero _ this.symm; exact CategoryTheory.Limits.isZero_initial
    let e : ∀ S : ExtrDisc, A.val.obj (op S.val) ≅ ⊥_ _ := fun S =>
      IsZero.iso (h S) CategoryTheory.Limits.isZero_initial
    symm
    apply (colimit.isColimit _).coconePointUniqueUpToIso (_ : is_colimit (CategoryTheory.Limits.asEmptyCocone _))
    haveI := reflectsColimitsOfSizeShrink.{0, u + 1, 0, u + 1} FF
    apply isColimitOfReflects.{0, 0, u + 1, u + 1, u + 2, u + 2} FF
    apply CategoryTheory.Limits.evaluationJointlyReflectsColimits
    intro S
    have :=
      CategoryTheory.Limits.isColimitEmptyCoconeEquiv Ab (CategoryTheory.Limits.asEmptyCocone (A.val.obj (op S.unop.val)))
        (((evaluation ExtrDiscᵒᵖ Ab).obj S).mapCocone (FF.map_cocone (CategoryTheory.Limits.asEmptyCocone A)))
        (eq_to_iso rfl)
    apply this.toFun
    specialize e S.unop
    let t : CategoryTheory.Limits.asEmptyCocone (A.val.obj (op (unop S).val)) ≅ CategoryTheory.Limits.asEmptyCocone (⊥_ _) :=
      Cocones.ext e (by rintro ⟨⟨⟩⟩)
    apply IsColimit.ofIsoColimit _ t.symm
    refine' ⟨fun r => _, _, _⟩
    · dsimp; refine' initial.to r.X
    · simp only [as_empty_cocone_ι_app, id.def, autoParam_eq]
      rintro s ⟨⟨⟩⟩
    · tidy

theorem is_epi_iff_forall_surjective {A B : Condensed.{u} Ab.{u + 1}} (f : A ⟶ B) :
    Epi f ↔ ∀ S : ExtrDisc, Function.Surjective (f.val.app (op S.val)) :=
  by
  rw [CategoryTheory.Limits.epi_iff_isZero_cokernel]
  rw [isZero_iff_forall_zero]
  apply forall_congr' fun S => _
  let FF := Condensed.evaluation Ab.{u + 1} S.val
  haveI : preserves_colimits FF := inferInstance
  let e : (cokernel f).val.obj (op S.val) ≅ cokernel (f.val.app (op S.val)) :=
    by
    change FF.obj (cokernel f) ≅ cokernel (FF.map f)
    change (FF.map_cocone _).pt ≅ _
    refine'
      (CategoryTheory.Limits.isColimitOfPreserves FF (colimit.isColimit _)).coconePointUniqueUpToIso
          (colimit.isColimit _) ≪≫
        _
    dsimp
    apply HasColimit.isoOfNatIso
    -- This isomorphism is probably somewhere in mathlib... or somewhere in this repo.
    refine' NatIso.ofComponents _ _
    · rintro (i | i)
      · exact iso.refl _
      · exact iso.refl _
    · rintro (i | i) (j | j) (f | f)
      · dsimp; simpa
      · dsimp; simp
      · dsimp; simpa
      · dsimp; simpa
  have : is_zero ((cokernel f).val.obj (op S.val)) ↔ is_zero (cokernel (f.val.app (op S.val))) :=
    by
    constructor
    · intro h; apply CategoryTheory.Limits.isZero_of_iso_of_zero h e
    · intro h; apply CategoryTheory.Limits.isZero_of_iso_of_zero h e.symm
  rw [this, ← CategoryTheory.Limits.epi_iff_isZero_cokernel]
  clear e
  constructor
  · intro h; apply AddCommGroupCat.surjective_of_epi
  · intro h; exact ConcreteCategory.epi_of_surjective (f.val.app (op S.val)) h

theorem condensed_ab_has_enough_projectives_aux (A : Condensed.{u} Ab.{u + 1}) :
    ∃ (B : Condensed Ab) (hB : Projective B) (f : B ⟶ A), Epi f :=
  by
  let II := Σ S : ExtrDisc, A.val.obj (op S.val)
  let X : II → Condensed Ab := fun i => ℤ[i.1.val]
  let f : ∀ i, X i ⟶ A := fun i => (homEquivEvaluation i.1.val A).symm i.2
  -- Move this.
  haveI : has_colimits (Condensed.{u} Ab.{u + 1}) :=
    by
    change has_colimits (Sheaf _ _)
    exact CategoryTheory.Sheaf.CategoryTheory.Limits.hasColimits.{u + 2, u, u + 1}
  use∐ X, inferInstance, sigma.desc f
  rw [is_epi_iff_forall_surjective]
  intro S t
  obtain ⟨w, hw⟩ := exists_homEquivEvaluation_symm_app_eq S.val A t
  use(sigma.ι X ⟨S, t⟩).val.app (op S.val) w
  rw [← comp_apply, ← NatTrans.comp_app]
  change ((sigma.ι X ⟨S, t⟩ ≫ sigma.desc f).val.app (op S.val)) w = _
  erw [colimit.ι_desc]
  exact hw

instance condensed_ab_has_enough_projective : EnoughProjectives (Condensed.{u} Ab.{u + 1}) :=
  by
  constructor
  intro B
  obtain ⟨X, hX, f, hf⟩ := condensed_ab_has_enough_projectives_aux B
  skip
  constructor
  refine' ⟨X, hX, f, hf⟩

