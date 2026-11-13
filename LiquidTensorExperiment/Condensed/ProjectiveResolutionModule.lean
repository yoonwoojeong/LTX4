import LiquidTensorExperiment.Condensed.Ab
import LiquidTensorExperiment.Condensed.TopComparison
import LiquidTensorExperiment.Condensed.AdjunctionsModule
import LiquidTensorExperiment.Condensed.Extr.Equivalence
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.ModuleEpi

#align_import condensed.projective_resolution_module

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

variable (R : Type (u + 1)) [Ring R]

def CondensedMod.free (S : CondensedSet) : CondensedMod R :=
  (condensedSetToCondensedMod R).obj <| S

local notation R "[" S "]" => CondensedMod.free R S.toCondensed

variable {R}

def Condensed.forgetMod (S : CondensedMod R) : CondensedSet :=
  (condensedModToCondensedSet R).obj S

def Quiver.Hom.forgetMod {S T : CondensedMod R} (e : S ⟶ T) : S.forgetMod ⟶ T.forgetMod :=
  (condensedModToCondensedSet R).map e

variable (R)

namespace CondensedMod

def toFree (S : CondensedSet) : S ⟶ (free R S).forgetMod :=
  (condensedModCondensedSetAdjunction R).homEquiv _ _ <| 𝟙 _

def freeLift {S : CondensedSet} {A : CondensedMod R} (e : S ⟶ A.forgetMod) : free R S ⟶ A :=
  ((condensedModCondensedSetAdjunction R).homEquiv _ _).symm e

@[simp]
theorem toFree_freeLift {S : CondensedSet} {A : CondensedMod R} (e : S ⟶ A.forgetMod) :
    toFree R S ≫ (freeLift R e).forgetMod = e :=
  by
  dsimp only [Condensed.forgetMod, to_free, free_lift, Quiver.Hom.forgetMod]
  rw [adjunction.hom_equiv_unit, adjunction.hom_equiv_counit, category.assoc,
    CategoryTheory.Functor.map_id, category.id_comp, functor.map_comp,
    (condensedModCondensedSetAdjunction R).unit_naturality_assoc,
    adjunction.right_triangle_components, category.comp_id]

theorem freeLift_unique {S : CondensedSet} {A : CondensedMod R} (e : S ⟶ A.forgetMod)
    (f : free R S ⟶ A) (h : toFree R S ≫ f.forgetMod = e) : f = freeLift R e :=
  by
  apply_fun (condensedModCondensedSetAdjunction R).homEquiv _ _
  dsimp [free_lift]
  rw [Equiv.apply_symm_apply]
  exact h

@[ext]
theorem free_hom_ext {S : CondensedSet} {A : CondensedMod R} (f g : free R S ⟶ A)
    (h : toFree R S ≫ f.forgetMod = toFree R S ≫ g.forgetMod) : f = g := by
  rw [free_lift_unique _ _ f rfl, free_lift_unique _ _ g rfl, h]

end CondensedMod

@[simps]
def homEquivEvaluationMod (S : Profinite.{u}) (A : CondensedMod R) :
    (R[S] ⟶ A) ≃ (condensedModToCondensedSet R ⋙ CondensedSet.evaluation S).obj A :=
  ((condensedModCondensedSetAdjunction R).homEquiv S.toCondensed A).trans <|
    (equivOfFullyFaithful <| sheafToPresheaf.{u} _ _).trans <| yoneda'Equiv _ _

theorem homEquivEvaluationMod_apply_eq_app_id (S : Profinite.{u}) (A : CondensedMod R)
    (f : R[S] ⟶ A) :
    homEquivEvaluationMod R S A f =
      (CondensedMod.toFree R _ ≫ (condensedModToCondensedSet R).map f).val.app _ ⟨𝟙 _⟩ :=
  rfl

open scoped BigOperators

theorem exists_hom_equiv_Mod_evaluation_symm_app_eq (S : Profinite.{u}) (A : CondensedMod R)
    (f : A.val.obj (Opposite.op S)) :
    ∃ t : R[S].val.obj (Opposite.op S), ((homEquivEvaluationMod R S A).symm f).val.app _ t = f :=
  by
  -- This proof can probably be made simpler using some adjunction voodoo...
  use(homEquivEvaluationMod _ _ _) (𝟙 _)
  dsimp [homEquivEvaluationMod, adjunction.whisker_right]
  simp_rw [← comp_apply, ← nat_trans.comp_app]
  erw [category.comp_id, proetale_topology.to_sheafify_sheafify_lift]
  dsimp [functor.preimage, full.preimage, yoneda'_equiv, condensedModToCondensedSet,
    functor.right_unitor, ulift_functor, Profinite.toCondensed]
  have := (ModuleCat.adj R).right_triangle_components
  apply_fun fun e => e f at this 
  dsimp at this 
  convert this
  dsimp [ModuleCat.adj]
  erw [Finsupp.lift_symm_apply (A.val.obj (Opposite.op S) →₀ R) R _ LinearMap.id f]
  erw [Finsupp.lift_symm_apply (ULift (S ⟶ S) →₀ R) R _ LinearMap.id (ULift.up (𝟙 S))]
  simp

attribute [local instance] limits.has_zero_object.has_zero

open CategoryTheory.Limits

open Opposite

-- sanity check
example (S : Profinite.{u}) : PreservesZeroObjects (Condensed.evaluation (ModuleCat.{u + 1} R) S) :=
  inferInstance

instance projective_free_condensedMod (S : Profinite.{u}) [Projective S] : Projective (R[S])
    where Factors A B f g hg := by
    rw [epi_iff_is_zero_cokernel] at hg 
    -- this follows from the fact that evaluation preserves colimits.
    let e : (cokernel g).val.obj (op S) ≅ cokernel (g.val.app (op S)) :=
      by
      refine'
        (is_colimit_of_preserves (Condensed.evaluation (ModuleCat R) S)
                (colimit.is_colimit _)).coconePointUniqueUpToIso
            (colimit.is_colimit _) ≪≫
          has_colimit.iso_of_nat_iso _
      refine' nat_iso.of_components _ _
      · rintro (a | b); exact eq_to_iso rfl; exact eq_to_iso rfl
      rintro (a | b) (c | d) (e | e)
      all_goals dsimp
      all_goals simp; try rfl
    replace hg := is_zero_of_preserves (Condensed.evaluation (ModuleCat.{u + 1} R) S) hg
    dsimp [Condensed.evaluation] at hg 
    replace hg := is_zero_of_iso_of_zero hg e
    rw [← epi_iff_is_zero_cokernel] at hg 
    replace hg : Function.Surjective (g.val.app (op S)) :=
      by
      skip
      apply ModuleCat.surjective_of_epi
    let f₁ := homEquivEvaluationMod _ _ _ f
    dsimp at f₁ 
    obtain ⟨f', h⟩ := hg f₁
    use(homEquivEvaluationMod _ _ _).symm f'
    apply_fun homEquivEvaluationMod _ _ _
    change _ = f₁
    rw [← h, homEquivEvaluationMod_apply, Sheaf.hom.comp_val, nat_trans.comp_app]
    dsimp [homEquivEvaluationMod, adjunction.whisker_right, functor.associator]
    erw [category.id_comp, ← comp_apply, ← comp_apply, ← category.assoc, ← nat_trans.comp_app, ←
      nat_trans.comp_app]
    erw [proetale_topology.to_sheafify_sheafify_lift]
    dsimp [functor.preimage, full.preimage, yoneda'_equiv, ulift_functor,
      condensedModToCondensedSet, Profinite.toCondensed]
    congr 1
    have := (ModuleCat.adj R).right_triangle_components
    apply_fun fun e => e f' at this 
    dsimp at this 
    convert this
    dsimp [ModuleCat.adj]
    erw [Finsupp.lift_symm_apply (A.val.obj (Opposite.op S) →₀ R) R _ LinearMap.id f']
    erw [Finsupp.lift_symm_apply (ULift (S ⟶ S) →₀ R) R _ LinearMap.id (ULift.up (𝟙 S))]
    simp

theorem isZero_iff_forall_zero_Mod {A : CondensedMod R} :
    IsZero A ↔ ∀ S : ExtrDisc, IsZero (A.val.obj (op S.val)) :=
  by
  constructor
  · intro h S
    apply is_zero_of_preserves (Condensed.evaluation (ModuleCat.{u + 1} R) S.val)
    assumption
  · intro h
    let FF :=
      (Sheaf_to_presheaf _ _ : CondensedMod R ⥤ _) ⋙
        (whiskering_left _ _ _).obj ExtrDisc_to_Profinite.op
    suffices A ≅ ⊥_ _ by apply is_zero_of_iso_of_zero _ this.symm; exact is_zero_initial
    let e : ∀ S : ExtrDisc, A.val.obj (op S.val) ≅ ⊥_ _ := fun S =>
      is_zero.iso (h S) is_zero_initial
    symm
    apply (colimit.is_colimit _).coconePointUniqueUpToIso (_ : is_colimit (as_empty_cocone _))
    haveI : creates_colimits FF :=
      @condensedToExtrDiscPresheafCreatesColimits.{u, u + 2} (@ModuleCat.{u + 1, u + 1} R _)
        (@ModuleCat.moduleCategory.{u + 1, u + 1} R _) _ _ _ _ _
    haveI := reflectsColimitsOfSizeShrink.{0, u + 1, 0, u + 1} FF
    apply isColimitOfReflects.{0, 0, u + 1, u + 1, u + 2, u + 2} FF
    apply evaluation_jointly_reflects_colimits
    intro S
    have :=
      is_colimit_empty_cocone_equiv (ModuleCat R) (as_empty_cocone (A.val.obj (op S.unop.val)))
        (((evaluation ExtrDiscᵒᵖ (ModuleCat R)).obj S).mapCocone
          (FF.map_cocone (as_empty_cocone A)))
        (eq_to_iso rfl)
    apply this.to_fun
    specialize e S.unop
    let t : as_empty_cocone (A.val.obj (op (unop S).val)) ≅ as_empty_cocone (⊥_ _) :=
      cocones.ext e (by rintro ⟨⟨⟩⟩)
    apply is_colimit.of_iso_colimit _ t.symm
    refine' ⟨fun r => _, _, _⟩
    · dsimp; refine' initial.to r.X
    · rintro s ⟨⟨⟩⟩
    · intro s m h; apply is_zero.eq_of_src; apply is_zero_initial

theorem is_epi_iff_forall_surjective_Mod {A B : CondensedMod R} (f : A ⟶ B) :
    Epi f ↔ ∀ S : ExtrDisc, Function.Surjective (f.val.app (op S.val)) :=
  by
  rw [epi_iff_is_zero_cokernel]
  rw [isZero_iff_forall_zero_Mod]
  apply forall_congr' fun S => _
  let FF := Condensed.evaluation (ModuleCat.{u + 1} R) S.val
  haveI : preserves_colimits FF := inferInstance
  let e : (cokernel f).val.obj (op S.val) ≅ cokernel (f.val.app (op S.val)) :=
    by
    change FF.obj (cokernel f) ≅ cokernel (FF.map f)
    change (FF.map_cocone _).pt ≅ _
    refine'
      (is_colimit_of_preserves FF (colimit.is_colimit _)).coconePointUniqueUpToIso
          (colimit.is_colimit _) ≪≫
        _
    dsimp
    apply has_colimit.iso_of_nat_iso
    -- This isomorphism is probably somewhere in mathlib... or somewhere in this repo.
    refine' nat_iso.of_components _ _
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
    · intro h; apply is_zero_of_iso_of_zero h e
    · intro h; apply is_zero_of_iso_of_zero h e.symm
  rw [this, ← epi_iff_is_zero_cokernel]
  clear e
  constructor
  · intro h
    apply ModuleCat.surjective_of_epi
  · intro h; exact concrete_category.epi_of_surjective (f.val.app (op S.val)) h

theorem condensedMod_has_enough_projectives_aux (A : CondensedMod R) :
    ∃ (B : CondensedMod R) (hB : Projective B) (f : B ⟶ A), Epi f :=
  by
  let II := Σ S : ExtrDisc, A.val.obj (op S.val)
  let X : II → CondensedMod R := fun i => R[i.1.val]
  let f : ∀ i, X i ⟶ A := fun i => (homEquivEvaluationMod _ i.1.val A).symm i.2
  -- Move this.
  haveI : has_colimits (CondensedMod R) :=
    by
    change has_colimits (Sheaf _ _)
    exact CategoryTheory.Sheaf.CategoryTheory.Limits.hasColimits.{u + 2, u, u + 1}
  use∐ X, inferInstance, sigma.desc f
  rw [is_epi_iff_forall_surjective_Mod]
  intro S t
  obtain ⟨w, hw⟩ := exists_hom_equiv_Mod_evaluation_symm_app_eq R S.val A t
  use(sigma.ι X ⟨S, t⟩).val.app (op S.val) w
  rw [← comp_apply, ← nat_trans.comp_app]
  change ((sigma.ι X ⟨S, t⟩ ≫ sigma.desc f).val.app (op S.val)) w = _
  erw [colimit.ι_desc]
  exact hw

instance condensedMod_has_enough_projective : EnoughProjectives (CondensedMod R) :=
  by
  constructor
  intro B
  obtain ⟨X, hX, f, hf⟩ := condensedMod_has_enough_projectives_aux R B
  skip
  constructor
  refine' ⟨X, hX, f, hf⟩

