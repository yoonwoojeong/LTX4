import LiquidTensorExperiment.ForMathlib.Derived.DerivedCat
import LiquidTensorExperiment.ForMathlib.Derived.Example
import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.ForMathlib.ShortExact
import LiquidTensorExperiment.ForMathlib.Derived.ProjectiveResolution

#align_import for_mathlib.derived.Ext_lemmas

open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Limits

namespace BoundedDerivedCategory

variable (A : Type _) [Category A] [Abelian A] [EnoughProjectives A]

instance ext_additive_fst (i : ℤ) (X : BoundedDerivedCategory A) :
    ((ext A i).flip.obj X).rightOp.Additive
    where map_add' := by
    intro Y Z f g; dsimp
    conv_rhs => rw [← op_add]; congr 1; ext e
    dsimp; rw [preadditive.add_comp]

instance extHomologicalFst (i : ℤ) (X : BoundedDerivedCategory A) :
    homologicalFunctor ((ext A i).flip.obj X).rightOp :=
  CategoryTheory.Triangulated.preadditiveYonedaOpHomological (X⟦i⟧)

noncomputable def ext'ZeroFlipIso (B : A) : (ext' 0).flip.obj B ≅ preadditiveYoneda.obj B :=
  Iso.symm <|
    NatIso.ofComponents (fun X => (ProjectiveResolution.of X.unop).extSingleIsoHom _)
      (by
        intro X Y f; ext F
        dsimp [ProjectiveResolution.Ext_single_iso_hom, ProjectiveResolution.Ext_iso,
          BoundedHomotopyCategory.extIso, ProjectiveResolution.hom_to, ext',
          BoundedHomotopyCategory.ext]
        simp only [comp_apply]
        dsimp
        simp only [functor.map_comp, category.assoc, BoundedHomotopyCategory.lift_lifts_assoc])

-- move me
theorem ext'_zero_left_isZero {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐] (A : 𝓐ᵒᵖ)
    (B : 𝓐) (hA : IsZero A) (i : ℤ) : IsZero (((ext' i).obj A).obj B) :=
  by
  rw [is_zero_iff_id_eq_zero] at hA ⊢
  rw [← functor.flip_obj_obj, ← CategoryTheory.Functor.map_id, hA, functor.map_zero]

theorem ext'_isZero_of_projective {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]
    (A B : 𝓐) (hA : Projective A) (i : ℤ) (hi : 0 < i) :
    IsZero (((ext' i).obj (Opposite.op A)).obj B) :=
  by
  let this.1 := ext'Iso (Opposite.op A) B i
  dsimp at this 
  refine' is_zero_of_iso_of_zero _ (this _ (𝟙 _) _).symm
  swap
  · refine' ⟨_, _, _⟩
    · rintro (_ | n); · exact hA; · exact projective_zero
    · apply exact_zero_left_of_mono
    · intro; apply exact_zero_left_of_mono
  rcases i with ((_ | i) | i)
  · exfalso; revert hi; decide
  swap
  · exfalso; revert hi; decide
  refine' is_zero.homology_is_zero _ _ _ _
  refine' AddCommGroupCat.isZero_of_eq _ _
  intro f g
  apply CategoryTheory.Limits.HasZeroObject.from_zero_ext

end BoundedDerivedCategory

