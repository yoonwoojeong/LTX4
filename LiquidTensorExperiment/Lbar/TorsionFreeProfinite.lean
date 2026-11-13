import Mathlib.Algebra.Category.GroupCat.Limits
import LiquidTensorExperiment.ForMathlib.Profinite.Extend
import LiquidTensorExperiment.Lbar.Basic
import LiquidTensorExperiment.Lbar.Functor
import LiquidTensorExperiment.PseudoNormedGroup.Category.StrictProFiltPseuNormGrpWithTinv
import LiquidTensorExperiment.PseudoNormedGroup.BoundedLimits

#align_import Lbar.torsion_free_profinite

noncomputable section

universe u v

open scoped NNReal

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

open Lbar Profinite CommGroupCat CategoryTheory.Limits

theorem limit_torsion_free_to_ab {C : Type u} [CategoryTheory.SmallCategory C] (J : C ⥤ Ab.{u})
    (h_tf : ∀ j, NoZeroSMulDivisors ℤ (J.obj j)) : NoZeroSMulDivisors ℤ (limit J).α :=
  by
  let L := get_limit_cone _
  haveI := AddCommGroupCat.forgetPreservesLimitsOfSize.{u, u}
  have h_inj :=
    @Concrete.to_product_injective_of_isLimit.{u} AddCommGroupCat.{u} _ _ C _ J _ L.cone L.is_limit
  fconstructor
  intro c x hx
  let φ := fun x : limit J => fun j => (L.cone.π.app j) x
  have h1 : φ 0 = 0 := by
    ext j
    exact (L.cone.π.app j).2
  have h2 : φ (c • x) = c • φ x := by
    ext j
    exact map_zsmul (L.cone.π.app j) _ _
  apply_fun φ at hx 
  simp only [h1, h2, Pi.zero_def, Function.funext_iff, Pi.smul_apply, smul_eq_zero] at hx 
  by_cases hc : c = 0
  · apply Or.intro_left; exact hc
  · simp only [hc, false_or_iff] at hx 
    apply Or.intro_right
    apply h_inj
    funext j
    specialize hx j
    simp only [_root_.map_zero]
    exact hx

--[FAE] not needed for LTE, may be for mathlib?
theorem AddCommGroup.limit_on_nat_torsion_free
    (J : CategoryTheory.AsSmall.{u} ℕ ⥤ AddCommGroupCat.{u})
    (h_tf : ∀ j, NoZeroSMulDivisors ℤ (J.obj j)) : NoZeroSMulDivisors ℤ (limit J).α :=
  limit_torsion_free_to_ab J h_tf

open CompHausFiltPseuNormGrp₁ CategoryTheory

instance : ConcreteCategory.{u} PseuNormGrp₁.{u}
    where
  forget :=
    { obj := fun M => M
      map := fun M N f => f
      map_id' := fun M => rfl
      map_comp' := fun _ _ _ f g => rfl }
  forget_faithful := { map_injective' := fun M N f g h => by ext; dsimp at h ; rw [h] }

theorem PNG₁.iso_injective {X Y : PseuNormGrp₁.{u}} (f : X ≅ Y) : Function.Injective f.Hom :=
  by
  intro x y h
  apply_fun f.inv at h 
  simp only [← CategoryTheory.comp_apply, f.hom_inv_id] at h 
  exact h

theorem PNG₁.map_zsmul {X Y : PseuNormGrp₁} (f : X ⟶ Y) (n : ℤ) (x : X) : f (n • x) = n • f x :=
  f.toAddMonoidHom.map_zsmul _ _

namespace Profinite

theorem extend_torsion_free (A : FintypeCat.{u} ⥤ CompHausFiltPseuNormGrp₁)
    (hA : ∀ X, NoZeroSMulDivisors ℤ (A.obj X)) (S : Profinite) :
    NoZeroSMulDivisors ℤ ((Profinite.extend A).obj S) :=
  by
  let T := Ab.explicitLimitCone.{u, u} ((S.fintype_diagram ⋙ A ⋙ to_PNG₁) ⋙ PseuNormGrp₁.toAb)
  set T' := limit.cone.{u, u} ((S.fintype_diagram ⋙ A ⋙ to_PNG₁) ⋙ PseuNormGrp₁.toAb) with hT'
  let hT : is_limit T := Ab.explicitLimitConeIsLimit _
  let E := PseuNormGrp₁.boundedCone.{u} ⟨T, hT⟩
  let hE : is_limit E := PseuNormGrp₁.boundedConeIsLimit _
  suffices claim : NoZeroSMulDivisors ℤ E.X
  · skip
    let iso : to_PNG₁.obj ((extend A).obj S) ≅ E.X :=
      (is_limit_of_preserves to_PNG₁ (limit.is_limit _)).conePointUniqueUpToIso hE
    apply Function.Injective.noZeroSMulDivisors iso.hom (PNG₁.iso_injective _)
    any_goals infer_instance
    · apply StrictPseudoNormedGroupHom.map_zero
    · intros; rw [PNG₁.map_zsmul]
  let ι : E.X →+ T.X := AddSubgroup.subtype _
  apply Function.Injective.noZeroSMulDivisors ι Subtype.val_injective.{u + 1} ι.map_zero
  any_goals infer_instance
  · intro c x; apply ι.map_zsmul
  let iso_pts :=
    functor.map_iso (Limits.Cones.forget.{u} _)
      (hT.unique_up_to_iso (LimitCone.isLimit.{u, u, u, u + 1} _))
  let φ := @Iso.addCommGroupIsoToAddEquiv.{u} T.X T'.X iso_pts
  apply Function.Injective.noZeroSMulDivisors φ φ.injective φ.map_zero
  · intro c x
    exact map_zsmul φ _ _
  apply limit_torsion_free_to_ab.{u}
  intro j
  exact hA (S.fintype_diagram.obj j)

end Profinite

