import LiquidTensorExperiment.Condensed.Tensor
import LiquidTensorExperiment.ForMathlib.PreservesFiniteLimits

#align_import condensed.tensor_short_exact

noncomputable section

universe u

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits Opposite

namespace AddCommGroupCat

@[reassoc]
theorem mapTensor_flip {A B C D : AddCommGroupCat} (f : A ⟶ B) (g : C ⟶ D) :
    mapTensor f g ≫ (tensorFlip _ _).Hom = (tensorFlip _ _).Hom ≫ mapTensor g f := by
  apply AddCommGroupCat.tensor_ext; intro a c; rfl

end AddCommGroupCat

namespace Condensed

def tensorTunit (A : AddCommGroupCat) (h : AddCommGroupCat.IsTensorUnit A) :
    tensorFunctor.flip.obj A ≅ 𝟭 _ :=
  by
  refine' _ ≪≫ (condensedExtrSheafEquiv Ab).counitIso
  refine' nat_iso.of_components _ _
  · intro M
    refine' (condensedExtrSheafEquiv Ab).Functor.mapIso _
    refine' Sheaf.iso.mk _ _ _
    refine' nat_iso.of_components _ _
    · intro S
      refine' (AddCommGroup.tensor_functor_iso_flip.app _).app _ ≪≫ _
      refine' AddCommGroupCat.tensorUnitIso _ _ h
    · intro S T f
      dsimp [ExtrSheaf.tensor, AddCommGroupCat.tensorFunctorIsoFlip]
      simp only [category.assoc]
      erw [AddCommGroupCat.tensorUnitIso_naturality]
      rw [← AddCommGroupCat.mapTensor_flip_assoc]; rfl
  · intro M N f
    dsimp only [tensor_functor, map_tensor, functor.flip_obj_map, functor.comp_map,
      functor.map_iso_hom]
    simp only [← functor.map_comp]; congr 1
    ext S : 3
    dsimp only [Sheaf.category_theory.category_comp_val, ExtrSheaf.mapTensor_val,
      Sheaf.iso.mk_hom_val, nat_iso.of_components_hom_app, nat_trans.comp_app,
      ExtrSheafProd.mapTensor_val_app, iso.trans_hom]
    simp only [category.assoc]
    dsimp [AddCommGroupCat.tensorFunctorIsoFlip]
    rw [AddCommGroupCat.mapTensor_flip_assoc]; congr 1
    symm; apply AddCommGroupCat.tensorUnitIso_naturality

def tensorPunit : tensorFunctor.flip.obj (AddCommGroupCat.of (PUnit →₀ ℤ)) ≅ 𝟭 _ :=
  tensorTunit _ <| by
    dsimp [AddCommGroupCat.IsTensorUnit]
    refine' ⟨Finsupp.single PUnit.unit 1, _⟩
    intro B; constructor
    · intro f g h; ext ⟨⟩; exact h
    · intro b; refine' ⟨(Finsupp.total _ _ _ _).toAddMonoidHom, _⟩
      · intro; exact b
      · dsimp; simp only [Finsupp.total_single, one_zsmul]

-- See comment around L20
instance preserves_mono_tensorFunctor (A : Condensed.{u} Ab.{u + 1})
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (A.val.obj (op S.val))] {X Y : Ab} (f : X ⟶ Y)
    [Mono f] : Mono ((tensorFunctor.obj A).map f) :=
  by
  suffices mono (ExtrSheaf.mapTensor ((condensedExtrSheafEquiv Ab).inverse.map (𝟙 A)) f) by
    dsimp only [tensor_functor, map_tensor]; skip; infer_instance
  constructor; intro X φ ψ h; ext S : 3
  apply_fun fun η => η.val.app S at h 
  dsimp [ExtrSheaf.mapTensor] at h 
  refine' (@cancel_mono _ _ _ _ _ _ (id _) _ _).mp h
  apply (config := { instances := false }) AddCommGroupCat.tensor_obj_map_preserves_mono
  infer_instance; apply_assumption

/-
We need one of the following two sorries.
If we prove the first, we can deduce the second using `exact_functor.lean`
But maybe it is easier to just prove `preserves_finite_limits_tensor_functor` second directly.
-/
-- lemma tensor_eval_iso_natural_right
--   (A : (Condensed.{u} Ab.{u+1})) {X Y : Ab} (f : X ⟶ Y) (S : ExtrDisc) :
--   AddCommGroup.map_tensor (𝟙 (A.val.obj (op S.val))) f ≫ (tensor_eval_iso A Y S).inv =
--   (tensor_eval_iso A X S).inv ≫ ((tensor_functor.obj A).map f).val.app (op S.val) :=
-- begin
--   rw [iso.comp_inv_eq],
--   dsimp only [tensor_eval_iso, tensor_functor, map_tensor,
--     functor.map_iso_hom, iso.app_hom, functor.map_iso_inv, iso.app_inv, iso.symm_hom, iso.symm_inv,
--     Sheaf_to_presheaf_map],
--   -- erw [equivalence.unit_app_inverse],
--   admit
-- end
-- lemma tensor_short_exact (A : (Condensed.{u} Ab.{u+1}))
--   [∀ S : ExtrDisc.{u}, no_zero_smul_divisors ℤ (A.val.obj (op S.val))]
--   {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : short_exact f g) :
--   short_exact ((tensor_functor.obj A).map f) ((tensor_functor.obj A).map g) :=
-- begin
--   rw short_exact_iff_ExtrDisc, intro S,
--   let eX := tensor_eval_iso A X S,
--   let eY := tensor_eval_iso A Y S,
--   let eZ := tensor_eval_iso A Z S,
--   refine commsq.short_exact.of_iso eX.inv eY.inv eZ.inv _ _ _,
--   { refine (AddCommGroup.tensor_functor.obj _).map f, },
--   { refine (AddCommGroup.tensor_functor.obj _).map g, },
--   { apply AddCommGroup.tensor_short_exact, exact hfg },
--   { apply commsq.of_eq, apply tensor_eval_iso_natural_right },
--   { apply commsq.of_eq, apply tensor_eval_iso_natural_right },
-- end
-- See comment around L20
instance preservesFiniteLimitsTensorFunctor (A : Condensed.{u} Ab.{u + 1})
    [∀ S : ExtrDisc.{u}, NoZeroSMulDivisors ℤ (A.val.obj (op S.val))] :
    PreservesFiniteLimits (tensorFunctor.obj A) :=
  preservesFiniteLimitsOfPreservesMonoPreservesFiniteColimits _ fun X Y f hf => by skip;
    infer_instance

end Condensed

