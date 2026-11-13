import LiquidTensorExperiment.ForMathlib.Derived.KProjective
import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp
import LiquidTensorExperiment.ForMathlib.HomologyIsoAb
import LiquidTensorExperiment.ForMathlib.HomSingleIso

#align_import for_mathlib.hom_single_iso2

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {C : Type u} {ι : Type _} [Category.{v} C] [Abelian C] {c : ComplexShape ι}

namespace BoundedHomotopyCategory

open HomSingleIsoSetup Opposite

theorem aux₁_naturality_snd_var (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂) :
    (aux₁ P B₁ i).Hom ≫
        (homology'Functor AddCommGroupCat (ComplexShape.up ℤ).symm i).map
          ((NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) (ComplexShape.up ℤ).symm).app
            P.val.as.op) =
      mapHomComplexHomology _ _ f _ _ ≫ (aux₁ P B₂ i).Hom :=
  by
  rw [← iso.comp_inv_eq]
  ext : 2
  dsimp only [aux₁, iso.symm_hom, iso.symm_inv, homology_iso', homology'.mapIso]
  simp only [category.assoc]
  rw [homology'.map_eq_desc'_lift_left, homology'.π'_desc'_assoc, homology'.map_eq_lift_desc'_left,
    homology'.lift_ι, map_hom_complex_homology, homology'.map_eq_lift_desc'_left, homology'.lift_ι,
    homology'.π'_desc']
  dsimp only [arrow.hom_mk_left, map_hom_complex', nat_trans.map_homological_complex_app_f,
    homology'Functor_map]
  let t : _ := _; show _ ≫ _ ≫ t = _
  have ht : t = homology'.ι _ _ _ ≫ cokernel.map _ _ (HomologicalComplex.xPrevIso _ _).Hom (𝟙 _) _
  rotate_left 2; · dsimp; rfl; · rw [category.comp_id]; apply HomologicalComplex.dTo_eq
  · ext1; erw [homology'.π'_ι_assoc, homology'.π'_desc', cokernel.π_desc]; rfl
  rw [ht, homology'.map_eq_lift_desc'_right, homology'.lift_ι_assoc]; clear ht t
  let t : _ := _; show t ≫ _ = _
  have ht : t = kernel.map _ _ (𝟙 _) (HomologicalComplex.xNextIso _ _).inv _ ≫ homology'.π' _ _ _
  rotate_left 2; · dsimp; apply sub_add_cancel
  · rw [category.id_comp]; symm; apply HomologicalComplex.dFrom_eq
  · ext1; erw [homology'.lift_ι, category.assoc, homology'.π'_ι, kernel.lift_ι_assoc]; rfl
  rw [ht, category.assoc, homology'.π'_desc'_assoc, category.assoc, category.assoc]; clear ht t
  rw [kernel.lift_ι_assoc, cokernel.π_desc]
  simp only [category.assoc, category.id_comp]; rfl

theorem aux₂_naturality_snd_var (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂) :
    (aux₂ P B₁ i).inv ≫ P.mapHomComplexHomology i f _ (HomologicalComplex.d_comp_d _ _ _ _) =
      AddCommGroupCat.homologyMap (HomologicalComplex.d_comp_d _ _ _ _)
          (HomologicalComplex.d_comp_d _ _ _ _)
          (Commsq.ofEq <| ((mapHomComplex' _ f).comm _ _).symm)
          (Commsq.ofEq <| ((mapHomComplex' _ f).comm _ _).symm) ≫
        (aux₂ P B₂ i).inv :=
  by
  dsimp only [aux₂, map_hom_complex_homology]
  rw [← AddCommGroupCat.homologyIso_inv_homologyMap]
  congr 1
  dsimp only [homology'.map']
  erw [← HasHomology.homology'_map_eq']
  congr

theorem QuotientAddGroup.lift_mk'' {G H : Type _} [AddGroup G] [AddGroup H] (N : AddSubgroup G)
    [N.Normal] {φ : G →+ H} (HN : ∀ x : G, x ∈ N → φ x = 0) (g : G) :
    (QuotientAddGroup.lift N φ HN) (QuotientAddGroup.mk' N g) = φ g :=
  QuotientAddGroup.lift_mk' _ _ _

theorem AddCommGroupCat.hasHomology_ι_eq {A B C : AddCommGroupCat} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) :
    (AddCommGroupCat.hasHomology f g w).ι =
      (AddCommGroupCat.ofHom <|
          QuotientAddGroup.lift _ ((QuotientAddGroup.mk' f.range).comp g.ker.Subtype)
            (by
              rintro x ⟨a, ha⟩
              simp only [AddMonoidHom.comp_apply, QuotientAddGroup.coe_mk',
                QuotientAddGroup.eq_zero_iff]
              exact ⟨a, ha⟩)) ≫
        (AddCommGroupCat.cokernelIsoRangeQuotient _).inv :=
  by
  dsimp only [AddCommGroupCat.hasHomology, AddCommGroupCat.ofHom]
  ext x
  apply_fun (AddCommGroupCat.cokernelIsoRangeQuotient f).Hom
  ·
    simp only [AddMonoidHom.comp_apply, comp_apply, quotient_add_group.lift_mk'',
      AddCommGroupCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply,
      CategoryTheory.Iso.inv_hom_id_apply]
  · erw [← AddCommGroupCat.mono_iff_injective]; infer_instance

theorem AddMonoidHom.liftOfSurjective_apply {A B C : Type _} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (hf : Function.Surjective f) (g : { g : A →+ C // f.ker ≤ g.ker })
    (a : A) : AddMonoidHom.liftOfSurjective f hf g (f a) = g a :=
  by
  show g _ = g _
  erw [← sub_eq_zero, ← g.val.map_sub, ← g.val.mem_ker]
  apply g.2
  rw [f.mem_ker, f.map_sub, sub_eq_zero]
  apply Function.surjInv_eq

theorem AddEquiv.symm_mk_apply {A B : Type _} [AddCommGroup A] [AddCommGroup B] (f : A → B)
    (g : B → A) (h1) (h2) (h3) (b : B) : AddEquiv.symm ⟨f, g, h1, h2, h3⟩ b = g b :=
  rfl

theorem AddMonoidHom.subtype_mk_apply {A B : Type _} [AddCommGroup A] [AddCommGroup B]
    (p : (A →+ B) → Prop) (f : A →+ B) (hf : p f) (a : A) : Subtype.mk f hf a = f a :=
  rfl

theorem homological_complex_hom_single_iso_natural_aux (P : BoundedHomotopyCategory C) {B₁ B₂ : C}
    (i : ℤ) (f : B₁ ⟶ B₂) (φ : AddMonoidHom.ker ((homComplex P B₁).d i (i - 1))) :
    ((mapHomComplex' P f).f i) φ ∈ AddMonoidHom.ker ((homComplex P B₂).d i (i - 1)) :=
  by
  cases' φ with φ hφ
  rw [AddMonoidHom.mem_ker] at hφ ⊢
  rw [← comp_apply, (map_hom_complex' P f).comm, comp_apply]
  erw [hφ, map_zero]

attribute [simps] eq_to_iso

theorem homologicalComplex_homSingleIso_natural (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (i : ℤ)
    (f : B₁ ⟶ B₂) (φ : AddMonoidHom.ker ((homComplex P B₁).d i (i - 1))) :
    HomotopyCategory.quotientMapHom P.val.as ((HomologicalComplex.single C _ i).obj B₁)
          ((HomologicalComplex.homSingleIso P.val.as B₁ i).symm φ) ≫
        (single C i).map f =
      HomotopyCategory.quotientMapHom P.val.as ((HomologicalComplex.single C _ i).obj B₂)
        ((HomologicalComplex.homSingleIso P.val.as B₂ i).symm
          ⟨(mapHomComplex' P f).f i φ, homological_complex_hom_single_iso_natural_aux P i f φ⟩) :=
  by
  dsimp only [HomotopyCategory.quotientMapHom, AddMonoidHom.mk'_apply, single,
    HomotopyCategory.single, functor.comp_map]
  rw [← functor.map_comp]; congr 1
  ext n
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.homSingleIso_symm_apply_f]
  split_ifs with hin; swap; · rw [zero_comp]
  subst n
  simp only [category.assoc]; refine' congr_arg₂ _ rfl _
  dsimp only [map_hom_complex', nat_trans.map_homological_complex_app_f,
    preadditive_yoneda_map_app_apply]
  simp only [category.assoc]; refine' congr_arg₂ _ rfl _
  dsimp only [HomologicalComplex.single]
  rw [← CategoryTheory.eqToIso_hom, ← iso.eq_inv_comp]
  exact dif_pos rfl

theorem homSingleIso_naturality_snd_var_good (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (i : ℤ)
    (f : B₁ ⟶ B₂) :
    (homSingleIso P B₁ i).Hom ≫
        (homology'Functor _ _ i).map
          (NatTrans.app (NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) _) _) =
      (preadditiveYoneda.map <| (single C i).map f).app (op P) ≫ (homSingleIso P B₂ i).Hom :=
  by
  dsimp only [hom_single_iso, iso.trans_hom, iso.symm_hom, functor.comp_map, functor.op_map,
    functor.right_op_map, Quiver.Hom.unop_op]
  simp only [category.assoc]
  rw [aux₁_naturality_snd_var]
  simp_rw [← category.assoc]; congr 1; simp_rw [category.assoc]
  rw [aux₂_naturality_snd_var]
  simp_rw [← category.assoc]; congr 1
  rw [← iso.eq_inv_comp]
  apply (AddCommGroupCat.hasHomology _ _ _).ext_ι
  apply (AddCommGroupCat.hasHomology _ _ _).ext_π
  rotate_left; · apply HomologicalComplex.d_comp_d; · apply HomologicalComplex.d_comp_d
  rw [AddCommGroupCat.homologyMap, HasHomology.map_ι, HasHomology.π_comp_desc]
  dsimp only [map_hom_complex', nat_trans.map_homological_complex_app_f, addEquivIsoAddCommGroupIso]
  simp only [AddCommGroupCat.hasHomology_ι_eq, ← category.assoc]
  rw [iso.eq_comp_inv]
  dsimp only [AddCommGroupCat.hasHomology]
  simp only [category.assoc]
  rw [← iso.inv_comp_eq]
  ext1 φ
  simp only [CategoryTheory.comp_apply, AddCommGroupCat.kernelIsoKer_inv_comp_ι_apply,
    AddCommGroupCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply, AddCommGroupCat.ofHom,
    AddEquiv.toAddCommGroupCatIso, AddEquiv.coe_toAddMonoidHom]
  dsimp only [aux₃, preadditive_yoneda_map_app_apply]
  dsimp only [AddEquiv.surjectiveCongr, AddEquiv.coe_mk, AddEquiv.symm_mk_apply]
  rw [AddMonoidHom.liftOfSurjective_apply, AddMonoidHom.subtype_mk_apply]
  dsimp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  erw [homological_complex_hom_single_iso_natural P i f φ]
  rw [AddMonoidHom.liftOfSurjective_apply, AddMonoidHom.subtype_mk_apply]
  dsimp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [quotient_add_group.lift_mk'', AddEquiv.apply_symm_apply, AddMonoidHom.comp_apply]
  rfl

theorem homSingleIso_naturality_snd_var (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (i : ℤ)
    (f : B₁ ⟶ B₂) (x : P ⟶ (single C i).obj B₁) :
    ((homology'Functor _ _ i).map
          ((NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) _).app P.val.as.op))
        ((homSingleIso P B₁ i).Hom x) =
      (homSingleIso P B₂ i).Hom (x ≫ (single C i).map f) :=
  by
  have := hom_single_iso_naturality_snd_var_good P i f
  apply_fun fun e => e x at this 
  exact this

end BoundedHomotopyCategory

