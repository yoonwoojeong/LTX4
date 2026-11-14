import LiquidTensorExperiment.ForMathlib.Derived.KProjective
import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp
import LiquidTensorExperiment.ForMathlib.HomologyIsoAb

#align_import for_mathlib.homSingleIso

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

variable {C : Type u} {ι : Type _} [Category.{v} C] [Abelian C] {c : ComplexShape ι}

def HomotopyCategory.quotientMapHom (A B : HomologicalComplex C c) :
    (A ⟶ B) →+ ((HomotopyCategory.quotient C c).obj A ⟶ (HomotopyCategory.quotient C c).obj B) :=
  AddMonoidHom.mk' (fun f => (HomotopyCategory.quotient C c).map f) fun f g => rfl

theorem Quot.mk_surjective {X : Type _} (r : X → X → Prop) : Function.Surjective (Quot.mk r) :=
  fun x => Quot.inductionOn x fun x => ⟨x, rfl⟩

noncomputable def Homotopy.toSingle [DecidableEq ι] [DecidableRel c.Rel]
    {X : HomologicalComplex C c} {B : C} {i j : ι} (r : c.Rel i j)
    (f g : X ⟶ (HomologicalComplex.single C c i).obj B) (h : X.pt j ⟶ B)
    (H : f.f i = X.d i j ≫ h ≫ eqToHom (if_pos rfl).symm + g.f i) : Homotopy f g
    where
  Hom i₁ i₂ :=
    if r' : c.Rel i₂ i₁ then
      if e : i₂ = i then
        (X.xEqToIso (c.next_eq (e ▸ r' : c.Rel i i₁) r)).hom ≫ h ≫ eqToHom (if_pos e).symm
      else 0
    else 0
  zero' _ _ e := dif_neg e
  comm k := by
    dsimp
    by_cases hki : k = i
    swap; · apply IsZero.eq_of_tgt; dsimp; rw [if_neg hki]; exact is_zero_zero _
    subst hki
    rw [← dNext_eq_dFrom_fromNext, ← prevD_eq_toPrev_dTo, dNext_eq _ r, dif_pos r, dif_pos rfl,
      X.X_eq_to_iso_refl, Category.id_comp, H]
    nth_rw_lhs 1 [← AddMonoid.add_zero (X.d k j ≫ h ≫ eq_to_hom _)]
    congr
    by_cases aux : c.rel (c.prev k) k
    · rw [prevD_eq _ aux, dif_pos aux]
      by_cases hk : c.prev k = k
      · rw [dif_pos hk, eq_comm]; apply comp_zero
      · rw [dif_neg hk, zero_comp]; rfl
    · delta prevD; dsimp only [AddMonoidHom.mk'_apply]
      rw [dif_neg aux, zero_comp]; rfl

theorem homotopic_to_single_iff [DecidableEq ι] {X : HomologicalComplex C c} {B : C} {i j : ι}
    (r : c.Rel i j) (f g : X ⟶ (HomologicalComplex.single C c i).obj B) :
    homotopic _ _ f g ↔ ∃ h : X.pt j ⟶ B, f.f i = X.d i j ≫ h ≫ eqToHom (if_pos rfl).symm + g.f i :=
  by
  haveI : DecidableRel c.rel := fun _ _ => Classical.dec _
  refine' ⟨_, fun ⟨h, H⟩ => ⟨Homotopy.toSingle r f g h H⟩⟩
  rintro ⟨h⟩
  use h.hom j i ≫ eq_to_hom (if_pos rfl)
  rw [Category.assoc, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl, Category.comp_id, ← add_zero (_ ≫ _)]
  have := h.comm i
  rw [dNext_eq _ r] at this 
  convert this
  delta prevD; dsimp only [AddMonoidHom.mk'_apply]
  rw [eq_comm]; apply comp_zero

instance : DecidableRel (ComplexShape.up ℤ).Rel := fun i j =>
  show Decidable (i + 1 = j) by infer_instance

@[simps]
noncomputable def HomologicalComplex.homSingleIso (P : CochainComplex C ℤ) (B : C) (i : ℤ) :
    (P ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) i).obj B) ≃+
      AddMonoidHom.ker
        ((((preadditiveYoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj P.op).d i
          (i - 1))
    where
  toFun f := by
    refine' ⟨f.f i ≫ eq_to_hom (if_pos rfl), _⟩
    change P.d (i - 1) i ≫ f.f i ≫ eq_to_hom _ = 0
    rw [← f.comm_assoc]
    dsimp
    rw [zero_comp, comp_zero]
  invFun f :=
    by
    refine'
      ⟨fun j => if e : j = i then (P.X_eq_to_iso <| e).hom ≫ f.1 ≫ eq_to_hom (if_pos e).symm else 0,
        _⟩
    rintro j k (rfl : j + 1 = k)
    dsimp
    rw [comp_zero]
    split_ifs
    · have := eq_sub_iff_add_eq.mpr h; subst this
      rw [P.X_d_eq_to_iso_assoc, ← Category.assoc, ← Subtype.val_eq_coe,
        show P.d (i - 1) i ≫ f.1 = 0 from f.2, zero_comp]
    · exact comp_zero.symm
  left_inv := by
    intro f
    ext j
    dsimp
    split_ifs
    · subst h; simp
    · apply IsZero.eq_of_tgt; rw [if_neg h]; exact is_zero_zero _
  right_inv f := by ext; dsimp; simp
  map_add' f g := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)

namespace BoundedHomotopyCategory

namespace HomSingleIsoSetup

def homComplex (P : BoundedHomotopyCategory C) (B : C) :=
  ((preadditiveYoneda.obj B).mapHomologicalComplex _).obj P.val.as.op

def mapHomComplex {P₁ P₂ : BoundedHomotopyCategory C} (f : P₁ ⟶ P₂) (B : C) :
    homComplex P₂ B ⟶ homComplex P₁ B :=
  ((preadditiveYoneda.obj B).mapHomologicalComplex _).map
    (HomologicalComplex.opFunctor.map f.out.op)

def mapHomComplex' (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (f : B₁ ⟶ B₂) :
    homComplex P B₁ ⟶ homComplex P B₂ :=
  (NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) _).app _

def aux₁ (P : BoundedHomotopyCategory C) (B : C) (i : ℤ) :
    homology' ((homComplex P B).d (i + 1) i) ((homComplex P B).d i (i - 1))
        ((homComplex P B).d_comp_d _ _ _) ≅
      (homComplex P B).homology' i :=
  (homologyIso' (homComplex P B) (i + 1) i (i - 1) (by simp) (by simp)).symm

def mapHomology {P₁ P₂ : BoundedHomotopyCategory C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    homology' ((homComplex P₂ B).d (i + 1) i) ((homComplex P₂ B).d i (i - 1))
        ((homComplex _ B).d_comp_d _ _ _) ⟶
      homology' ((homComplex P₁ B).d (i + 1) i) ((homComplex P₁ B).d i (i - 1))
        ((homComplex _ B).d_comp_d _ _ _) :=
  homology'.map _ _ (Arrow.homMk <| (mapHomComplex f B).comm _ _)
    (Arrow.homMk <| (mapHomComplex f B).comm _ _) rfl

theorem aux₁_naturality (P₁ P₂ : BoundedHomotopyCategory C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    (aux₁ P₂ B i).hom ≫ (homology'Functor _ _ _).map (mapHomComplex f B) =
      mapHomology f _ _ ≫ (aux₁ P₁ B i).hom :=
  by
  dsimp only [BoundedHomotopyCategory.HomSingleIsoSetup.mapHomology, aux₁, CategoryTheory.homologyIso', Iso.symm_hom, homology'.mapIso,
    homology'Functor_map]
  rw [homology'.map_eq_desc'_lift_left]
  rw [homology'.map_eq_lift_desc'_left]
  rw [homology'.map_eq_desc'_lift_left]
  rw [homology'.map_eq_lift_desc'_left]
  apply homology'.hom_from_ext; apply homology'.hom_to_ext
  simp only [homology'.π'_desc', Category.assoc, homology'.π'_desc'_assoc, homology'.lift_ι,
    homology'.lift_ι_assoc]
  let t := _; change t ≫ _ = _
  have ht : t = kernel.lift _ (kernel.ι _) _ ≫ homology'.π' _ _ _
  rotate_left 2
  · rw [HomologicalComplex.dFrom_eq]
    rw [kernel.condition_assoc, zero_comp]
    simp
  · apply homology'.hom_to_ext
    simp; dsimp; simp
  rw [ht]; clear ht; clear t
  simp only [kernel.lift_ι_assoc, Category.assoc, Arrow.homMk_left, Arrow.isoMk_inv_left,
    Iso.refl_inv, HomologicalComplex.Hom.sqFrom_left, homology'.π'_desc']
  let t := _; change _ = _ ≫ t
  have ht : t = homology'.ι _ _ _ ≫ cokernel.desc _ (cokernel.π _) _
  rotate_left 2
  · have := (BoundedHomotopyCategory.HomSingleIsoSetup.homComplex P₁ B).dTo_eq (by simp : (ComplexShape.up ℤ).symm.Rel (i + 1) i)
    rw [← Iso.inv_comp_eq] at this 
    rw [← this, Category.assoc, cokernel.condition, comp_zero]
  · apply homology'.hom_from_ext
    simp; dsimp; simp
  rw [ht]; clear ht; clear t
  simp only [Category.assoc, cokernel.π_desc, homology'.lift_ι_assoc]

def aux₂ (P : BoundedHomotopyCategory C) (B : C) (i : ℤ) :
    homology' ((homComplex P B).d (i + 1) i) ((homComplex P B).d i (i - 1))
        (HomologicalComplex.d_comp_d _ _ _ _) ≅
      AddCommGroupCat.homology ((homComplex P B).d (i + 1) i) ((homComplex P B).d i (i - 1)) :=
  AddCommGroupCat.homologyIso _ _ _

def kerHom {P₁ P₂ : BoundedHomotopyCategory C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    ((homComplex P₂ B).d i (i - 1)).ker →+ ((homComplex P₁ B).d i (i - 1)).ker
    where
  toFun x :=
    ⟨(mapHomComplex f B).f _ ↑x, by
      change _ = _
      have : _ = _ := x.2
      dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.homComplex, BoundedHomotopyCategory.HomSingleIsoSetup.mapHomComplex] at *
      rw [← Category.assoc, ← f.out.comm, Category.assoc, this, comp_zero]⟩
  map_zero' := by ext; simp
  map_add' := by intro x y; ext; dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.mapHomComplex]; simp

def mapExplicitHomology {P₁ P₂ : BoundedHomotopyCategory C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    AddCommGroupCat.homology ((homComplex P₂ B).d (i + 1) i) ((homComplex P₂ B).d i (i - 1)) ⟶
      AddCommGroupCat.homology ((homComplex P₁ B).d (i + 1) i) ((homComplex P₁ B).d i (i - 1)) :=
  QuotientAddGroup.lift _ (AddMonoidHom.comp (QuotientAddGroup.mk' _) <| kerHom f _ _)
    (by
      rintro ⟨x, hx : _ = _⟩ hh
      dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.kerHom, BoundedHomotopyCategory.HomSingleIsoSetup.mapHomComplex]
      rw [QuotientAddGroup.eq_zero_iff]
      rw [AddSubgroup.mem_comap] at *; dsimp at *
      change ∃ e, _
      obtain ⟨e, he⟩ := hh
      dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.homComplex] at *
      use f.out.f _ ≫ e
      rw [← Category.assoc, ← f.out.comm, Category.assoc, he])

--TODO: This relates the above construction to AddcommGroup.homology_map
-- the above def has more convenient defeq properties for some of the proofs below, but
-- the `AddCommGroup.homology_map` is better suited for `aux₂_naturality`.
theorem mapExplicitHomology_eq {P₁ P₂ : BoundedHomotopyCategory C} (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    mapExplicitHomology f B i =
      AddCommGroupCat.homologyMap ((homComplex P₂ B).d_comp_d _ _ _)
        ((homComplex P₁ B).d_comp_d _ _ _)
        (Commsq.ofEq <| ((mapHomComplex f B).comm (i + 1) i).symm)
        (Commsq.ofEq <| ((mapHomComplex f B).comm i (i - 1)).symm) :=
  by
  ext ⟨t⟩
  symm; apply AddCommGroupCat.homologyMap_apply_mk

theorem aux₂_naturality (P₁ P₂ : BoundedHomotopyCategory C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    (aux₂ P₂ B i).hom ≫ mapExplicitHomology f _ _ = mapHomology f _ _ ≫ (aux₂ P₁ B i).hom :=
  by
  rw [BoundedHomotopyCategory.HomSingleIsoSetup.mapExplicitHomology_eq]
  dsimp [aux₂]
  dsimp [AddCommGroupCat.homologyIso, AddCommGroupCat.homologyMap, BoundedHomotopyCategory.HomSingleIsoSetup.mapHomology]
  generalize_proofs _ _ w _ w'
  apply (homology'.has _ _ w).ext_π
  apply (AddCommGroupCat.hasHomology _ _ w').ext_ι
  rw [HasHomology.homology'_map_eq]
  simp only [HasHomology.π_map, Category.assoc, HasHomology.π_map_assoc, HasHomology.map_ι,
    HasHomology.map_ι_assoc]
  let t := _; change t ≫ _ = _
  have ht : t = kernel.lift _ (kernel.ι _) _ ≫ (AddCommGroupCat.hasHomology _ _ w).π
  rotate_left 2
  · apply kernel.condition
  · apply (AddCommGroupCat.hasHomology _ _ w).ext_ι
    simp [HasHomology.π_ι]
  rw [ht]; clear ht; clear t
  let t := _; change _ = _ ≫ t
  have ht : t = (homology'.has _ _ w').ι ≫ cokernel.desc _ (cokernel.π _) _
  rotate_left 2
  · apply cokernel.condition
  · apply (homology'.has _ _ w').ext_π
    rw [← Category.assoc, HasHomology.π_ι]
    simp
  rw [ht]; clear ht; clear t
  simp

theorem aux₂_naturality_inv (P₁ P₂ : BoundedHomotopyCategory C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    mapExplicitHomology f _ _ ≫ (aux₂ P₁ B i).inv = (aux₂ P₂ B i).inv ≫ mapHomology f _ _ := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, aux₂_naturality]

def aux₃ (P : BoundedHomotopyCategory C) (B : C) (i : ℤ) :
    (P ⟶ (single C i).obj B) ≃+
      AddCommGroupCat.homology ((homComplex P B).d (i + 1) i) ((homComplex P B).d i (i - 1)) :=
  by
  refine'
    AddEquiv.surjectiveCongr (HomologicalComplex.homSingleIso P.val.as B i)
      (HomotopyCategory.quotientMapHom _ _) (QuotientAddGroup.mk' _) (Quot.mk_surjective _)
      (Quot.mk_surjective _) _
  ext f
  dsimp
  simp only [HomotopyCategory.quotientMapHom, QuotientAddGroup.ker_mk', AddEquiv.coe_toAddMonoidHom,
    AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.coeSubtype, AddMonoidHom.mk'_apply,
    AddSubgroup.coe_mk, AddEquiv.coe_mk, AddMonoidHom.mem_range]
  rw [← (HomotopyCategory.quotient _ _).map_zero]
  any_goals infer_instance
  erw [Quotient.functor_map_eq_iff]
  rw [homotopic_to_single_iff (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
  apply exists_congr
  intro g
  simp only [add_zero, Quiver.Hom.unop_op, LinearMap.toAddMonoidHom_coe,
    preadditive_yoneda_obj_map_apply, HomologicalComplex.zero_f_apply,
    HomologicalComplex.homSingleIso_apply_coe]
  rw [← IsIso.comp_inv_eq, eq_comm]
  constructor
  · intro h
    rw [h, IsIso.comp_inv_eq, Category.assoc, Category.assoc, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
      Category.comp_id]
    rfl
  · intro h
    rw [h, IsIso.eq_comp_inv, Category.assoc, Category.assoc, CategoryTheory.eqToHom_trans, CategoryTheory.eqToHom_refl,
      Category.comp_id]
    rfl

theorem aux₃_apply (P : BoundedHomotopyCategory C) (B : C) (i : ℤ) (f : P ⟶ (single C i).obj B) :
    aux₃ P B i f =
      QuotientAddGroup.mk
        ⟨f.out.f i ≫ eqToHom (if_pos rfl), by
          change _ = _; dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.homComplex]
          rw [← Category.assoc, ← f.out.comm, Category.assoc]
          convert zero_comp
          apply IsZero.eq_of_tgt; convert is_zero_zero _
          dsimp [single]; rw [if_neg]; simp⟩ :=
  rfl

theorem aux₃_naturality (P₁ P₂ : BoundedHomotopyCategory C) (f : P₁ ⟶ P₂) (B : C) (i : ℤ) :
    (mapExplicitHomology f B i).comp (aux₃ P₂ B i).toAddMonoidHom =
      AddMonoidHom.comp (aux₃ P₁ B i).toAddMonoidHom ((preadditiveYoneda.obj _).map f.op) :=
  by
  ext ⟨x⟩
  dsimp; simp_rw [aux₃_apply]
  dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.mapExplicitHomology, BoundedHomotopyCategory.HomSingleIsoSetup.kerHom, BoundedHomotopyCategory.HomSingleIsoSetup.mapHomComplex]
  rw [← sub_eq_zero]
  erw [QuotientAddGroup.eq_zero_iff]
  rw [AddSubgroup.mem_comap]
  dsimp [BoundedHomotopyCategory.HomSingleIsoSetup.homComplex]
  -- now we need to use a homotopy...
  simp_rw [← Category.assoc, ← HomologicalComplex.comp_f]
  let t := _; let s := _
  change ∃ _, _ = HomologicalComplex.Hom.f t i ≫ _ - HomologicalComplex.Hom.f s i ≫ _
  let hh : Homotopy t s := by
    apply HomotopyCategory.homotopyOfEq
    simpa
  let e := hh.hom (i + 1) i
  use e ≫ eq_to_hom (if_pos rfl)
  rw [← Preadditive.sub_comp _ _ (eq_to_hom _), ← Category.assoc]
  congr 1
  erw [hh.comm i]
  simp only [HomologicalComplex.cochainComplex_dNext, HomologicalComplex.cochainComplex_prevD,
    add_sub_cancel, self_eq_add_right]
  exact comp_zero

theorem comp_addEquiv_iso_AddcommGroup_iso_eq_comp (X X' B : AddCommGroupCat.{u}) (e' : X' ≃+ B)
    (f : X ⟶ X') : f ≫ (addEquivIsoAddCommGroupIso.hom e').hom = e'.toAddMonoidHom.comp f :=
  rfl

def homMk {A B : Type u} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    AddCommGroupCat.of A ⟶ AddCommGroupCat.of B :=
  f

end HomSingleIsoSetup

open HomSingleIsoSetup

noncomputable def homSingleIso (P : BoundedHomotopyCategory C) (B : C) (i : ℤ) :
    AddCommGroupCat.of (P ⟶ (BoundedHomotopyCategory.single C i).obj B) ≅
      (((preadditiveYoneda.obj B).mapHomologicalComplex _).obj P.val.as.op).homology' i :=
  by
  refine' _ ≪≫ aux₁ P B i
  refine' add_equiv_iso_AddCommGroup_iso.hom _ ≪≫ (aux₂ P B i).symm
  exact aux₃ P B i

open Opposite

variable {X Y Z : CochainComplex C ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

def of' (X : CochainComplex C ℤ)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)] :
    BoundedHomotopyCategory C :=
  of <| (HomotopyCategory.quotient _ _).obj X

def ofHom (f : X ⟶ Y) [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] : of' X ⟶ of' Y :=
  (HomotopyCategory.quotient _ _).map f

instance valAsBddAbove (P : BoundedHomotopyCategory C) :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P.val.as).IsBoundedAbove := by
  rcases P with ⟨P, ⟨a, ha⟩⟩; use a; intro i hi; exact ha i hi

theorem homSingleIso_naturality (P₁ P₂ : BoundedHomotopyCategory C) (B : C) (i : ℤ) (f : P₁ ⟶ P₂) :
    (preadditiveYoneda.obj _).map f.op ≫ (homSingleIso P₁ B i).hom =
      (homSingleIso P₂ B i).hom ≫
        (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                HomologicalComplex.unopFunctor.rightOp ⋙ (homology'Functor _ _ _).op).map
            f.out).unop :=
  by
  dsimp only [hom_single_iso, Iso.trans_hom, Iso.symm_hom, Functor.comp_map, Functor.op_map,
    Functor.rightOp_map, Quiver.Hom.unop_op]
  simp_rw [← Category.assoc, comp_add_equiv_iso_AddcommGroup_iso_eq_comp]
  rw [← aux₃_naturality]
  rw [Category.assoc]
  let t := hom_mk (aux₃ P₂ B i).toAddMonoidHom
  change (t ≫ BoundedHomotopyCategory.HomSingleIsoSetup.mapExplicitHomology f B i) ≫ _ ≫ _ = _
  slice_lhs 2 3 => rw [aux₂_naturality_inv]
  simp_rw [Category.assoc]
  rw [← aux₁_naturality]
  rfl

theorem homSingleIso_naturality' (P₁ P₂ : BoundedHomotopyCategory C) (B : C) (i : ℤ)
    (f : P₁.val.as ⟶ P₂.val.as) :
    (preadditiveYoneda.obj ((single C i).obj B)).map (ofHom f).op ≫ (homSingleIso P₁ B i).hom =
      (homSingleIso P₂ B i).hom ≫
        (((preadditiveYoneda.obj B).rightOp.mapHomologicalComplex _ ⋙
                HomologicalComplex.unopFunctor.rightOp ⋙ (homology'Functor _ _ _).op).map
            f).unop :=
  by
  erw [BoundedHomotopyCategory.homSingleIso_naturality P₁ P₂ B i (of_hom f)]
  refine' congr_arg₂ _ rfl _
  apply homology'_map_eq_of_homotopy
  let h := (preadditive_yoneda.obj B).rightOp.mapHomotopy (HomotopyCategory.homotopyOutMap f)
  refine' ⟨fun i j => (h.hom j i).unop, _, _⟩
  · intro i j hij; rw [h.zero, unop_zero]; exact hij
  · intro i
    conv_rhs =>
      congr
      rw [add_comm]
    exact congr_arg Quiver.Hom.unop (h.comm i)

def mapHomComplexHomology (P : BoundedHomotopyCategory C) {B₁ B₂ : C} (i : ℤ) (f : B₁ ⟶ B₂)
    (w₁ w₂) :
    homology' ((homComplex P B₁).d (i + 1) i) ((homComplex P B₁).d i (i - 1)) w₁ ⟶
      homology' ((homComplex P B₂).d (i + 1) i) ((homComplex P B₂).d i (i - 1)) w₂ :=
  homology'.map _ _ (Arrow.homMk ((mapHomComplex' _ f).comm _ _))
    (Arrow.homMk ((mapHomComplex' _ f).comm _ _)) rfl

end BoundedHomotopyCategory

