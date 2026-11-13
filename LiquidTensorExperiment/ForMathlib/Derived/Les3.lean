import LiquidTensorExperiment.ForMathlib.Derived.Les2

#align_import for_mathlib.derived.les3

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] [Abelian A]

local notation "𝒦" => HomotopyCategory A (ComplexShape.up ℤ)

namespace BoundedHomotopyCategory

variable {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

section

open HomotopyCategory

-- move me
@[reassoc]
theorem ext_map_extIso [EnoughProjectives A] (i : ℤ) (P₁ P₂ X₁ X₂ Y : BoundedHomotopyCategory A)
    [IsKProjective P₁.val] [IsKProjective P₂.val] (f₁ : P₁ ⟶ X₁) [IsQuasiIso f₁] (f₂ : P₂ ⟶ X₂)
    [IsQuasiIso f₂] (φ : X₁ ⟶ X₂) (φ' : P₁ ⟶ P₂) (h : φ' ≫ f₂ = f₁ ≫ φ) :
    ((ext i).flip.obj Y).map φ.op ≫ (extIso i P₁ X₁ Y f₁).Hom =
      (extIso i P₂ X₂ Y f₂).Hom ≫ (preadditiveYoneda.obj (Y⟦i⟧)).map φ'.op :=
  by
  dsimp only [Ext_iso, functor.map_iso_hom, iso.op_hom, Ext, Ext0, functor.flip_obj_map,
    functor.comp_map, whiskering_left_obj_map, whisker_left_app, functor.flip_map_app]
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, ← CategoryTheory.Functor.map_comp, ← op_comp]
  congr 2
  dsimp only [replacement_iso_hom, Opposite.unop_op]
  refine' lift_ext X₂.π _ _ _
  simp only [category.assoc, lift_lifts, lift_lifts_assoc, Quiver.Hom.unop_op, h]

-- move me
@[reassoc]
theorem ext_map_ext_iso' [EnoughProjectives A] (i : ℤ) (X₁ X₂ Y : BoundedHomotopyCategory A)
    (φ : X₁ ⟶ X₂) :
    ((ext i).flip.obj Y).map φ.op ≫ (extIso i _ X₁ Y X₁.π).Hom =
      (extIso i _ X₂ Y X₂.π).Hom ≫ (preadditiveYoneda.obj (Y⟦i⟧)).map (lift (X₁.π ≫ φ) X₂.π).op :=
  ext_map_extIso _ _ _ _ _ _ _ _ _ _ <| by rw [lift_lifts]

theorem extIso_naturality_snd_component [EnoughProjectives A] (i : ℤ)
    (P X Y₁ Y₂ : BoundedHomotopyCategory A) [IsKProjective P.val] (f : P ⟶ X) [IsQuasiIso f]
    (g : Y₁ ⟶ Y₂) :
    ((ext i).obj _).map g ≫ (extIso i P X _ f).Hom =
      (extIso i P X _ f).Hom ≫ (preadditiveYoneda.flip.obj (Opposite.op P)).map (g⟦i⟧') :=
  by
  dsimp only [Ext_iso, Ext, Ext0]; ext t
  dsimp; simp only [comp_apply]; dsimp; simp

end

def shiftIso [EnoughProjectives A] (n : ℤ) (X : CochainComplex A ℤ) (Y : BoundedHomotopyCategory A)
    [((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj X).IsBoundedAbove] :
    ((ext (n + 1)).flip.obj Y).obj (Opposite.op <| of' X⟦(1 : ℤ)⟧) ≅
      ((ext n).flip.obj Y).obj (Opposite.op <| of' X) :=
  by
  let e := Ext_iso n (of' X).replace (of' X) Y (of' X).π
  let e' := Ext_iso (n + 1) ((of' X).replace⟦1⟧) (of' X⟦1⟧) Y ((of' X).π⟦(1 : ℤ)⟧')
  refine' e' ≪≫ _ ≪≫ e.symm
  clear e e'
  refine' AddEquiv.toAddCommGroupCatIso _
  refine' shift_iso_aux 1 n _ _

open CategoryTheory.Preadditive

theorem shiftIso_conj (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] :
    (shiftIso _ _ _).inv ≫
        (((ext (n + 1)).flip.obj W).rightOp.map (ofHom f⟦(1 : ℤ)⟧')).unop ≫ (shiftIso _ _ _).Hom =
      ((ext n).flip.obj W).map (ofHom f).op :=
  by
  dsimp only [shift_iso, iso.trans_hom, iso.trans_inv, iso.symm_inv, iso.symm_hom,
    functor.right_op_map, Quiver.Hom.unop_op]
  simp only [category.assoc]
  rw [Ext_map_Ext_iso_assoc (n + 1)
      ((shift_functor (BoundedHomotopyCategory A) (1 : ℤ)).obj (of' X).replace)
      ((shift_functor (BoundedHomotopyCategory A) (1 : ℤ)).obj (of' Y).replace) _ _ _
      ((shift_functor (BoundedHomotopyCategory A) 1).map (of' X).π)
      ((shift_functor (BoundedHomotopyCategory A) 1).map (of' Y).π) _
      (lift ((of' X).π ≫ of_hom f) (of' Y).π⟦1⟧'),
    iso.inv_hom_id_assoc]
  swap
  · simp only [comp_neg, neg_comp, neg_inj, ← CategoryTheory.Functor.map_comp, lift_lifts]
  simp only [← category.assoc, iso.comp_inv_eq]
  rw [Ext_map_Ext_iso', category.assoc, category.assoc]; congr 1
  rw [← category.assoc, ← iso.eq_comp_inv]
  apply AddCommGroupCat.ext; intro φ
  dsimp only [shift_iso_aux, AddEquiv.toAddCommGroupCatIso]
  rw [comp_apply, comp_apply]
  dsimp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.symm, Equiv.symm, AddEquiv.to_equiv_mk,
    AddEquiv.coe_mk]
  erw [preadditive_yoneda_obj_map_apply, preadditive_yoneda_obj_map_apply]
  simp only [← category.assoc, Quiver.Hom.unop_op, ← CategoryTheory.Functor.map_comp]

--attribute [simps] shift_iso_aux
theorem shiftIso_conj' (n : ℤ) [EnoughProjectives A]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    (W₁ W₂ : BoundedHomotopyCategory A) (f : W₁ ⟶ W₂) :
    (shiftIso n X W₁).inv ≫ ((ext (n + 1)).obj _).map f ≫ (shiftIso n X _).Hom =
      ((ext n).obj _).map f :=
  by
  dsimp only [shift_iso, iso.trans_hom, iso.trans_inv, iso.symm_hom, iso.symm_inv]
  simp only [category.assoc]
  slice_lhs 4 5 => rw [Ext_iso_naturality_snd_component]
  simp only [category.assoc, iso.inv_hom_id_assoc, category.id_comp]
  rw [← iso.eq_inv_comp]
  simp_rw [← category.assoc]
  rw [iso.comp_inv_eq]
  simp_rw [category.assoc]
  rw [Ext_iso_naturality_snd_component]
  rw [iso.inv_hom_id_assoc]
  ext t
  dsimp
  simp only [comp_apply]
  dsimp
  simp only [add_zero, unit_of_tensor_iso_unit_inv_app, discrete.functor_map_id, nat_trans.id_app,
    category.id_comp, category.assoc, nat_trans.naturality, functor.comp_map, μ_hom_inv_app_assoc,
    functor.map_comp, ε_inv_app_obj, discrete.right_unitor_def, eq_to_iso.hom, eq_to_hom_map,
    eq_to_hom_app, μ_naturality_assoc, μ_inv_hom_app_assoc]
  erw [← nat_trans.naturality_assoc]
  erw [← nat_trans.naturality_assoc]
  dsimp; let s := _; change _ ≫ _ ≫ s = _; rw [← category.assoc]; convert category.comp_id _
  dsimp [s]
  simp only [eq_to_hom_map, eq_to_hom_app, eq_to_iso.inv, ε_app_obj, discrete.right_unitor_def,
    category.assoc, μ_inv_hom_app_assoc, eq_to_hom_trans, eq_to_hom_refl]

@[reassoc]
theorem shiftIso_ext_map (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] :
    (((ext (n + 1)).flip.obj W).rightOp.map (ofHom f⟦(1 : ℤ)⟧')).unop ≫ (shiftIso _ _ _).Hom =
      (shiftIso _ _ _).Hom ≫ ((ext n).flip.obj W).map (ofHom f).op :=
  by rw [← iso.inv_comp_eq, shift_iso_conj]

@[reassoc]
theorem ext_map_shiftIso_inv (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)] :
    (shiftIso _ _ _).inv ≫ (((ext (n + 1)).flip.obj W).rightOp.map (ofHom f⟦(1 : ℤ)⟧')).unop =
      ((ext n).flip.obj W).map (ofHom f).op ≫ (shiftIso _ _ _).inv :=
  by rw [iso.eq_comp_inv, category.assoc, shift_iso_conj]

def extδ (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) :
    ((ext n).flip.obj W).obj (Opposite.op <| of' X) ⟶
      ((ext (n + 1)).flip.obj W).obj (Opposite.op <| of' Z) :=
  (shiftIso n X W).inv ≫ (connectingHom' f g (n + 1) W w).unop

def mapCone {A₁ A₂ B₁ B₂ : CochainComplex A ℤ}
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj A₁)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj B₁)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj A₂)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj B₂)] (f₁ : A₁ ⟶ B₁)
    (f₂ : A₂ ⟶ B₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (sq : f₁ ≫ b = a ≫ f₂) : cone f₁ ⟶ cone f₂ :=
  (HomotopyCategory.quotient _ _).map <|
    { f := fun i => biprod.lift (biprod.fst ≫ a.f _) (biprod.snd ≫ b.f _)
      comm' := by
        rintro i j ⟨⟨rfl⟩⟩
        ext
        · dsimp [HomologicalComplex.Cone.d]; simp
        · dsimp [HomologicalComplex.Cone.d]; simp
          simp only [← HomologicalComplex.comp_f, sq]
        · dsimp [HomologicalComplex.Cone.d]; simp
        · dsimp [HomologicalComplex.Cone.d]; simp }

theorem extδ_natural (i : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    {X₁ Y₁ Z₁ : CochainComplex A ℤ} (f₁ : X₁ ⟶ Y₁) (f₂ : Y₁ ⟶ Z₁) {X₂ Y₂ Z₂ : CochainComplex A ℤ}
    (g₁ : X₂ ⟶ Y₂) (g₂ : Y₂ ⟶ Z₂) (α₁ : X₁ ⟶ X₂) (α₂ : Y₁ ⟶ Y₂) (α₃ : Z₁ ⟶ Z₂)
    (sq₁ : f₁ ≫ α₂ = α₁ ≫ g₁) (sq₂ : f₂ ≫ α₃ = α₂ ≫ g₂)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X₁)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y₁)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z₁)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X₂)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y₂)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z₂)]
    (w₁ : ∀ i, ShortExact (f₁.f i) (f₂.f i)) (w₂ : ∀ i, ShortExact (g₁.f i) (g₂.f i)) :
    ((ext i).flip.obj W).map (ofHom α₁).op ≫ extδ f₁ f₂ i W w₁ =
      extδ g₁ g₂ i W w₂ ≫ ((ext (i + 1)).flip.obj W).map (ofHom α₃).op :=
  by
  -- TODO: This proof is SLOW.
  delta Ext_δ
  let F := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  simp only [category.assoc]
  dsimp only [connecting_hom', unop_comp]
  simp only [unop_inv, category.assoc]
  simp only [← category.assoc, is_iso.comp_inv_eq]
  simp only [category.assoc]
  dsimp only [functor.right_op, Quiver.Hom.unop_op, functor.flip, Opposite.unop_op]
  let t := _; change _ = _ ≫ _ ≫ t
  have ht : t = ((Ext (i + 1)).map (Quiver.Hom.op _)).app W
  rotate_left 2
  · apply map_cone
    exact sq₁
  · -- Move the inv, and this should be doable.
    dsimp [t]; rw [is_iso.inv_comp_eq]
    ext f
    dsimp [Ext, shift_iso, Ext_iso, preadditive_yoneda_obj, LinearMap.toAddMonoidHom]
    simp only [comp_apply]; dsimp
    simp only [← category.assoc]
    congr 1
    apply lift_ext (of' Z₂).π; swap; infer_instance
    simp only [category.assoc, lift_lifts, lift_lifts_assoc]
    congr 1; dsimp [map_cone, cone.π, HomotopyCategory.cone.π]
    erw [← F.map_comp, ← F.map_comp]; congr 1
    dsimp [HomologicalComplex.cone.π]
    ext
    · simp
    · simp
      simp only [← HomologicalComplex.comp_f, sq₂]
  rw [ht]; clear ht; clear t
  ext f
  dsimp [Ext, shift_iso, Ext_iso, preadditive_yoneda_obj, LinearMap.toAddMonoidHom]
  dsimp only [shift_iso_aux, AddEquiv.symm]
  simp only [comp_apply]
  dsimp
  simp only [← category.assoc]; congr 1
  simp only [functor.map_comp, ← category.assoc]; congr 1
  simp only [category.assoc]
  apply lift_ext ((of' X₂).π⟦(1 : ℤ)⟧')
  swap; infer_instance
  simp only [category.assoc, ← functor.map_comp, lift_lifts]
  simp only [functor.map_comp, lift_lifts_assoc, lift_lifts, category.assoc]
  congr 1
  dsimp [cone_triangle, map_cone]
  simp only [comp_neg, neg_comp]; congr 1
  erw [← F.map_comp, ← F.map_comp]; congr 1
  dsimp [HomologicalComplex.cone.out]
  ext
  · simp
  · simp

theorem extδ_natural' (i : ℤ) [EnoughProjectives A] (W₁ W₂ : BoundedHomotopyCategory A)
    (e : W₁ ⟶ W₂) {X Y Z : CochainComplex A ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) :
    ((ext i).obj _).map e ≫ extδ f g i W₂ w = extδ f g i W₁ w ≫ ((ext (i + 1)).obj _).map e :=
  by
  delta Ext_δ
  dsimp [connecting_hom']
  simp only [Quiver.Hom.unop_op, unop_inv]
  simp_rw [← category.assoc]
  rw [is_iso.comp_inv_eq]
  simp_rw [category.assoc]
  let t := _; change _ = _ ≫ _ ≫ t
  have ht : t = ((Ext (i + 1)).obj _).map e :=
    by
    dsimp only [t]
    rw [is_iso.inv_comp_eq, nat_trans.naturality]
  rw [ht]; clear ht t
  rw [iso.eq_inv_comp]
  rw [← nat_trans.naturality]
  simp only [← category.assoc]
  congr 1
  rw [iso.comp_inv_eq, ← shift_iso_conj', iso.hom_inv_id_assoc]

theorem ext_five_term_exact_seq' (n : ℤ) [EnoughProjectives A] (W : BoundedHomotopyCategory A)
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj X)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Y)]
    [HomotopyCategory.IsBoundedAbove ((HomotopyCategory.quotient _ _).obj Z)]
    (w : ∀ i, ShortExact (f.f i) (g.f i)) :
    let E n := (ext n).flip.obj W
    ExactSeq Ab.{v} <|
      [(E n).map (ofHom g).op, (E n).map (ofHom f).op, extδ f g n W w,
        (E (n + 1)).map (ofHom g).op] :=
  by
  refine' (Ext_five_term_exact_seq f g n W w).pair.unop.cons _
  refine' exact.cons _ (exact.exact_seq _)
  · rw [Ext_δ, functor.right_op_map, Quiver.Hom.unop_op, ← shift_iso_conj f n W, exact_iso_comp,
      exact_comp_hom_inv_comp_iff]
    have := (Ext_five_term_exact_seq f g (n + 1) W w).unop.pair
    erw [functor.map_neg, CategoryTheory.unop_neg, abelian.exact_neg_left_iff] at this 
    exact this
  · rw [Ext_δ, exact_iso_comp]
    exact ((Ext_five_term_exact_seq f g (n + 1) W w).drop 1).pair.unop

end BoundedHomotopyCategory

namespace BoundedDerivedCategory

variable [EnoughProjectives A]

variable {X Y Z : BoundedDerivedCategory A} (f : X ⟶ Y) (g : Y ⟶ Z)

open HomologicalComplex

def cone (f : X ⟶ Y) : BoundedDerivedCategory A :=
  (localizationFunctor _).obj <|
    { val := HomotopyCategory.cone f.val.out
      bdd := by
        obtain ⟨a, ha⟩ := HomotopyCategory.IsBoundedAbove.cond X.val.val
        obtain ⟨b, hb⟩ := HomotopyCategory.IsBoundedAbove.cond Y.val.val
        constructor; use max a b + 1
        intro t ht
        apply is_zero_biprod
        · apply ha; refine' le_trans (le_trans _ ht) _
          refine' le_trans (le_max_left a b) _
          all_goals linarith
        · apply hb
          refine' le_trans _ ht; refine' le_trans (le_max_right a b) _
          linarith }

-- UGH
end BoundedDerivedCategory

-- move me
instance singleIsBoundedAbove (X : A) :
    HomotopyCategory.IsBoundedAbove
      { as := (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X } :=
  by
  refine' ⟨⟨1, _⟩⟩
  intro i hi
  dsimp
  rw [if_neg]
  · exact is_zero_zero _
  · rintro rfl; exact zero_lt_one.not_le hi

-- move me
instance quotientSingleIsBoundedAbove (X : A) :
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X)).IsBoundedAbove :=
  singleIsBoundedAbove X

def ext'δ [EnoughProjectives A] {X Y Z : A} (W : A) {f : X ⟶ Y} {g : Y ⟶ Z} (h : ShortExact f g)
    (n : ℤ) :
    ((ext' n).flip.obj W).obj (Opposite.op <| X) ⟶
      ((ext' (n + 1)).flip.obj W).obj (Opposite.op <| Z) :=
  by
  refine'
    @BoundedHomotopyCategory.extδ _ _ _ _ _ _ ((HomologicalComplex.single _ _ _).map f)
      ((HomologicalComplex.single _ _ _).map g) n _ _ (quotientSingleIsBoundedAbove _)
      (quotientSingleIsBoundedAbove _) (quotientSingleIsBoundedAbove _) _
  intro i; dsimp; by_cases hi : i = 0
  · subst i; dsimp; simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, h]
  · rw [dif_neg hi, dif_neg hi, if_neg hi, if_neg hi, if_neg hi]
    refine' ⟨exact_of_zero _ _⟩

theorem ext'δ_natural [EnoughProjectives A] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : A} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) (α₁ : X₁ ⟶ Y₁) (α₂ : X₂ ⟶ Y₂) (α₃ : X₃ ⟶ Y₃)
    (sq₁ : f₁ ≫ α₂ = α₁ ≫ g₁) (sq₂ : f₂ ≫ α₃ = α₂ ≫ g₂) (Z : A) (hf : ShortExact f₁ f₂)
    (hg : ShortExact g₁ g₂) (i : ℤ) :
    ((ext' i).flip.obj Z).map α₁.op ≫ ext'δ Z hf i =
      ext'δ Z hg i ≫ ((ext' (i + 1)).flip.obj Z).map α₃.op :=
  by
  delta ext' ext'δ
  apply
    BoundedHomotopyCategory.extδ_natural _ _ _ _ _ _ _
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map α₂)
  all_goals simp only [← CategoryTheory.Functor.map_comp, sq₁, sq₂, Quiver.Hom.unop_op]

namespace CategoryTheory

namespace ShortExact

theorem ext'_five_term_exactSeq [EnoughProjectives A] {X Y Z : A} (W : A) {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : ShortExact f g) (n : ℤ) :
    let E n := (ext' n).flip.obj W
    ExactSeq Ab.{v} <| [(E n).map g.op, (E n).map f.op, ext'δ W h n, (E (n + 1)).map g.op] :=
  by
  let f' := (HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map f
  let g' := (HomologicalComplex.single _ (ComplexShape.up ℤ) (0 : ℤ)).map g
  let W' := (BoundedHomotopyCategory.single _ 0).obj W
  have Hfg : ∀ i : ℤ, short_exact (f'.f i) (g'.f i) :=
    by
    intro i; dsimp; by_cases hi : i = 0
    · subst i; dsimp; simp only [eq_self_iff_true, category.comp_id, category.id_comp, if_true, h]
    · rw [dif_neg hi, dif_neg hi, if_neg hi, if_neg hi, if_neg hi]
      refine' ⟨exact_of_zero _ _⟩
  convert BoundedHomotopyCategory.ext_five_term_exact_seq' f' g' n W' Hfg

end ShortExact

end CategoryTheory

