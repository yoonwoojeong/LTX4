import LiquidTensorExperiment.Condensed.Extr.Basic
import LiquidTensorExperiment.Condensed.ProetaleSite
import LiquidTensorExperiment.Condensed.Basic
import Mathlib.CategoryTheory.Sites.InducedTopology
import LiquidTensorExperiment.ForMathlib.SheafificationEquivCompatibility
import LiquidTensorExperiment.ForMathlib.Presieve

#align_import condensed.extr.equivalence

noncomputable section

open CategoryTheory

universe u v' u'

theorem ExtrDisc.isCoverDense :
    CategoryTheory.Functor.IsCoverDense proetaleTopology.{u} extrDiscToProfinite.{u} :=
  CategoryTheory.Functor.IsCoverDense.mk fun U =>
    by
    change ∃ R, _
    obtain ⟨⟨T, hT, π, hπ⟩⟩ := enough_projectives.presentation U
    dsimp at hT hπ 
    let R : presieve U := presieve.of_arrows (fun i : PUnit => T) fun i => π
    use R
    constructor
    · refine' ⟨PUnit, inferInstance, fun i => T, fun i => π, fun x => ⟨PUnit.unit, _⟩, rfl⟩
      rw [Profinite.epi_iff_surjective] at hπ 
      exact hπ x
    intro Y f hf
    change Nonempty _
    rcases hf with ⟨a, b⟩
    let t : presieve.cover_by_image_structure extrDiscToProfinite π := _
    swap
    · skip
      refine' ⟨⟨T⟩, 𝟙 _, π, by simp⟩
    use t

def ExtrDisc.proetaleTopology : GrothendieckTopology ExtrDisc.{u} :=
  ExtrDisc.isCoverDense.inducedTopology

instance extrDisc_proetaleTopology_filtered (X : ExtrDisc.{u}) :
    IsFiltered (ExtrDisc.proetaleTopology.{u}.cover X)ᵒᵖ :=
  inferInstance

def ExtrSheaf (C : Type u') [Category.{v'} C] :=
  Sheaf ExtrDisc.proetaleTopology.{u} C
deriving Category

-- TODO: cover_densed.Sheaf_equiv still has unecessary universe restrictions that can be relaxed.
def condensedExtrSheafEquiv (C : Type u') [Category.{u + 1} C] [Limits.HasLimits C] :
    ExtrSheaf.{u} C ≌ Condensed.{u} C :=
  ExtrDisc.isCoverDense.sheafEquivOfCoverPreservingCoverLifting
    ExtrDisc.isCoverDense.LocallyCoverDense.inducedTopology_coverPreserving
    ExtrDisc.isCoverDense.LocallyCoverDense.inducedTopology_isCocontinuous

-- Sanity check
@[simp]
theorem condensedExtrSheafEquiv_inverse_val (C : Type u') [Category.{u + 1} C] [Limits.HasLimits C]
    (F : Condensed.{u} C) :
    ((condensedExtrSheafEquiv C).inverse.obj F).val = extrDiscToProfinite.op ⋙ F.val :=
  rfl

def extrDiscSheafificationIso :
    (whiskeringLeft _ _ _).obj extrDiscToProfinite.op ⋙
        presheafToSheaf ExtrDisc.proetaleTopology Ab.{u + 1} ≅
      presheafToSheaf proetaleTopology _ ⋙ (condensedExtrSheafEquiv _).inverse :=
  Sites.pullbackSheafificationCompatibility _ _
    ExtrDisc.isCoverDense.LocallyCoverDense.inducedTopology_isCocontinuous _

open Opposite

theorem isExtrSheafOfTypes_of_isSheaf_extrDisc_proetaleTopology (F : ExtrDiscᵒᵖ ⥤ Type u')
    (H : Presieve.IsSheaf ExtrDisc.proetaleTopology F) : IsExtrSheafOfTypes F :=
  by
  intro B ι _ X f hf x hx
  let S : presieve B := presieve.of_arrows X f
  specialize H (sieve.generate S) _
  · dsimp [ExtrDisc.proetaleTopology]
    let R : presieve B.val := presieve.of_arrows (fun i => (X i).val) fun i => (f i).val
    use R
    constructor
    · use ι, inferInstance, fun i => (X i).val, fun i => (f i).val, hf, rfl
    · intro Y f hf
      rcases hf with ⟨i⟩
      use X i, f i, 𝟙 _
      refine' ⟨_, by simp⟩
      use X i, 𝟙 _, f i, presieve.of_arrows.mk i
      simp
  rw [← presieve.is_sheaf_for_iff_generate] at H 
  let t : S.family_of_elements F := presieve.mk_family_of_elements_of_arrows X f F x
  have ht : t.compatible := presieve.mk_family_of_elements_of_arrows_compatible X f F x hx
  specialize H t ht
  -- now use H.
  obtain ⟨tt, htt, htt'⟩ := H
  refine' ⟨tt, _, _⟩
  · dsimp
    intro i
    specialize htt (f i) (presieve.of_arrows.mk i)
    rw [htt]
    apply presieve.mk_family_of_elements_of_arrows_eval _ _ _ _ hx
  · intro y hy
    apply htt'
    intro Z f hf
    rcases hf with ⟨i⟩
    rw [hy]
    symm
    apply presieve.mk_family_of_elements_of_arrows_eval _ _ _ _ hx

theorem is_seprated_of_isExtrSheafOfTypes (F : ExtrDiscᵒᵖ ⥤ Type u') (H : IsExtrSheafOfTypes F) :
    Presieve.IsSeparated ExtrDisc.proetaleTopology F :=
  by
  intro B S hS x t₁ t₂ h₁ h₂
  change proetaleTopology _ _ at hS 
  rw [ExtrDisc.cover_dense.locally_cover_dense.pushforward_cover_iff_cover_pullback] at hS 
  obtain ⟨⟨T, hT⟩, rfl⟩ := hS
  obtain ⟨R, hR, hRT⟩ := hT
  obtain ⟨ι, _, X, f, surj, rfl⟩ := hR
  skip
  let XX : ι → ExtrDisc := fun i => (X i).pres
  let ff : ∀ i, XX i ⟶ B := fun i => ⟨(X i).presπ ≫ f i⟩
  have surjff : ∀ b : B, ∃ (i : ι) (q : XX i), (ff i) q = b :=
    by
    intro b
    obtain ⟨i, y, rfl⟩ := surj b
    obtain ⟨z, rfl⟩ := (X i).presπ_surjective y
    use i, z, rfl
  have hff : ∀ i, T (ff i).val := by
    intro i
    dsimp [ff]
    apply sieve.downward_closed
    apply hRT
    exact presieve.of_arrows.mk i
  let xx : ∀ i, F.obj (op (XX i)) := fun i => x _ _
  swap; · exact ff i
  swap; · exact hff i
  specialize H B ι XX ff surjff xx _
  · intro i j Z g₁ g₂ h
    have hxcompat : x.compatible :=
      by
      apply presieve.is_compatible_of_exists_amalgamation
      exact ⟨t₁, h₁⟩
    dsimp [presieve.family_of_elements.compatible] at hxcompat 
    dsimp [xx]
    specialize hxcompat g₁ g₂
    apply hxcompat
    exact h
  obtain ⟨t, ht, ht'⟩ := H
  have ht₁ : t₁ = t := by
    apply ht'
    intro i
    apply h₁
  have ht₂ : t₂ = t := by
    apply ht'
    intro i
    apply h₂
  rw [ht₁, ht₂]

theorem isSheaf_extrDisc_proetaleTopology_of_isExtrSheafOfTypes (F : ExtrDiscᵒᵖ ⥤ Type u')
    (H : IsExtrSheafOfTypes F) : Presieve.IsSheaf ExtrDisc.proetaleTopology F :=
  by
  have hF : presieve.is_separated ExtrDisc.proetaleTopology F :=
    by
    apply is_seprated_of_isExtrSheafOfTypes
    assumption
  intro B S hS
  rw [← presieve.is_separated_for_and_exists_is_amalgamation_iff_sheaf_for]
  constructor; · apply hF _ hS
  intro x hx
  change proetaleTopology _ _ at hS 
  rw [ExtrDisc.cover_dense.locally_cover_dense.pushforward_cover_iff_cover_pullback] at hS 
  obtain ⟨⟨T, hT⟩, rfl⟩ := hS
  obtain ⟨R, hR, hRT⟩ := hT
  obtain ⟨ι, _, X, f, surj, rfl⟩ := hR
  skip
  let XX : ι → ExtrDisc := fun i => (X i).pres
  let ff : ∀ i, XX i ⟶ B := fun i => ⟨(X i).presπ ≫ f i⟩
  have surjff : ∀ b : B, ∃ (i : ι) (q : XX i), (ff i) q = b :=
    by
    intro b
    obtain ⟨i, y, rfl⟩ := surj b
    obtain ⟨z, rfl⟩ := (X i).presπ_surjective y
    use i, z, rfl
  have hff : ∀ i, T (ff i).val := by
    intro i
    dsimp [ff]
    apply sieve.downward_closed
    apply hRT
    exact presieve.of_arrows.mk i
  let xx : ∀ i, F.obj (op (XX i)) := fun i => x _ _
  swap; · exact ff i
  swap; · exact hff i
  specialize H B ι XX ff surjff xx _
  · intro i j Z g₁ g₂ h
    dsimp [presieve.family_of_elements.compatible] at hx 
    dsimp [xx]
    specialize hx g₁ g₂
    apply hx
    exact h
  obtain ⟨t, ht, ht'⟩ := H
  use t
  intro Y f hf
  let PP : ι → Profinite := fun i => Profinite.pullback f.val (ff i).val
  let QQ : ι → ExtrDisc := fun i => (PP i).pres
  let ππ : ∀ i, QQ i ⟶ XX i := fun i => ⟨(PP i).presπ ≫ Profinite.pullback.snd _ _⟩
  let gg : ∀ i, QQ i ⟶ Y := fun i => ⟨(PP i).presπ ≫ Profinite.pullback.fst _ _⟩
  let W : sieve Y := sieve.generate (presieve.of_arrows QQ gg)
  specialize hF W _
  · change ∃ _, _
    use presieve.of_arrows (fun i => (QQ i).val) fun i => (gg i).val
    constructor
    · use ι, inferInstance, fun i => (QQ i).val, fun i => (gg i).val
      refine' ⟨_, rfl⟩
      intro y
      obtain ⟨i, t, ht⟩ := surj (f y)
      obtain ⟨w, hw⟩ := (X i).presπ_surjective t
      obtain ⟨z, hz⟩ := (PP i).presπ_surjective ⟨⟨y, w⟩, _⟩
      swap; · dsimp; rw [hw]; exact ht.symm
      use i, z
      dsimp [gg]
      rw [hz]; rfl
    · intro Z f hf
      obtain ⟨i⟩ := hf
      change ∃ _, _
      use QQ i, gg i, 𝟙 _
      constructor
      · apply sieve.le_generate
        apply presieve.of_arrows.mk
      · ext1; simp
  dsimp [presieve.is_separated_for] at hF 
  have : ∀ (Z : ExtrDisc) (g : Z ⟶ Y) (hg : W g), ∃ (i : ι) (e : Z ⟶ QQ i), g = e ≫ gg i :=
    by
    intro Z g hg
    obtain ⟨QQ', e₁, e₂, h1, h2⟩ := hg
    obtain ⟨i⟩ := h1
    use i, e₁, h2.symm
  choose ii ee hee using this
  let y : presieve.family_of_elements F W := fun Z g hg =>
    F.map (ee _ _ hg ≫ ππ _).op (xx (ii _ _ hg))
  have hy : y.compatible := by
    intro T₁ T₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    dsimp [y, xx]
    simp only [← F.map_comp, ← op_comp]
    change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _
    simp only [← F.map_comp, ← op_comp]
    apply hx
    apply_fun fun e => e ≫ f at w 
    simp only [category.assoc] at w ⊢
    convert w using 2
    · ext1
      dsimp [ππ, ff]
      simp only [category.assoc]
      rw [← Profinite.pullback.condition, ← category.assoc]
      change ((ee T₁ f₁ h₁ ≫ gg _) ≫ f).val = (f₁ ≫ f).val
      congr 2
      symm
      apply hee
    · ext1
      dsimp [ππ, ff]
      simp only [category.assoc]
      rw [← Profinite.pullback.condition, ← category.assoc]
      change ((ee T₂ f₂ h₂ ≫ gg _) ≫ f).val = (f₂ ≫ f).val
      congr 2
      symm
      apply hee
  apply hF y (F.map f.op t) (x f hf)
  · intro L e he
    dsimp [y]
    have := hee _ _ he
    conv_lhs => rw [this]
    rw [← ht]
    simp only [← comp_apply, ← F.map_comp, ← op_comp]
    change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _
    simp_rw [← F.map_comp, ← op_comp]
    congr 2
    simp only [category.assoc]
    congr 1
    ext1
    dsimp
    simp [Profinite.pullback.condition]
  · intro L e he
    dsimp [y]
    have := hee _ _ he
    conv_lhs => rw [this]
    dsimp only [xx]
    simp only [← F.map_comp, ← op_comp]
    apply hx
    simp only [category.assoc]
    congr 1
    ext1
    dsimp
    simp [Profinite.pullback.condition]

theorem isExtrSheafOfTypes_iff (F : ExtrDiscᵒᵖ ⥤ Type u') :
    IsExtrSheafOfTypes F ↔ Presieve.IsSheaf ExtrDisc.proetaleTopology F :=
  ⟨fun H => isSheaf_extrDisc_proetaleTopology_of_isExtrSheafOfTypes _ H, fun H =>
    isExtrSheafOfTypes_of_isSheaf_extrDisc_proetaleTopology _ H⟩

theorem isExtrSheaf_iff (C : Type u') [Category.{v'} C] (F : ExtrDiscᵒᵖ ⥤ C) :
    IsExtrSheaf F ↔ Presheaf.IsSheaf ExtrDisc.proetaleTopology F :=
  by
  rw [isExtrSheaf_iff_forall_yoneda]
  apply forall_congr' fun T => _
  apply isExtrSheafOfTypes_iff

theorem isSheaf_extrDisc_proetale_iff_product_condition (C : Type u') [Category.{v'} C]
    [Limits.HasFiniteProducts C] (F : ExtrDiscᵒᵖ ⥤ C) :
    Presheaf.IsSheaf ExtrDisc.proetaleTopology F ↔ ExtrDisc.FiniteProductCondition F :=
  by
  rw [← isExtrSheaf_iff]
  rw [isExtrSheaf_iff_product_condition]

structure ExtrSheafProd (C : Type u') [Category.{v'} C] [Limits.HasFiniteProducts C] where
  val : ExtrDisc.{u}ᵒᵖ ⥤ C
  cond : ExtrDisc.FiniteProductCondition val

namespace ExtrSheafProd

variable (C : Type u') [Category.{v'} C] [Limits.HasFiniteProducts C]

@[ext]
structure Hom (X Y : ExtrSheafProd C) where mk ::
  val : X.val ⟶ Y.val

@[simps]
instance : Category (ExtrSheafProd C) where
  Hom := Hom C
  id X := ⟨𝟙 _⟩
  comp X Y Z f g := ⟨f.val ≫ g.val⟩

end ExtrSheafProd

-- TODO: Break up this structure into individual components... it's too slow as is.
def extrSheafExtrSheafProdEquiv (C : Type u') [Category.{v'} C] [Limits.HasFiniteProducts C] :
    ExtrSheaf C ≌ ExtrSheafProd C
    where
  Functor :=
    { obj := fun F => ⟨F.val, (isSheaf_extrDisc_proetale_iff_product_condition _ _).mp F.2⟩
      map := fun F G f => ⟨f.val⟩
      map_id' := fun X => by ext1; rfl
      map_comp' := fun X Y Z f g => by ext1; rfl }
  inverse :=
    { obj := fun F => ⟨F.val, (isSheaf_extrDisc_proetale_iff_product_condition _ _).mpr F.2⟩
      map := fun F G f => ⟨f.val⟩
      map_id' := fun X => by ext1; rfl
      map_comp' := fun X Y Z f g => by ext1; rfl }
  unitIso :=
    NatIso.ofComponents
      (fun X =>
        { Hom := ⟨𝟙 _⟩
          inv := ⟨𝟙 _⟩
          hom_inv_id' := by ext1; dsimp; simp
          inv_hom_id' := by ext1; dsimp; simp })
      (by
        intro X Y f
        ext1
        dsimp
        simp)
  counitIso :=
    NatIso.ofComponents
      (fun X =>
        { Hom := ⟨𝟙 _⟩
          inv := ⟨𝟙 _⟩
          hom_inv_id' := by ext1; dsimp; simp
          inv_hom_id' := by ext1; dsimp; simp })
      (by
        intro X Y f
        ext1
        dsimp
        simp)
  functor_unitIso_comp' := by
    intros
    ext1
    dsimp
    simp

def condensedExtrSheafProdEquiv (C : Type u') [Category.{u + 1} C] [Limits.HasLimits C] :
    Condensed.{u} C ≌ ExtrSheafProd.{u} C :=
  (condensedExtrSheafEquiv C).symm.trans (extrSheafExtrSheafProdEquiv C)

-- Sanity check
@[simp]
theorem condensedExtrSheafProdEquiv_functor_obj_val {C : Type u'} [Category.{u + 1} C]
    [Limits.HasLimits C] (F : Condensed C) :
    ((condensedExtrSheafProdEquiv C).Functor.obj F).val = extrDiscToProfinite.op ⋙ F.val :=
  rfl

def extrSheafProdToPresheaf (C : Type u') [Category.{v'} C] [Limits.HasFiniteProducts C] :
    ExtrSheafProd.{u} C ⥤ ExtrDisc.{u}ᵒᵖ ⥤ C
    where
  obj F := F.val
  map F G f := f.val
  map_id' X := rfl
  map_comp' X Y Z f g := rfl

instance (C : Type u') [Category.{v'} C] [Limits.HasFiniteProducts C] :
    Full (extrSheafProdToPresheaf C)
    where
  preimage X Y f := ⟨f⟩
  witness' _ _ _ := rfl

instance (C : Type u') [Category.{v'} C] [Limits.HasFiniteProducts C] :
    Faithful (extrSheafProdToPresheaf C) where

open CategoryTheory.Limits

--set_option pp.universes true
section

open scoped Classical

namespace FiniteProductColimitSetup

section

parameter {C : Type u'} [Category.{u + 1} C] [HasLimits C] [HasColimits C] [HasZeroMorphisms C]
  [HasFiniteBiproducts C]

parameter {J : Type (u + 1)} [SmallCategory J] (K : J ⥤ ExtrSheafProd.{u} C)

parameter {ι : Type} [Fintype ι] (X : ι → ExtrDisc.{u})

def kC : ExtrDisc.{u}ᵒᵖ ⥤ C :=
  colimit (K ⋙ extrSheafProdToPresheaf C)

def p₀ : C :=
  ∏ fun i => KC.obj (op (X i))

def p : C :=
  ∏ fun i : ULift.{u + 1} ι => KC.obj (op (X i.down))

def s : C :=
  ⨁ fun i : ι => KC.obj (op (X i))

def prodIsoP : P₀ ≅ P where
  Hom := Pi.lift fun i => Pi.π _ _
  inv := Pi.lift fun i => Pi.π _ ⟨i⟩ ≫ (Iso.refl _).Hom
  hom_inv_id' := by ext ⟨j⟩; simp
  inv_hom_id' := by ext ⟨⟨j⟩⟩; simp

def biprodIsoP : P ≅ S
    where
  Hom := biproduct.lift fun b => Pi.π (fun i : ULift.{u + 1} ι => KC.obj (op (X i.down))) ⟨b⟩
  inv := Pi.lift fun b => biproduct.π _ _
  hom_inv_id' := by ext ⟨⟨j⟩⟩; simp
  inv_hom_id' := by
    apply biproduct.hom_ext
    -- we need to choose the correct extensionality lemma here...
    intro i
    simp

def q₀ (j : J) : C :=
  ∏ fun i : ι => (K.obj j).val.obj (op (X i))

def q₁ (j : J) : C :=
  ∏ fun i : ULift.{u} ι => (K.obj j).val.obj (op (X i.down))

def q (j : J) : C :=
  ∏ fun i : ULift.{u + 1} ι => (K.obj j).val.obj (op (X i.down))

def t (j : J) : C :=
  ⨁ fun i : ι => (K.obj j).val.obj (op (X i))

def prodIsoQ (j : J) : Q₀ j ≅ Q j
    where
  Hom := Pi.lift fun b => Pi.π _ _
  inv := Pi.lift fun b => Pi.π _ ⟨b⟩ ≫ (Iso.refl _).Hom
  hom_inv_id' := by ext ⟨j⟩; simp
  inv_hom_id' := by ext ⟨⟨j⟩⟩; simp

def prodIsoQ' (j : J) : Q₀ j ≅ Q₁ j
    where
  Hom := Pi.lift fun b => Pi.π _ _
  inv := Pi.lift fun b => Pi.π (fun i : ULift ι => (K.obj j).val.obj (op (X i.down))) ⟨b⟩
  hom_inv_id' := by ext ⟨j⟩; simp
  inv_hom_id' := by ext ⟨⟨j⟩⟩; simp

def biprodIsoQ (j : J) : Q j ≅ T j
    where
  Hom :=
    biproduct.lift fun b => Pi.π (fun i : ULift.{u + 1} ι => (K.obj j).val.obj (op (X i.down))) ⟨b⟩
  inv := Pi.lift fun b => biproduct.π _ _
  hom_inv_id' := by ext ⟨⟨j⟩⟩; simp
  inv_hom_id' := by
    apply biproduct.hom_ext
    -- we need to choose the correct extensionality lemma here...
    intro i
    simp

def kQ₀ (j) : (K.obj j).val.obj (op (ExtrDisc.sigma (X ∘ ULift.down))) ≅ Q₀ j :=
  by
  -- Lean is being annoying... again...
  let t : (K.obj j).val.obj (op (ExtrDisc.sigma (X ∘ ULift.down))) ⟶ Q₀ K X j :=
    pi.lift fun i : ι => (K.obj j).val.map (ExtrDisc.sigma.ι (X ∘ ULift.down) ⟨i⟩).op
  have := (K.obj j).cond (ULift ι) (X ∘ ULift.down); dsimp at this 
  let s := _; change is_iso s at this 
  have ht : t = s ≫ (prod_iso_Q' _ _ _).inv :=
    by
    dsimp [s, t, prod_iso_Q']; apply limit.hom_ext; rintro ⟨q⟩
    simp
  haveI : is_iso t := by rw [ht]; skip; apply is_iso.comp_is_iso
  exact as_iso t

def mapQ₀ {i j : J} (f : i ⟶ j) : Q₀ i ⟶ Q₀ j :=
  Pi.lift fun a => Pi.π _ a ≫ (K.map f).val.app _

def mapQ {i j : J} (f : i ⟶ j) : Q i ⟶ Q j :=
  Pi.lift fun a => Pi.π _ a ≫ (K.map f).val.app _

def mapT {i j : J} (f : i ⟶ j) : T i ⟶ T j :=
  biproduct.map fun a => (K.map f).val.app _

--λ a, biproduct.π _ a ≫ (K.map f).val.app _
def q₀Functor : J ⥤ C where
  obj := Q₀
  map i j f := map_Q₀ f
  map_id' := by
    intro i
    dsimp [map_Q₀]
    ext1 ⟨j⟩
    simp
  map_comp' := by
    intro i j k f g
    dsimp [map_Q₀]
    ext1
    simp

def qFunctor : J ⥤ C where
  obj := Q
  map i j f := map_Q f
  map_id' := by intro i; dsimp [map_Q]; ext1 ⟨j⟩; simp
  map_comp' := by intro i j k f g; dsimp [map_Q]; ext1; simp

def tFunctor : J ⥤ C where
  obj := T
  map i j f := map_T f
  map_id' := by
    intro i; dsimp [map_T]
    apply biproduct.hom_ext; intro a; simp; erw [category.id_comp]
  map_comp' := by
    intro i j k f g
    dsimp [map_T]
    apply biproduct.hom_ext
    intro a
    simp

def kQ₀NatIso :
    K ⋙ extrSheafProdToPresheaf _ ⋙ (evaluation _ _).obj (op (ExtrDisc.sigma (X ∘ ULift.down))) ≅
      Q₀_functor :=
  NatIso.ofComponents (fun j => KQ₀ _)
    (by
      intro i j f
      dsimp [extrSheafProdToPresheaf, Q₀_functor, KQ₀, map_Q₀]
      ext
      simp)

def q₀QNatIso : Q₀_functor ≅ Q_functor :=
  NatIso.ofComponents (fun j => prod_iso_Q _)
    (by
      intro i j f
      dsimp [Q₀_functor, prod_iso_Q, map_Q₀, Q_functor, map_Q]
      ext1
      simp)

def qTNatIso : Q_functor ≅ T_functor :=
  NatIso.ofComponents (fun j => biprod_iso_Q _)
    (by
      intro i j f
      dsimp [Q_functor, biprod_iso_Q, map_T, T_functor, map_Q]
      apply biproduct.hom_ext; intro i
      simp)

def colimitKQ₀NatIso : KC ≅ (K ⋙ extrSheafProdToPresheaf _).flip ⋙ colim :=
  colimitIsoFlipCompColim (K ⋙ extrSheafProdToPresheaf C)

def colimitKQ₀NatIsoEval :
    KC.obj (op (ExtrDisc.sigma (X ∘ ULift.down))) ≅
      colimit
        (K ⋙
          extrSheafProdToPresheaf _ ⋙
            (evaluation _ _).obj (op (ExtrDisc.sigma (X ∘ ULift.down)))) :=
  colimit_KQ₀_nat_iso.app _

def cT : C :=
  ⨁ fun i : ι => colimit (K ⋙ extrSheafProdToPresheaf _ ⋙ (evaluation _ _).obj (op (X i)))

def ctIso (i : ι) :
    (colimit (K ⋙ extrSheafProdToPresheaf _)).obj (op (X i)) ≅
      colimit (K ⋙ extrSheafProdToPresheaf _ ⋙ (evaluation _ _).obj (op (X i))) :=
  colimit_KQ₀_nat_iso.app _

def cTIso : CT ≅ S where
  Hom := biproduct.map fun b => (ct_iso _).inv
  inv := biproduct.map fun b => (ct_iso _).Hom
  hom_inv_id' := by
    ext1
    simp
    erw [category.comp_id]
  inv_hom_id' := by
    ext1
    simp
    erw [category.comp_id]

-- This is the main point where we prove that colimits commute with biproducts.
-- The rest is glue.
def colimitTIso : colimit T_functor ≅ CT
    where
  Hom :=
    colimit.desc T_functor
      ⟨CT,
        { app := fun j =>
            biproduct.map fun i =>
              colimit.ι (K ⋙ extrSheafProdToPresheaf C ⋙ (evaluation ExtrDiscᵒᵖ C).obj (op (X i))) j
          naturality' := by
            intro a b f
            dsimp [T_functor, map_T]
            apply biproduct.hom_ext'
            intro i
            simp
            rw [← colimit.w _ f]
            simp only [category.assoc]
            rfl }⟩
  inv :=
    biproduct.desc fun b =>
      colimit.desc (K ⋙ extrSheafProdToPresheaf _ ⋙ (evaluation _ _).obj (op (X b)))
        ⟨colimit T_functor,
          { app := fun j =>
              by
                dsimp [extrSheafProdToPresheaf, T_functor, T]
                apply biproduct.ι _ b ≫ colimit.ι _ j
            naturality' := by
              intro i j f
              dsimp [extrSheafProdToPresheaf]
              simp
              rw [← colimit.w _ f]
              dsimp only [T_functor, map_T]
              simp }⟩
  hom_inv_id' := by
    ext1 j
    dsimp
    apply biproduct.hom_ext'
    intro b
    simp
  inv_hom_id' := by
    apply biproduct.hom_ext'
    intro b
    simp
    apply colimit.hom_ext
    intro j
    simp
    erw [category.comp_id]

/- warning: finite_product_colimit_setup.t clashes with finite_product_colimit_setup.T -> FiniteProductColimitSetup.t
Case conversion may be inaccurate. Consider using '#align finite_product_colimit_setup.t FiniteProductColimitSetup.tₓ'. -/
-- We want this to be an isomorphism.
def t : KC.obj (op (ExtrDisc.sigma (X ∘ ULift.down))) ⟶ P₀ :=
  Pi.lift fun i => KC.map (ExtrDisc.sigma.ι (X ∘ ULift.down) ⟨i⟩).op

theorem key_lemma :
    t =
      colimit_KQ₀_nat_iso_eval.Hom ≫
        (HasColimit.isoOfNatIso KQ₀_nat_iso).Hom ≫
          (HasColimit.isoOfNatIso Q₀Q_nat_iso).Hom ≫
            (HasColimit.isoOfNatIso QT_nat_iso).Hom ≫
              colimit_T_iso.Hom ≫ CT_iso.Hom ≫ biprod_iso_P.inv ≫ prod_iso_P.inv :=
  by
  dsimp [prod_iso_P, biprod_iso_P, CT_iso, colimit_T_iso, colimit_KQ₀_nat_iso_eval, t,
    colimit_KQ₀_nat_iso, KC, ct_iso]
  ext : 2
  simp
  erw [colimit.ι_desc_assoc]
  dsimp [cocones.precompose, KQ₀_nat_iso, Q₀Q_nat_iso, QT_nat_iso, KQ₀, prod_iso_Q, biprod_iso_Q]
  simp
  erw [colimit.ι_desc]
  dsimp
  simp

theorem main : IsIso t := by
  rw [key_lemma]
  apply is_iso.comp_is_iso

-- ;-)
end

end FiniteProductColimitSetup

variable {C : Type u'} [Category.{u + 1} C] [HasZeroMorphisms C] [HasFiniteBiproducts C]

-- move me
theorem pi_π_comp_eqToHom {α : Type} [Fintype α] (X : α → C) (a b : α) (h : a = b) :
    Pi.π X a ≫ eqToHom (by rw [h]) = Pi.π X b := by induction h; simp

-- move me
theorem pi_π_comp_eq_to_hom' {α : Type u} [Fintype α] (X : α → C) (a b : α) (h : a = b) :
    Pi.π X a ≫ eqToHom (by rw [h]) = Pi.π X b := by induction h; simp

-- move me
attribute [reassoc] ExtrDisc.sigma.ι_desc

variable [HasLimits C] [HasColimits C]

theorem ExtrDisc.sigma.eqToHom_ι_eq_ι {α : Type u} [Fintype α] (X : α → ExtrDisc.{u}) (a b : α)
    (h : a = b) : eqToHom (by rw [h]) ≫ ExtrDisc.sigma.ι X a = ExtrDisc.sigma.ι X b := by
  induction h; simp

def ExtrDisc.sigmaIsoOfEquiv {α β : Type u} [Fintype α] [Fintype β] (X : α → ExtrDisc.{u})
    (e : β ≃ α) : ExtrDisc.sigma (X ∘ e) ≅ ExtrDisc.sigma X
    where
  Hom := ExtrDisc.sigma.desc _ fun b => ExtrDisc.sigma.ι _ _
  inv :=
    ExtrDisc.sigma.desc _ fun a =>
      eqToHom
          (by
            dsimp
            refine' congr_arg _ _
            exact (e.apply_symm_apply _).symm) ≫
        ExtrDisc.sigma.ι _ (e.symm a)
  hom_inv_id' := by
    apply ExtrDisc.sigma.hom_ext; intro b
    simp [ExtrDisc.sigma.ι_desc_assoc, ExtrDisc.sigma.ι_desc]
    apply ExtrDisc.sigma.eqToHom_ι_eq_ι (X ∘ e)
    simp
  inv_hom_id' := by
    apply ExtrDisc.sigma.hom_ext; intro b
    simp [ExtrDisc.sigma.ι_desc_assoc, ExtrDisc.sigma.ι_desc]
    apply ExtrDisc.sigma.eqToHom_ι_eq_ι X
    simp

theorem finiteProductCondition_holds_for_colimit {J : Type (u + 1)} [SmallCategory J]
    (K : J ⥤ ExtrSheafProd.{u} C) [HasColimits C] :
    ExtrDisc.FiniteProductCondition (colimit (K ⋙ extrSheafProdToPresheaf C)) :=
  by
  intro ι _ X
  let e : ι ≃ Fin _ := Fintype.equivFin _
  let X' := X ∘ e.symm
  dsimp
  let E : ExtrDisc.sigma (X' ∘ ULift.down) ≅ ExtrDisc.sigma X :=
    ExtrDisc.sigmaIsoOfEquiv X (equiv.ulift.trans e.symm)
  have := FiniteProductColimitSetup.main K X'
  let eL :
    (colimit (K ⋙ extrSheafProdToPresheaf C)).obj (op (ExtrDisc.sigma X)) ≅
      (colimit (K ⋙ extrSheafProdToPresheaf C)).obj (op (ExtrDisc.sigma (X' ∘ ULift.down))) :=
    functor.map_iso _ E.op
  let E' :
    FiniteProductColimitSetup.p₀ K X' ≅
      ∏ fun i : ι => (colimit (K ⋙ extrSheafProdToPresheaf C)).obj (op (X i)) :=
    ⟨limits.pi.lift _, limits.pi.lift _, _, _⟩
  rotate_left
  · intro i
    dsimp [FiniteProductColimitSetup.p₀]
    refine' pi.π _ (e i) ≫ _
    refine' CategoryTheory.Functor.map _ _
    refine' Quiver.Hom.op _
    refine' eq_to_hom _
    refine' congr_arg X _
    exact (e.symm_apply_apply _).symm
  · intro i
    refine' pi.π _ (e.symm i)
  · apply limits.limit.hom_ext
    rintro ⟨j⟩; dsimp
    simp only [eq_to_hom_op, category.assoc, limit.lift_π, fan.mk_π_app, category.id_comp]
    rw [CategoryTheory.eqToHom_map]
    apply pi_π_comp_eqToHom; simp
  · apply limits.limit.hom_ext
    rintro ⟨j⟩; dsimp
    simp only [eq_to_hom_op, category.assoc, limit.lift_π, fan.mk_π_app, category.id_comp]
    rw [CategoryTheory.eqToHom_map]
    rw [limit.lift_π_assoc]; dsimp
    change _ = pi.π _ _
    apply pi_π_comp_eq_to_hom' fun i : ι => (colimit (K ⋙ extrSheafProdToPresheaf C)).obj (op (X i))
    simp
  let t := _; change is_iso t; let s := _; change is_iso s at this 
  have ht : t = eL.hom ≫ s ≫ E'.hom := by
    dsimp [t, eL, s, E', E]
    apply limit.hom_ext; rintro ⟨j⟩
    simp only [category.assoc, limit.lift_π]
    dsimp
    rw [CategoryTheory.eqToHom_op]
    rw [CategoryTheory.eqToHom_map]
    dsimp [FiniteProductColimitSetup.t]
    simp only [limit.lift_π_assoc]
    dsimp [FiniteProductColimitSetup.kC]
    simp only [← category.assoc, ← functor.map_comp, ← op_comp]
    erw [ExtrDisc.sigma.ι_desc]
    dsimp
    rw [← ExtrDisc.sigma.eqToHom_ι_eq_ι X (e.symm (e j)) j (by simp)]
    simp [CategoryTheory.eqToHom_map]
  rw [ht]; skip; infer_instance

instance extrSheafProdToPresheafCreatesColimit {J : Type (u + 1)} [SmallCategory J]
    (K : J ⥤ ExtrSheafProd.{u} C) [HasColimits C] :
    CreatesColimit K (extrSheafProdToPresheaf.{u} C) :=
  createsColimitOfFullyFaithfulOfIso
      ⟨colimit (K ⋙ extrSheafProdToPresheaf _), finiteProductCondition_holds_for_colimit _⟩ <|
    eqToIso rfl

instance extrSheafProdToPresheafCreatesColimitsOfShape {J : Type (u + 1)} [SmallCategory J]
    [HasColimits C] : CreatesColimitsOfShape J (extrSheafProdToPresheaf.{u} C) :=
  ⟨fun K =>
    { reflects := by
        intro c hc
        haveI : has_colimit (K ⋙ extrSheafProdToPresheaf C) := has_colimit.mk ⟨_, hc⟩
        apply is_colimit_of_reflects (extrSheafProdToPresheaf.{u} C)
        assumption
      lifts := fun c hc =>
        { liftedCocone :=
            haveI : has_colimit (K ⋙ extrSheafProdToPresheaf C) := has_colimit.mk ⟨_, hc⟩
            lift_colimit hc
          validLift :=
            by
            haveI : has_colimit (K ⋙ extrSheafProdToPresheaf C) := has_colimit.mk ⟨_, hc⟩
            apply lifted_colimit_maps_to_original } }⟩

instance extrSheafProdToPresheafCreatesColimits [HasColimits C] :
    CreatesColimits (extrSheafProdToPresheaf.{u} C) := by constructor

-- Forgetting to presheaves, and restricting to `ExtrDisc` creates colimits.
instance condensedToExtrDiscPresheafCreatesColimits [HasColimits C] :
    CreatesColimits
      ((sheafToPresheaf _ _ : Condensed C ⥤ _) ⋙
        (whiskeringLeft _ _ _).obj extrDiscToProfinite.op) :=
  by
  change creates_colimits ((condensedExtrSheafProdEquiv C).Functor ⋙ extrSheafProdToPresheaf C)
  apply (config := { instances := false }) CategoryTheory.compCreatesColimits <;> infer_instance

end

