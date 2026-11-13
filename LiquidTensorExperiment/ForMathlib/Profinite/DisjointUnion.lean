import Mathlib.CategoryTheory.Limits.Shapes.Products
import LiquidTensorExperiment.ForMathlib.Profinite.CompatDiscreteQuotient
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Projective
import LiquidTensorExperiment.ForMathlib.QuotientMap
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

#align_import for_mathlib.Profinite.disjoint_union

/-!

In this file we show that a finite disjoint union of profinite sets agrees with the coproduct.
*Note:* The existence of the coproduct is currently shown using some abstract nonsense.

-/


namespace Profinite

universe u

variable {α : Type u} [Fintype α] (X : α → Profinite.{u})

def empty : Profinite.{u} :=
  Profinite.of PEmpty

def empty.elim (X : Profinite.{u}) : empty ⟶ X where toFun := PEmpty.elim

def sum (X Y : Profinite.{u}) : Profinite.{u} :=
  Profinite.of <| Sum X Y

def sum.inl (X Y : Profinite.{u}) : X ⟶ sum X Y where toFun := Sum.inl

def sum.inr (X Y : Profinite.{u}) : Y ⟶ sum X Y where toFun := Sum.inr

def sum.desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z
    where
  toFun x := Sum.recOn x f g
  continuous_toFun := by
    simp only [continuous_sup_dom, continuous_coinduced_dom]
    exact ⟨f.continuous, g.continuous⟩

@[simp, reassoc]
theorem sum.inl_desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) :
    sum.inl X Y ≫ sum.desc X Y f g = f := by ext; rfl

@[simp, reassoc]
theorem sum.inr_desc {Z} (X Y : Profinite.{u}) (f : X ⟶ Z) (g : Y ⟶ Z) :
    sum.inr X Y ≫ sum.desc X Y f g = g := by ext; rfl

theorem sum.hom_ext {Z} (X Y : Profinite.{u}) (e₁ e₂ : sum X Y ⟶ Z)
    (hl : sum.inl X Y ≫ e₁ = sum.inl X Y ≫ e₂) (hr : sum.inr X Y ≫ e₁ = sum.inr X Y ≫ e₂) :
    e₁ = e₂ := by
  ext (u | u)
  · apply_fun fun e => e u at hl ; exact hl
  · apply_fun fun e => e u at hr ; exact hr

def sigma : Profinite.{u} :=
  Profinite.of <| Σ a, X a

def sigma.ι (a : α) : X a ⟶ sigma X where
  toFun t := ⟨_, t⟩
  continuous_toFun := by
    apply continuous_sSup_rng
    exact ⟨a, rfl⟩
    apply continuous_coinduced_rng

theorem sigma.ι_injective (a : α) : Function.Injective (sigma.ι X a) := by dsimp [sigma.ι];
  exact sigma_mk_injective

theorem sigma.ι_jointly_surjective (t : sigma X) : ∃ (a : _) (x : X a), sigma.ι X a x = t := by
  rcases t with ⟨a, t⟩; exact ⟨a, t, rfl⟩

def sigma.desc {Y} (f : ∀ a, X a ⟶ Y) : sigma X ⟶ Y
    where
  toFun := fun ⟨a, t⟩ => f a t
  continuous_toFun := by
    rw [continuous_sSup_dom]
    rintro _ ⟨a, rfl⟩
    skip
    rw [continuous_coinduced_dom]
    exact (f a).Continuous

theorem sigma.desc_surjective {Y} (f : ∀ a, X a ⟶ Y) (surj : ∀ y, ∃ (a : _) (x : X a), f a x = y) :
    Function.Surjective (sigma.desc X f) := by
  intro y
  obtain ⟨a, x, hx⟩ := surj y
  exact ⟨⟨a, x⟩, hx⟩

@[simp, reassoc]
theorem sigma.ι_desc {Y} (a) (f : ∀ a, X a ⟶ Y) : sigma.ι X a ≫ sigma.desc X f = f a := by ext; rfl

theorem sigma.hom_ext {Y} (f g : sigma X ⟶ Y) (w : ∀ a, sigma.ι X a ≫ f = sigma.ι X a ≫ g) :
    f = g := by
  ext ⟨a, t⟩
  specialize w a
  apply_fun fun e => e t at w 
  exact w

open CategoryTheory

def sigmaCofan : Limits.Cofan X :=
  Limits.Cofan.mk (sigma X) (sigma.ι X)

def sigmaCofanIsColimit : Limits.IsColimit (sigmaCofan X)
    where
  desc S := sigma.desc _ fun a => S.ι.app ⟨a⟩
  fac := by
    rintro S ⟨j⟩
    ext t
    rfl
  uniq := by
    intro S m h
    apply sigma.hom_ext
    intro a
    convert h ⟨a⟩
    simp

#print Profinite.pullback /-
def pullback {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) : Profinite
    where
  toCompHaus :=
    { toTop := TopCat.of {a : X × Y | f a.1 = g a.2}
      IsCompact := by
        erw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        apply isClosed_eq
        all_goals continuity
      is_hausdorff := by
        change T2Space {a : X × Y | f a.1 = g a.2}
        infer_instance }
  IsTotallyDisconnected := Subtype.totallyDisconnectedSpace
-/

#print Profinite.pullback.fst /-
def pullback.fst {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) : pullback f g ⟶ X
    where toFun a := a.1.1
-/

#print Profinite.pullback.snd /-
def pullback.snd {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) : pullback f g ⟶ Y
    where toFun a := a.1.2
-/

#print Profinite.pullback.condition /-
@[reassoc]
theorem pullback.condition {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g := by ext ⟨t, ht⟩; exact ht
-/

#print Profinite.pullback.lift /-
def pullback.lift {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e₁ : W ⟶ X) (e₂ : W ⟶ Y)
    (w : e₁ ≫ f = e₂ ≫ g) : W ⟶ pullback f g
    where toFun t := ⟨(e₁ t, e₂ t), by apply_fun fun ee => ee t at w ; exact w⟩
-/

#print Profinite.pullback.lift_fst /-
@[simp, reassoc]
theorem pullback.lift_fst {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e₁ : W ⟶ X)
    (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) : pullback.lift f g e₁ e₂ w ≫ pullback.fst f g = e₁ := by
  ext; rfl
-/

#print Profinite.pullback.lift_snd /-
@[simp, reassoc]
theorem pullback.lift_snd {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B) (e₁ : W ⟶ X)
    (e₂ : W ⟶ Y) (w : e₁ ≫ f = e₂ ≫ g) : pullback.lift f g e₁ e₂ w ≫ pullback.snd f g = e₂ := by
  ext; rfl
-/

#print Profinite.pullback.hom_ext /-
theorem pullback.hom_ext {W X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (e₁ e₂ : W ⟶ pullback f g) (w₁ : e₁ ≫ pullback.fst f g = e₂ ≫ pullback.fst f g)
    (w₂ : e₁ ≫ pullback.snd f g = e₂ ≫ pullback.snd f g) : e₁ = e₂ :=
  by
  ext t
  · apply_fun fun e => e t at w₁ ; exact w₁
  · apply_fun fun e => e t at w₂ ; exact w₂
-/

def sigmaPullbackToPullbackSigma {B} (f : ∀ a, X a ⟶ B) :
    (sigma fun a : α × α => pullback (f a.1) (f a.2)) ⟶
      pullback (sigma.desc X f) (sigma.desc X f) :=
  sigma.desc _ fun a =>
    pullback.lift _ _ (pullback.fst _ _ ≫ sigma.ι _ _) (pullback.snd _ _ ≫ sigma.ι _ _)
      (by cases a; dsimp at *; ext1 x; cases x; assumption)

instance {B} (f : ∀ a, X a ⟶ B) : IsIso (sigmaPullbackToPullbackSigma X f) :=
  isIso_of_bijective _
    (by
      constructor
      · rintro ⟨⟨a, b⟩, ⟨⟨x₁, x₂⟩, hx⟩⟩ ⟨⟨a', b'⟩, ⟨⟨x'₁, x'₂⟩, hx'⟩⟩ h
        dsimp [sigma_pullback_to_pullback_sigma, sigma.desc, pullback.lift, sigma.ι, pullback.fst,
          pullback.snd] at *
        tidy
      · rintro ⟨⟨⟨a, x⟩, ⟨b, y⟩⟩, h⟩
        refine' ⟨⟨⟨a, b⟩, ⟨⟨x, y⟩, h⟩⟩, rfl⟩)

@[simp]
theorem sigmaPullbackToPullbackSigma_fst {B} (f : ∀ a, X a ⟶ B) :
    sigmaPullbackToPullbackSigma X f ≫ pullback.fst _ _ =
      sigma.desc _ fun a => pullback.fst _ _ ≫ sigma.ι _ a.1 :=
  by ext ⟨_, _⟩ <;> rfl

@[simp]
theorem sigmaPullbackToPullbackSigma_snd {B} (f : ∀ a, X a ⟶ B) :
    sigmaPullbackToPullbackSigma X f ≫ pullback.snd _ _ =
      sigma.desc _ fun a => pullback.snd _ _ ≫ sigma.ι _ a.2 :=
  by ext ⟨_, _⟩ <;> rfl

theorem sigma_iso_of_equiv_aux {α β : Type u} [Fintype α] [Fintype β] (e : α ≃ β)
    (X : β → Profinite.{u}) (b : β) (h : b = e (e.symm b)) :
    eqToHom (by rw [h]) ≫ sigma.ι _ _ = sigma.ι X b :=
  by
  induction h
  simp

def sigmaIsoOfEquiv {α β : Type u} [Fintype α] [Fintype β] (e : α ≃ β) (X : β → Profinite.{u}) :
    sigma (X ∘ e) ≅ sigma X
    where
  Hom := sigma.desc _ fun a => sigma.ι _ (e a)
  inv := sigma.desc _ fun b => eqToHom (by simp) ≫ sigma.ι _ (e.symm b)
  hom_inv_id' := by
    apply sigma.hom_ext
    intro a
    dsimp
    simp only [sigma.ι_desc_assoc, sigma.ι_desc, category.comp_id]
    apply sigma_iso_of_equiv_aux
    simp
  inv_hom_id' := by
    apply sigma.hom_ext
    intro b
    dsimp
    simp only [sigma.ι_desc_assoc, category.assoc, sigma.ι_desc, category.comp_id]
    apply sigma_iso_of_equiv_aux
    simp

def sigmaIsoEmpty : sigma PEmpty.elim ≅ empty
    where
  Hom := sigma.desc _ fun a => a.elim
  inv := empty.elim _
  hom_inv_id' := by
    apply sigma.hom_ext
    rintro ⟨⟩
  inv_hom_id' := by ext ⟨⟩

-- fin_zero_elim is terrible!
def sigmaIsoEmpty' (X : (PEmpty : Type u) → Profinite.{u}) : sigma X ≅ (empty : Profinite.{u})
    where
  Hom := sigma.desc _ fun i => i.elim
  inv := empty.elim _
  hom_inv_id' := by
    apply sigma.hom_ext
    rintro ⟨⟩
  inv_hom_id' := by ext ⟨⟩

def sigmaSumIso {α β : Type u} [Fintype α] [Fintype β] (X : α → Profinite.{u})
    (Y : β → Profinite.{u}) : (sigma fun x : Sum α β => Sum.recOn x X Y) ≅ sum (sigma X) (sigma Y)
    where
  Hom :=
    sigma.desc _ fun x =>
      Sum.recOn x (fun a => by dsimp; exact sigma.ι _ _ ≫ Profinite.sum.inl _ _) fun b =>
        by dsimp; exact sigma.ι _ _ ≫ Profinite.sum.inr _ _
  inv :=
    sum.desc _ _
      (sigma.desc _ fun a => by
        refine' _ ≫ sigma.ι _ (_root_.sum.inl a)
        exact 𝟙 _)
      (sigma.desc _ fun b => by
        refine' _ ≫ sigma.ι _ (_root_.sum.inr b)
        exact 𝟙 _)
  hom_inv_id' := by
    apply sigma.hom_ext
    rintro (a | b)
    all_goals dsimp; simp
  inv_hom_id' := by
    apply sum.hom_ext
    all_goals
      dsimp
      simp
      apply sigma.hom_ext
      intros
      simp

def sigmaSumIso' {α β : Type u} [Fintype α] [Fintype β] (X : Sum α β → Profinite.{u}) :
    sigma X ≅ sum (sigma (X ∘ Sum.inl)) (sigma (X ∘ Sum.inr))
    where
  Hom :=
    sigma.desc _ fun x =>
      Sum.recOn x (fun a => sigma.ι (X ∘ _root_.sum.inl) a ≫ sum.inl _ _) fun b =>
        sigma.ι (X ∘ _root_.sum.inr) b ≫ sum.inr _ _
  inv := sum.desc _ _ (sigma.desc _ fun a => sigma.ι _ _) (sigma.desc _ fun b => sigma.ι _ _)
  hom_inv_id' := by
    apply sigma.hom_ext
    rintro (a | b)
    all_goals dsimp; simp
  inv_hom_id' := by
    apply sum.hom_ext
    all_goals
      dsimp
      simp
      apply sigma.hom_ext
      intros; simp

def sigmaPunitIso (X : (PUnit : Type u) → Profinite.{u}) : X PUnit.unit ≅ sigma X
    where
  Hom := sigma.ι _ _
  inv := sigma.desc _ fun ⟨⟩ => 𝟙 _

def sigmaWalkingPairIso (X : ULift.{u} Limits.WalkingPair → Profinite.{u}) :
    sigma X ≅ (X ⟨Limits.WalkingPair.left⟩).Sum (X ⟨Limits.WalkingPair.right⟩)
    where
  Hom :=
    sigma.desc _ fun a =>
      match a with
      | ⟨a⟩ => Limits.WalkingPair.recOn a (sum.inl _ _) (sum.inr _ _)
  inv := sum.desc _ _ (sigma.ι X (ULift.up _)) (sigma.ι X (ULift.up _))
  hom_inv_id' := by
    apply sigma.hom_ext
    rintro (⟨a⟩ | ⟨b⟩)
    all_goals
      dsimp; simp only [sigma.ι_desc_assoc, category.comp_id]
      dsimp [sigma_walking_pair_iso._match_1]
      simp only [sum.inl_desc, sum.inr_desc]
  inv_hom_id' := by
    apply sum.hom_ext
    all_goals dsimp; simpa only [sum.inl_desc_assoc, sigma.ι_desc, category.comp_id]

--TODO: Finish off the api for the explicit pullback
def equalizer {X Y : Profinite.{u}} (f g : X ⟶ Y) : Profinite
    where
  toCompHaus :=
    { toTop := TopCat.of {x | f x = g x}
      IsCompact := by
        erw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        apply isClosed_eq
        exact f.continuous
        exact g.continuous
      is_hausdorff := by
        change T2Space {x | f x = g x}
        infer_instance }
  IsTotallyDisconnected := Subtype.totallyDisconnectedSpace

def equalizer.ι {X Y : Profinite.{u}} (f g : X ⟶ Y) : equalizer f g ⟶ X where toFun x := x.1

def equalizer.lift {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e : W ⟶ X) (w : e ≫ f = e ≫ g) :
    W ⟶ equalizer f g where toFun t := ⟨e t, by apply_fun fun ee => ee t at w ; exact w⟩

@[simp, reassoc]
theorem equalizer.lift_ι {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e : W ⟶ X) (w : e ≫ f = e ≫ g) :
    equalizer.lift f g e w ≫ equalizer.ι f g = e := by ext; rfl

theorem equalizer.hom_ext {W X Y : Profinite.{u}} (f g : X ⟶ Y) (e₁ e₂ : W ⟶ equalizer f g)
    (w : e₁ ≫ equalizer.ι f g = e₂ ≫ equalizer.ι f g) : e₁ = e₂ :=
  by
  ext t
  apply_fun fun ee => ee t at w 
  exact w

/-- Descend a morphism along a surjective morphism. -/
noncomputable def descend {X B Y : Profinite} (π : X ⟶ B) (t : X ⟶ Y) (hπ : Function.Surjective π)
    (w : pullback.fst π π ≫ t = pullback.snd π π ≫ t) : B ⟶ Y
    where
  toFun :=
    (fun i =>
        Quotient.liftOn' i t
          (by
            rintro a b (h : π _ = π _)
            apply_fun fun e => e ⟨(a, b), h⟩ at w 
            exact w) :
        Quotient (Setoid.ker π) → Y) ∘
      (Profinite.quotientMap π hπ).Homeomorph.symm
  continuous_toFun := by
    apply Continuous.comp
    · apply continuous_quot_lift; exact t.continuous
    · exact (QuotientMap π hπ).Homeomorph.symm.Continuous

-- TODO: Define `foo_to_Top` analogues for the colimit-like constructions above.
noncomputable def descendToTop {X B : Profinite} {Y : TopCat} (π : X ⟶ B)
    (t : Profinite.toTopCat.obj X ⟶ Y) (hπ : Function.Surjective π)
    (w :
      Profinite.toTopCat.map (pullback.fst π π) ≫ t =
        Profinite.toTopCat.map (pullback.snd π π) ≫ t) :
    Profinite.toTopCat.obj B ⟶ Y
    where
  toFun :=
    (fun i =>
        Quotient.liftOn' i t
          (by
            rintro a b (h : π _ = π _)
            apply_fun fun e => e ⟨(a, b), h⟩ at w 
            exact w) :
        Quotient (Setoid.ker π) → Y) ∘
      (Profinite.quotientMap π hπ).Homeomorph.symm
  continuous_toFun := by
    apply Continuous.comp
    · apply continuous_quot_lift; exact t.continuous
    · exact (QuotientMap π hπ).Homeomorph.symm.Continuous

@[simp]
theorem π_descend {X B Y : Profinite} (π : X ⟶ B) (t : X ⟶ Y) (hπ : Function.Surjective π)
    (w : pullback.fst π π ≫ t = pullback.snd π π ≫ t) : π ≫ descend π t hπ w = t :=
  by
  ext i
  dsimp [descend, Setoid.quotientKerEquivOfSurjective, Setoid.quotientKerEquivOfRightInverse,
    QuotientMap.homeomorph]
  let c : pullback π π := ⟨(Function.surjInv hπ (π i), i), Function.surjInv_eq hπ (π i)⟩
  apply_fun fun e => e c at w 
  exact w

theorem π_descendToTop {X B : Profinite} {Y : TopCat} (π : X ⟶ B) (t : Profinite.toTopCat.obj X ⟶ Y)
    (hπ : Function.Surjective π)
    (w :
      Profinite.toTopCat.map (pullback.fst π π) ≫ t =
        Profinite.toTopCat.map (pullback.snd π π) ≫ t) :
    Profinite.toTopCat.map π ≫ descendToTop π t hπ w = t :=
  by
  ext i
  dsimp [descend_to_Top, Setoid.quotientKerEquivOfSurjective, Setoid.quotientKerEquivOfRightInverse,
    QuotientMap.homeomorph]
  let c : pullback π π := ⟨(Function.surjInv hπ (π i), i), Function.surjInv_eq hπ (π i)⟩
  apply_fun fun e => e c at w 
  exact w

def product {α : Type} (X : α → Profinite.{u}) : Profinite :=
  Profinite.of <| ∀ a, X a

def product.π {α : Type} (X : α → Profinite.{u}) (a : α) : product X ⟶ X a :=
  ⟨fun t => t a, continuous_apply _⟩

def product.lift {α : Type} {Y : Profinite.{u}} (X : α → Profinite.{u}) (f : ∀ a, Y ⟶ X a) :
    Y ⟶ product X :=
  ⟨fun y a => f a y, by
    apply continuous_pi
    intro i
    exact (f i).2⟩

@[simp, reassoc]
theorem product.lift_π {α : Type} {Y : Profinite.{u}} (X : α → Profinite.{u}) (f : ∀ a, Y ⟶ X a)
    (a) : product.lift X f ≫ product.π X a = f _ := by ext; rfl

theorem product.hom_ext {α : Type} {Y : Profinite.{u}} (X : α → Profinite.{u}) (f g : Y ⟶ product X)
    (h : ∀ a, f ≫ product.π X a = g ≫ product.π X a) : f = g :=
  by
  ext y a
  specialize h a
  apply_fun fun e => e y at h 
  exact h

def punit : Profinite.{u} :=
  Profinite.of PUnit

def punit.elim (X : Profinite.{u}) : X ⟶ punit :=
  ⟨fun x => PUnit.unit, by tidy⟩

theorem punit.hom_ext (X : Profinite.{u}) (f g : X ⟶ punit) : f = g := by ext

def fromPunit {X : Profinite.{u}} (x : X) : punit ⟶ X :=
  ⟨fun _ => x, by tidy⟩

def pow (X : Profinite.{u}) (n : ℕ) : Profinite.{u} :=
  Profinite.product fun i : Fin n => X

def mapPow {X Y : Profinite.{u}} (f : X ⟶ Y) (n : ℕ) : X.pow n ⟶ Y.pow n :=
  Profinite.product.lift _ fun n => Profinite.product.π _ n ≫ f

end Profinite

