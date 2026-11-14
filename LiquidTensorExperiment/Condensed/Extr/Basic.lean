import Mathlib.Topology.Category.Profinite.Projective
import LiquidTensorExperiment.ForMathlib.Profinite.DisjointUnion
import LiquidTensorExperiment.ForMathlib.ConcreteEqualizer

#align_import condensed.extr.basic

noncomputable section

open CategoryTheory

universe u w v

structure ExtrDisc where
  val : Profinite.{u}
  [cond : Projective val]

namespace ExtrDisc

@[ext]
structure Hom (X Y : ExtrDisc) where mk ::
  val : X.val ⟶ Y.val

def of (X : Profinite) [Projective X] : ExtrDisc :=
  ⟨X⟩

@[simp]
theorem of_val (X : Profinite) [Projective X] : (of X).val = X :=
  rfl

@[simps]
instance : Category ExtrDisc where
  hom := Hom
  id X := ⟨𝟙 _⟩
  comp X Y Z f g := ⟨f.val ≫ g.val⟩

@[simps]
-- Porting note: `_root_` as in Lean 3 (mathport dropped it)
def _root_.extrDiscToProfinite : ExtrDisc ⥤ Profinite
    where
  obj := val
  map X Y f := f.val

instance : Full extrDiscToProfinite where preimage X Y f := ⟨f⟩

instance : Faithful extrDiscToProfinite where

instance : ConcreteCategory ExtrDisc.{u}
    where
  forget := extrDiscToProfinite ⋙ forget _
  forget_faithful := ⟨⟩

instance : CoeSort ExtrDisc (Type _) :=
  ConcreteCategory.hasCoeToSort _

instance {X Y : ExtrDisc} : CoeFun (X ⟶ Y) fun f => X → Y :=
  ⟨fun f => f.val⟩

@[simp]
theorem coe_fun_eq {X Y : ExtrDisc} (f : X ⟶ Y) (x : X) : f x = f.val x :=
  rfl

instance (X : ExtrDisc) : Projective X.val :=
  X.cond

example (X : ExtrDisc) : Projective (extrDiscToProfinite.obj X) := by dsimp; infer_instance

def lift {X Y : Profinite} {P : ExtrDisc} (f : X ⟶ Y) (hf : Function.Surjective f) (e : P.val ⟶ Y) :
    P.val ⟶ X := by
  haveI : epi f := by rwa [Profinite.epi_iff_surjective f]
  choose g h using Projective.factors e f
  exact g

@[reassoc (attr := simp)]
theorem lift_lifts {X Y : Profinite} {P : ExtrDisc} (f : X ⟶ Y) (hf : Function.Surjective f)
    (e : P.val ⟶ Y) : lift f hf e ≫ f = e :=
  by
  haveI : epi f := by rwa [Profinite.epi_iff_surjective f]
  apply (Projective.factors e f).choose_spec

instance (X : ExtrDisc) : TopologicalSpace X :=
  show TopologicalSpace X.val by infer_instance

instance (X : ExtrDisc) : CompactSpace X :=
  show CompactSpace X.val by infer_instance

instance (X : ExtrDisc) : T2Space X :=
  show T2Space X.val by infer_instance

instance (X : ExtrDisc) : TotallyDisconnectedSpace X :=
  show TotallyDisconnectedSpace X.val by infer_instance

-- move this
-- @[simps]
def Profinite.sumIsoCoprod (X Y : Profinite.{u}) : Profinite.sum X Y ≅ X ⨿ Y
    where
  hom := Profinite.sum.desc _ _ Limits.coprod.inl Limits.coprod.inr
  inv := Limits.coprod.desc (Profinite.sum.inl _ _) (Profinite.sum.inr _ _)
  hom_inv_id := by
    apply Profinite.sum.hom_ext <;>
      simp only [← Category.assoc, Category.comp_id, Profinite.sum.inl_desc, Limits.coprod.inl_desc,
        Profinite.sum.inr_desc, Limits.coprod.inr_desc]
  inv_hom_id := by
    apply Limits.coprod.hom_ext <;>
      simp only [← Category.assoc, Category.comp_id, Profinite.sum.inl_desc, Limits.coprod.inl_desc,
        Profinite.sum.inr_desc, Limits.coprod.inr_desc]

@[simps]
def sum (X Y : ExtrDisc.{u}) : ExtrDisc.{u}
    where
  val := Profinite.sum X.val Y.val
  cond := by
    let Z := Profinite.sum X.val Y.val
    apply Projective.of_iso (Profinite.sumIsoCoprod X.val Y.val).symm
    infer_instance

@[simps]
def sum.inl (X Y : ExtrDisc) : X ⟶ sum X Y :=
  ⟨Profinite.sum.inl _ _⟩

@[simps]
def sum.inr (X Y : ExtrDisc) : Y ⟶ sum X Y :=
  ⟨Profinite.sum.inr _ _⟩

@[simps]
def sum.desc {X Y Z : ExtrDisc} (f : X ⟶ Z) (g : Y ⟶ Z) : sum X Y ⟶ Z :=
  ⟨Profinite.sum.desc _ _ f.val g.val⟩

@[simp]
theorem sum.inl_desc {X Y Z : ExtrDisc} (f : X ⟶ Z) (g : Y ⟶ Z) : sum.inl X Y ≫ sum.desc f g = f :=
  by ext1; dsimp; simp

@[simp]
theorem sum.inr_desc {X Y Z : ExtrDisc} (f : X ⟶ Z) (g : Y ⟶ Z) : sum.inr X Y ≫ sum.desc f g = g :=
  by ext1; dsimp; simp

@[ext]
theorem sum.hom_ext {X Y Z : ExtrDisc} (f g : sum X Y ⟶ Z) (hl : sum.inl X Y ≫ f = sum.inl X Y ≫ g)
    (hr : sum.inr X Y ≫ f = sum.inr X Y ≫ g) : f = g :=
  by
  ext1
  apply Profinite.sum.hom_ext
  · apply_fun fun e => e.val at hl ; exact hl
  · apply_fun fun e => e.val at hr ; exact hr

-- move this
def Profinite.emptyIsInitial : Limits.IsInitial Profinite.empty.{u} :=
  @Limits.IsInitial.ofUnique.{u} _ _ _ fun Y =>
    ⟨⟨Profinite.empty.elim _⟩, fun f => by ext x; cases x⟩

@[simps]
def empty : ExtrDisc where
  val := Profinite.empty
  cond :=
    by
    let e : Profinite.empty ≅ ⊥_ _ :=
      Profinite.empty_is_initial.uniqueUpToIso Limits.initialIsInitial
    apply Projective.of_iso e.symm
    -- apply_instance, <-- missing instance : projective (⊥_ _)
    constructor
    intro A B f g _
    refine' ⟨Limits.initial.to A, by simp⟩

@[simps]
def empty.elim (X : ExtrDisc) : empty ⟶ X :=
  ⟨Profinite.empty.elim _⟩

@[ext]
theorem empty.hom_ext {X : ExtrDisc} (f g : empty ⟶ X) : f = g := by ext x; cases x

def sigma {ι : Type u} [Fintype ι] (X : ι → ExtrDisc) : ExtrDisc
    where
  val := Profinite.sigma fun i => (X i).val
  cond :=
    by
    let e : (Profinite.sigma fun i => (X i).val) ≅ ∐ fun i => (X i).val :=
      (Profinite.sigmaCofanIsColimit _).coconePointUniqueUpToIso (Limits.colimit.isColimit _)
    apply Projective.of_iso e.symm
    infer_instance

def sigma.ι {ι : Type u} [Fintype ι] (X : ι → ExtrDisc) (i) : X i ⟶ sigma X :=
  ⟨Profinite.sigma.ι _ i⟩

def sigma.desc {ι : Type u} {Y : ExtrDisc} [Fintype ι] (X : ι → ExtrDisc) (f : ∀ i, X i ⟶ Y) :
    sigma X ⟶ Y :=
  ⟨Profinite.sigma.desc _ fun i => (f i).val⟩

theorem sigma.ι_desc {ι : Type u} {Y : ExtrDisc} [Fintype ι] (X : ι → ExtrDisc) (f : ∀ i, X i ⟶ Y)
    (i) : sigma.ι X i ≫ sigma.desc X f = f i :=
  by
  ext1
  apply Profinite.sigma.ι_desc

theorem sigma.hom_ext {ι : Type u} {Y : ExtrDisc} [Fintype ι] (X : ι → ExtrDisc) (a b : sigma X ⟶ Y)
    (w : ∀ i, sigma.ι X i ≫ a = sigma.ι X i ≫ b) : a = b :=
  by
  ext1
  apply Profinite.sigma.hom_ext
  intro i
  specialize w i
  apply_fun fun e => e.val at w 
  exact w

theorem sigma.ι_jointly_surjective {ι : Type u} [Fintype ι] (X : ι → ExtrDisc) (x : sigma X) :
    ∃ (i : _) (t : X i), sigma.ι X i t = x :=
  Profinite.sigma.ι_jointly_surjective _ _

open Opposite

variable {C : Type v} [Category.{w} C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C)

def TerminalCondition [Limits.HasTerminal C] : Prop :=
  IsIso (Limits.terminal.from (F.obj (op empty)))

def BinaryProductCondition [Limits.HasBinaryProducts C] : Prop :=
  ∀ X Y : ExtrDisc.{u}, IsIso (Limits.prod.lift (F.map (sum.inl X Y).op) (F.map (sum.inr X Y).op))

def FiniteProductCondition [Limits.HasFiniteProducts C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (X : ι → ExtrDisc),
    by
    -- Lean is being annoying here...
    skip
    let t : ∀ i, F.obj (op (Sigma X)) ⟶ F.obj (op (X i)) := fun i => F.map (sigma.ι X i).op
    exact is_iso (Limits.Pi.lift t)

def FiniteProductConditionForTypes (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (X : ι → ExtrDisc),
    by
    skip
    dsimp_result =>
      let t : ∀ i, F.obj (op (Sigma X)) → F.obj (op (X i)) := fun i => F.map (sigma.ι X i).op
      let tt : F.obj (op (Sigma X)) → ∀ i, F.obj (op (X i)) := fun x i => t i x
      exact Function.Bijective tt

def EqualizerCondition [Limits.HasEqualizers C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) : Prop :=
  ∀ {R X B : ExtrDisc} (f : X ⟶ B) (hf : Function.Surjective f)
    (g : R.val ⟶ Profinite.pullback f.val f.val) (hg : Function.Surjective g),
    let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩
    let e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩
    let w : e₁ ≫ f = e₂ ≫ f := by ext1; dsimp [e₁, e₂]; simp [Profinite.pullback.condition]
    let h : F.map f.op ≫ F.map e₁.op = F.map f.op ≫ F.map e₂.op := by
      simp only [← F.map_comp, ← op_comp, w]
    IsIso (Limits.equalizer.lift _ h)

def EqualizerConditionForTypes (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) : Prop :=
  ∀ {R X B : ExtrDisc} (f : X ⟶ B) (hf : Function.Surjective f)
    (g : R.val ⟶ Profinite.pullback f.val f.val) (hg : Function.Surjective g), by
    dsimp_result =>
      exact
        let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩
        let e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩
        let w : e₁ ≫ f = e₂ ≫ f := by ext1; dsimp [e₁, e₂]; simp [Profinite.pullback.condition]
        let h : F.map f.op ≫ F.map e₁.op = F.map f.op ≫ F.map e₂.op := by
          simp only [← F.map_comp, ← op_comp, w]
        let E := { x : F.obj (op X) // F.map e₁.op x = F.map e₂.op x }
        let t : F.obj (op B) → E := fun x =>
          ⟨F.map f.op x,
            by
            change (F.map f.op ≫ F.map e₁.op) x = (F.map f.op ≫ F.map e₂.op) x
            rw [h]⟩
        Function.Bijective t

theorem equalizerCondition_holds [Limits.HasEqualizers C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
    EqualizerCondition F := by
  intro R X B f hf g hg
  dsimp
  let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩
  let e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩
  let σ : B ⟶ X := ⟨ExtrDisc.lift _ hf (𝟙 _)⟩
  let t : X ⟶ R := ⟨ExtrDisc.lift _ hg _⟩
  swap
  · refine' Profinite.pullback.lift _ _ (𝟙 _) (f.val ≫ σ.val) _
    dsimp; simp
  have h₁ : t ≫ e₁ = 𝟙 _ := by ext1; dsimp; simp
  have h₂ : t ≫ e₂ = f ≫ σ := by ext1; dsimp; simp
  have hh : σ ≫ f = 𝟙 _ := by ext1; dsimp; simp
  use Limits.equalizer.ι _ _ ≫ F.map σ.op
  constructor
  · simp only [Limits.equalizer.lift_ι_assoc]
    simp only [← F.map_comp, ← op_comp, hh]
    simp
  · ext
    simp only [Limits.equalizer.lift_ι, Category.id_comp, Category.assoc]
    simp only [← F.map_comp, ← op_comp]
    erw [← h₂, op_comp, F.map_comp]
    dsimp [e₂]
    erw [← Limits.equalizer.condition_assoc]
    change _ ≫ F.map e₁.op ≫ F.map t.op = _
    rw [← F.map_comp, ← op_comp, h₁]
    simp

theorem equalizerConditionForTypes_holds (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) :
    EqualizerConditionForTypes F :=
  by
  -- Should be fairly easy, just mimic the proof in the general case above.
  intro R X B f hf g hg
  let e₁ : R ⟶ X := ⟨g ≫ Profinite.pullback.fst _ _⟩
  let e₂ : R ⟶ X := ⟨g ≫ Profinite.pullback.snd _ _⟩
  have w : e₁ ≫ f = e₂ ≫ f := by
    dsimp [e₁, e₂]
    apply ExtrDisc.Hom.ext
    simp [Category.assoc, Profinite.pullback.condition]
  have h : F.map f.op ≫ F.map e₁.op = F.map f.op ≫ F.map e₂.op := by
    simp only [← F.map_comp, ← op_comp, w]
  let E := { x : F.obj (op X) // F.map e₁.op x = F.map e₂.op x }
  let t : F.obj (op B) → E := fun x =>
    ⟨F.map f.op x,
      by
      change (F.map f.op ≫ F.map e₁.op) x = (F.map f.op ≫ F.map e₂.op) x
      rw [h]⟩
  change Function.Bijective t
  let ee := Limits.Concrete.equalizerEquiv (F.map e₁.op) (F.map e₂.op)
  suffices Function.Bijective (ee.symm ∘ t) by
    exact (Equiv.comp_bijective t (Equiv.symm ee)).mp this
  have : ee.symm ∘ t = Limits.equalizer.lift _ h :=
    by
    suffices t = ee ∘ Limits.equalizer.lift _ h by rw [this]; ext; simp
    ext
    apply Subtype.ext
    change _ = (Limits.equalizer.lift _ h ≫ Limits.equalizer.ι _ _) _
    rw [Limits.equalizer.lift_ι]
    rfl
  rw [this]
  rw [← CategoryTheory.isIso_iff_bijective]
  apply ExtrDisc.equalizerCondition_holds
  assumption'

end ExtrDisc

namespace Profinite

theorem exists_projective_presentation (B : Profinite.{u}) :
    ∃ (X : ExtrDisc) (π : X.val ⟶ B), Function.Surjective π :=
  by
  obtain ⟨⟨X, h, π, hπ⟩⟩ := EnoughProjectives.presentation B
  skip
  use⟨X⟩, π
  rwa [← epi_iff_surjective]

def pres (B : Profinite.{u}) : ExtrDisc :=
  B.exists_projective_presentation.some

def presπ (B : Profinite.{u}) : B.pres.val ⟶ B :=
  B.exists_projective_presentation.choose_spec.some

theorem presπ_surjective (B : Profinite.{u}) : Function.Surjective B.presπ :=
  B.exists_projective_presentation.choose_spec.choose_spec

end Profinite

open Opposite

variable {C : Type v} [Category.{w} C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C)

def IsExtrSheafOfTypes (P : ExtrDisc.{u}ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (B : ExtrDisc.{u}) (ι : Type u) [Fintype ι] (α : ι → ExtrDisc.{u}) (f : ∀ i, α i ⟶ B)
    (hf : ∀ b : B, ∃ (i : _) (x : α i), f i x = b) (x : ∀ i, P.obj (op (α i)))
    (hx :
      ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
        g₁ ≫ f _ = g₂ ≫ f _ → P.map g₁.op (x _) = P.map g₂.op (x _)),
    ∃! t : P.obj (op B), ∀ i, P.map (f i).op t = x _

-- We encode the general condition essentially using Yoneda.
def IsExtrSheaf (P : ExtrDisc.{u}ᵒᵖ ⥤ C) : Prop :=
  ∀ (B : ExtrDisc.{u}) (ι : Type u) [Fintype ι] (α : ι → ExtrDisc.{u}) (f : ∀ i, α i ⟶ B)
    (hf : ∀ b : B, ∃ (i : _) (x : α i), f i x = b) (T : C) (x : ∀ i, T ⟶ P.obj (op (α i)))
    (hx :
      ∀ (i j : ι) (Z : ExtrDisc) (g₁ : Z ⟶ α i) (g₂ : Z ⟶ α j),
        g₁ ≫ f _ = g₂ ≫ f _ → x _ ≫ P.map g₁.op = x _ ≫ P.map g₂.op),
    ∃! t : T ⟶ P.obj (op B), ∀ i, t ≫ P.map (f i).op = x _

theorem subsingleton_of_empty_of_isExtrSheafOfTypes (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w)
    (hF : IsExtrSheafOfTypes F) (Z : ExtrDisc) [hZ : IsEmpty Z] : Subsingleton (F.obj (op Z)) :=
  by
  constructor
  intro a b
  specialize hF Z PEmpty PEmpty.elim (fun a => a.elim) hZ.elim (fun a => a.elim) fun a => a.elim
  obtain ⟨t, h1, h2⟩ := hF
  have : a = t := by apply h2; intro i; exact i.elim
  have : b = t := by apply h2; intro i; exact i.elim
  cc

theorem finiteProductConditionForTypes_of_isExtrSheafOfTypes (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w)
    (hF : IsExtrSheafOfTypes F) : ExtrDisc.FiniteProductConditionForTypes F :=
  by
  intro ι _ X
  have hF' := hF
  specialize hF (ExtrDisc.sigma X) ι X (ExtrDisc.sigma.ι _) (ExtrDisc.sigma.ι_jointly_surjective _)
  constructor
  · intro x y hh
    dsimp at hh 
    have hx := hF (fun i => F.map (ExtrDisc.sigma.ι X i).op x) _
    swap
    · intro i j Z g₁ g₂ hh
      dsimp
      change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _
      simp only [← F.map_comp, ← op_comp]
      rw [hh]
    have hy := hF (fun i => F.map (ExtrDisc.sigma.ι X i).op y) _
    swap
    · intro i j Z g₁ g₂ hh
      dsimp
      change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _
      simp only [← F.map_comp, ← op_comp]
      rw [hh]
    obtain ⟨tx, htx1, htx2⟩ := hx
    obtain ⟨ty, hty1, hty2⟩ := hy
    have : x = tx := by
      apply htx2
      intro i
      rfl
    rw [this]
    symm
    apply htx2
    intro i
    apply_fun fun e => e i at hh 
    exact hh.symm
  · intro x
    have hx := hF x _
    swap
    · intro i j Z g₁ g₂ hh
      by_cases hZ : Nonempty Z
      · obtain ⟨z⟩ := hZ
        have : i = j := by apply_fun fun e => (e z).1 at hh ; exact hh
        subst this
        have : g₁ = g₂ := by
          ext t : 2
          apply_fun ExtrDisc.sigma.ι X i
          swap
          · apply Profinite.sigma.ι_injective
          apply_fun fun e => e t at hh 
          exact hh
        rw [this]
      · simp at hZ ; skip
        haveI := subsingleton_of_empty_of_isExtrSheafOfTypes F hF' Z
        apply Subsingleton.elim
    obtain ⟨t, ht, _⟩ := hx
    use t
    ext1
    apply ht

namespace ProductConditionSetup

section

parameter {P : ExtrDisc.{u}ᵒᵖ ⥤ Type w} (hP : ExtrDisc.FiniteProductConditionForTypes P)

parameter {B : ExtrDisc.{u}} {ι : Type u} [Fintype ι] (X : ι → ExtrDisc.{u}) (f : ∀ i, X i ⟶ B)

def g : ι × ι → ExtrDisc := fun ii => (Profinite.pullback (f ii.1).val (f ii.2).val).pres

def gfst : ∀ ii : ι × ι, G ii ⟶ X ii.1 := fun ii => ⟨Profinite.presπ _ ≫ Profinite.pullback.fst _ _⟩

def gsnd : ∀ ii : ι × ι, G ii ⟶ X ii.2 := fun ii => ⟨Profinite.presπ _ ≫ Profinite.pullback.snd _ _⟩

theorem hX :
    Function.Bijective fun (x : P.obj (op (ExtrDisc.sigma X))) (i : ι) =>
      P.map (ExtrDisc.sigma.ι X i).op x :=
  hP ι X

theorem hG :
    Function.Bijective fun (x : P.obj (op (ExtrDisc.sigma G))) (i : ι × ι) =>
      P.map (ExtrDisc.sigma.ι G i).op x :=
  hP (ι × ι) G

def π : ExtrDisc.sigma X ⟶ B :=
  ExtrDisc.sigma.desc X f

theorem hπ (surj : ∀ b : B, ∃ (i : _) (x : X i), f i x = b) : Function.Surjective π :=
  by
  intro b
  have := surj
  obtain ⟨i, x, hx⟩ := surj b
  use ExtrDisc.sigma.ι X i x
  exact hx

def r : (ExtrDisc.sigma G).val ⟶ Profinite.pullback π.val π.val :=
  by
  refine' Profinite.pullback.lift _ _ _ _ _
  · refine' Profinite.sigma.desc _ _
    intro ii
    refine' _ ≫ Profinite.sigma.ι _ ii.1
    refine' (gfst _ _ _).val
  · refine' Profinite.sigma.desc _ _
    intro ii
    refine' _ ≫ Profinite.sigma.ι _ ii.2
    dsimp
    refine' (gsnd _ _ _).val
  · apply Profinite.sigma.hom_ext
    rintro ⟨i, j⟩
    dsimp [π, ExtrDisc.sigma.desc, gfst, gsnd]
    simp [Profinite.pullback.condition]

theorem hr : Function.Surjective r :=
  by
  rintro ⟨⟨⟨i, a⟩, ⟨j, b⟩⟩, h⟩
  dsimp [π, ExtrDisc.sigma.desc, Profinite.sigma.desc] at a b h 
  let ab : Profinite.pullback (f i).val (f j).val := ⟨⟨a, b⟩, h⟩
  obtain ⟨c, hc⟩ := Profinite.presπ_surjective _ ab
  use ExtrDisc.sigma.ι (G X f) (i, j) c
  apply Subtype.ext
  apply Prod.ext
  · apply Sigma.ext; · rfl
    apply hEq_of_eq
    change ((Profinite.pullback (f i).val (f j).val).presπ c).val.fst = _
    rw [hc]; rfl
  · apply Sigma.ext; · rfl
    apply hEq_of_eq
    change ((Profinite.pullback (f i).val (f j).val).presπ c).val.snd = _
    rw [hc]; rfl

-- this lemma has an extremely annoying type to write down
@[nolint def_lemma]
def hE (surj : ∀ b : B, ∃ (i : _) (x : X i), f i x = b) :=
  ExtrDisc.equalizerConditionForTypes_holds P π (hπ surj) r hr

def qX : P.obj (op (ExtrDisc.sigma X)) ≃ ∀ i, P.obj (op (X i)) :=
  Equiv.ofBijective _ hX

def qG : P.obj (op (ExtrDisc.sigma G)) ≃ ∀ ii, P.obj (op (G ii)) :=
  Equiv.ofBijective _ hG

def rfst : ExtrDisc.sigma G ⟶ ExtrDisc.sigma X :=
  ⟨r ≫ Profinite.pullback.fst _ _⟩

def rsnd : ExtrDisc.sigma G ⟶ ExtrDisc.sigma X :=
  ⟨r ≫ Profinite.pullback.snd _ _⟩

theorem ι_rfst (ii : ι × ι) : ExtrDisc.sigma.ι G ii ≫ rfst = gfst ii ≫ ExtrDisc.sigma.ι _ _ :=
  by
  ext1
  dsimp [rfst, gfst, ExtrDisc.sigma.ι, ExtrDisc.sigma.desc, r]
  simp [Profinite.pullback.condition, Profinite.pullback.condition_assoc]

theorem ι_rsnd (ii : ι × ι) : ExtrDisc.sigma.ι G ii ≫ rsnd = gsnd ii ≫ ExtrDisc.sigma.ι _ _ :=
  by
  ext1
  dsimp [rsnd, gsnd, ExtrDisc.sigma.ι, ExtrDisc.sigma.desc, r]
  simp [Profinite.pullback.condition, Profinite.pullback.condition_assoc]

theorem qX_symm_ι_aux (q : ∀ i, P.obj (op (X i))) :
    q = fun i => P.map (ExtrDisc.sigma.ι X i).op (QX.symm q) :=
  by
  apply_fun (QX hP X).symm
  change _ = (QX hP X).symm ((QX hP X) _)
  rw [Equiv.symm_apply_apply]

theorem qX_symm_ι (q : ∀ i, P.obj (op (X i))) (i : ι) :
    P.map (ExtrDisc.sigma.ι X i).op (QX.symm q) = q i :=
  by
  revert i
  rw [← Function.funext_iff]
  change _ = q
  symm
  apply QX_symm_ι_aux hP X q

theorem qX_qG_compat_fst (q : ∀ i, P.obj (op (X i))) (i : ι × ι) :
    QG (P.map rfst.op (QX.symm q)) i = P.map (gfst i).op (q i.fst) :=
  by
  dsimp [QG]
  change (P.map _ ≫ P.map _) _ = _
  simp only [← P.map_comp, ← op_comp, ι_rfst]
  simp only [P.map_comp, op_comp]
  dsimp
  rw [QX_symm_ι]

theorem qX_qG_compat_snd (q : ∀ i, P.obj (op (X i))) (i : ι × ι) :
    QG (P.map rsnd.op (QX.symm q)) i = P.map (gsnd i).op (q i.snd) :=
  by
  dsimp [QG]
  change (P.map _ ≫ P.map _) _ = _
  simp only [← P.map_comp, ← op_comp, ι_rsnd]
  simp only [P.map_comp, op_comp]
  dsimp
  rw [QX_symm_ι]

end

end ProductConditionSetup

open ProductConditionSetup

theorem isExtrSheafOfTypes_of_finiteProductConditionForTypes (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w)
    (hF : ExtrDisc.FiniteProductConditionForTypes F) : IsExtrSheafOfTypes F :=
  by
  intro B ι _ X f surj x hx
  have hrfst :
    ∀ q : ∀ i, F.obj (op (X i)),
      (QG hF X f) (F.map (rfst X f).op ((QX hF X).symm q)) = fun ii =>
        F.map (gfst X f ii).op (q ii.1) :=
    by
    intro q; funext ii
    change (F.map _ ≫ F.map _) _ = _
    simp only [← F.map_comp, ← op_comp, ι_rfst]
    simp only [F.map_comp, op_comp]
    dsimp
    rw [QX_symm_ι hF X q]
  have hrgsnd :
    ∀ q : ∀ i, F.obj (op (X i)),
      (QG hF X f) (F.map (rsnd X f).op ((QX hF X).symm q)) = fun ii =>
        F.map (gsnd X f ii).op (q ii.2) :=
    by
    intro q; funext ii
    change (F.map _ ≫ F.map _) _ = _
    simp only [← F.map_comp, ← op_comp, ι_rsnd]
    simp only [F.map_comp, op_comp]
    dsimp
    rw [QX_symm_ι hF X q]
  let EE :
    F.obj (op B) ≃
      { t : F.obj (op (ExtrDisc.sigma X)) // F.map (rfst X f).op t = F.map (rsnd X f).op t } :=
    Equiv.ofBijective _ (hE X f surj)
  let x' : F.obj (op (ExtrDisc.sigma X)) := (QX hF X).symm x
  -- Should follow from hx,
  have hx' : F.map (rfst X f).op x' = F.map (rsnd X f).op x' :=
    by
    apply_fun QG hF X f
    funext ii
    rw [QX_QG_compat_fst]
    rw [QX_QG_compat_snd]
    apply hx
    ext1
    dsimp [gfst, gsnd]
    simp [Profinite.pullback.condition]
  let b : F.obj (op B) := EE.symm ⟨x', hx'⟩
  use b
  have hb : ∀ i, F.map (f i).op b = x i := by
    intro i
    have : f i = ExtrDisc.sigma.ι X i ≫ π X f := by dsimp [π]; rw [ExtrDisc.sigma.ι_desc]
    rw [this, op_comp, F.map_comp]
    dsimp
    have : F.map (π X f).op b = x' := by
      change ↑(EE b) = x'
      dsimp only [b]
      rw [Equiv.apply_symm_apply]
      rfl
    rw [this]
    dsimp [x']
    change ((QX hF X) ((QX hF X).symm x)) _ = _
    rw [Equiv.apply_symm_apply]
  refine' ⟨hb, _⟩
  · intro b' hb'
    apply_fun EE
    ext1
    apply_fun QX hF X
    dsimp [EE, QX, π]
    funext i
    change (F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _) _
    simp only [← F.map_comp, ← op_comp, ExtrDisc.sigma.ι_desc, hb, hb']

theorem isExtrSheafOfTypes_iff_product_condition_for_types (F : ExtrDisc.{u}ᵒᵖ ⥤ Type w) :
    IsExtrSheafOfTypes F ↔ ExtrDisc.FiniteProductConditionForTypes F :=
  by
  constructor
  · intro h; exact finiteProductConditionForTypes_of_isExtrSheafOfTypes _ h
  · intro h; exact isExtrSheafOfTypes_of_finiteProductConditionForTypes _ h

theorem isExtrSheaf_iff_forall_yoneda (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
    IsExtrSheaf F ↔ ∀ T : C, IsExtrSheafOfTypes (F ⋙ coyoneda.obj (op T)) :=
  by
  constructor
  · intro h T B ι _ X f surj x hx
    exact h B ι X f surj T x hx
  · intro h B ι _ X f surj T x hx
    exact h T B ι X f surj x hx

theorem finiteProductCondition_iff_forall_yoneda [Limits.HasFiniteProducts C]
    (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
    ExtrDisc.FiniteProductCondition F ↔
      ∀ T : C, ExtrDisc.FiniteProductConditionForTypes (F ⋙ coyoneda.obj (op T)) :=
  by
  constructor
  · intro h T ι _ X
    let t : F.obj (op (ExtrDisc.sigma X)) ⟶ ∏ fun i : ι => F.obj (op (X i)) :=
      Limits.Pi.lift fun i : ι => F.map (ExtrDisc.sigma.ι X i).op
    specialize h ι X
    dsimp at h ⊢
    change is_iso t at h 
    skip
    constructor
    · intro a b hab
      dsimp at hab 
      suffices a ≫ t = b ≫ t by apply_fun fun e => e ≫ inv t at this ; simpa using this
      ext1
      rw [Function.funext_iff] at hab 
      simp [hab]
    · intro a
      use Limits.Pi.lift a ≫ inv t
      dsimp
      funext i
      have : inv t ≫ F.map (ExtrDisc.sigma.ι X i).op = limits.pi.π _ i := by
        simp [IsIso.inv_comp_eq]
      simp [this]
  · intro h ι _ X
    dsimp
    let h₁ := h (∏ fun i : ι => F.obj (op (X i))) ι X
    let h₂ := h (F.obj (op (ExtrDisc.sigma X))) ι X
    dsimp at h₁ h₂ 
    replace h₁ := h₁.2
    replace h₂ := h₂.1
    obtain ⟨s, hs⟩ := h₁ fun i => limits.pi.π _ i
    use s
    rw [Function.funext_iff] at hs 
    dsimp at *
    constructor
    · apply h₂
      ext1 i
      dsimp
      simp [hs i]
    · ext1 i
      cases i
      simp [hs i]

theorem isExtrSheaf_iff_product_condition [Limits.HasFiniteProducts C] (F : ExtrDisc.{u}ᵒᵖ ⥤ C) :
    IsExtrSheaf F ↔ ExtrDisc.FiniteProductCondition F :=
  by
  rw [isExtrSheaf_iff_forall_yoneda]
  rw [finiteProductCondition_iff_forall_yoneda]
  apply forall_congr' fun T => _
  apply isExtrSheafOfTypes_iff_product_condition_for_types

