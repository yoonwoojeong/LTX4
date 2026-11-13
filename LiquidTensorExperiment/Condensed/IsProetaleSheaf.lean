import LiquidTensorExperiment.Condensed.ProetaleSite
import LiquidTensorExperiment.ForMathlib.Presieve
import Mathlib.Topology.Category.Profinite.Projective
import LiquidTensorExperiment.ForMathlib.Profinite.DisjointUnion
import LiquidTensorExperiment.ForMathlib.FintypeInduction
import Mathlib.Tactic.DeriveFintype

#align_import condensed.is_proetale_sheaf

-- for pbool
-- for pbool
universe w v u

namespace CategoryTheory.Functor

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] (Q : Profinite.{w}ᵒᵖ ⥤ C)

variable (P : Profinite.{w}ᵒᵖ ⥤ Type u)

/-- A presheaf of types `P` on `Profinite` satisfies the finite product
condition if given any finite collection of topological spaces `X i`
indexed by `i` in `(α : Fintype)`, the map from `P (∑ i, X i)`
to `Π (a : α), P (X a)` sending `x` to the dependent function sending
`a : α` to  `P (the inclusion X a → Σ i, X i), evaluated at x`,
is a bijection. -/
def FiniteProductCondition : Prop :=
  ∀ (α : FintypeCat.{w}) (X : α → Profinite.{w}),
    Function.Bijective fun (x : P.obj (op (Profinite.sigma X))) (a : α) =>
      P.map (Profinite.sigma.ι X a).op x

def FiniteProductConditionOf (α : FintypeCat.{w}) : Prop :=
  ∀ X : α → Profinite.{w},
    Function.Bijective fun (x : P.obj (op (Profinite.sigma X))) (a : α) =>
      P.map (Profinite.sigma.ι X a).op x

def FiniteProductCondition' : Prop :=
  ∀ (n : ℕ) (X : ULift.{w} (Fin n) → Profinite.{w}),
    Function.Bijective fun (x : P.obj (op (Profinite.sigma X))) (a : ULift (Fin n)) =>
      P.map (Profinite.sigma.ι X a).op x

namespace FiniteProductAux

def objEquiv {α β : Type _} (e : α ≃ β) (X : β → Profinite.{w}) (b : β) : X b ≅ X (e (e.symm b)) :=
  eqToIso (congr_arg X (e.apply_symm_apply _).symm)

def productEquiv {α β : Type _} (e : α ≃ β) (X : β → Profinite.{w}) :
    (∀ a : α, P.obj (Opposite.op (X (e a)))) ≃ ∀ b, P.obj (Opposite.op (X b)) :=
  e.piCongr fun b => Equiv.refl _

def sigmaEquiv {α β : Type w} [Fintype α] [Fintype β] (e : α ≃ β) (X : β → Profinite.{w}) :
    P.obj (Opposite.op (Profinite.sigma (X ∘ e))) ≃ P.obj (Opposite.op (Profinite.sigma X)) :=
  (P.mapIso (Profinite.sigmaIsoOfEquiv _ _).op).symm.toEquiv

theorem productEquiv_compatible {α β : Type w} [Fintype α] [Fintype β] (e : α ≃ β)
    (X : β → Profinite.{w}) (a) (b) :
    P.map (Profinite.sigma.ι _ b).op ((sigmaEquiv P e X).symm a) =
      (productEquiv P e X).symm (fun b => P.map (Profinite.sigma.ι _ _).op a) b :=
  by
  dsimp [product_equiv, sigma_equiv]
  simp only [← functor_to_types.map_comp_apply]
  rfl

end FiniteProductAux

open FiniteProductAux

theorem finiteProductConditionOf_equiv (α β : FintypeCat.{w}) (e : α ≃ β)
    (h : P.FiniteProductConditionOf α) : P.FiniteProductConditionOf β :=
  by
  intro X
  specialize h (X ∘ e)
  let f := _; show Function.Bijective f
  let g := _; change Function.Bijective g at h 
  have : f = product_equiv _ _ _ ∘ g ∘ (sigma_equiv P e X).symm :=
    by
    suffices (product_equiv _ _ _).symm ∘ f = g ∘ (sigma_equiv P e X).symm by rw [← this]; ext; simp
    symm
    ext a
    apply product_equiv_compatible
  rw [this]
  apply Function.Bijective.comp (Equiv.bijective _) (h.comp (Equiv.bijective _))

theorem finiteProductCondition_iff_finiteProductCondition' :
    P.FiniteProductCondition ↔ P.FiniteProductCondition' :=
  by
  constructor
  · intro h n X
    apply h ⟨ULift (Fin n)⟩ X
  · intro h α X
    let n := Fintype.card α
    let e : ULift.{w} (Fin n) ≃ α := equiv.ulift.trans (Fintype.equivFin _).symm
    let f := _; show Function.Bijective f
    specialize h n (X ∘ e)
    let g := _; change Function.Bijective g at h 
    have : f = product_equiv _ _ _ ∘ g ∘ (sigma_equiv P e X).symm :=
      by
      suffices (product_equiv _ _ _).symm ∘ f = g ∘ (sigma_equiv P e X).symm by rw [← this]; ext;
        simp
      symm
      ext a
      apply product_equiv_compatible
    rw [this]
    apply Function.Bijective.comp (Equiv.bijective _) (h.comp (Equiv.bijective _))

def EmptyCondition : Prop :=
  Function.Bijective fun t : P.obj (op Profinite.empty) => PUnit.unit.{u}

def ProductCondition : Prop :=
  ∀ X Y : Profinite.{w},
    Function.Bijective fun t : P.obj (op <| Profinite.sum X Y) =>
      ((P.map (Profinite.sum.inl X Y).op t, P.map (Profinite.sum.inr X Y).op t) :
        P.obj (op X) × P.obj (op Y))

open Opposite

theorem finiteProductConditionOf_empty_iff_emptyCondition :
    P.FiniteProductConditionOf ⟨PEmpty⟩ ↔ P.EmptyCondition :=
  by
  constructor
  · intro h
    let f := _; show Function.Bijective f
    let X : (PEmpty : Type w) → Profinite.{w} := PEmpty.elim
    specialize h X
    let g := _; change Function.Bijective g at h 
    let e : P.obj (Opposite.op Profinite.empty) ≃ P.obj (op (Profinite.sigma X)) :=
      (P.map_iso (Profinite.sigmaIsoEmpty' X).op).toEquiv
    let q : (∀ a : PEmpty, P.obj (op (X a))) ≃ PUnit :=
      ⟨fun a => PUnit.unit, fun _ a => a.elim, by intro i; ext ⟨⟩, by rintro ⟨⟩; rfl⟩
    have : f = q ∘ g ∘ e := by ext
    rw [this]
    exact q.bijective.comp (h.comp e.bijective)
  · intro h X
    let f := _; show Function.Bijective f
    let g := _; change Function.Bijective g at h 
    let e : P.obj (op (Profinite.sigma X)) ≃ P.obj (op Profinite.empty) :=
      (P.map_iso (Profinite.sigmaIsoEmpty' X).op).symm.toEquiv
    let q : PUnit ≃ ∀ a : PEmpty, P.obj (op (X a)) :=
      ⟨fun _ a => a.elim, fun _ => PUnit.unit, by rintro ⟨⟩; rfl, by intro i; ext ⟨⟩⟩
    have : f = q ∘ g ∘ e := by ext _ ⟨⟩
    rw [this]
    exact q.bijective.comp (h.comp e.bijective)

theorem finiteProductConditionOf_pair_iff_productCondition :
    P.FiniteProductConditionOf ⟨ULift Limits.WalkingPair⟩ ↔ P.ProductCondition :=
  by
  constructor
  · intro h A B
    let f := _; show Function.Bijective f
    let X : limits.walking_pair → Profinite.{w} := fun i => limits.walking_pair.rec_on i A B
    specialize h (X ∘ ULift.down)
    let g := _; change Function.Bijective g at h 
    let e : P.obj (op (A.sum B)) ≃ P.obj (op (Profinite.sigma (X ∘ ULift.down))) :=
      (P.map_iso (Profinite.sigmaWalkingPairIso (X ∘ ULift.down)).op).toEquiv
    let q : (∀ a : limits.walking_pair, P.obj (op (X a))) ≃ P.obj (op A) × P.obj (op B) :=
      ⟨fun f => ⟨f limits.walking_pair.left, f limits.walking_pair.right⟩, fun x a =>
        limits.walking_pair.rec_on a x.1 x.2, _, _⟩
    rotate_left; · intro a; ext ⟨x | x⟩; rfl; rfl; · rintro ⟨a, b⟩; ext ⟨x | x⟩; rfl; rfl
    let g' :
      (∀ a : FintypeCat.of (ULift.{w} limits.walking_pair), P.obj (Opposite.op (X a.down))) ≃
        ∀ a : limits.walking_pair, P.obj (Opposite.op (X a)) :=
      ⟨fun f a => f ⟨a⟩, fun f a => f a.down, _, _⟩
    rotate_left
    · intro f; ext ⟨a⟩; rfl
    · intro f; ext a; rfl
    have : f = q ∘ g' ∘ g ∘ e := by
      ext a
      all_goals
        dsimp [f, q, g, e]
        simp_rw [← functor_to_types.map_comp_apply, ← op_comp]
        rfl
    rw [this]
    refine' q.bijective.comp _
    refine' g'.bijective.comp (h.comp e.bijective)
  · intro h X
    let f := _; show Function.Bijective f
    specialize h (X ⟨limits.walking_pair.left⟩) (X ⟨limits.walking_pair.right⟩)
    let g := _; change Function.Bijective g at h 
    let e : P.obj (op (Profinite.sigma X)) ≃ P.obj (op (Profinite.sum _ _)) :=
      (P.map_iso (Profinite.sigmaWalkingPairIso X).op).symm.toEquiv
    let q :
      P.obj (op (X ⟨limits.walking_pair.left⟩)) × P.obj (op (X ⟨limits.walking_pair.right⟩)) ≃
        ∀ a : ULift.{w} limits.walking_pair, P.obj (op (X a)) :=
      ⟨fun x ⟨a⟩ => limits.walking_pair.rec_on a x.1 x.2, fun f =>
        (f ⟨limits.walking_pair.left⟩, f ⟨limits.walking_pair.right⟩), _, _⟩
    rotate_left
    · rintro ⟨a, b⟩; ext ⟨x | x⟩; rfl; rfl
    · intro a; ext ⟨x | x⟩; rfl; rfl
    have : f = q ∘ g ∘ e := by
      ext a ⟨x | x⟩
      all_goals
        dsimp [f, q, g, e]
        simp_rw [← functor_to_types.map_comp_apply, ← op_comp]
        rfl
    rw [this]
    exact q.bijective.comp (h.comp e.bijective)

theorem finiteProductConditionOf_sum (α β : FintypeCat.{w}) (h1 : P.ProductCondition)
    (h2 : P.FiniteProductConditionOf α) :
    P.FiniteProductConditionOf (FintypeCat.of <| Sum α (PUnit : Type w)) :=
  by
  intro X
  let f := _; show Function.Bijective f
  let I : Profinite.sigma X ≅ _ := Profinite.sigmaSumIso' _
  let t : P.obj (Opposite.op (Profinite.sigma X)) ≃ _ := (P.map_iso I.symm.op).toEquiv
  specialize h1 (Profinite.sigma (X ∘ Sum.inl)) (Profinite.sigma (X ∘ Sum.inr))
  let g := _; change Function.Bijective g at h1 
  let e :
    (∀ a : ↥(FintypeCat.of (Sum (↥α) PUnit)), P.obj (Opposite.op (X a))) ≃
      (∀ a : α, P.obj (op (X (Sum.inl a)))) × P.obj (op (X (Sum.inr PUnit.unit))) :=
    ⟨fun f => ⟨fun a => f (Sum.inl a), f (Sum.inr _)⟩, fun f x =>
      Sum.recOn x (fun a => f.1 a) fun ⟨⟩ => f.2, _, _⟩
  rotate_left; · rintro x; ext (a | ⟨⟨⟩⟩); rfl; rfl; · rintro ⟨a, b⟩; ext ⟨a | ⟨⟨⟩⟩⟩; rfl; rfl
  let l : P.obj (op (X (Sum.inr PUnit.unit))) ≃ P.obj (op (Profinite.sigma (X ∘ Sum.inr))) :=
    (P.map_iso (Profinite.sigmaPunitIso (X ∘ Sum.inr)).op).symm.toEquiv
  specialize h2 (X ∘ Sum.inl)
  let p := _; change Function.Bijective p at h2 
  let q :
    P.obj (op (Profinite.sigma (X ∘ Sum.inl))) × P.obj (op (Profinite.sigma (X ∘ Sum.inr))) ≃
      (∀ a : α, P.obj (op (X (Sum.inl a)))) × P.obj (op (Profinite.sigma (X ∘ Sum.inr))) :=
    (Equiv.ofBijective p h2).prodCongr (Equiv.refl _)
  let r : (∀ a : α, P.obj (op (X (Sum.inl a)))) × _ ≃ _ × _ := (Equiv.refl _).prodCongr l.symm
  have : f = e.symm ∘ Prod.map id l.symm ∘ q ∘ g ∘ t :=
    by
    ext x ⟨a | ⟨⟨⟩⟩⟩
    ext i
    cases i
    · dsimp [f, e, q, g, t, p, I, Profinite.sigmaSumIso']
      simp_rw [← functor_to_types.map_comp_apply, ← op_comp]
      rfl
    · cases i
      dsimp [f, e, q, g, t, p, I, Profinite.sigmaSumIso']
      simp_rw [← functor_to_types.map_comp_apply, ← op_comp]
      rfl
  rw [this]
  exact e.symm.bijective.comp (r.bijective.comp (q.bijective.comp (h1.comp t.bijective)))

theorem finiteProductCondition_iff_empty_product :
    P.FiniteProductCondition ↔ P.EmptyCondition ∧ P.ProductCondition :=
  by
  constructor
  · intro h
    constructor
    rw [← finite_product_condition_of_empty_iff_empty_condition]
    apply h
    rw [← finite_product_condition_of_pair_iff_product_condition]
    apply h
  · rintro ⟨h1, h2⟩
    have :=
      @FintypeCat.induction_empty_sum fun α : FintypeCat.{w} => P.finite_product_condition_of α
    apply this
    · intro α β e h
      apply finite_product_condition_of_equiv _ _ _ e h
    · erw [finite_product_condition_of_empty_iff_empty_condition]
      assumption
    · intro α h
      apply finite_product_condition_of_sum P α (FintypeCat.of PUnit)
      assumption
      assumption

-- should this be in mathlib in some form?
section IsSingleton

-- is_singleton X is [nonempty X] [subsingleton X]
theorem is_singleton_iff_forall_bijective_to_pUnit (X : Sort _) :
    Nonempty X ∧ Subsingleton X ↔ ∀ f : X → PUnit, Function.Bijective f :=
  by
  constructor
  · rintro ⟨h1, h2⟩ f
    haveI := h2
    exact ⟨fun a b h => Subsingleton.elim _ _, fun s => ⟨h1.some, Subsingleton.elim _ _⟩⟩
  · intro h
    cases' h fun x => PUnit.unit with finj fsurj
    choose g hg using fsurj
    refine' ⟨⟨g PUnit.unit⟩, Subsingleton.intro fun a b => finj rfl⟩

theorem is_singleton_iff_forall_bijective_to_is_singleton (X : Sort _) :
    Nonempty X ∧ Subsingleton X ↔
      ∀ (Y : Sort _) [Nonempty Y] [Subsingleton Y] (f : X → Y), Function.Bijective f :=
  by
  constructor
  · rintro ⟨⟨x⟩, hx⟩ Y hY1 hY2 f
    haveI := hY2
    haveI := hx
    refine' ⟨fun a b h => Subsingleton.elim a b, fun s => ⟨x, Subsingleton.elim _ _⟩⟩
  · intro h
    cases' h PUnit fun x => PUnit.unit with finj fsurj
    choose g hg using fsurj
    refine' ⟨⟨g PUnit.unit⟩, Subsingleton.intro fun a b => finj rfl⟩

theorem is_singleton_iff_exists_bijective_to_pUnit (X : Sort _) :
    Nonempty X ∧ Subsingleton X ↔ ∃ f : X → PUnit, Function.Bijective f :=
  by
  constructor
  · rintro ⟨⟨x⟩, hx⟩
    haveI := hx
    use fun x => PUnit.unit
    refine' ⟨fun a b _ => Subsingleton.elim a b, fun a => ⟨x, Subsingleton.elim _ _⟩⟩
  · rintro ⟨f, finj, fsurj⟩
    choose g hg using fsurj
    refine' ⟨⟨g PUnit.unit⟩, Subsingleton.intro fun a b => finj <| Subsingleton.elim _ _⟩

theorem is_singleton_iff_exists_bijective_to_is_singleton (X : Sort _) :
    Nonempty X ∧ Subsingleton X ↔
      ∃ (Y : Sort _) (_ : Nonempty Y) (_ : Subsingleton Y) (f : X → Y), Function.Bijective f :=
  by
  constructor
  · rintro ⟨⟨x⟩, hx⟩
    haveI := hx
    use PUnit, inferInstance, inferInstance, fun x => PUnit.unit
    refine' ⟨fun a b _ => Subsingleton.elim a b, fun a => ⟨x, Subsingleton.elim _ _⟩⟩
  · rintro ⟨Y, hY1, hY2, f, finj, fsurj⟩
    choose g hg using fsurj
    haveI := hY2
    refine' ⟨⟨g hY1.some⟩, ⟨fun a b => finj <| Subsingleton.elim _ _⟩⟩

theorem Subsingleton.map_equiv {X Y : Type _} (e : X ≃ Y) : Subsingleton X → Subsingleton Y :=
  fun h => ⟨fun a b => e.symm.Injective <| @Subsingleton.elim _ h _ _⟩

end IsSingleton

section Pbool

-- The category theory library has a type called `walking_pair` which accomplishes the same thing.
-- It's used in the API for binary (co)products.
inductive Pbool : Type u
  | ff : pbool
  | tt : pbool
  deriving Fintype

end Pbool

/-
-- Kevin is working on this
--lemma finite_product_condition_iff_empty_condition_product_condition :
--  P.finite_product_condition ↔ P.empty_condition ∧ P.product_condition :=
--begin
  /-
  split,
  { intro h_prod,
    split,
    { specialize h_prod (Fintype.of pempty) (λ x, Profinite.empty),
      suffices hs : nonempty (P.obj (op Profinite.empty)) ∧ subsingleton (P.obj (op Profinite.empty)),
      { rw is_singleton_iff_forall_bijective_to_punit at hs,
        apply hs },
      let e : Profinite.sigma.{w} (λ (x : ↥(Fintype.of.{w} pempty)), Profinite.empty) ≅ Profinite.empty :=
      { hom := Profinite.sigma.desc _ (λ i, by cases i),
        inv := Profinite.empty.elim _,
        hom_inv_id' := by {ext1 x, rcases x with ⟨⟨⟩⟩ },
        inv_hom_id' := by {ext1 x, cases x } },
      let e2 := category_theory.iso.op e,
      let e3 := category_theory.functor.map_iso P e2,
      let e4 := category_theory.iso.to_equiv e3,
      have := (is_singleton_iff_exists_bijective_to_is_singleton _).2 ⟨_, _, _, _, h_prod⟩,
      { exact ⟨nonempty.map e4.symm this.1, subsingleton.map_equiv e4.symm this.2⟩ },
      { exact ⟨λ x, by rcases x with ⟨⟨⟩⟩⟩ },
      { exact ⟨λ f g, by {ext x, rcases x with ⟨⟨⟩⟩ }⟩ } },
    { specialize h_prod (Fintype.of pbool),
      /-
      ∀ (X : ↥(Fintype.of pbool)) → Profinite), function.bijective
       (λ (x : P.obj (opposite.op (Profinite.sigma X))) (a : ↥(Fintype.of pbool)), P.map (Profinite.sigma.ι X a).op x)

      For all X : pbool -> Profinite, the obvious map from
      P(Σ X) to Π (a : pbool), P (X a) is bijective
      -/
      intros S T,
      let X : ↥(Fintype.of pbool) → Profinite :=
        λ a, pbool.rec S T a,
      specialize h_prod X,
      /-
      hypothesis : if X : pbool -> Profinite sends ff to S
      and tt to T, then the obvious map from
      P(Σ X) to Π (a : pbool), P (X a) is bijective.

      Goal: the obvious map from P (S ⊕ T) to P S × P T is bijective

      plan : triangle S → Σ X ≃ S ⊕ T commutes;
      triangle T → Σ X ≃ S ⊕ T commutes;

      Claim: the obvious map from P (S ⊕ T) to P S × P T
      is the obvious map from P (S ⊕ T) to Π (a : pbool), P (X a)
      composed with the obvious bijection
        from Π a, P (X a) to P S × P T.

      Reid says work with the commutative square, i.e. the two maps
      P (Σ a, X a) ⟶ P S × P T

      -/
      admit
    } },
  { admit }
  -/
--end
-/
def mapToEqualizer {W X B : Profinite.{w}} (f : X ⟶ B) (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → {x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x} := fun t =>
  ⟨P.map f.op t, by
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _
    simp_rw [← P.map_comp, ← op_comp, w]⟩

def EqualizerCondition : Prop :=
  ∀ (X B : Profinite.{w}) (π : X ⟶ B) (surj : Function.Surjective π),
    Function.Bijective
      (mapToEqualizer P π (Profinite.pullback.fst π π) (Profinite.pullback.snd π π)
        (Profinite.pullback.condition _ _))

-- Should we make this `unique` instead of `subsingleton`?
def SubsingletonEmpty : Prop :=
  ∀ (Z : Profinite.{w}) [IsEmpty Z], Subsingleton (P.obj (op Z))

def IsProetaleSheafOfTypes : Prop :=
  ∀
    -- a finite family of morphisms with base B
    (α : Type w)
    [Fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : ∀ a, X a ⟶ B)
    -- jointly surjective
    (surj : ∀ b : B, ∃ (a : _) (x : X a), f a x = b)
    -- family of terms
    (x : ∀ a, P.obj (op (X a)))
    -- which is compatible
    (compat :
      ∀ (a b : α) (Z : Profinite.{w}) (g₁ : Z ⟶ X a) (g₂ : Z ⟶ X b),
        g₁ ≫ f a = g₂ ≫ f b → P.map g₁.op (x a) = P.map g₂.op (x b)),-- the actual condition
    ∃! t : P.obj (op B), ∀ a : α, P.map (f a).op t = x a

def IsProetaleSheafOfTypesPullback : Prop :=
  ∀
    -- a finite family of morphisms with base B
    (α : Type w)
    [Fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : ∀ a, X a ⟶ B)
    -- jointly surjective
    (surj : ∀ b : B, ∃ (a : _) (x : X a), f a x = b)
    -- family of terms
    (x : ∀ a, P.obj (op (X a)))
    -- which is compatible
    (compat :
      ∀ a b : α,
        P.map (Limits.pullback.fst : Limits.pullback (f a) (f b) ⟶ _).op (x a) =
          P.map Limits.pullback.snd.op (x b)),-- the actual condition
    ∃! t : P.obj (op B), ∀ a : α, P.map (f a).op t = x a

def IsProetaleSheafOfTypesExplicitPullback : Prop :=
  ∀
    -- a finite family of morphisms with base B
    (α : Type w)
    [Fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : ∀ a, X a ⟶ B)
    -- jointly surjective
    (surj : ∀ b : B, ∃ (a : _) (x : X a), f a x = b)
    -- family of terms
    (x : ∀ a, P.obj (op (X a)))
    -- which is compatible
    (compat :
      ∀ a b : α,
        P.map (Profinite.pullback.fst (f a) (f b)).op (x a) =
          P.map (Profinite.pullback.snd _ _).op (x b)),-- the actual condition
    ∃! t : P.obj (op B), ∀ a : α, P.map (f a).op t = x a

def IsProetaleSheafOfTypesProjective : Prop :=
  ∀
    -- a finite family of projective objects
    (α : FintypeCat.{w})
    (X : α → Profinite.{w}) [∀ a, Projective (X a)],
    Function.Bijective fun (x : P.obj (op <| Profinite.sigma X)) (a : α) =>
      P.map (Profinite.sigma.ι _ a).op x

theorem subsingletonEmpty_of_isProetaleSheafOfTypes (h : P.IsProetaleSheafOfTypes) :
    P.subsingleton_empty := by
  intro Z hZ
  specialize h PEmpty Z PEmpty.elim (fun a => a.elim) hZ.elim (fun a => a.elim) fun a => a.elim
  obtain ⟨t, ht1, ht2⟩ := h
  constructor
  intro x y
  have : x = t := by apply ht2; exact fun a => a.elim
  have : y = t := by apply ht2; exact fun a => a.elim
  cc

theorem finiteProductCondition_of_isProetaleSheafOfTypes (h : P.IsProetaleSheafOfTypes) :
    P.FiniteProductCondition := by
  intro α X
  constructor
  · intro x y hh
    dsimp at hh 
    specialize
      h α (Profinite.sigma X) X (Profinite.sigma.ι X) (Profinite.sigma.ι_jointly_surjective X)
        (fun a => P.map (Profinite.sigma.ι X a).op x) _
    · intro a b Z g₁ g₂ hhh
      dsimp
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _
      simp_rw [← P.map_comp, ← op_comp, hhh]
    obtain ⟨t, ht1, ht2⟩ := h
    have hx : x = t := by
      apply ht2
      intro a
      rfl
    have hy : y = t := by
      apply ht2
      intro a
      apply_fun fun e => e a at hh 
      exact hh.symm
    rw [hx, ← hy]
  · intro bb
    dsimp
    specialize
      h α (Profinite.sigma X) X (Profinite.sigma.ι X) (Profinite.sigma.ι_jointly_surjective X) bb _
    · intro a b Z g₁ g₂ hhh
      by_cases hZ : IsEmpty Z
      · haveI := hZ
        haveI := subsingleton_empty_of_is_proetale_sheaf_of_types P h Z
        apply Subsingleton.elim
      simp at hZ 
      obtain ⟨z⟩ := hZ
      have : a = b := by
        apply_fun fun e => (e z).1 at hhh 
        exact hhh
      subst this
      have : g₁ = g₂ := by
        ext1 t
        apply_fun Profinite.sigma.ι X a
        swap; · exact Profinite.sigma.ι_injective X a
        apply_fun fun e => e t at hhh 
        exact hhh
      rw [this]
    obtain ⟨t, ht1, ht2⟩ := h
    use t
    ext
    apply ht1

theorem isProetaleSheafOfTypes_iff :
    P.IsProetaleSheafOfTypes ↔ Presieve.IsSheaf proetaleTopology P :=
  by
  erw [presieve.is_sheaf_pretopology]
  constructor
  · intro h B S hS
    obtain ⟨α, _, X, f, surj, rfl⟩ := hS
    skip
    intro x hx
    dsimp [presieve.family_of_elements] at x 
    let y : ∀ a : α, P.obj (op (X a)) := fun a => x (f a) _
    swap
    · rw [presieve.mem_of_arrows_iff]; use a, rfl; simp
    specialize h α B X f surj y _
    · intro a b Z g₁ g₂ hh
      dsimp [presieve.family_of_elements.compatible] at hx 
      apply hx
      assumption
    convert h
    ext t
    constructor
    · intro hh
      intro a
      apply hh
    · intro hh Y g hg
      rw [presieve.mem_of_arrows_iff] at hg 
      obtain ⟨u, rfl, rfl⟩ := hg
      simp [hh]
  · intro h α _ B X f surj x compat
    let R : presieve B := presieve.of_arrows X f
    have hR : R ∈ proetalePretopology B := ⟨α, inferInstance, X, f, surj, rfl⟩
    have hhh : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), ∃ (a : α) (ha : Y = X a), g = eq_to_hom ha ≫ f a :=
      by
      intro Y g hg
      rcases hg with ⟨a⟩
      use a, rfl
      simp
    let aa : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), α := fun Y g hg => (hhh g hg).some
    have haa : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), Y = X (aa g hg) := fun Y g hg =>
      (hhh g hg).choose_spec.some
    have haa' : ∀ ⦃Y⦄ (g : Y ⟶ B) (hg : R g), g = eq_to_hom (haa g hg) ≫ f (aa g hg) :=
      fun Y g hg => (hhh g hg).choose_spec.choose_spec
    let y : R.family_of_elements P := fun Y g hg => P.map (eq_to_hom (haa g hg)).op (x (aa g hg))
    specialize h R hR y _
    · rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨a⟩ ⟨b⟩ hh
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _
      simp_rw [← P.map_comp, ← op_comp]
      apply compat
      simp_rw [category.assoc]
      convert hh
      all_goals
        symm
        apply haa'
    convert h
    ext t
    constructor
    · intro hh Y g hg
      conv_lhs => rw [haa' g hg]
      dsimp [y]
      simp [hh]
    · intro hh a
      have : R (f a) := by
        dsimp [R]
        rw [presieve.mem_of_arrows_iff]
        use a, rfl
        simp
      rw [hh (f a) this]
      dsimp [y]
      specialize compat (aa (f a) this) a (X a) (eq_to_hom _) (𝟙 _) _
      · apply haa
      rw [category.id_comp]
      apply (haa' _ _).symm
      simpa using compat

theorem isProetaleSheafOfTypesPullback_iff :
    P.IsProetaleSheafOfTypes ↔ P.IsProetaleSheafOfTypesPullback :=
  by
  constructor
  · intro h α _ B X f surj x compat
    apply h α B X f surj x
    intro a b Z g₁ g₂ h
    let g : Z ⟶ limits.pullback (f a) (f b) := limits.pullback.lift _ _ h
    rw [show g₁ = g ≫ limits.pullback.fst by simp [g]]
    rw [show g₂ = g ≫ limits.pullback.snd by simp [g]]
    simp only [op_comp, P.map_comp]
    dsimp
    rw [compat]
  · intro h α _ B X f surj x compat
    apply h α B X f surj x
    intro a b
    apply compat
    exact limits.pullback.condition

theorem isProetaleSheafOfTypesExplicitPullback_iff :
    P.IsProetaleSheafOfTypes ↔ P.IsProetaleSheafOfTypesExplicitPullback :=
  by
  constructor
  · intro h α _ B X f surj x compat
    apply h α B X f surj x
    intro a b Z g₁ g₂ h
    let g : Z ⟶ Profinite.pullback (f a) (f b) := Profinite.pullback.lift (f a) (f b) g₁ g₂ h
    rw [show g₁ = g ≫ Profinite.pullback.fst (f a) (f b) by simp [g]]
    rw [show g₂ = g ≫ Profinite.pullback.snd (f a) (f b) by simp [g]]
    simp only [op_comp, P.map_comp]
    dsimp
    rw [compat]
  · intro h α _ B X f surj x compat
    apply h α B X f surj x
    intro a b
    apply compat
    exact Profinite.pullback.condition _ _

theorem equalizerCondition_of_isProetaleSheafOfTypes (h : P.IsProetaleSheafOfTypes) :
    P.EqualizerCondition := by
  intro X B π surj
  rw [is_proetale_sheaf_of_types_explicit_pullback_iff] at h 
  specialize h PUnit B (fun _ => X) (fun _ => π) _
  · intro b
    use PUnit.unit
    apply surj
  dsimp at h 
  constructor
  · intro x y hh
    dsimp [map_to_equalizer] at hh 
    apply_fun fun e => e.val at hh 
    specialize h (fun _ => P.map π.op x) _
    · intros
      dsimp
      change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _
      simp_rw [← P.map_comp, ← op_comp, Profinite.pullback.condition]
    obtain ⟨t, ht1, ht2⟩ := h
    have hx : x = t := by
      apply ht2
      intros
      rfl
    have hy : y = t := by
      apply ht2
      intro a
      exact hh.symm
    rw [hx, ← hy]
  · rintro ⟨x, hx⟩
    specialize h (fun _ => x) _
    · intros
      exact hx
    obtain ⟨t, ht1, ht2⟩ := h
    use t
    ext1
    exact ht1 PUnit.unit

noncomputable section

def sigmaPiEquiv {α : FintypeCat.{w}} (X : α → Profinite.{w}) (h : P.FiniteProductCondition) :
    P.obj (op <| Profinite.sigma X) ≃ ∀ a, P.obj (op <| X a) :=
  Equiv.ofBijective _ (h α X)

def equalizerEquiv {S₁ S₂ : Profinite} (h : P.EqualizerCondition) (f : S₁ ⟶ S₂)
    (surj : Function.Surjective f) :
    P.obj (op S₂) ≃
      {x : P.obj (op S₁) |
        P.map (Profinite.pullback.fst f f).op x = P.map (Profinite.pullback.snd f f).op x} :=
  Equiv.ofBijective _ (h _ _ _ surj)

theorem equalizes_of_compat {α : FintypeCat.{w}} {B} {X : α → Profinite.{w}}
    (h : P.FiniteProductCondition) (f : ∀ a, X a ⟶ B) (x : ∀ a, P.obj (op <| X a))
    (compat :
      ∀ a b,
        P.map (Profinite.pullback.fst (f a) (f b)).op (x a) =
          P.map (Profinite.pullback.snd (f a) (f b)).op (x b)) :
    P.map (Profinite.pullback.fst (Profinite.sigma.desc X f) (Profinite.sigma.desc X f)).op
        ((sigmaPiEquiv P X h).symm x) =
      P.map (Profinite.pullback.snd (Profinite.sigma.desc X f) (Profinite.sigma.desc X f)).op
        ((sigmaPiEquiv P X h).symm x) :=
  by
  let I := Profinite.sigmaPullbackToPullbackSigma X f
  apply_fun P.map I.op
  swap;
  · intro i j hh
    apply_fun P.map (CategoryTheory.inv I).op at hh 
    change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _ at hh 
    simp_rw [← P.map_comp, ← op_comp] at hh 
    simpa using hh
  change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _
  simp_rw [← P.map_comp, ← op_comp]
  erw [Profinite.sigmaPullbackToPullbackSigma_fst]
  erw [Profinite.sigmaPullbackToPullbackSigma_snd]
  let E := sigma_pi_equiv P X h
  specialize h ⟨α × α⟩ fun a => Profinite.pullback (f a.1) (f a.2)
  let E' := Equiv.ofBijective _ h
  apply_fun E'
  ext1 ⟨a, b⟩
  dsimp [E']
  change (P.map _ ≫ P.map _) _ = (P.map _ ≫ P.map _) _
  simp_rw [← P.map_comp, ← op_comp, Profinite.sigma.ι_desc]
  dsimp
  simp_rw [P.map_comp]
  convert compat a b
  all_goals
    dsimp [coe_comp]
    congr 1
    change ((E ∘ E.symm) x) _ = _
    simp

theorem is_proetale_sheaf_of_finiteProductCondition_of_equalizerCondition
    (h1 : P.FiniteProductCondition) (h2 : P.EqualizerCondition) : P.IsProetaleSheafOfTypes :=
  by
  rw [is_proetale_sheaf_of_types_explicit_pullback_iff]
  intro α _ B X f surj x compat
  let A : FintypeCat := FintypeCat.of α
  change ∀ x : A, _ at x 
  change ∀ x : A, _ at f 
  change ∀ a b : A, _ at compat 
  change A → _ at X 
  let E := sigma_pi_equiv P X h1
  let F :=
    equalizer_equiv P h2 (Profinite.sigma.desc X f) (Profinite.sigma.desc_surjective _ _ surj)
  let π1 := Profinite.pullback.fst (Profinite.sigma.desc X f) (Profinite.sigma.desc X f)
  let π2 := Profinite.pullback.snd (Profinite.sigma.desc X f) (Profinite.sigma.desc X f)
  let S := P.obj (op <| Profinite.sigma X)
  let x' : {t : S | P.map π1.op t = P.map π2.op t} := ⟨E.symm x, _⟩
  swap; · exact equalizes_of_compat P h1 f x compat
  use F.symm x'
  constructor
  · dsimp
    intro a
    have :
      P.map (f a).op =
        (fun u : ∀ a, P.obj (op <| X a) => u a) ∘
          (fun u : {t : S | P.map π1.op t = P.map π2.op t} => E u.val) ∘ F :=
      by
      ext t; dsimp [E, F, sigma_pi_equiv, equalizer_equiv, map_to_equalizer]
      change _ = (P.map _ ≫ P.map _) _
      simp_rw [← P.map_comp, ← op_comp, Profinite.sigma.ι_desc]
    rw [this]
    change
      ((fun u : ∀ a, P.obj (op <| X a) => u a) ∘
            (fun u : {t : S | P.map π1.op t = P.map π2.op t} => E u.val) ∘ F ∘ F.symm)
          x' =
        _
    simp
  · intro y hy
    apply_fun F
    change _ = (F ∘ F.symm) x'
    simp only [Equiv.self_comp_symm, id.def]
    ext1
    apply_fun E
    change _ = (E ∘ E.symm) _
    simp only [Equiv.self_comp_symm, id.def]
    dsimp [E, F, sigma_pi_equiv, equalizer_equiv, map_to_equalizer]
    ext a
    change (P.map _ ≫ P.map _) _ = _
    simp_rw [← P.map_comp, ← op_comp, Profinite.sigma.ι_desc, hy a]

theorem isProetaleSheafOfTypes_tFAE :
    [Presieve.IsSheaf proetaleTopology P, P.IsProetaleSheafOfTypes,
        P.IsProetaleSheafOfTypesPullback, P.IsProetaleSheafOfTypesExplicitPullback,
        P.FiniteProductCondition ∧ P.EqualizerCondition,
        P.EmptyCondition ∧ P.ProductCondition ∧ P.EqualizerCondition].TFAE :=
  by
  tfae_have 1 ↔ 2; · exact P.is_proetale_sheaf_of_types_iff.symm
  tfae_have 2 ↔ 3; · exact P.is_proetale_sheaf_of_types_pullback_iff
  tfae_have 2 ↔ 4; · exact P.is_proetale_sheaf_of_types_explicit_pullback_iff
  tfae_have 2 → 5;
  · intro h
    constructor
    · exact finite_product_condition_of_is_proetale_sheaf_of_types _ h
    · exact equalizer_condition_of_is_proetale_sheaf_of_types _ h
  tfae_have 5 → 2;
  · rintro ⟨h1, h2⟩
    apply is_proetale_sheaf_of_finite_product_condition_of_equalizer_condition
    assumption'
  tfae_have 5 ↔ 6;
  · rw [finite_product_condition_iff_empty_product]
    rw [and_assoc']
  tfae_finish

def IsProetaleSheaf : Prop :=
  ∀
    -- a finite family of morphisms with base B
    (α : Type w)
    [Fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : ∀ a, X a ⟶ B)
    -- jointly surjective
    (surj : ∀ b : B, ∃ (a : _) (x : X a), f a x = b)
    -- test object
    (T : C)
    -- family of moprhisms
    (x : ∀ a, T ⟶ Q.obj (op (X a)))
    -- which is compatible
    (compat :
      ∀ (a b : α) (Z : Profinite.{w}) (g₁ : Z ⟶ X a) (g₂ : Z ⟶ X b),
        g₁ ≫ f a = g₂ ≫ f b → x a ≫ Q.map g₁.op = x b ≫ Q.map g₂.op),-- the actual condition
    ∃! t : T ⟶ Q.obj (op B), ∀ a : α, t ≫ Q.map (f a).op = x a

def IsProetaleSheafPullback : Prop :=
  ∀
    -- a finite family of morphisms with base B
    (α : Type w)
    [Fintype α] (B : Profinite.{w}) (X : α → Profinite.{w}) (f : ∀ a, X a ⟶ B)
    -- jointly surjective
    (surj : ∀ b : B, ∃ (a : _) (x : X a), f a x = b)
    -- test object
    (T : C)
    -- family of moprhisms
    (x : ∀ a, T ⟶ Q.obj (op (X a)))
    -- which is compatible
    (compat :
      ∀ a b : α,
        x a ≫ Q.map (Limits.pullback.fst : Limits.pullback (f a) (f b) ⟶ _).op =
          x b ≫ Q.map Limits.pullback.snd.op),-- the actual condition
    ∃! t : T ⟶ Q.obj (op B), ∀ a : α, t ≫ Q.map (f a).op = x a

theorem isProetaleSheafPullback_iff : Q.IsProetaleSheaf ↔ Q.IsProetaleSheafPullback :=
  by
  constructor
  · intro h α _ B X f surj T x compat
    apply h α B X f surj T x
    intro a b Z g₁ g₂ h
    specialize compat a b
    let g : Z ⟶ limits.pullback (f a) (f b) := limits.pullback.lift g₁ g₂ h
    rw [show g₁ = g ≫ limits.pullback.fst by simp [g]]
    rw [show g₂ = g ≫ limits.pullback.snd by simp [g]]
    simp only [op_comp, Q.map_comp, reassoc_of compat]
  · intro h α _ B X f surj T x compat
    apply h α B X f surj T x
    intro a b
    apply compat
    exact limits.pullback.condition

theorem isProetaleSheaf_iff : Q.IsProetaleSheaf ↔ Presheaf.IsSheaf proetaleTopology Q :=
  by
  constructor
  · intro h T
    rw [← (Q ⋙ coyoneda.obj (op T)).isProetaleSheafOfTypes_iff]
    intro α _ B X f surj x compat
    exact h α B X f surj T x compat
  · intro h α _ B X f surj T x compat
    specialize h T
    rw [← (Q ⋙ coyoneda.obj (op T)).isProetaleSheafOfTypes_iff] at h 
    exact h α B X f surj x compat

def EmptyCondition' [Limits.HasTerminal C] : Prop :=
  IsIso (Limits.terminal.from (Q.obj (op Profinite.empty)))

def ProductCondition' [Limits.HasBinaryProducts C] : Prop :=
  ∀ X Y : Profinite.{w},
    IsIso (Limits.prod.lift (Q.map (Profinite.sum.inl X Y).op) (Q.map (Profinite.sum.inr X Y).op))

def mapToEqualizer' [Limits.HasEqualizers C] {X Y Z : Profinite.{w}} (f : Y ⟶ X) (g₁ g₂ : Z ⟶ Y)
    (w : g₁ ≫ f = g₂ ≫ f) : Q.obj (op X) ⟶ Limits.equalizer (Q.map g₁.op) (Q.map g₂.op) :=
  Limits.equalizer.lift (Q.map f.op) (by simp only [← Q.map_comp, ← op_comp, w])

def EqualizerCondition' [Limits.HasEqualizers C] : Prop :=
  ∀ (X Y : Profinite.{w}) (f : X ⟶ Y) (hf : Function.Surjective f),
    IsIso
      (Q.mapToEqualizer' f (Profinite.pullback.fst f f) (Profinite.pullback.snd f f)
        (Profinite.pullback.condition _ _))

theorem empty_of_empty_coyoneda [Limits.HasTerminal C] :
    (∀ X : C, (Q ⋙ coyoneda.obj (op X)).EmptyCondition) → Q.EmptyCondition' :=
  by
  intro h
  have hh := h (⊤_ C)
  have hh' := h (Q.obj (op <| Profinite.empty))
  let P := Q ⋙ coyoneda.obj (op <| Q.obj (op <| Profinite.empty))
  rcases hh with ⟨h1, h2⟩
  rcases hh' with ⟨h1', h2'⟩
  dsimp [empty_condition']
  obtain ⟨f, -⟩ := h2 PUnit.unit
  use f
  simp only [and_true_iff, eq_iff_true_of_subsingleton]
  apply h1'
  simp

theorem empty_coyoneda_of_empty [Limits.HasTerminal C] :
    Q.EmptyCondition' → ∀ X : C, (Q ⋙ coyoneda.obj (op X)).EmptyCondition :=
  by
  intro h X
  let e := limits.terminal.from (Q.obj (op <| Profinite.empty))
  change is_iso e at h 
  skip
  constructor
  · rintro f g -
    dsimp [coyoneda, empty_condition'] at f g 
    suffices f ≫ e = g ≫ e
      by
      apply_fun fun t => t ≫ CategoryTheory.inv e at this 
      simp_rw [category.assoc] at this 
      simpa only [category.comp_id, is_iso.hom_inv_id] using this
    simp only [eq_iff_true_of_subsingleton]
  · rintro a
    dsimp [coyoneda]
    use limits.terminal.from X ≫ CategoryTheory.inv e
    simp

theorem product_of_product_coyoneda [Limits.HasBinaryProducts C] :
    (∀ X : C, (Q ⋙ coyoneda.obj (op X)).ProductCondition) → Q.ProductCondition' :=
  by
  intro h
  intro X Y
  have hh := h (Q.obj (op X) ⨯ Q.obj (op Y))
  have hh' := h (Q.obj (op <| Profinite.sum X Y))
  let P1 := Q ⋙ coyoneda.obj (op <| Q.obj (op X) ⨯ Q.obj (op Y))
  let P2 := Q ⋙ coyoneda.obj (op <| Q.obj (op <| Profinite.sum X Y))
  specialize hh X Y
  specialize hh' X Y
  dsimp [P1, P2, coyoneda] at hh hh' 
  rcases hh with ⟨-, hh⟩
  rcases hh' with ⟨hh', -⟩
  obtain ⟨f, hf⟩ := hh ⟨limits.prod.fst, limits.prod.snd⟩
  use f
  dsimp at *
  simp only [Prod.mk.inj_iff] at hf 
  cases' hf with hf1 hf2
  simp only [hf1, hf2, and_true_iff, limits.prod.comp_lift, limits.prod.lift_fst_snd,
    eq_self_iff_true]
  apply hh'
  simp [hf1, hf2]

theorem product_coyoneda_of_product [Limits.HasBinaryProducts C] :
    Q.ProductCondition' → ∀ X : C, (Q ⋙ coyoneda.obj (op X)).ProductCondition :=
  by
  intro h X A B
  specialize h A B
  let e := limits.prod.lift (Q.map (Profinite.sum.inl A B).op) (Q.map (Profinite.sum.inr A B).op)
  change is_iso e at h 
  skip
  constructor
  · intro f g hh
    dsimp at f g hh 
    simp only [Prod.mk.inj_iff] at hh 
    rcases hh with ⟨hl, hr⟩
    suffices f ≫ e = g ≫ e
      by
      apply_fun fun t => t ≫ CategoryTheory.inv e at this 
      simp_rw [category.assoc] at this 
      simpa using this
    apply limits.prod.hom_ext
    · simp [hl]
    · simp [hr]
  · rintro ⟨a, b⟩
    dsimp at a b ⊢
    use limits.prod.lift a b ≫ CategoryTheory.inv e
    have ha : CategoryTheory.inv e ≫ Q.map (Profinite.sum.inl A B).op = limits.prod.fst := by
      simp [is_iso.inv_comp_eq, e]
    have hb : CategoryTheory.inv e ≫ Q.map (Profinite.sum.inr A B).op = limits.prod.snd := by
      simp [is_iso.inv_comp_eq, e]
    simp [ha, hb]

theorem equalizer_of_equalizer_coyoneda [Limits.HasEqualizers C] :
    (∀ X : C, (Q ⋙ coyoneda.obj (op X)).EqualizerCondition) → Q.EqualizerCondition' :=
  by
  intro h X B f hf
  let h1 := h (Q.obj (Opposite.op B)) X B f hf
  let π1 := Profinite.pullback.fst f f
  let π2 := Profinite.pullback.snd f f
  let h2 := h (limits.equalizer (Q.map π1.op) (Q.map π2.op)) X B f hf
  dsimp [map_to_equalizer] at h1 h2 
  obtain ⟨e, he⟩ := h2.2 ⟨limits.equalizer.ι _ _, _⟩
  swap; · dsimp [π1, π2]; simp [limits.equalizer.condition]
  use e
  dsimp [map_to_equalizer'] at *
  simp at he 
  constructor
  · apply h1.1
    simp [he]
  · apply limits.equalizer.hom_ext; simp [he]

theorem equalizer_coyoneda_of_equalizer [Limits.HasEqualizers C] :
    Q.EqualizerCondition' → ∀ X : C, (Q ⋙ coyoneda.obj (op X)).EqualizerCondition :=
  by
  intro h X A B f hf
  specialize h A B f hf
  let e :=
    Q.map_to_equalizer' f (Profinite.pullback.fst f f) (Profinite.pullback.snd f f)
      (Profinite.pullback.condition _ _)
  change is_iso e at h 
  skip
  constructor
  · intro a b hh
    dsimp [map_to_equalizer] at a b hh 
    simp at hh 
    suffices a ≫ e = b ≫ e
      by
      apply_fun fun t => t ≫ CategoryTheory.inv e at this 
      simp_rw [category.assoc] at this 
      simpa using this
    apply limits.equalizer.hom_ext
    simpa [e, map_to_equalizer']
  · rintro ⟨a, ha⟩
    dsimp at a ha 
    use limits.equalizer.lift a ha ≫ CategoryTheory.inv e
    have : CategoryTheory.inv e ≫ Q.map f.op = limits.equalizer.ι _ _ := by
      simp [e, is_iso.comp_inv_eq, map_to_equalizer']
    simp [map_to_equalizer, this]

theorem isProetaleSheaf_of_empty_of_product_of_equalizer [Limits.HasTerminal C]
    [Limits.HasBinaryProducts C] [Limits.HasEqualizers C] :
    Q.EmptyCondition' ∧ Q.ProductCondition' ∧ Q.EqualizerCondition' → Q.IsProetaleSheaf :=
  by
  rintro ⟨h1, h2, h3⟩
  rw [is_proetale_sheaf_iff]
  intro X
  rw [(Q ⋙ coyoneda.obj (op X)).isProetaleSheafOfTypes_tFAE.out 0 5]
  refine' ⟨_, _, _⟩
  · apply empty_coyoneda_of_empty; exact h1
  · apply product_coyoneda_of_product; exact h2
  · apply equalizer_coyoneda_of_equalizer; exact h3

theorem isProetaleSheaf_tFAE [Limits.HasTerminal C] [Limits.HasBinaryProducts C]
    [Limits.HasEqualizers C] :
    [Presheaf.IsSheaf proetaleTopology Q, Q.IsProetaleSheaf, Q.IsProetaleSheafPullback,
        Q.EmptyCondition' ∧ Q.ProductCondition' ∧ Q.EqualizerCondition'].TFAE :=
  by
  tfae_have 1 ↔ 2; · exact Q.is_proetale_sheaf_iff.symm
  tfae_have 2 ↔ 3; · exact Q.is_proetale_sheaf_pullback_iff
  tfae_have 1 → 4
  · intro h
    refine' ⟨_, _, _⟩
    · apply empty_of_empty_coyoneda
      intro X
      specialize h X
      rw [(Q ⋙ coyoneda.obj (op X)).isProetaleSheafOfTypes_tFAE.out 0 5] at h 
      exact h.1
    · apply product_of_product_coyoneda
      intro X
      specialize h X
      rw [(Q ⋙ coyoneda.obj (op X)).isProetaleSheafOfTypes_tFAE.out 0 5] at h 
      exact h.2.1
    · apply equalizer_of_equalizer_coyoneda
      intro X
      specialize h X
      rw [(Q ⋙ coyoneda.obj (op X)).isProetaleSheafOfTypes_tFAE.out 0 5] at h 
      exact h.2.2
  tfae_have 4 → 1
  · intro h X
    rw [(Q ⋙ coyoneda.obj (op X)).isProetaleSheafOfTypes_tFAE.out 0 5]
    refine' ⟨_, _, _⟩
    · apply empty_coyoneda_of_empty; exact h.1
    · apply product_coyoneda_of_product; exact h.2.1
    · apply equalizer_coyoneda_of_equalizer; exact h.2.2
  tfae_finish

end CategoryTheory.Functor

