import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import LiquidTensorExperiment.ForMathlib.HomologicalComplexShift
import LiquidTensorExperiment.ForMathlib.MonoidalCategory
import LiquidTensorExperiment.ForMathlib.Int

#align_import for_mathlib.triangle_shift

noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v u

-- Move + generalize!
@[simp]
theorem CategoryTheory.Discrete.associator_def (a b c : Discrete ℤ) :
    α_ a b c = eqToIso (Discrete.ext _ _ <| add_assoc a.1 b.1 c.1) :=
  rfl

-- Move + generalize!
@[simp]
theorem CategoryTheory.Discrete.leftUnitor_def (a : Discrete ℤ) :
    λ_ a = eqToIso (Discrete.ext _ _ <| zero_add _) :=
  rfl

-- Move + generalize!
@[simp]
theorem CategoryTheory.Discrete.rightUnitor_def (a : Discrete ℤ) :
    ρ_ a = eqToIso (Discrete.ext _ _ <| add_zero _) :=
  rfl

namespace CategoryTheory.Triangulated

open CategoryTheory.Category

variable (C : Type u) [Category.{v} C] [Preadditive C]

variable [HasShift C ℤ]

attribute [local instance, local reducible] CategoryTheory.endofunctorMonoidalCategory

namespace Triangle

@[simps]
def triangleShiftObj (T : triangle C) (i : ℤ) : triangle C :=
  Triangle.mk C (i.neg_one_pow • (shiftFunctor _ i).map T.mor₁)
    (i.neg_one_pow • (shiftFunctor _ i).map T.mor₂)
    (i.neg_one_pow • (shiftFunctor C i).map T.mor₃ ≫ (shiftComm _ _ _).hom)

@[simps]
def triangleShiftMap {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) :
    triangleShiftObj C T₁ i ⟶ triangleShiftObj C T₂ i
    where
  hom₁ := (shiftFunctor _ i).map f.hom₁
  hom₂ := (shiftFunctor _ i).map f.hom₂
  hom₃ := (shiftFunctor _ i).map f.hom₃
  comm₁' := by dsimp;
    simp only [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, ←
      Functor.map_comp, f.comm₁]
  comm₂' := by dsimp;
    simp only [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, ←
      Functor.map_comp, f.comm₂]
  comm₃' := by
    dsimp
    simp only [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    congr 1
    simp only [CategoryTheory.shiftComm_hom_comp, assoc, Iso.cancel_iso_hom_right_assoc, ← Functor.map_comp,
      f.comm₃]

@[simps]
def triangleShiftFunctor (i : ℤ) : triangle C ⥤ triangle C
    where
  obj T := triangleShiftObj C T i
  map T₁ T₂ f := triangleShiftMap C f _
  map_id := by
    intro T
    ext
    all_goals dsimp; simp
  map_comp := by
    intro T₁ T₂ T₃ f g
    ext
    all_goals dsimp; simp

variable {C}

@[simps]
def Iso.ofComponents {T₁ T₂ : triangle C} (e₁ : T₁.obj₁ ≅ T₂.obj₁) (e₂ : T₁.obj₂ ≅ T₂.obj₂)
    (e₃ : T₁.obj₃ ≅ T₂.obj₃) (h₁ h₂ h₃) : T₁ ≅ T₂
    where
  hom :=
    { hom₁ := e₁.hom
      hom₂ := e₂.hom
      hom₃ := e₃.hom
      comm₁' := h₁
      comm₂' := h₂
      comm₃' := h₃ }
  inv :=
    { hom₁ := e₁.inv
      hom₂ := e₂.inv
      hom₃ := e₃.inv
      comm₁' := by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, h₁]
      comm₂' := by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, h₂]
      comm₃' := by
        rw [← Functor.mapIso_inv, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
          Functor.mapIso_hom, h₃] }
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

variable (C)

@[simps]
def triangleShiftFunctorε : 𝟭 (triangulated.triangle C) ≅ triangleShiftFunctor C 0 :=
  NatIso.ofComponents
    (fun T =>
      Iso.ofComponents (shiftZero _ _).symm (shiftZero _ _).symm (shiftZero _ _).symm
        (by
          convert (CategoryTheory.shiftFunctorZero _ _).inv.naturality _
          dsimp only [CategoryTheory.Triangulated.Triangle.triangleShiftFunctor, CategoryTheory.Triangulated.Triangle.triangleShiftObj]
          simpa)
        (by
          convert (CategoryTheory.shiftFunctorZero _ _).inv.naturality _
          dsimp only [CategoryTheory.Triangulated.Triangle.triangleShiftFunctor, CategoryTheory.Triangulated.Triangle.triangleShiftObj]
          simpa)
        (by
          dsimp
          rw [one_smul]
          rw [← NatTrans.naturality_assoc]; dsimp [CategoryTheory.shiftComm]
          simp only [obj_ε_app, Discrete.functor_map_id, NatTrans.id_app, ε_app_obj, assoc,
            id_comp]
          rw [← NatTrans.comp_app, ← NatTrans.comp_app]
          erw [monoidal_functor.μ_inv_hom_id_assoc, id_comp]; rfl))
    (by intro T₁ T₂ f;
      ext <;>
        · dsimp only [TriangleMorphism.comp_hom₁, Iso.ofComponents_hom_hom₁,
            triangle_shift_map_hom₁, TriangleMorphism.comp_hom₂, Iso.ofComponents_hom_hom₂,
            triangle_shift_map_hom₂, TriangleMorphism.comp_hom₃, Iso.ofComponents_hom_hom₃,
            triangle_shift_map_hom₃, Functor.id_map, CategoryTheory.Pretriangulated.triangleCategory_comp, Iso.symm_hom,
            Iso.app_inv, Iso.symm_inv, monoidal_functor.ε_iso_hom, CategoryTheory.Triangulated.Triangle.triangleShiftFunctor_map]
          rw [← NatTrans.naturality _ _]; rfl)

variable [∀ i : ℤ, (shiftFunctor C i).Additive]

@[reassoc]
theorem shiftComm_eq_eqToHom (X : C) (i j : ℤ) :
    (shiftAdd X i j).hom ≫ (shiftComm X i j).hom ≫ (shiftAdd X j i).inv =
      eqToHom (by congr 2; exact add_comm i j) :=
  by
  dsimp [CategoryTheory.shiftAdd, CategoryTheory.shiftComm]
  simp only [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app, assoc, μ_inv_hom_app, μ_inv_hom_app_assoc]
  erw [comp_id]

@[reassoc]
theorem shiftAdd_comp_eqToHom (X : C) (i j k : ℤ) (h : i + j = j + i) :
    (shiftAdd X (i + j) k).hom ≫ eqToHom (by congr 3) ≫ (shiftAdd X (j + i) k).inv =
      eqToHom (by congr 3) :=
  by
  dsimp [CategoryTheory.shiftAdd]
  induction h; dsimp; simpa

@[reassoc]
theorem shiftAdd_comp_eq_to_hom' (X : C) (i j k : ℤ) (h : j + k = k + j) :
    (shiftAdd X i (j + k)).hom ≫ eqToHom (by congr 3) ≫ (shiftAdd X i (k + j)).inv =
      eqToHom (by congr 3) :=
  by
  dsimp [CategoryTheory.shiftAdd]
  induction h; dsimp; simpa

theorem triangle_shiftFunctor_μ_aux (X : C) (i j : ℤ) :
    (shiftFunctor C j).map (shiftComm X 1 i).hom ≫
        (shiftComm ((shiftFunctor C i).obj X) 1 j).hom ≫
          (shiftFunctor C 1).map (shiftAdd X i j).inv =
      (shiftAdd ((shiftFunctor C 1).obj X) i j).inv ≫ (shiftComm X 1 (i + j)).hom :=
  by
  dsimp [CategoryTheory.shiftAdd, CategoryTheory.shiftComm]
  simp only [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app, Functor.map_comp, obj_μ_app,
    CategoryTheory.Discrete.associator_def, eqToIso.inv, obj_μ_inv_app, eqToIso.hom, assoc,
    μ_inv_hom_app_assoc]
  congr 2
  simp only [← assoc]; congr 1; simp only [assoc]
  erw [CategoryTheory.Triangulated.Triangle.shiftAdd_comp_eqToHom_assoc]
  erw [CategoryTheory.Triangulated.Triangle.shiftAdd_comp_eq_to_hom'_assoc]
  simpa; exact add_comm _ _; exact add_comm _ _

@[simps]
def triangleShiftFunctorμ (i j : ℤ) :
    triangleShiftFunctor C i ⋙ triangleShiftFunctor C j ≅ triangleShiftFunctor C (i + j) :=
  NatIso.ofComponents
    (fun T =>
      Iso.ofComponents (shiftAdd _ _ _).symm (shiftAdd _ _ _).symm (shiftAdd _ _ _).symm
        (by
          dsimp [CategoryTheory.Triangulated.Triangle.triangleShiftFunctor, CategoryTheory.Triangulated.Triangle.triangleShiftObj]
          simp only [zsmul_comp, comp_zsmul, Iso.symm_hom, Iso.app_inv, Iso.symm_inv,
            monoidal_functor.μ_iso_hom, Functor.map_zsmul, smul_smul, Int.negOnePow_add]
          have := (shift_functor_add _ i j).inv.naturality T.mor₁
          rw [Functor.comp_map] at this 
          erw [this, mul_comm]; rfl)
        (by
          dsimp [CategoryTheory.Triangulated.Triangle.triangleShiftFunctor, CategoryTheory.Triangulated.Triangle.triangleShiftObj]
          simp only [zsmul_comp, comp_zsmul, Iso.symm_hom, Iso.app_inv, Iso.symm_inv,
            monoidal_functor.μ_iso_hom, Functor.map_zsmul, smul_smul, Int.negOnePow_add]
          have := (shift_functor_add _ i j).inv.naturality T.mor₂
          rw [Functor.comp_map] at this 
          erw [this, mul_comm]; rfl)
        (by
          dsimp [CategoryTheory.Triangulated.Triangle.triangleShiftFunctor, CategoryTheory.Triangulated.Triangle.triangleShiftObj]
          simp only [zsmul_comp, comp_zsmul, Iso.symm_hom, Iso.app_inv, Iso.symm_inv,
            monoidal_functor.μ_iso_hom, Functor.map_zsmul, smul_smul, Int.negOnePow_add,
            mul_comm j.neg_one_pow]
          have := (shift_functor_add _ i j).inv.naturality T.mor₃
          dsimp [Functor.comp_map] at this 
          erw [← reassoc_of this]; clear this
          simp only [Functor.map_comp, assoc, obj_μ_app]
          congr 2
          --have := (shift_monoidal_functor C ℤ).to_lax_monoidal_functor.associativity i j 1,
          rw [(CategoryTheory.shiftMonoidalFunctor C ℤ).map_associator_inv]
          dsimp
          simp only [assoc, IsIso.inv_id, NatTrans.hcomp_app, comp_id, id_comp]
          slice_lhs 4 5 => rw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
          erw [id_comp]
          rw [CategoryTheory.NatIso.isIso_inv_app]
          --rw nat_trans.id_hcomp_app,
          dsimp
          simp only [CategoryTheory.Functor.map_id, comp_id, assoc, IsIso.hom_inv_id_assoc]
          slice_lhs 4 5 =>
            rw [← NatTrans.comp_app, (CategoryTheory.shiftMonoidalFunctor C ℤ).μ_hom_inv_id, NatTrans.id_app]
          erw [comp_id]; apply triangle_shift_functor_μ_aux))
    (by intro T₁ T₂ f;
      ext <;>
        · dsimp only [TriangleMorphism.comp_hom₁, Iso.ofComponents_hom_hom₁,
            triangle_shift_map_hom₁, TriangleMorphism.comp_hom₂, Iso.ofComponents_hom_hom₂,
            triangle_shift_map_hom₂, TriangleMorphism.comp_hom₃, Iso.ofComponents_hom_hom₃,
            triangle_shift_map_hom₃, Functor.id_map, CategoryTheory.Pretriangulated.triangleCategory_comp, Iso.symm_hom,
            Iso.app_inv, Iso.symm_inv, monoidal_functor.ε_iso_hom, CategoryTheory.Triangulated.Triangle.triangleShiftFunctor_map]
          rw [← NatTrans.naturality _ _]; rfl)

/-
def triangle_shift_core : shift_mk_core (triangle C) ℤ :=
{ F := triangle_shift_functor _,
  ε := triangle_shift_functor_ε _,
  μ := λ i j, triangle_shift_functor_μ _ _ _,
  associativity := begin
    intros i j k T, ext,
    { have := (shift_monoidal_functor C ℤ).to_lax_monoidal_functor.associativity i j k,
      apply_fun (λ α, α.app T.obj₁) at this,
      simp only [nat_trans.comp_app, obj_μ_app, assoc, μ_inv_hom_app_assoc, map_inv_hom_app,
        comp_id, functor.associator_hom_app, nat_trans.hcomp_app, nat_trans.id_app,
        category_theory.functor.map_id, id_comp] at this,
      erw [id_comp] at this,
      refine eq.trans _ this, clear this,
      dsimp, simp only [obj_μ_app, assoc],
      -- I don't like that `(eq_to_hom _).hom₁`.
      admit },
    admit,
    admit
  end,
  left_unitality := admit,
  right_unitality := admit }
-/
@[simps]
def mapTriangleShiftFunctor (m n : Discrete ℤ) (f : m ⟶ n) :
    triangleShiftFunctor C m.1 ⟶ triangleShiftFunctor C n.1
    where
  app T :=
    { hom₁ := eqToHom <| by rw [Discrete.eq_of_hom f]
      hom₂ := eqToHom <| by rw [Discrete.eq_of_hom f]
      hom₃ := eqToHom <| by rw [Discrete.eq_of_hom f]
      comm₁' := by
        rcases m, n with ⟨⟨_⟩, ⟨_⟩⟩; rcases f with ⟨⟨rfl : m = n⟩⟩
        simp only [CategoryTheory.eqToHom_refl, id_comp, comp_id]
      comm₂' := by
        rcases m, n with ⟨⟨_⟩, ⟨_⟩⟩; rcases f with ⟨⟨rfl : m = n⟩⟩
        simp only [CategoryTheory.eqToHom_refl, id_comp, comp_id]
      comm₃' := by
        rcases m, n with ⟨⟨_⟩, ⟨_⟩⟩; rcases f with ⟨⟨rfl : m = n⟩⟩
        dsimp; rw [(shift_functor C (1 : ℤ)).map_id]; simp only [comp_id, id_comp] }
  naturality := by
    rcases m, n with ⟨⟨_⟩, ⟨_⟩⟩; rcases f with ⟨⟨rfl : m = n⟩⟩
    rintro X Y g; ext <;> · dsimp; simp only [CategoryTheory.eqToHom_refl, id_comp, comp_id]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem associativity_aux (X : C) (a b c : ℤ) :
    (𝟙 ((shiftFunctor C c).obj ((shiftFunctor C b).obj ((shiftFunctor C a).obj X))) ≫
          (shiftFunctor C c).map (((shiftMonoidalFunctor C ℤ).μ ⟨a⟩ ⟨b⟩).app X)) ≫
        ((shiftMonoidalFunctor C ℤ).μ (⟨a⟩ ⊗ ⟨b⟩) ⟨c⟩).app X ≫
          eqToHom
            (show
              ((shiftMonoidalFunctor C ℤ).obj ((⟨a⟩ ⊗ ⟨b⟩) ⊗ ⟨c⟩)).obj X =
                ((shiftMonoidalFunctor C ℤ).obj (⟨a⟩ ⊗ ⟨b⟩ ⊗ ⟨c⟩)).obj X
              by congr 2; ext; apply add_assoc) =
      𝟙 ((shiftFunctor C c).obj ((shiftFunctor C b).obj ((shiftFunctor C a).obj X))) ≫
        (((shiftMonoidalFunctor C ℤ).μ ⟨b⟩ ⟨c⟩).app ((shiftFunctor C a).obj X) ≫
            (shiftFunctor C (b + c)).map (𝟙 ((shiftFunctor C a).obj X))) ≫
          ((shiftMonoidalFunctor C ℤ).toLaxMonoidalFunctor.μ ⟨a⟩ (⟨b⟩ ⊗ ⟨c⟩)).app X :=
  by
  have := (CategoryTheory.shiftMonoidalFunctor C ℤ).associativity' ⟨a⟩ ⟨b⟩ ⟨c⟩
  apply_fun fun e => e.app X at this 
  dsimp at this ⊢
  simp only [id_comp, comp_id, CategoryTheory.Functor.map_id, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app] at this
    ⊢
  erw [comp_id]
  exact this

theorem left_unitality_aux (X : C) (a : ℤ) :
    𝟙 ((shiftFunctor C a).obj X) =
      (𝟙 ((shiftFunctor C a).obj X) ≫
          (shiftFunctor C a).map ((shiftMonoidalFunctor C ℤ).toLaxMonoidalFunctor.ε.app X)) ≫
        ((shiftMonoidalFunctor C ℤ).toLaxMonoidalFunctor.μ (𝟙_ (Discrete ℤ)) ⟨a⟩).app X ≫
          eqToHom (by congr; ext; exact zero_add a) :=
  by
  have := (CategoryTheory.shiftMonoidalFunctor C ℤ).left_unitality' ⟨a⟩
  apply_fun fun e => e.app X at this 
  dsimp at this ⊢
  simp only [id_comp, comp_id, CategoryTheory.Functor.map_id, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app] at this
    ⊢
  exact this

theorem right_unitality_aux (X : C) (a : ℤ) :
    𝟙 ((shiftFunctor C a).obj X) =
      ((shiftMonoidalFunctor C ℤ).toLaxMonoidalFunctor.ε.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor C (𝟙_ (Discrete ℤ)).as).map (𝟙 ((shiftFunctor C a).obj X))) ≫
        ((shiftMonoidalFunctor C ℤ).toLaxMonoidalFunctor.μ ⟨a⟩ (𝟙_ (Discrete ℤ))).app X ≫
          eqToHom (by congr; ext; apply add_zero) :=
  by
  have := (CategoryTheory.shiftMonoidalFunctor C ℤ).right_unitality' ⟨a⟩
  apply_fun fun e => e.app X at this 
  dsimp at this ⊢
  simp only [id_comp, comp_id, CategoryTheory.Functor.map_id, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app] at this
    ⊢
  erw [comp_id]
  exact this

instance hasShift : HasShift (triangle C) ℤ :=
  HasShift.mk <|
    { obj := fun i => triangleShiftFunctor _ i.as
      map := fun m n f => mapTriangleShiftFunctor _ _ _ f
      map_id := fun X => by ext <;> rfl
      map_comp := fun X Y Z f g => by ext <;> simp
      ε := (triangleShiftFunctorε _).hom
      μ := fun m n => (triangleShiftFunctorμ _ m.as n.as).hom
      μ_natural' := by rintro ⟨m⟩ ⟨m'⟩ ⟨n⟩ ⟨n'⟩ ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩;
        ext <;> · dsimp; simp only [id_comp, comp_id, CategoryTheory.Functor.map_id]
      associativity' := fun a b c => by ext <;> apply associativity_aux
      left_unitality' := fun a => by ext <;> apply left_unitality_aux
      right_unitality' := fun a => by ext <;> apply right_unitality_aux
      ε_isIso := inferInstance
      μ_isIso := inferInstance }

@[simp]
theorem shift_obj₁ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₁ = T.obj₁⟦i⟧ :=
  rfl

@[simp]
theorem shift_obj₂ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₂ = T.obj₂⟦i⟧ :=
  rfl

@[simp]
theorem shift_obj₃ (T : triangle C) (i : ℤ) : T⟦i⟧.obj₃ = T.obj₃⟦i⟧ :=
  rfl

@[simp]
theorem shift_mor₁ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₁ = i.neg_one_pow • T.mor₁⟦i⟧' :=
  rfl

@[simp]
theorem shift_mor₂ (T : triangle C) (i : ℤ) : T⟦i⟧.mor₂ = i.neg_one_pow • T.mor₂⟦i⟧' :=
  rfl

@[simp]
theorem shift_mor₃ (T : triangle C) (i : ℤ) :
    T⟦i⟧.mor₃ = i.neg_one_pow • T.mor₃⟦i⟧' ≫ (shiftComm _ _ _).hom :=
  rfl

@[simp]
theorem shift_hom₁ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₁ = f.hom₁⟦i⟧' :=
  rfl

@[simp]
theorem shift_hom₂ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₂ = f.hom₂⟦i⟧' :=
  rfl

@[simp]
theorem shift_hom₃ {T₁ T₂ : triangle C} (f : T₁ ⟶ T₂) (i : ℤ) : f⟦i⟧'.hom₃ = f.hom₃⟦i⟧' :=
  rfl

end Triangle

/-
instance {C : Type*} [category C] [preadditive C] (X Y : C) : has_neg (X ≅ Y) :=
⟨λ f,
{ hom := -f.hom,
  inv := -f.inv,
  hom_inv_id' := by simp only [comp_neg, neg_comp, iso.hom_inv_id, neg_neg],
  inv_hom_id' := by simp only [comp_neg, neg_comp, iso.inv_hom_id, neg_neg] }⟩

@[simp] lemma _root_.category_theory.neg_hom
   {C : Type*} [category C] [preadditive C] {X Y : C} (f : X ≅ Y) :
   (-f).hom = -(f.hom) := rfl

@[simp] lemma _root_.category_theory.neg_inv
   {C : Type*} [category C] [preadditive C] {X Y : C} (f : X ≅ Y) :
   (-f).inv = -(f.inv) := rfl
-/
namespace Pretriangulated

@[simp]
theorem shiftComm_self (X : C) (i : ℤ) : shiftComm X i i = Iso.refl _ :=
  by
  ext
  dsimp [CategoryTheory.shiftComm]
  simpa only [Discrete.functor_map_id, NatTrans.id_app, id_comp, μ_hom_inv_app]

variable [HasZeroObject C] [∀ i : ℤ, (shiftFunctor C i).Additive] [pretriangulated C]

theorem dist_triangle_iff_of_iso {T₁ T₂ : triangle C} (e : T₁ ≅ T₂) :
    T₁ ∈ (dist_triang C) ↔ T₂ ∈ (dist_triang C) :=
  ⟨fun h => isomorphic_distinguished _ h _ e.symm, fun h => isomorphic_distinguished _ h _ e⟩

theorem dist_triangle_rot_iff (T : triangle C) : T.rotate ∈ (dist_triang C) ↔ T ∈ (dist_triang C) :=
  by
  refine' ⟨fun h => _, fun h => CategoryTheory.Pretriangulated.rot_of_distTriang _ _ h⟩
  let e : T ≅ T.rotate.invRotate := rot_comp_inv_rot.app T
  rw [← dist_triangle_iff_of_iso _ e.symm]
  exact CategoryTheory.Pretriangulated.inv_rot_of_distTriang _ _ h

theorem shift_of_dist_triangle (T : triangle C) (hT : T ∈ (dist_triang C)) (i : ℤ) :
    T⟦i⟧ ∈ (dist_triang C) :=
  by
  induction' i using Int.induction_on_iff with i
  · exact isomorphic_distinguished T hT _ (shift_zero _ _)
  · suffices T⟦(i + 1 : ℤ)⟧ ≅ T⟦(i : ℤ)⟧.rotate.rotate.rotate
      by
      dsimp
      rw [dist_triangle_iff_of_iso _ this]
      iterate 3 rw [dist_triangle_rot_iff]
    refine' CategoryTheory.shiftAdd _ _ _ ≪≫ _
    refine' Triangle.Iso.ofComponents (iso.refl _) (iso.refl _) (iso.refl _) _ _ _
    · dsimp; simp only [Category.id_comp, Category.comp_id, comp_neg, neg_one_smul]
    · dsimp; simp only [Category.id_comp, Category.comp_id, neg_comp, neg_one_smul]
    · dsimp; simp only [Category.id_comp, Category.comp_id, neg_comp, neg_one_smul]
      simp only [Functor.map_comp, assoc, CategoryTheory.Functor.map_id, comp_id, Functor.map_zsmul,
        Preadditive.zsmul_comp, Preadditive.comp_zsmul, CategoryTheory.Triangulated.Pretriangulated.shiftComm_self, Iso.refl_hom]

end Pretriangulated

end CategoryTheory.Triangulated

