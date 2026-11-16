import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.Functor.Currying
import LiquidTensorExperiment.ForMathlib.ExactSeq
import LiquidTensorExperiment.ForMathlib.PreadditiveYoneda
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

#align_import for_mathlib.derived.homological

namespace CategoryTheory.Triangulated

open CategoryTheory

open CategoryTheory.Limits

open Pretriangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

-- Move me
instance preadditiveYoneda_flip_additive (X : C) :
    (preadditiveYoneda.flip.obj (Opposite.op X)).Additive where
  -- Porting note: `fconstructor` replaced by a structure instance
  map_add := by
    intros
    ext1
    apply Preadditive.comp_add

variable {R : Type _} [Ring R] [Linear R C]

-- Move me
instance linearYoneda_flip_additive (X : C) :
    ((linearYoneda R C).flip.obj (Opposite.op X)).Additive where
  -- Porting note: `fconstructor` replaced by a structure instance
  map_add := by
    intros
    ext1
    dsimp
    apply Preadditive.comp_add

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-- A functor `F` is a *homological* functor if for every distinguished triangle
`A ⟶ B ⟶ C ⟶ A[1]` the sequence `F(A) ⟶ F(B) ⟶ F(C)` is exact. -/
-- Porting note: in Lean 4 the projection `homologicalFunctor.cond` takes `F` implicitly, so it is
-- used below as `homologicalFunctor.cond (F := F)`
class homologicalFunctor {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive] : Prop where
  cond : ∀ (T : Triangle C) (hT : T ∈ (distTriang C)), Exact (F.map T.mor₁) (F.map T.mor₂)

theorem four_term_exactSeq {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : Triangle C) (hT : T ∈ (distTriang C)) :
    ExactSeq A [F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
  by
  apply ExactSeq.cons
  apply homologicalFunctor.cond (F := F) _ hT
  rw [← CategoryTheory.exact_iff_exactSeq]
  apply homologicalFunctor.cond (F := F) _ ((rotate_distinguished_triangle T).mp hT)

theorem five_term_exactSeq {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : Triangle C) (hT : T ∈ (distTriang C)) :
    ExactSeq A [F.map T.invRotate.mor₁, F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
  by
  apply ExactSeq.cons _ _ _ _ (CategoryTheory.Triangulated.four_term_exactSeq F _ hT)
  apply homologicalFunctor.cond (F := F)
  apply inv_rot_of_distTriang _ hT

theorem five_term_exact_seq' {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : Triangle C) (hT : T ∈ (distTriang C)) :
    ExactSeq A [F.map T.mor₁, F.map T.mor₂, F.map T.mor₃, F.map T.rotate.mor₃] :=
  by
  apply ExactSeq.cons
  apply homologicalFunctor.cond (F := F) T hT
  exact CategoryTheory.Triangulated.four_term_exactSeq F T.rotate (rot_of_distTriang _ hT)

theorem complete_distinguished_triangle_morphism' (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ (distTriang C))
    (h₂ : T₂ ∈ (distTriang C)) (f₂ : T₁.obj₂ ⟶ T₂.obj₂) (f₃ : T₁.obj₃ ⟶ T₂.obj₃)
    (w : T₁.mor₂ ≫ f₃ = f₂ ≫ T₂.mor₂) :
    ∃ f₁ : T₁.obj₁ ⟶ T₂.obj₁, T₁.mor₁ ≫ f₂ = f₁ ≫ T₂.mor₁ ∧ T₁.mor₃ ≫ f₁⟦1⟧' = f₃ ≫ T₂.mor₃ :=
  by
  -- Porting note: mathlib4 has this statement as `complete_distinguished_triangle_morphism₁`
  exact complete_distinguished_triangle_morphism₁ T₁ T₂ h₁ h₂ f₂ f₃ w

theorem dist_triang_to_exact_complex (T : Triangle C) (hT : T ∈ (distTriang C)) (X : C)
    (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : ∃ g : X ⟶ T.obj₁, g ≫ T.mor₁ = f :=
  by
  let I : Triangle C := contractibleTriangle X
  obtain ⟨f₁, h₁, h₂⟩ :=
    complete_distinguished_triangle_morphism' I T (contractible_distinguished _) hT f 0
      (by simpa using hf.symm)
  use f₁
  rw [← h₁]
  dsimp
  simp

/-- The functor `Y ↦ Hom(X,Y)` is homological. -/
instance preadditiveYonedaFlipHomological (X : C) :
    homologicalFunctor (preadditiveYoneda.flip.obj (Opposite.op X)) :=
  by
  constructor
  intro T hT
  suffices
    AddMonoidHom.range ((preadditiveYoneda.flip.obj (Opposite.op X)).map T.mor₁) =
      AddMonoidHom.ker ((preadditiveYoneda.flip.obj (Opposite.op X)).map T.mor₂)
    by rwa [AddCommGroupCat.exact_iff]
  apply le_antisymm
  · rintro _ ⟨g : X ⟶ _, rfl⟩
    dsimp
    obtain ⟨e, h1, he⟩ :=
      complete_distinguished_triangle_morphism (contractibleTriangle X) T
        (contractible_distinguished _) hT g (g ≫ T.mor₁) (by dsimp; simp)
    show (g ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [← h1]
    simp
  · rintro (f : X ⟶ _) (hf : f ≫ _ = 0)
    apply dist_triang_to_exact_complex _ hT _ _ hf

/-- The functor `Y ↦ Hom(Y,X)` is homological. -/
instance preadditiveYonedaOpHomological (X : C) :
    homologicalFunctor (preadditiveYoneda.obj X).rightOp :=
  by
  constructor
  intro T hT
  -- Porting note: the `let f := _; let g := _` trick replaced by an explicit statement
  suffices Exact ((preadditiveYoneda.obj X).map T.mor₂.op) ((preadditiveYoneda.obj X).map T.mor₁.op) from
    Abelian.Exact.op _ _ this
  rw [AddCommGroupCat.exact_iff]
  apply le_antisymm
  · rintro _ ⟨q : _ ⟶ X, rfl⟩
    -- Porting note: explicit `show` instead of `change _ ≫ _ = 0; dsimp`
    show T.mor₁ ≫ (T.mor₂ ≫ q) = 0
    have :=
      complete_distinguished_triangle_morphism T.rotate (contractibleTriangle X)
        (rot_of_distTriang _ hT) (contractible_distinguished _) (T.mor₂ ≫ q) q (by dsimp; simp)
    obtain ⟨c, h1, h2⟩ := this
    dsimp at h2 
    simp at h2 
    simp only [← Functor.map_comp] at h2 
    rw [← (shiftFunctor C (1 : ℤ)).map_zero] at h2 
    exact (shiftFunctor C (1 : ℤ)).map_injective h2
  · rintro (q : _ ⟶ X) (hq : _ ≫ _ = 0)
    -- Porting note: explicit `change`s instead of `dsimp`, which unfolds too much in Lean 4
    change ∃ p : T.obj₃ ⟶ X, T.mor₂ ≫ p = q
    change T.mor₁ ≫ q = 0 at hq
    obtain ⟨c, h1, h2⟩ :=
      complete_distinguished_triangle_morphism T (contractibleTriangle X).invRotate hT
        (inv_rot_of_distTriang _ (contractible_distinguished X)) 0 q
        (by simp [hq])
    use c
    rw [h1]
    simp

-- Prove this using the above theorem.
instance linearYonedaFlipHomological (X : C) :
    homologicalFunctor ((linearYoneda R C).flip.obj (Opposite.op X)) :=
  by
  constructor
  intro T hT
  rw [ModuleCat.exact_iff]
  apply le_antisymm
  · rintro _ ⟨g : X ⟶ _, rfl⟩
    dsimp
    obtain ⟨e, h1, he⟩ :=
      complete_distinguished_triangle_morphism (contractibleTriangle X) T
        (contractible_distinguished _) hT g (g ≫ T.mor₁) (by dsimp; simp)
    show (g ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [← h1]
    simp
  · rintro (f : X ⟶ _) (hf : f ≫ _ = 0)
    apply dist_triang_to_exact_complex _ hT _ _ hf

theorem isIso_triangle_hom_of_isIso (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂) [IsIso e.hom₁] [IsIso e.hom₂]
    [IsIso e.hom₃] : IsIso e := by
  -- Porting note: Lean 3 proof replaced by the corresponding mathlib lemma
  exact Triangle.isIso_of_isIsos e inferInstance inferInstance inferInstance

theorem isIso_of_isIso_rotate (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂) [h : IsIso ((rotate C).map e)] :
    IsIso e := by
  haveI : IsIso ((triangleRotation C).functor.map e) := h
  apply CategoryTheory.isIso_of_fully_faithful ((triangleRotation C).functor : Triangle C ⥤ Triangle C)

theorem isIso_of_isIso_inv_rotate (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂)
    [h : IsIso ((invRotate C).map e)] : IsIso e :=
  by
  haveI : IsIso ((triangleRotation C).inverse.map e) := h
  apply CategoryTheory.isIso_of_fully_faithful ((triangleRotation C).inverse : Triangle C ⥤ Triangle C)

theorem isIso_of_isIso_of_isIso (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ (distTriang C))
    (h₂ : T₂ ∈ (distTriang C)) (e : T₁ ⟶ T₂) [IsIso e.hom₁] [IsIso e.hom₃] : IsIso e :=
  by
  -- Porting note: `apply (config := { instances := false })` replaced by a `haveI`
  haveI : IsIso e.hom₂ := by
    suffices h : ∀ W : C, IsIso ((preadditiveYoneda.map e.hom₂).app (Opposite.op W)) by
      exact CategoryTheory.isIso_of_isIso_preadditiveYoneda_map_app C e.hom₂
    intro W
    let Y := preadditiveYoneda.flip.obj (Opposite.op W)
    have H1 := CategoryTheory.Triangulated.five_term_exactSeq Y _ h₁
    have H2 := CategoryTheory.Triangulated.five_term_exactSeq Y _ h₂
    have sq1 := ((invRotate C).map e).comm₁
    apply_fun fun e => Y.map e at sq1 
    simp only [Functor.map_comp] at sq1 
    have sq2 := e.comm₁
    apply_fun fun e => Y.map e at sq2 
    simp only [Functor.map_comp] at sq2 
    have sq3 := e.comm₂
    apply_fun fun e => Y.map e at sq3 
    simp only [Functor.map_comp] at sq3 
    have sq4 := e.comm₃
    apply_fun fun e => Y.map e at sq4 
    simp only [Functor.map_comp] at sq4 
    have : IsIso (Y.map ((invRotate C).map e).hom₁) :=
      by
      dsimp only [invRotate]
      rw [← Functor.comp_map]
      apply Functor.map_isIso
    have : IsIso (Y.map ((invRotate C).map e).hom₂) :=
      by
      dsimp only [invRotate]
      apply Functor.map_isIso
    have : IsIso (Y.map e.hom₃) := by apply Functor.map_isIso
    have : IsIso (Y.map ((shiftFunctor C (1 : ℤ)).map e.hom₁)) :=
      by
      rw [← Functor.comp_map]
      apply Functor.map_isIso
    exact
      @Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ sq1.symm sq2.symm sq3.symm _ _ _ _ _ sq4.symm
        ((CategoryTheory.exact_iff_exactSeq _ _).mpr (H1.extract 0 2))
        ((CategoryTheory.exact_iff_exactSeq _ _).mpr (H1.extract 1 2))
        ((CategoryTheory.exact_iff_exactSeq _ _).mpr (H1.extract 2 3))
        ((CategoryTheory.exact_iff_exactSeq _ _).mpr (H2.extract 0 2))
        ((CategoryTheory.exact_iff_exactSeq _ _).mpr (H2.extract 1 2))
        ((CategoryTheory.exact_iff_exactSeq _ _).mpr (H2.extract 2 3)) _ _ _ _
  exact isIso_triangle_hom_of_isIso T₁ T₂ e

theorem isIso_of_isIso_of_is_iso' (T₁ T₂ : Triangle C) (h₁ : T₁ ∈ (distTriang C))
    (h₂ : T₂ ∈ (distTriang C)) (e : T₁ ⟶ T₂) [h1 : IsIso e.hom₁] [h2 : IsIso e.hom₂] : IsIso e :=
  by
  suffices IsIso ((rotate C).map e) by skip; apply CategoryTheory.Triangulated.isIso_of_isIso_rotate
  haveI : IsIso ((rotate C).map e).hom₁ := h2
  have : IsIso ((rotate C).map e).hom₃ := by apply Functor.map_isIso
  apply CategoryTheory.Triangulated.isIso_of_isIso_of_isIso
  all_goals erw [← rotate_distinguished_triangle]; assumption

instance isIso_hom₁ (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₁ :=
  -- Porting note: proof rewritten using `congrArg`
  ⟨⟨(inv e).hom₁, congrArg TriangleMorphism.hom₁ (IsIso.hom_inv_id e),
    congrArg TriangleMorphism.hom₁ (IsIso.inv_hom_id e)⟩⟩

instance isIso_hom₂ (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₂ :=
  -- Porting note: proof rewritten using `congrArg`
  ⟨⟨(inv e).hom₂, congrArg TriangleMorphism.hom₂ (IsIso.hom_inv_id e),
    congrArg TriangleMorphism.hom₂ (IsIso.inv_hom_id e)⟩⟩

instance isIso_hom₃ (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₃ :=
  -- Porting note: proof rewritten using `congrArg`
  ⟨⟨(inv e).hom₃, congrArg TriangleMorphism.hom₃ (IsIso.hom_inv_id e),
    congrArg TriangleMorphism.hom₃ (IsIso.inv_hom_id e)⟩⟩

theorem homological_of_exists_aux {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (T₁ T₂ : Triangle C) (e : T₁ ⟶ T₂) [IsIso e] (H : Exact (F.map T₁.mor₁) (F.map T₁.mor₂)) :
    Exact (F.map T₂.mor₁) (F.map T₂.mor₂) :=
  by
  have : T₂.mor₁ = inv e.hom₁ ≫ T₁.mor₁ ≫ e.hom₂ :=
    by
    rw [IsIso.eq_inv_comp]
    exact e.comm₁.symm
  rw [this]; clear this
  have : T₂.mor₂ = inv e.hom₂ ≫ T₁.mor₂ ≫ e.hom₃ :=
    by
    rw [IsIso.eq_inv_comp]
    exact e.comm₂.symm
  rw [this]; clear this
  simp only [F.map_comp, F.map_inv]
  simp only [exact_iso_comp]
  simp only [← Category.assoc]
  simp only [exact_comp_iso]
  change Exact (_ ≫ (CategoryTheory.asIso (F.map e.hom₂)).hom) ((CategoryTheory.asIso (F.map e.hom₂)).inv ≫ _)
  rwa [exact_comp_hom_inv_comp_iff]

theorem homologicalOfExists {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (X Y : C) (f : X ⟶ Y),
        ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk f g h ∈ (distTriang C)),
          Exact (F.map f) (F.map g)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.obj₁ T.obj₂ T.mor₁
  obtain ⟨Z, g, h, hT', hE⟩ := h
  let T' := Triangle.mk T.mor₁ g h
  obtain ⟨e, h1, h2⟩ := complete_distinguished_triangle_morphism T' T hT' hT (𝟙 _) (𝟙 _) (by simp)
  let E : T' ⟶ T := ⟨𝟙 _, 𝟙 _, e, by simp, h1, h2⟩
  have : IsIso E := by apply CategoryTheory.Triangulated.isIso_of_isIso_of_is_iso' _ _ hT' hT
  exact homological_of_exists_aux F T' T E hE

theorem homologicalOfRotate {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (T : Triangle C) (hT : T ∈ (distTriang C)),
        Exact (F.map T.rotate.mor₁) (F.map T.rotate.mor₂)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.invRotate (inv_rot_of_distTriang T hT)
  let E : T.invRotate.rotate ≅ T := invRotCompRot.app _
  apply homological_of_exists_aux _ _ _ E.hom
  assumption'

theorem homologicalOfInvRotate {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (T : Triangle C) (hT : T ∈ (distTriang C)),
        Exact (F.map T.invRotate.mor₁) (F.map T.invRotate.mor₂)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.rotate (rot_of_distTriang T hT)
  let E : T.rotate.invRotate ≅ T := (rotCompInvRot.app _).symm
  apply homological_of_exists_aux _ _ _ E.hom
  assumption'

theorem homologicalOfNatIso {A : Type _} [Category A] [Abelian A] (F G : C ⥤ A) [F.Additive]
    [G.Additive] [homologicalFunctor F] (e : F ≅ G) : homologicalFunctor G :=
  by
  constructor
  intro T hT
  have h₁ := e.hom.naturality T.mor₁
  have h₂ := e.hom.naturality T.mor₂
  rw [← IsIso.inv_comp_eq] at h₁ h₂ 
  rw [← h₁, ← h₂, exact_iso_comp, ← Category.assoc, exact_comp_iso]
  let E := CategoryTheory.asIso (e.hom.app T.obj₂)
  change Exact (F.map T.mor₁ ≫ E.hom) (E.inv ≫ _)
  have : Exact (F.map T.mor₁) (F.map T.mor₂) := by apply homologicalFunctor.cond (F := F) _ hT
  rwa [exact_comp_hom_inv_comp_iff]

end CategoryTheory.Triangulated

