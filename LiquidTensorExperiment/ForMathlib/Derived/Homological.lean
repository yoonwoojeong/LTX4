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
    (preadditiveYoneda.flip.obj (Opposite.op X)).Additive := by fconstructor; dsimp; intros; ext1;
  apply Preadditive.comp_add

variable {R : Type _} [Ring R] [Linear R C]

-- Move me
instance linearYoneda_flip_additive (X : C) :
    ((linearYoneda R C).flip.obj (Opposite.op X)).Additive := by fconstructor; dsimp; intros; ext1;
  dsimp; apply Preadditive.comp_add

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [pretriangulated C]

/- ./././Mathport/Syntax/Translate/Command.lean:394:30: infer kinds are unsupported in Lean 4: #[`cond] [] -/
/-- A functor `F` is a *homological* functor if for every distinguished triangle
`A ⟶ B ⟶ C ⟶ A[1]` the sequence `F(A) ⟶ F(B) ⟶ F(C)` is exact. -/
class homologicalFunctor {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive] : Prop where
  cond : ∀ (T : triangle C) (hT : T ∈ (dist_triang C)), Exact (F.map T.mor₁) (F.map T.mor₂)

theorem four_term_exactSeq {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : triangle C) (hT : T ∈ (dist_triang C)) :
    ExactSeq A [F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
  by
  apply ExactSeq.cons
  apply homologicalFunctor.cond F _ hT
  rw [← CategoryTheory.exact_iff_exactSeq]
  apply homologicalFunctor.cond F _ ((rotate_distinguished_triangle T).mp hT)

theorem five_term_exactSeq {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : triangle C) (hT : T ∈ (dist_triang C)) :
    ExactSeq A [F.map T.invRotate.mor₁, F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
  by
  apply ExactSeq.cons _ _ _ _ (CategoryTheory.Triangulated.four_term_exactSeq F _ hT)
  apply homologicalFunctor.cond F
  apply CategoryTheory.Pretriangulated.inv_rot_of_distTriang _ _ hT

theorem five_term_exact_seq' {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : triangle C) (hT : T ∈ (dist_triang C)) :
    ExactSeq A [F.map T.mor₁, F.map T.mor₂, F.map T.mor₃, F.map T.rotate.mor₃] :=
  by
  apply ExactSeq.cons
  apply homologicalFunctor.cond F T hT
  exact CategoryTheory.Triangulated.four_term_exactSeq F T.rotate (CategoryTheory.Pretriangulated.rot_of_distTriang _ _ hT)

theorem complete_distinguished_triangle_morphism' (T₁ T₂ : triangle C) (h₁ : T₁ ∈ (dist_triang C))
    (h₂ : T₂ ∈ (dist_triang C)) (f₂ : T₁.obj₂ ⟶ T₂.obj₂) (f₃ : T₁.obj₃ ⟶ T₂.obj₃)
    (w : T₁.mor₂ ≫ f₃ = f₂ ≫ T₂.mor₂) :
    ∃ f₁ : T₁.obj₁ ⟶ T₂.obj₁, T₁.mor₁ ≫ f₂ = f₁ ≫ T₂.mor₁ ∧ T₁.mor₃ ≫ f₁⟦1⟧' = f₃ ≫ T₂.mor₃ :=
  by
  let T₁' := T₁.rotate
  let T₂' := T₂.rotate
  obtain ⟨g, h1, h2⟩ := complete_distinguished_triangle_morphism T₁' T₂' _ _ f₂ f₃ w
  use(CategoryTheory.shiftShiftNeg _ _).inv ≫ g⟦(-1 : ℤ)⟧' ≫ (CategoryTheory.shiftShiftNeg _ _).hom
  constructor
  · dsimp at h2 
    apply_fun fun e => -(shift_functor C (-1 : ℤ)).map e ≫ (CategoryTheory.shiftShiftNeg _ _).hom at h2 
    simp only [Category.assoc, Functor.map_comp] at h2 ⊢
    rw [Iso.eq_inv_comp]
    convert h2 using 1
    · simp
    · simp
  · convert h1 using 1
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    rw [shift_neg_shift']
    simp only [Category.assoc, ← Functor.mapIso_inv, ← Functor.mapIso_hom]
    have : (shift_functor C 1).mapIso (CategoryTheory.shiftShiftNeg T₂.obj₁ 1) = CategoryTheory.shiftNegShift T₂'.obj₃ 1 := by
      dsimp; simp;
    rw [this]; clear this
    have :
      (shift_functor C 1).mapIso (CategoryTheory.shiftShiftNeg T₁.obj₁ (1 : ℤ)) =
        CategoryTheory.shiftNegShift ((shift_functor C (1 : ℤ)).obj T₁.obj₁) (1 : ℤ) :=
      by simp;
    rw [this]; clear this
    simp only [Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.id_comp, Category.comp_id]
  · rw [← rotate_distinguished_triangle]; exact h₁
  · rw [← rotate_distinguished_triangle]; exact h₂

theorem dist_triang_to_exact_complex (T : triangle C) (hT : T ∈ (dist_triang C)) (X : C)
    (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : ∃ g : X ⟶ T.obj₁, g ≫ T.mor₁ = f :=
  by
  let I : triangle C := CategoryTheory.Pretriangulated.contractibleTriangle C X
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
    AddMonoidHom.range ((preadditive_yoneda.flip.obj (Opposite.op X)).map T.mor₁) =
      AddMonoidHom.ker ((preadditive_yoneda.flip.obj (Opposite.op X)).map T.mor₂)
    by rwa [AddCommGroupCat.exact_iff]
  apply le_antisymm
  · rintro _ ⟨g : X ⟶ _, rfl⟩
    dsimp
    obtain ⟨e, h1, he⟩ :=
      complete_distinguished_triangle_morphism (CategoryTheory.Pretriangulated.contractibleTriangle _ X) T
        (contractible_distinguished _) hT g (g ≫ T.mor₁) (by dsimp; simp)
    dsimp at he 
    simp only [zero_comp] at he 
    change _ = _
    simp [← h1]
  · rintro (f : X ⟶ _) (hf : f ≫ _ = 0)
    apply dist_triang_to_exact_complex _ hT _ _ hf

/-- The functor `Y ↦ Hom(Y,X)` is homological. -/
instance preadditiveYonedaOpHomological (X : C) :
    homologicalFunctor (preadditiveYoneda.obj X).rightOp :=
  by
  constructor
  intro T hT
  dsimp
  let f := _; let g := _; show exact f g
  suffices exact g.unop f.unop by rw [← f.op_unop]; rw [← g.op_unop]; apply this.op
  rw [AddCommGroupCat.exact_iff]
  apply le_antisymm
  · rintro _ ⟨q : _ ⟶ X, rfl⟩
    change _ ≫ _ = 0
    dsimp
    have :=
      complete_distinguished_triangle_morphism T.rotate (CategoryTheory.Pretriangulated.contractibleTriangle _ X) _
        (contractible_distinguished _) (T.mor₂ ≫ q) q (by dsimp; simp)
    swap; rwa [← rotate_distinguished_triangle]
    obtain ⟨c, h1, h2⟩ := this
    dsimp at h2 
    simp at h2 
    simp only [← Functor.map_comp] at h2 
    rw [← (shift_functor C (1 : ℤ)).map_zero] at h2 
    exact (shift_functor C (1 : ℤ)).map_injective h2
  · rintro (q : _ ⟶ X) (hq : _ ≫ _ = 0)
    change ∃ p, _
    dsimp at hq ⊢
    obtain ⟨c, h1, h2⟩ :=
      complete_distinguished_triangle_morphism T (CategoryTheory.Pretriangulated.contractibleTriangle _ X).invRotate hT _ 0 q
        (by simp [hq])
    · use c
      simp only [h1, Triangle.invRotate_mor₂, contractible_triangle_mor₁]
      erw [Category.comp_id]
    · apply CategoryTheory.Pretriangulated.inv_rot_of_distTriang; apply contractible_distinguished

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
      complete_distinguished_triangle_morphism (CategoryTheory.Pretriangulated.contractibleTriangle _ X) T
        (contractible_distinguished _) hT g (g ≫ T.mor₁) (by dsimp; simp)
    dsimp at he 
    simp only [zero_comp] at he 
    simp [← h1]
  · rintro (f : X ⟶ _) (hf : f ≫ _ = 0)
    apply dist_triang_to_exact_complex _ hT _ _ hf

theorem isIso_triangle_hom_of_isIso (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e.hom₁] [IsIso e.hom₂]
    [IsIso e.hom₃] : IsIso e := by
  constructor
  refine' ⟨⟨inv e.hom₁, inv e.hom₂, inv e.hom₃, _, _⟩, _, _⟩
  · dsimp
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, e.comm₁]
  · dsimp
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, e.comm₂]
  · ext <;> dsimp <;> simp
  · ext <;> dsimp <;> simp

theorem isIso_of_isIso_rotate (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [h : IsIso ((rotate C).map e)] :
    IsIso e := by
  haveI : is_iso ((CategoryTheory.Pretriangulated.triangleRotation C).Functor.map e) := h
  apply CategoryTheory.isIso_of_fully_faithful ((CategoryTheory.Pretriangulated.triangleRotation C).Functor : triangle C ⥤ triangle C)

theorem isIso_of_isIso_inv_rotate (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂)
    [h : IsIso ((inv_rotate C).map e)] : IsIso e :=
  by
  haveI : is_iso ((CategoryTheory.Pretriangulated.triangleRotation C).inverse.map e) := h
  apply CategoryTheory.isIso_of_fully_faithful ((CategoryTheory.Pretriangulated.triangleRotation C).inverse : triangle C ⥤ triangle C)

theorem isIso_of_isIso_of_isIso (T₁ T₂ : triangle C) (h₁ : T₁ ∈ (dist_triang C))
    (h₂ : T₂ ∈ (dist_triang C)) (e : T₁ ⟶ T₂) [IsIso e.hom₁] [IsIso e.hom₃] : IsIso e :=
  by
  apply (config := { instances := false }) CategoryTheory.Triangulated.isIso_triangle_hom_of_isIso
  any_goals infer_instance
  infer_instance
  apply (config := { instances := false }) CategoryTheory.isIso_of_isIso_preadditiveYoneda_map_app
  swap; infer_instance
  intro W
  let Y := preadditive_yoneda.flip.obj (Opposite.op W)
  have H1 := CategoryTheory.Triangulated.five_term_exactSeq Y _ h₁
  have H2 := CategoryTheory.Triangulated.five_term_exactSeq Y _ h₂
  have sq1 := e.invRotate.comm₁
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
  have : is_iso (Y.map (triangulated.TriangleMorphism.invRotate e).hom₁) :=
    by
    dsimp only [triangulated.TriangleMorphism.invRotate]
    rw [← Functor.comp_map]
    apply Functor.map_isIso
  have : is_iso (Y.map (triangulated.TriangleMorphism.invRotate e).hom₂) :=
    by
    dsimp only [triangulated.TriangleMorphism.invRotate]
    apply Functor.map_isIso
  have : is_iso (Y.map e.hom₃) := by apply Functor.map_isIso
  have : is_iso (Y.map ((shift_functor C (1 : ℤ)).map e.hom₁)) :=
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

theorem isIso_of_isIso_of_is_iso' (T₁ T₂ : triangle C) (h₁ : T₁ ∈ (dist_triang C))
    (h₂ : T₂ ∈ (dist_triang C)) (e : T₁ ⟶ T₂) [h1 : IsIso e.hom₁] [h2 : IsIso e.hom₂] : IsIso e :=
  by
  suffices is_iso ((rotate C).map e) by skip; apply CategoryTheory.Triangulated.isIso_of_isIso_rotate
  haveI : is_iso ((rotate C).map e).hom₁ := h2
  have : is_iso ((rotate C).map e).hom₃ := by apply Functor.map_isIso
  apply CategoryTheory.Triangulated.isIso_of_isIso_of_isIso
  all_goals erw [← rotate_distinguished_triangle]; assumption

instance isIso_hom₁ (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₁ :=
  ⟨⟨(inv e).hom₁, show (e ≫ inv e).hom₁ = _ by simpa only [IsIso.hom_inv_id],
      show (inv e ≫ e).hom₁ = _ by simpa only [IsIso.inv_hom_id]⟩⟩

instance isIso_hom₂ (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₂ :=
  ⟨⟨(inv e).hom₂, show (e ≫ inv e).hom₂ = _ by simpa only [IsIso.hom_inv_id],
      show (inv e ≫ e).hom₂ = _ by simpa only [IsIso.inv_hom_id]⟩⟩

instance isIso_hom₃ (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₃ :=
  ⟨⟨(inv e).hom₃, show (e ≫ inv e).hom₃ = _ by simpa only [IsIso.hom_inv_id],
      show (inv e ≫ e).hom₃ = _ by simpa only [IsIso.inv_hom_id]⟩⟩

theorem homological_of_exists_aux {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] (H : Exact (F.map T₁.mor₁) (F.map T₁.mor₂)) :
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
  change exact (_ ≫ (CategoryTheory.asIso (F.map e.hom₂)).hom) ((CategoryTheory.asIso (F.map e.hom₂)).inv ≫ _)
  rwa [exact_comp_hom_inv_comp_iff]

theorem homologicalOfExists {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (X Y : C) (f : X ⟶ Y),
        ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : Triangle.mk _ f g h ∈ (dist_triang C)),
          Exact (F.map f) (F.map g)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.obj₁ T.obj₂ T.mor₁
  obtain ⟨Z, g, h, hT', hE⟩ := h
  let T' := Triangle.mk _ T.mor₁ g h
  obtain ⟨e, h1, h2⟩ := complete_distinguished_triangle_morphism T' T hT' hT (𝟙 _) (𝟙 _) (by simp)
  let E : T' ⟶ T := ⟨𝟙 _, 𝟙 _, e, by simp, h1⟩
  have : is_iso E := by apply CategoryTheory.Triangulated.isIso_of_isIso_of_is_iso' _ _ hT' hT
  exact homological_of_exists_aux F T' T E hE

theorem homologicalOfRotate {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (T : triangle C) (hT : T ∈ (dist_triang C)),
        Exact (F.map T.rotate.mor₁) (F.map T.rotate.mor₂)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.inv_rotate (CategoryTheory.Pretriangulated.inv_rot_of_distTriang C T hT)
  let E : T.inv_rotate.rotate ≅ T := inv_rot_comp_rot.app _
  apply homological_of_exists_aux _ _ _ E.hom
  assumption'

theorem homologicalOfInvRotate {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (T : triangle C) (hT : T ∈ (dist_triang C)),
        Exact (F.map T.invRotate.mor₁) (F.map T.invRotate.mor₂)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.rotate (CategoryTheory.Pretriangulated.rot_of_distTriang C T hT)
  let E : T.rotate.invRotate ≅ T := (rot_comp_inv_rot.app _).symm
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
  change exact (F.map T.mor₁ ≫ E.hom) (E.inv ≫ _)
  have : exact (F.map T.mor₁) (F.map T.mor₂) := by apply homologicalFunctor.cond F _ hT
  rwa [exact_comp_hom_inv_comp_iff]

end CategoryTheory.Triangulated

