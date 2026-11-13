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
  apply preadditive.comp_add

variable {R : Type _} [Ring R] [Linear R C]

-- Move me
instance linearYoneda_flip_additive (X : C) :
    ((linearYoneda R C).flip.obj (Opposite.op X)).Additive := by fconstructor; dsimp; intros; ext1;
  dsimp; apply preadditive.comp_add

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
  apply exact_seq.cons
  apply homological_functor.cond F _ hT
  rw [← exact_iff_exact_seq]
  apply homological_functor.cond F _ ((rotate_distinguished_triangle T).mp hT)

theorem five_term_exactSeq {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : triangle C) (hT : T ∈ (dist_triang C)) :
    ExactSeq A [F.map T.invRotate.mor₁, F.map T.mor₁, F.map T.mor₂, F.map T.mor₃] :=
  by
  apply exact_seq.cons _ _ _ _ (four_term_exact_seq F _ hT)
  apply homological_functor.cond F
  apply inv_rot_of_dist_triangle _ _ hT

theorem five_term_exact_seq' {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    [homologicalFunctor F] (T : triangle C) (hT : T ∈ (dist_triang C)) :
    ExactSeq A [F.map T.mor₁, F.map T.mor₂, F.map T.mor₃, F.map T.rotate.mor₃] :=
  by
  apply exact_seq.cons
  apply homological_functor.cond F T hT
  exact four_term_exact_seq F T.rotate (rot_of_dist_triangle _ _ hT)

theorem complete_distinguished_triangle_morphism' (T₁ T₂ : triangle C) (h₁ : T₁ ∈ (dist_triang C))
    (h₂ : T₂ ∈ (dist_triang C)) (f₂ : T₁.obj₂ ⟶ T₂.obj₂) (f₃ : T₁.obj₃ ⟶ T₂.obj₃)
    (w : T₁.mor₂ ≫ f₃ = f₂ ≫ T₂.mor₂) :
    ∃ f₁ : T₁.obj₁ ⟶ T₂.obj₁, T₁.mor₁ ≫ f₂ = f₁ ≫ T₂.mor₁ ∧ T₁.mor₃ ≫ f₁⟦1⟧' = f₃ ≫ T₂.mor₃ :=
  by
  let T₁' := T₁.rotate
  let T₂' := T₂.rotate
  obtain ⟨g, h1, h2⟩ := complete_distinguished_triangle_morphism T₁' T₂' _ _ f₂ f₃ w
  use(shift_shift_neg _ _).inv ≫ g⟦(-1 : ℤ)⟧' ≫ (shift_shift_neg _ _).Hom
  constructor
  · dsimp at h2 
    apply_fun fun e => -(shift_functor C (-1 : ℤ)).map e ≫ (shift_shift_neg _ _).Hom at h2 
    simp only [category.assoc, functor.map_comp] at h2 ⊢
    rw [iso.eq_inv_comp]
    convert h2 using 1
    · simp
    · simp
  · convert h1 using 1
    congr 1
    simp only [functor.map_comp, category.assoc]
    rw [shift_neg_shift']
    simp only [category.assoc, ← functor.map_iso_inv, ← functor.map_iso_hom]
    have : (shift_functor C 1).mapIso (shift_shift_neg T₂.obj₁ 1) = shift_neg_shift T₂'.obj₃ 1 := by
      dsimp; simp;
    rw [this]; clear this
    have :
      (shift_functor C 1).mapIso (shift_shift_neg T₁.obj₁ (1 : ℤ)) =
        shift_neg_shift ((shift_functor C (1 : ℤ)).obj T₁.obj₁) (1 : ℤ) :=
      by simp;
    rw [this]; clear this
    simp only [iso.inv_hom_id, iso.inv_hom_id_assoc, category.id_comp, category.comp_id]
  · rw [← rotate_distinguished_triangle]; exact h₁
  · rw [← rotate_distinguished_triangle]; exact h₂

theorem dist_triang_to_exact_complex (T : triangle C) (hT : T ∈ (dist_triang C)) (X : C)
    (f : X ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) : ∃ g : X ⟶ T.obj₁, g ≫ T.mor₁ = f :=
  by
  let I : triangle C := contractible_triangle C X
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
      complete_distinguished_triangle_morphism (contractible_triangle _ X) T
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
      complete_distinguished_triangle_morphism T.rotate (contractible_triangle _ X) _
        (contractible_distinguished _) (T.mor₂ ≫ q) q (by dsimp; simp)
    swap; rwa [← rotate_distinguished_triangle]
    obtain ⟨c, h1, h2⟩ := this
    dsimp at h2 
    simp at h2 
    simp only [← functor.map_comp] at h2 
    rw [← (shift_functor C (1 : ℤ)).map_zero] at h2 
    exact (shift_functor C (1 : ℤ)).map_injective h2
  · rintro (q : _ ⟶ X) (hq : _ ≫ _ = 0)
    change ∃ p, _
    dsimp at hq ⊢
    obtain ⟨c, h1, h2⟩ :=
      complete_distinguished_triangle_morphism T (contractible_triangle _ X).invRotate hT _ 0 q
        (by simp [hq])
    · use c
      simp only [h1, triangle.inv_rotate_mor₂, contractible_triangle_mor₁]
      erw [category.comp_id]
    · apply inv_rot_of_dist_triangle; apply contractible_distinguished

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
      complete_distinguished_triangle_morphism (contractible_triangle _ X) T
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
    rw [is_iso.comp_inv_eq, category.assoc, is_iso.eq_inv_comp, e.comm₁]
  · dsimp
    rw [is_iso.comp_inv_eq, category.assoc, is_iso.eq_inv_comp, e.comm₂]
  · ext <;> dsimp <;> simp
  · ext <;> dsimp <;> simp

theorem isIso_of_isIso_rotate (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [h : IsIso ((rotate C).map e)] :
    IsIso e := by
  haveI : is_iso ((triangle_rotation C).Functor.map e) := h
  apply is_iso_of_fully_faithful ((triangle_rotation C).Functor : triangle C ⥤ triangle C)

theorem isIso_of_isIso_inv_rotate (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂)
    [h : IsIso ((inv_rotate C).map e)] : IsIso e :=
  by
  haveI : is_iso ((triangle_rotation C).inverse.map e) := h
  apply is_iso_of_fully_faithful ((triangle_rotation C).inverse : triangle C ⥤ triangle C)

theorem isIso_of_isIso_of_isIso (T₁ T₂ : triangle C) (h₁ : T₁ ∈ (dist_triang C))
    (h₂ : T₂ ∈ (dist_triang C)) (e : T₁ ⟶ T₂) [IsIso e.hom₁] [IsIso e.hom₃] : IsIso e :=
  by
  apply (config := { instances := false }) is_iso_triangle_hom_of_is_iso
  any_goals infer_instance
  infer_instance
  apply (config := { instances := false }) is_iso_of_is_iso_preadditive_yoneda_map_app
  swap; infer_instance
  intro W
  let Y := preadditive_yoneda.flip.obj (Opposite.op W)
  have H1 := five_term_exact_seq Y _ h₁
  have H2 := five_term_exact_seq Y _ h₂
  have sq1 := e.inv_rotate.comm₁
  apply_fun fun e => Y.map e at sq1 
  simp only [functor.map_comp] at sq1 
  have sq2 := e.comm₁
  apply_fun fun e => Y.map e at sq2 
  simp only [functor.map_comp] at sq2 
  have sq3 := e.comm₂
  apply_fun fun e => Y.map e at sq3 
  simp only [functor.map_comp] at sq3 
  have sq4 := e.comm₃
  apply_fun fun e => Y.map e at sq4 
  simp only [functor.map_comp] at sq4 
  have : is_iso (Y.map (triangulated.triangle_morphism.inv_rotate e).hom₁) :=
    by
    dsimp only [triangulated.triangle_morphism.inv_rotate]
    rw [← functor.comp_map]
    apply functor.map_is_iso
  have : is_iso (Y.map (triangulated.triangle_morphism.inv_rotate e).hom₂) :=
    by
    dsimp only [triangulated.triangle_morphism.inv_rotate]
    apply functor.map_is_iso
  have : is_iso (Y.map e.hom₃) := by apply functor.map_is_iso
  have : is_iso (Y.map ((shift_functor C (1 : ℤ)).map e.hom₁)) :=
    by
    rw [← functor.comp_map]
    apply functor.map_is_iso
  exact
    @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ sq1.symm sq2.symm sq3.symm _ _ _ _ _ sq4.symm
      ((exact_iff_exact_seq _ _).mpr (H1.extract 0 2))
      ((exact_iff_exact_seq _ _).mpr (H1.extract 1 2))
      ((exact_iff_exact_seq _ _).mpr (H1.extract 2 3))
      ((exact_iff_exact_seq _ _).mpr (H2.extract 0 2))
      ((exact_iff_exact_seq _ _).mpr (H2.extract 1 2))
      ((exact_iff_exact_seq _ _).mpr (H2.extract 2 3)) _ _ _ _

theorem isIso_of_isIso_of_is_iso' (T₁ T₂ : triangle C) (h₁ : T₁ ∈ (dist_triang C))
    (h₂ : T₂ ∈ (dist_triang C)) (e : T₁ ⟶ T₂) [h1 : IsIso e.hom₁] [h2 : IsIso e.hom₂] : IsIso e :=
  by
  suffices is_iso ((rotate C).map e) by skip; apply is_iso_of_is_iso_rotate
  haveI : is_iso ((rotate C).map e).hom₁ := h2
  have : is_iso ((rotate C).map e).hom₃ := by apply functor.map_is_iso
  apply is_iso_of_is_iso_of_is_iso
  all_goals erw [← rotate_distinguished_triangle]; assumption

instance isIso_hom₁ (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₁ :=
  ⟨⟨(inv e).hom₁, show (e ≫ inv e).hom₁ = _ by simpa only [is_iso.hom_inv_id],
      show (inv e ≫ e).hom₁ = _ by simpa only [is_iso.inv_hom_id]⟩⟩

instance isIso_hom₂ (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₂ :=
  ⟨⟨(inv e).hom₂, show (e ≫ inv e).hom₂ = _ by simpa only [is_iso.hom_inv_id],
      show (inv e ≫ e).hom₂ = _ by simpa only [is_iso.inv_hom_id]⟩⟩

instance isIso_hom₃ (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] : IsIso e.hom₃ :=
  ⟨⟨(inv e).hom₃, show (e ≫ inv e).hom₃ = _ by simpa only [is_iso.hom_inv_id],
      show (inv e ≫ e).hom₃ = _ by simpa only [is_iso.inv_hom_id]⟩⟩

theorem homological_of_exists_aux {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (T₁ T₂ : triangle C) (e : T₁ ⟶ T₂) [IsIso e] (H : Exact (F.map T₁.mor₁) (F.map T₁.mor₂)) :
    Exact (F.map T₂.mor₁) (F.map T₂.mor₂) :=
  by
  have : T₂.mor₁ = inv e.hom₁ ≫ T₁.mor₁ ≫ e.hom₂ :=
    by
    rw [is_iso.eq_inv_comp]
    exact e.comm₁.symm
  rw [this]; clear this
  have : T₂.mor₂ = inv e.hom₂ ≫ T₁.mor₂ ≫ e.hom₃ :=
    by
    rw [is_iso.eq_inv_comp]
    exact e.comm₂.symm
  rw [this]; clear this
  simp only [F.map_comp, F.map_inv]
  simp only [exact_iso_comp]
  simp only [← category.assoc]
  simp only [exact_comp_iso]
  change exact (_ ≫ (as_iso (F.map e.hom₂)).Hom) ((as_iso (F.map e.hom₂)).inv ≫ _)
  rwa [exact_comp_hom_inv_comp_iff]

theorem homologicalOfExists {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (X Y : C) (f : X ⟶ Y),
        ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧) (hT : triangle.mk _ f g h ∈ (dist_triang C)),
          Exact (F.map f) (F.map g)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.obj₁ T.obj₂ T.mor₁
  obtain ⟨Z, g, h, hT', hE⟩ := h
  let T' := triangle.mk _ T.mor₁ g h
  obtain ⟨e, h1, h2⟩ := complete_distinguished_triangle_morphism T' T hT' hT (𝟙 _) (𝟙 _) (by simp)
  let E : T' ⟶ T := ⟨𝟙 _, 𝟙 _, e, by simp, h1⟩
  have : is_iso E := by apply is_iso_of_is_iso_of_is_iso' _ _ hT' hT
  exact homological_of_exists_aux F T' T E hE

theorem homologicalOfRotate {A : Type _} [Category A] [Abelian A] (F : C ⥤ A) [F.Additive]
    (h :
      ∀ (T : triangle C) (hT : T ∈ (dist_triang C)),
        Exact (F.map T.rotate.mor₁) (F.map T.rotate.mor₂)) :
    homologicalFunctor F := by
  constructor
  intro T hT
  specialize h T.inv_rotate (inv_rot_of_dist_triangle C T hT)
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
  specialize h T.rotate (rot_of_dist_triangle C T hT)
  let E : T.rotate.inv_rotate ≅ T := (rot_comp_inv_rot.app _).symm
  apply homological_of_exists_aux _ _ _ E.hom
  assumption'

theorem homologicalOfNatIso {A : Type _} [Category A] [Abelian A] (F G : C ⥤ A) [F.Additive]
    [G.Additive] [homologicalFunctor F] (e : F ≅ G) : homologicalFunctor G :=
  by
  constructor
  intro T hT
  have h₁ := e.hom.naturality T.mor₁
  have h₂ := e.hom.naturality T.mor₂
  rw [← is_iso.inv_comp_eq] at h₁ h₂ 
  rw [← h₁, ← h₂, exact_iso_comp, ← category.assoc, exact_comp_iso]
  let E := as_iso (e.hom.app T.obj₂)
  change exact (F.map T.mor₁ ≫ E.hom) (E.inv ≫ _)
  have : exact (F.map T.mor₁) (F.map T.mor₂) := by apply homological_functor.cond F _ hT
  rwa [exact_comp_hom_inv_comp_iff]

end CategoryTheory.Triangulated

