import LiquidTensorExperiment.ForMathlib.MappingCone
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

#align_import for_mathlib.homotopy_category_pretriangulated

noncomputable section

universe v u

open scoped Classical ZeroObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

open HomologicalComplex

namespace HomotopyCategory

variable (V : Type u) [Category.{v} V] [Abelian V]

local notation "𝒦" => HomotopyCategory V (ComplexShape.up ℤ)

def distinguishedTriangles : Set (triangle 𝒦) := fun T =>
  ∃ (X Y Z : CochainComplex V ℤ) (f : X ⟶ Y) (g : Y ⟶ Z) (h : _),
    Nonempty (T ≅ triangleₕOfTermwiseSplit f g h)

variable {V}

local notation "𝒦" => HomotopyCategory V (ComplexShape.up ℤ)

theorem mem_distinguished_of_iso {T₁ T₂ : triangle 𝒦} (e : T₁ ≅ T₂)
    (hT : T₁ ∈ distinguishedTriangles V) : T₂ ∈ distinguishedTriangles V :=
  ⟨_, _, _, _, _, _,
    ⟨e.symm ≪≫ hT.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some⟩⟩

theorem mem_distinguished_iff_exists_iso_cone (T : triangle 𝒦) :
    T ∈ distinguishedTriangles V ↔
      ∃ (X Y : _) (f : X ⟶ Y), Nonempty (T ≅ (neg₃Functor _).obj (cone.triangleₕ f)) :=
  by
  constructor
  · rintro ⟨X, Y, Z, f, g, h, ⟨e⟩⟩
    refine' ⟨_, _, f, ⟨e ≪≫ iso_cone_of_termwise_split f g h⟩⟩
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine' ⟨_, _, _, _, _, _, ⟨e ≪≫ iso_termwise_split_of_cone f⟩⟩

theorem triangleₕOfTermwiseSplit_mem_distinguishedTriangles (X Y Z : CochainComplex V ℤ) (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : ∀ i, Splitting (f.f i) (g.f i)) :
    triangleₕOfTermwiseSplit f g h ∈ distinguishedTriangles V :=
  ⟨_, _, _, _, _, _, ⟨Iso.refl _⟩⟩

theorem cone_triangleₕ_mem_distinguishedTriangles (X Y : CochainComplex V ℤ) (f : X ⟶ Y) :
    (neg₃Functor _).obj (cone.triangleₕ f) ∈ distinguishedTriangles V :=
  (mem_distinguished_iff_exists_iso_cone _).mpr ⟨_, _, _, ⟨Iso.refl _⟩⟩

theorem rotate_mem_distinguishedTriangles (T : triangle 𝒦) (h : T ∈ distinguishedTriangles V) :
    T.rotate ∈ distinguishedTriangles V :=
  by
  obtain ⟨X, Y, f, ⟨e⟩⟩ := (mem_distinguished_iff_exists_iso_cone _).mp h
  exact
    ⟨_, _, _, _, _, _,
      ⟨(rotate _).mapIso e ≪≫
          neg₃_rotate.app _ ≪≫
            (triangle.nonneg_rotate_iso _).symm ≪≫
              (HomotopyCategory.liftTriangle _).mapIso
                (triangle_of_termwise_split_cone_iso f).symm⟩⟩

def invRotateLiftTriangle (V : Type u) [Category.{v} V] [Abelian V] :
    inv_rotate _ ⋙ HomotopyCategory.liftTriangle V ≅
      HomotopyCategory.liftTriangle _ ⋙ inv_rotate _ :=
  NatIso.ofComponents
    (fun X =>
      mkTriangleIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp;
          simp only [category.comp_id, functor.map_neg, discrete.functor_map_id, category.id_comp,
            preadditive.comp_neg, shift_ε_inv_app, category.assoc, neg_inj, functor.map_comp,
            nat_trans.id_app, preadditive.neg_comp])
        (by dsimp; rw [category.comp_id, category.id_comp])
        (by
          dsimp;
          simp only [shift_ε_app, discrete.functor_map_id, category.id_comp, category.assoc,
            functor.map_comp, nat_trans.id_app, CategoryTheory.Functor.map_id,
            unit_of_tensor_iso_unit_inv_app, shift_μ_inv_app]
          erw [category.comp_id]))
    (by intros; ext <;> exact (category.comp_id _).trans (category.id_comp _).symm)

theorem inv_rotate_mem_distinguishedTriangles (T : triangle 𝒦) (h : T ∈ distinguishedTriangles V) :
    T.invRotate ∈ distinguishedTriangles V :=
  by
  obtain ⟨X, Y, Z, f, g, h, ⟨e⟩⟩ := h
  exact
    (mem_distinguished_iff_exists_iso_cone _).mpr
      ⟨_, _, _,
        ⟨(inv_rotate _).mapIso e ≪≫
            ((inv_rotate_lift_triangle _).app _).symm ≪≫
              (HomotopyCategory.liftTriangle _).mapIso
                ((neg₃_equiv _).isoEquiv _ _
                  ((triangle.nonneg_inv_rotate_iso _).symm ≪≫ inv_rotate_iso_cone_triangle f g h))⟩⟩

instance : pretriangulated 𝒦
    where
  distinguishedTriangles := distinguishedTriangles V
  isomorphic_distinguished T₁ hT T₂ e := mem_distinguished_of_iso e.symm hT
  contractible_distinguished := by
    rintro ⟨X⟩
    refine' ⟨X, X, HomologicalComplex.zero, 𝟙 _, 0, _, ⟨_⟩⟩
    · intro i; simp only [id_f, zero_f_apply]
      refine' splitting.splitting_of_is_iso_zero _ (homological_complex.zero_X _ _)
      exact HomologicalComplex.isZero_zero
    refine' mk_triangle_iso (iso.refl _) (iso.refl _) _ _ _ _
    · dsimp [triangleₕ_of_termwise_split]
      refine' homotopy_category.is_zero_zero.iso_zero.symm
    all_goals dsimp <;> simp <;> rfl
  distinguished_cocone_triangle := by
    rintro ⟨X⟩ ⟨Y⟩ f
    induction f using Quot.inductionOn
    exact ⟨_, _, _, _, _, _, _, _, _, ⟨iso_termwise_split_of_cone f⟩⟩
  rotate_distinguished_triangle := by
    intro T
    constructor
    · apply rotate_mem_distinguished_triangles
    · intro h
      exact
        mem_distinguished_of_iso ((triangle_rotation _).unitIso.app T).symm
          (inv_rotate_mem_distinguished_triangles _ h)
  complete_distinguished_triangle_morphism := by
    intros
    obtain ⟨X₁, Y₁, f₁, ⟨e₁⟩⟩ := (mem_distinguished_iff_exists_iso_cone _).mp h₁
    obtain ⟨X₂, Y₂, f₂, ⟨e₂⟩⟩ := (mem_distinguished_iff_exists_iso_cone _).mp h₂
    let h :
      Homotopy (f₁ ≫ Quot.out (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂))
        (Quot.out (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) ≫ f₂) :=
      by
      apply homotopy_of_eq
      simp only [quotient_map_out, category.assoc, functor.map_comp]
      erw [← e₂.hom.comm₁, reassoc_of e₁.inv.comm₁, reassoc_of comm₁]
    refine' ⟨e₁.hom.hom₃ ≫ (Quotient V _).map (cone.map h) ≫ e₂.inv.hom₃, _, _⟩
    · rw [reassoc_of e₁.hom.comm₂, ← is_iso.eq_inv_comp]
      simp_rw [← category.assoc]
      rw [← is_iso.eq_comp_inv, ← inv_hom₃, ← inv_hom₂, is_iso.iso.inv_inv, is_iso.iso.inv_hom]
      simp_rw [category.assoc]
      rw [e₂.hom.comm₂]
      convert (cone.triangleₕ_map h).comm₂ using 1
      dsimp; simp
    · simp_rw [category.assoc]
      rw [← is_iso.inv_comp_eq, ← inv_hom₃, is_iso.iso.inv_hom, ← reassoc_of e₁.inv.comm₃, ←
        e₂.inv.comm₃]
      dsimp
      have := (cone.triangleₕ_map h).comm₃
      dsimp at this 
      rw [← homotopy_category.quotient_map_shift, quotient_map_out] at this 
      simp only [preadditive.neg_comp_assoc, preadditive.comp_neg, category.assoc, neg_inj,
        preadditive.neg_comp]
      rw [← reassoc_of this, ← functor.map_comp, ← functor.map_comp]
      congr 2
      rw [← is_iso.comp_inv_eq, ← inv_hom₁, is_iso.iso.inv_inv, category.assoc]

end HomotopyCategory

