import Mathlib.CategoryTheory.Functor.LeftDerived
import Mathlib.Data.Matrix.Notation
import LiquidTensorExperiment.ForMathlib.HomologicalComplex
import LiquidTensorExperiment.ForMathlib.Horseshoe
import LiquidTensorExperiment.ForMathlib.LesHomology
import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import for_mathlib.derived_functor

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open ShortExactSequence

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type _} [Category D]

-- Importing `category_theory.abelian.projective` and assuming
-- `[abelian C] [enough_projectives C] [abelian D]` suffices to acquire all the following:
-- variables [preadditive C] [has_zero_object C] [has_equalizers C]
-- variables [has_images C] [has_projective_resolutions C]
-- variables [preadditive D] [has_zero_object D] [has_equalizers D] [has_cokernels D]
-- variables [has_images D] [has_image_maps D]
variable [Abelian C] [EnoughProjectives C] [Abelian D]

namespace Functor

namespace LeftDerived

variable (F : C ⥤ D)

/-- We can compute a left derived functor using a chosen projective resolution. -/
@[simps]
def Functor.leftDerivedObjIso' (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) (P : ChainComplex C ℕ)
    (π : P ⟶ (ChainComplex.single₀ C).obj X) (h : P.IsProjectiveResolution X π) :
    (F.leftDerived n).obj X ≅ (homology'Functor D _ n).obj ((F.mapHomologicalComplex _).obj P) :=
  (F.leftDerivedObjIso n (h.mkProjectiveResolution P X π) : _)

/-- We can compute a left derived functor on a morphism using a lift of that morphism to a chain map
between chosen projective resolutions. -/
theorem Functor.leftDerived_map_eq' (F : C ⥤ D) [F.Additive] (n : ℕ) (X Y : C) (f : X ⟶ Y)
    (PX : ChainComplex C ℕ) (πX : PX ⟶ (ChainComplex.single₀ C).obj X) (PY : ChainComplex C ℕ)
    (πY : PY ⟶ (ChainComplex.single₀ C).obj Y) (g : PX ⟶ PY) (hX : PX.IsProjectiveResolution X πX)
    (hY : PY.IsProjectiveResolution Y πY) (w : g ≫ πY = πX ≫ (ChainComplex.single₀ C).map f) :
    (F.leftDerived n).map f =
      (Functor.leftDerivedObjIso' F n X PX πX hX).Hom ≫
        (homology'Functor D _ n).map ((F.mapHomologicalComplex _).map g) ≫
          (Functor.leftDerivedObjIso' F n Y PY πY hY).inv :=
  by
  let PXr := hX.mk_ProjectiveResolution PX X πX
  let PYr := hY.mk_ProjectiveResolution PY Y πY
  let gr : PXr.complex ⟶ PYr.complex := g
  simpa using functor.left_derived_map_eq F n f gr w

abbrev α [F.Additive] :
    (ShortExactSequence.fst C ⋙ F).mapHomologicalComplex (ComplexShape.down ℕ) ⟶
      (ShortExactSequence.snd C ⋙ F).mapHomologicalComplex (ComplexShape.down ℕ) :=
  NatTrans.mapHomologicalComplex (whiskerRight (ShortExactSequence.fNat _) _) _

abbrev β [F.Additive] :
    (ShortExactSequence.snd C ⋙ F).mapHomologicalComplex (ComplexShape.down ℕ) ⟶
      (ShortExactSequence.trd C ⋙ F).mapHomologicalComplex (ComplexShape.down ℕ) :=
  NatTrans.mapHomologicalComplex (whiskerRight (ShortExactSequence.gNat _) _) _

theorem exact_α_β_horseshoe [F.Additive] (A : ShortExactSequence C) (n : ℕ) :
    ShortExact (((α F).app (horseshoe A)).f n) (((β F).app (horseshoe A)).f n) :=
  by
  apply split.short_exact
  apply split.map
  obtain ⟨φ, χ, h1, h2, h3, h4⟩ := horseshoe_split A n
  exact ⟨⟨φ, χ, h1, h2, short_exact_sequence.f_comp_g _, h3, h4⟩⟩

def δ [F.Additive] (n : ℕ) (A : ShortExactSequence C) :
    (F.leftDerived (n + 1)).obj A.3 ⟶ (F.leftDerived n).obj A.1 :=
  by
  let f₃ := functor.left_derived_obj_iso' F (n + 1) _ _ _ (horseshoe_is_projective_resolution₃ A)
  let f₁ := functor.left_derived_obj_iso' F n _ _ _ (horseshoe_is_projective_resolution₁ A)
  exact f₃.hom ≫ HomologicalComplex.δ _ _ (exact_α_β_horseshoe F A) _ _ rfl ≫ f₁.symm.hom

theorem exact_of_short_exact [F.Additive] (n : ℕ) (A : ShortExactSequence C) :
    Exact ((F.leftDerived n).map A.f) ((F.leftDerived n).map A.g) :=
  by
  have := ((HomologicalComplex.six_term_exactSeq _ _ (exact_α_β_horseshoe F A) _ n rfl).drop 3).pair
  have H₁₂ :=
    functor.left_derived_map_eq' F n A.1 A.2 A.f ((HomologicalComplex.fst C).obj (horseshoe A))
      (horseshoe_to_single₁ A) ((HomologicalComplex.snd C).obj (horseshoe A))
      (horseshoe_to_single₂ A) ((HomologicalComplex.fstSnd C).app (horseshoe A))
      (horseshoe_is_projective_resolution₁ A) (horseshoe_is_projective_resolution₂ A) _
  have H₂₃ :=
    functor.left_derived_map_eq' F n A.2 A.3 A.g ((HomologicalComplex.snd C).obj (horseshoe A))
      (horseshoe_to_single₂ A) ((HomologicalComplex.trd C).obj (horseshoe A))
      (horseshoe_to_single₃ A) ((HomologicalComplex.sndTrd C).app (horseshoe A))
      (horseshoe_is_projective_resolution₂ A) (horseshoe_is_projective_resolution₃ A) _
  refine' Preadditive.exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ this
  · let this.1 :=
      functor.left_derived_obj_iso' F n A.1 ((HomologicalComplex.fst C).obj (horseshoe A))
        (horseshoe_to_single₁ A) (horseshoe_is_projective_resolution₁ A)
    exact this.symm
  · let this.1 :=
      functor.left_derived_obj_iso' F n A.2 ((HomologicalComplex.snd C).obj (horseshoe A))
        (horseshoe_to_single₂ A) (horseshoe_is_projective_resolution₂ A)
    exact this.symm
  · let this.1 :=
      functor.left_derived_obj_iso' F n A.3 ((HomologicalComplex.trd C).obj (horseshoe A))
        (horseshoe_to_single₃ A) (horseshoe_is_projective_resolution₃ A)
    exact this.symm
  · rw [H₁₂, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp]
    simpa
  · rw [H₂₃, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp]
    simpa
  · ext i
    apply horseshoe_g_comp_to_single₃_f
  · ext i
    apply horseshoe_f_comp_to_single₂_f

theorem exact_of_short_exact.δ_right [F.Additive] (n : ℕ) (A : ShortExactSequence C) :
    Exact ((F.leftDerived (n + 1)).map A.g) (δ F n A) :=
  by
  have := ((HomologicalComplex.six_term_exactSeq _ _ (exact_α_β_horseshoe F A) _ n rfl).drop 1).pair
  have H₂₃ :=
    functor.left_derived_map_eq' F (n + 1) A.2 A.3 A.g
      ((HomologicalComplex.snd C).obj (horseshoe A)) (horseshoe_to_single₂ A)
      ((HomologicalComplex.trd C).obj (horseshoe A)) (horseshoe_to_single₃ A)
      ((HomologicalComplex.sndTrd C).app (horseshoe A)) (horseshoe_is_projective_resolution₂ A)
      (horseshoe_is_projective_resolution₃ A) _
  refine' Preadditive.exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ this
  · let this.1 :=
      functor.left_derived_obj_iso' F (n + 1) A.2 ((HomologicalComplex.snd C).obj (horseshoe A))
        (horseshoe_to_single₂ A) (horseshoe_is_projective_resolution₂ A)
    exact this.symm
  · let this.1 :=
      functor.left_derived_obj_iso' F (n + 1) A.3 ((HomologicalComplex.trd C).obj (horseshoe A))
        (horseshoe_to_single₃ A) (horseshoe_is_projective_resolution₃ A)
    exact this.symm
  · let this.1 :=
      functor.left_derived_obj_iso' F n A.1 ((HomologicalComplex.fst C).obj (horseshoe A))
        (horseshoe_to_single₁ A) (horseshoe_is_projective_resolution₁ A)
    exact this.symm
  · rw [H₂₃, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp]
    simpa
  · unfold δ
    dsimp
    simp only [category.assoc, iso.inv_hom_id_assoc]
  · ext i
    apply horseshoe_g_comp_to_single₃_f

theorem exact_of_short_exact.δ_left [F.Additive] (n : ℕ) (A : ShortExactSequence C) :
    Exact (δ F n A) ((F.leftDerived n).map A.f) :=
  by
  have := ((HomologicalComplex.six_term_exactSeq _ _ (exact_α_β_horseshoe F A) _ n rfl).drop 2).pair
  have H₁₂ :=
    functor.left_derived_map_eq' F n A.1 A.2 A.f ((HomologicalComplex.fst C).obj (horseshoe A))
      (horseshoe_to_single₁ A) ((HomologicalComplex.snd C).obj (horseshoe A))
      (horseshoe_to_single₂ A) ((HomologicalComplex.fstSnd C).app (horseshoe A))
      (horseshoe_is_projective_resolution₁ A) (horseshoe_is_projective_resolution₂ A) _
  refine' Preadditive.exact_of_iso_of_exact' _ _ _ _ _ _ _ _ _ this
  · let this.1 :=
      functor.left_derived_obj_iso' F (n + 1) A.3 ((HomologicalComplex.trd C).obj (horseshoe A))
        (horseshoe_to_single₃ A) (horseshoe_is_projective_resolution₃ A)
    exact this.symm
  · let this.1 :=
      functor.left_derived_obj_iso' F n A.1 ((HomologicalComplex.fst C).obj (horseshoe A))
        (horseshoe_to_single₁ A) (horseshoe_is_projective_resolution₁ A)
    exact this.symm
  · let this.1 :=
      functor.left_derived_obj_iso' F n A.2 ((HomologicalComplex.snd C).obj (horseshoe A))
        (horseshoe_to_single₂ A) (horseshoe_is_projective_resolution₂ A)
    exact this.symm
  · unfold δ
    dsimp
    simp only [category.assoc, iso.inv_hom_id_assoc]
  · rw [H₁₂, ← category.assoc, iso.symm_hom, iso.inv_hom_id, category.id_comp]
    simpa
  · ext i
    apply horseshoe_f_comp_to_single₂_f

theorem six_term_exactSeq [F.Additive] (n : ℕ) (A : ShortExactSequence C) :
    ExactSeq D
      [(F.leftDerived (n + 1)).map A.f, (F.leftDerived (n + 1)).map A.g, δ F n A,
        (F.leftDerived n).map A.f, (F.leftDerived n).map A.g] :=
  (exact_of_short_exact _ _ _).cons <|
    (exact_of_short_exact.δ_right _ _ _).cons <|
      (exact_of_short_exact.δ_left _ _ _).cons <| (exact_of_short_exact _ _ _).ExactSeq

end LeftDerived

end Functor

end CategoryTheory

