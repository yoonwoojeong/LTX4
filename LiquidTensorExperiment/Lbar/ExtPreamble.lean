import LiquidTensorExperiment.ForMathlib.Derived.LesFacts
import LiquidTensorExperiment.Liquid
import LiquidTensorExperiment.Lbar.Functor
import LiquidTensorExperiment.Condensed.ProjectiveResolution
import LiquidTensorExperiment.Condensed.Condensify
import LiquidTensorExperiment.Condensed.BdLemma
import LiquidTensorExperiment.BreenDeligne.Eg
import LiquidTensorExperiment.ForMathlib.Derived.ExtCoproducts
import LiquidTensorExperiment.Condensed.Ab4
import LiquidTensorExperiment.Lbar.Squares
import LiquidTensorExperiment.PseudoNormedGroup.QprimeFP
import LiquidTensorExperiment.ForMathlib.Acyclic
import LiquidTensorExperiment.FreePfpng.Acyclic
import LiquidTensorExperiment.ForMathlib.SemiNormedGroupUlift
import LiquidTensorExperiment.ForMathlib.Bicartesian4
import LiquidTensorExperiment.ForMathlib.HasHomologyAux
import LiquidTensorExperiment.ForMathlib.Derived.ExtLemmas

#align_import Lbar.ext_preamble

noncomputable section

universe u

open Opposite CategoryTheory CategoryTheory.Limits

open scoped NNReal ZeroObject

variable (r r' : ℝ≥0)

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r < 1)] [Fact (r' < 1)]

abbrev SemiNormedGroupCat.toCond (V : SemiNormedGroupCat.{u}) :=
  Condensed.ofTopAb V

section

open BoundedHomotopyCategory

variable (BD : BreenDeligne.Data)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

theorem ExtQprime_iso_aux_system_aux (c : ℝ≥0) (k i : ℤ) (hi : i > 0) :
    IsZero
      (((ext' i).obj
            (op
              (((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj
                    ((qprimeFPNat.{u} r' BD κ M).obj c)).pt
                k))).obj
        V.toCond) :=
  by
  rcases k with ((_ | _) | _)
  · apply free_acyclic.{u} _ V i hi
  · apply BoundedDerivedCategory.ext'_zero_left_isZero; refine' (is_zero_zero _).op
  · apply free_acyclic.{u} _ V i hi

def embedUnop {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] :
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).op ⋙
        @HomologicalComplex.unopFunctor 𝓐 _ _ _ _ ≅
      HomologicalComplex.unopFunctor ⋙
        HomologicalComplex.embed ComplexShape.Embedding.natUpIntDown :=
  by
  refine' NatIso.ofComponents _ _
  · intro X; refine' HomologicalComplex.Hom.isoOfComponents _ _
    · rintro ((_ | n) | n)
      · exact iso.refl _
      · refine' IsZero.iso (is_zero_zero _).unop (is_zero_zero _)
      · exact iso.refl _
    · rintro i (j | (_ | j)) (rfl : _ = _)
      · apply IsZero.eq_of_src; exact (is_zero_zero _).unop
      · dsimp only [Iso.refl_hom]; erw [Category.id_comp, Category.comp_id]; rfl
      · dsimp only [Iso.refl_hom]; erw [Category.id_comp, Category.comp_id]; rfl
  · intro X Y f; ext ((_ | n) | n)
    · dsimp only [HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
        Iso.refl_hom]
      erw [Category.id_comp, Category.comp_id]; rfl
    · apply IsZero.eq_of_tgt; exact is_zero_zero _
    · dsimp only [HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
        Iso.refl_hom]
      erw [Category.id_comp, Category.comp_id]; rfl

-- move me
theorem natUpIntDown_cIff : ComplexShape.Embedding.natUpIntDown.CIff := fun i j =>
  ComplexShape.Embedding.natDownIntUp_cIff j i

def forget₂Unop :
    ((forget₂ SemiNormedGroupCat Ab).op.mapHomologicalComplex (ComplexShape.down ℕ)).op ⋙
        HomologicalComplex.unopFunctor ≅
      HomologicalComplex.unopFunctor ⋙
        (forget₂ SemiNormedGroupCat Ab).mapHomologicalComplex (ComplexShape.down ℕ).symm :=
  by
  refine' NatIso.ofComponents _ _
  · intro X; refine' HomologicalComplex.Hom.isoOfComponents _ _
    · intro n; exact iso.refl _
    · rintro i j (rfl : _ = _); dsimp only [Iso.refl_hom]
      rw [Category.id_comp, Category.comp_id]; rfl
  · intro X Y f; ext n
    dsimp only [HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
      Iso.refl_hom]
    rw [Category.id_comp, Category.comp_id]; rfl

def preadditiveYonedaObjObjCondensedSetToCondensedAb (M : Condensed.{u} Ab.{u + 1})
    (X : Profinite) :
    (preadditiveYoneda.obj M).obj
        (op <| condensedSetToCondensedAb.obj (profiniteToCondensed.obj X)) ≅
      M.val.obj (op X) :=
  let e := condensedAbCondensedSetAdjunction.homEquiv X.toCondensed M
  AddEquiv.toAddCommGroupCatIso <|
    { toFun := fun t => yoneda'Equiv _ _ (e t).val
      invFun := fun t => e.symm <| ⟨(yoneda'Equiv _ _).symm <| by apply t⟩
      left_inv := fun t => by
        dsimp only
        apply_fun e; rw [Equiv.apply_symm_apply]; ext1
        dsimp only; erw [Equiv.apply_symm_apply]
      right_inv := fun t => by
        dsimp only
        rw [Equiv.apply_symm_apply]
        rw [Equiv.apply_symm_apply]
      map_add' := by
        intro x y
        rfl }

@[reassoc]
theorem preadditiveYonedaObjObjCondensedSetToCondensedAb_natural {M₁ M₂ : Condensed.{u} Ab.{u + 1}}
    (f : M₁ ⟶ M₂) (X : Profinite) :
    (preadditiveYonedaObjObjCondensedSetToCondensedAb M₁ X).hom ≫ f.val.app _ =
      (preadditiveYoneda.map f).app _ ≫
        (preadditiveYonedaObjObjCondensedSetToCondensedAb M₂ X).hom :=
  by ext; rfl

@[reassoc]
theorem preadditiveYonedaObjObjCondensedSetToCondensedAb_natural' (M : Condensed.{u} Ab.{u + 1})
    {X Y : Profinite.{u}} (f : X ⟶ Y) :
    (preadditiveYonedaObjObjCondensedSetToCondensedAb M Y).hom ≫ M.val.map f.op =
      (preadditiveYoneda.obj M).map
          (condensedSetToCondensedAb.map <| profiniteToCondensed.map f).op ≫
        (preadditiveYonedaObjObjCondensedSetToCondensedAb M X).hom :=
  by
  ext t
  rw [comp_apply]
  rw [comp_apply]
  dsimp [preadditiveYonedaObjObjCondensedSetToCondensedAb, Adjunction.whiskerRight]
  simp only [← NatTrans.comp_app]
  rw [← GrothendieckTopology.toSheafify_naturality_assoc]
  dsimp [Functor.rightUnitor]
  simp only [← comp_apply, Category.assoc, ← NatTrans.comp_app, ← NatTrans.comp_app_assoc]
  simp only [← NatTrans.naturality, Functor.comp_map, Category.assoc]
  rfl

end

