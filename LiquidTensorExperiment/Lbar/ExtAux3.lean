import LiquidTensorExperiment.Lbar.ExtAux2
import LiquidTensorExperiment.Lbar.Iota

#align_import Lbar.ext_aux3

noncomputable section

universe v u u'

open Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

open scoped NNReal ZeroObject

variable (r r' : ℝ≥0)

variable [Fact (0 < r)] [Fact (0 < r')] [Fact (r < r')] [Fact (r < 1)] [Fact (r' < 1)]

open BoundedHomotopyCategory

variable {r'}

variable (BD : BreenDeligne.Package)

variable (κ κ₂ : ℝ≥0 → ℕ → ℝ≥0)

variable [∀ c : ℝ≥0, BD.data.Suitable (κ c)] [∀ n, Fact (Monotone (Function.swap κ n))]

variable [∀ c : ℝ≥0, BD.data.Suitable (κ₂ c)] [∀ n, Fact (Monotone (Function.swap κ₂ n))]

variable (M : ProFiltPseuNormGrpWithTinv₁.{u} r')

section Preps

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

variable (ι : ULift.{u + 1} ℕ → ℝ≥0) (hι : Monotone ι)

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

theorem cofanPointIsoColimit_conj_eq_desc
    {e :
      (HomotopyCategory.colimitCofan fun a : ULift ℕ =>
            ((fun k : ULift ℕ => (qprimeFP r' BD.data κ₂ M).obj (ι k)) a).val).pt.IsBoundedAbove} :
    (cofanPointIsoColimit fun k : ULift ℕ => (qprimeFP r' BD.data κ₂ M).obj (ι k)).inv ≫
        ofHom (sigmaShift ι hι (qprimeFPInt r' BD.data κ₂ M)) ≫
          (cofanPointIsoColimit fun k : ULift ℕ => (qprimeFP r' BD.data κ₂ M).obj (ι k)).hom =
      by
      apply sigma.desc
      intro k
      refine' _ ≫ sigma.ι _ (ULift.up <| ULift.down k + 1)
      refine' (qprimeFP r' BD.data κ₂ M).map _
      refine' hom_of_le (hι _)
      exact_mod_cast k.down.le_succ :=
  by
  ext j
  dsimp only [cofanPointIsoColimit]
  rw [colimit.ι_desc, cofan.mk_ι_app, colimit.comp_cocone_point_unique_up_to_iso_inv_assoc]
  simp only [← category.assoc]; rw [← iso.eq_comp_inv]; simp only [category.assoc]
  rw [colimit.comp_cocone_point_unique_up_to_iso_inv]
  dsimp only [sigmaShift, BoundedHomotopyCategory.cofan, cofan.mk_ι_app, of_hom,
    HomotopyCategory.colimitCofan]
  erw [← functor.map_comp, colimit.ι_desc]
  dsimp only [sigmaShiftCone, discrete.nat_trans_app]
  refine' functor.map_comp _ _ _

def piExtIsoExtSigma (i : ℤ) :
    (∏ fun k : ULift ℕ =>
        ((qprimeFP r' BD.data κ₂ M).op ⋙
              (ext i).flip.obj ((single (Condensed Ab) 0).obj V.toCond)).obj
          (op (ι k))) ≅
      ((ext i).obj (op (of' (∐ fun k : ULift ℕ => (qprimeFPInt r' BD.data κ₂ M).obj (ι k))))).obj
        ((single (Condensed Ab) 0).obj (Condensed.ofTopAb ↥V)) :=
  (extCoproductIso (fun k : ULift ℕ => (qprimeFP r' BD.data κ₂ M).obj (ι k)) i
        ((single (Condensed Ab) 0).obj V.toCond)).symm ≪≫
    ((ext i).flip.obj ((single (Condensed Ab) 0).obj V.toCond)).mapIso
      (by
        refine'
          iso.op (cofanPointIsoColimit fun k : ULift ℕ => (qprimeFP r' BD.data κ₂ M).obj (ι k)))

-- move me
@[simp]
theorem CategoryTheory.op_nsmul {C : Type _} [Category C] [Preadditive C] {X Y : C} (n : ℕ)
    (f : X ⟶ Y) : (n • f).op = n • f.op :=
  rfl

-- move me
@[simp]
theorem CategoryTheory.op_sub {C : Type _} [Category C] [Preadditive C] {X Y : C} (f g : X ⟶ Y) :
    (f - g).op = f.op - g.op :=
  rfl

@[simp]
theorem HomologicalComplex.ofHom_sub {C : Type _} [Category C] [Abelian C]
    (X Y : HomologicalComplex C (ComplexShape.up ℤ)) (f g : X ⟶ Y)
    [((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X).IsBoundedAbove]
    [((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y).IsBoundedAbove] :
    ofHom (f - g) = ofHom f - ofHom g :=
  rfl

@[reassoc]
theorem extCoproductIso_naturality_inv (A : Type u) [Category.{v} A] [Abelian A]
    [EnoughProjectives A] [HasCoproducts.{v} A] [AB4 A] {α : Type v}
    (X₁ X₂ : α → BoundedHomotopyCategory A) [UniformlyBounded X₁] [UniformlyBounded X₂]
    (g : X₁ ⟶ X₂) (i : ℤ) (Y) :
    (extCoproductIso _ _ _).inv ≫
        ((ext i).map (Sigma.desc fun b => g b ≫ Sigma.ι X₂ b : ∐ X₁ ⟶ ∐ X₂).op).app Y =
      (Pi.lift fun b => Pi.π _ b ≫ ((ext i).map (g b).op).app Y) ≫ (extCoproductIso _ _ _).inv :=
  by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv]
  apply Ext_coproduct_iso_naturality

end Preps

