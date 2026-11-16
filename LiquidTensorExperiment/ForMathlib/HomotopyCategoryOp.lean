import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp
import LiquidTensorExperiment.ForMathlib.HomotopyCategory

#align_import for_mathlib.homotopy_category_op

noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

variable {ι : Type _} (c : ComplexShape ι)

namespace ComplexShape

@[simp]
theorem symm_next (i : ι) : c.symm.next i = c.prev i :=
  rfl

@[simp]
theorem symm_prev (i : ι) : c.symm.prev i = c.next i :=
  rfl

end ComplexShape

namespace HomologicalComplex

theorem opFunctorMapHomotopy {ι C : Type _} {c : ComplexShape ι} [Category C] [Preadditive C]
    {X Y : HomologicalComplex C c} (f₁ f₂ : X ⟶ Y) (H : Homotopy f₁ f₂) :
    Homotopy (HomologicalComplex.opFunctor.map f₁.op) (HomologicalComplex.opFunctor.map f₂.op) :=
  { hom := fun i j => (H.hom j i).op
    zero := fun i j hij => by dsimp only; rw [H.zero j i hij, op_zero]
    comm := fun i =>
      by
      simp only [HomologicalComplex.opFunctor_map_f, Quiver.Hom.unop_op, H.comm i, op_add,
        add_left_inj]
      conv_lhs => rw [add_comm] }

end HomologicalComplex

namespace HomotopyCategory

variable {C : Type _} [Category C] [Preadditive C] {c}

def opFunctor : (HomotopyCategory C c)ᵒᵖ ⥤ HomotopyCategory Cᵒᵖ c.symm :=
  Functor.leftOp
    (CategoryTheory.Quotient.lift _
      (HomologicalComplex.opFunctor ⋙ HomotopyCategory.quotient Cᵒᵖ c.symm).rightOp
      fun X Y f₁ f₂ h => by
      dsimp only [Functor.rightOp]
      congr 1
      dsimp only [Functor.comp_map]
      erw [Quotient.functor_map_eq_iff]
      refine' ⟨HomologicalComplex.opFunctorMapHomotopy f₁ f₂ h.some⟩)

def quotientOpFunctor :
    (quotient C c).op ⋙ opFunctor ≅ HomologicalComplex.opFunctor ⋙ quotient Cᵒᵖ c.symm :=
  CategoryTheory.NatIso.ofComponents (app := fun X => eqToIso (by rfl))
    (naturality := fun {X Y} f => by
      -- Porting note: unfold the definition of `opFunctor` and use the lemma for lifts through quotients
      dsimp [opFunctor]
      erw [CategoryTheory.Quotient.lift_map_functor_map]
      simp)

def unopFunctor : (HomotopyCategory Cᵒᵖ c)ᵒᵖ ⥤ HomotopyCategory C c.symm :=
  Functor.leftOp
    (CategoryTheory.Quotient.lift _
      (HomologicalComplex.unopFunctor ⋙ HomotopyCategory.quotient C c.symm).rightOp
      fun X Y f₁ f₂ h => by
      dsimp only [Functor.rightOp]
      congr 1
      dsimp only [Functor.comp_map]
      erw [Quotient.functor_map_eq_iff]
      let H := h.some
      exact
        Nonempty.intro
          { hom := fun i j => (H.hom j i).unop
            zero := fun i j hij => by dsimp only; rw [H.zero j i hij, unop_zero]
            comm := fun i => by
              apply Quiver.Hom.op_inj
              simp only [HomologicalComplex.unopFunctor_map_f, op_add, Quiver.Hom.op_unop,
                Quiver.Hom.unop_op, H.comm i]
              first
                | simpa using congrArg Quiver.Hom.op (H.comm i)
                | simpa [dNext, prevD] using congrArg Quiver.Hom.op (H.comm i)
                | (unfold dNext prevD at *; simp_all [op_add])
                | (abel_nf; congr 2) })

def quotientUnopFunctor :
    (quotient Cᵒᵖ c).op ⋙ unopFunctor ≅ HomologicalComplex.unopFunctor ⋙ quotient C c.symm :=
  CategoryTheory.NatIso.ofComponents (app := fun X => eqToIso (by rfl))
    (naturality := fun {X Y} f => by
      -- Porting note: unfold the definition of `opFunctor` and use the lemma for lifts through quotients
      dsimp [unopFunctor]
      erw [CategoryTheory.Quotient.lift_map_functor_map]
      simp)

end HomotopyCategory

