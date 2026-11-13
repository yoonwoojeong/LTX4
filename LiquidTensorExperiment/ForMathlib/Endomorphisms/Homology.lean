import LiquidTensorExperiment.ForMathlib.Endomorphisms.Basic
import LiquidTensorExperiment.ForMathlib.ExactFunctor

#align_import for_mathlib.endomorphisms.homology

universe v

namespace CategoryTheory

namespace Endomorphisms

open HomologicalComplex CategoryTheory CategoryTheory.Limits Category

variable (𝓐 : Type _) [Category.{v} 𝓐]

@[simps]
def tautologicalNatTrans : Endomorphisms.forget 𝓐 ⟶ Endomorphisms.forget 𝓐 where app X := X.e

variable {𝓐}

variable [Abelian 𝓐] [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐] [HasProductsOfShape (ULift.{v} ℕ) 𝓐]

variable {M : Type _} {c : ComplexShape M} (F : Endomorphisms 𝓐 ⥤ HomologicalComplex 𝓐 c)

variable (Y : HomologicalComplex (Endomorphisms 𝓐) c)

@[simps]
def HomologicalComplex.tautologicalEndomorphism : Y ⟶ Y where f i := ⟨(Y.pt i).e, rfl⟩

theorem homology'Functor_obj_e (i : M) :
    ((homology'Functor (Endomorphisms 𝓐) c i).obj Y).e =
      ((homology'Functor (Endomorphisms 𝓐) c i).map Y.tautologicalEndomorphism).f :=
  by
  have h₁ :=
    ((endomorphisms.forget 𝓐).homology'FunctorIso c i).Hom.naturality Y.tautological_endomorphism
  rw [← cancel_mono (((endomorphisms.forget 𝓐).homology'FunctorIso c i).inv.app Y), assoc] at h₁ 
  conv_lhs at h₁ =>
    congr
    skip
    rw [← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app]
  rw [comp_id] at h₁ 
  conv_lhs at h₁ => dsimp only [Functor.Comp, endomorphisms.forget]
  rw [h₁]
  clear h₁
  have h₂ :=
    nat_trans.congr_app (functor.naturality_homology_functor_iso (tautological_nat_trans 𝓐) c i) Y
  dsimp [nat_trans.hcomp] at h₂ 
  rw [comp_id, id_comp, ←
    cancel_mono (((endomorphisms.forget 𝓐).homology'FunctorIso c i).inv.app Y), assoc] at h₂ 
  conv_lhs at h₂ =>
    congr
    skip
    rw [← nat_trans.comp_app, iso.hom_inv_id, nat_trans.id_app]
  erw [comp_id] at h₂ 
  exact h₂

end Endomorphisms

end CategoryTheory

