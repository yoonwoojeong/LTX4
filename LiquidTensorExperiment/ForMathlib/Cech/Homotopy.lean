import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import LiquidTensorExperiment.ForMathlib.Cech.Split
import LiquidTensorExperiment.ForMathlib.AbelianCategory

#align_import for_mathlib.Cech.homotopy

noncomputable section

universe v u v' u'

namespace CategoryTheory

open scoped Simplicial

open CategoryTheory.Limits

namespace Arrow

section Contravariant

variable {P : Type u} {N : Type u'} [Category.{v} P] [Category.{v'} N] (M : Pᵒᵖ ⥤ N)

variable (f : Arrow P)

variable [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.Hom]

variable [Arrow.Split f] [Preadditive N]

def contractingHomotopy' : Homotopy (𝟙 (f.conerve M).toCocomplex) 0
    where
  Hom i j := if h : j + 1 = i then eqToHom (by subst h) ≫ f.contractingHomotopy M j else 0
  zero' i j h := dif_neg h
  comm i :=
    by
    simp only [HomologicalComplex.id_f, Homotopy.dNext_cochainComplex,
      HomologicalComplex.zero_f_apply, add_zero]
    rcases i with (_ | _ | i)
    · rw [← is_contracting_homotopy_zero, Homotopy.prevD_zero_cochainComplex]
      simp only [eq_self_iff_true, dif_pos, eq_to_hom_refl, category.id_comp, add_zero]
    · rw [← is_contracting_homotopy_one, Homotopy.prevD_succ_cochainComplex]
      simp only [eq_self_iff_true, dif_pos, eq_to_hom_refl, category.id_comp, add_zero]
    · rw [← is_contracting_homotopy, Homotopy.prevD_succ_cochainComplex]
      simp only [eq_self_iff_true, dif_pos, eq_to_hom_refl, category.id_comp, add_zero]

variable [HasEqualizers N] [HasCokernels N] [HasImages N] [HasImageMaps N]

theorem conerve_toCocomplex_homology'_isZero (i : ℕ) :
    IsZero ((f.conerve M).toCocomplex.homology' i) :=
  by
  rw [is_zero_iff_id_eq_zero]
  simpa only [CategoryTheory.Functor.map_id, functor.map_zero] using
    homology'_map_eq_of_homotopy (f.contracting_homotopy' M) i

end Contravariant

section Covariant

variable {P : Type u} {N : Type u'} [Category.{v} P] [Category.{v'} N] (M : P ⥤ N)

variable (f : Arrow P)

variable [∀ n : ℕ, HasWidePullback f.right (fun i : Fin (n + 1) => f.left) fun i => f.Hom]

variable [Arrow.Split f] [Preadditive N]

def covariantContractingHomotopy' : Homotopy (𝟙 (f.nerve M).toComplex) 0
    where
  Hom i j := if h : i + 1 = j then f.covariantContractingHomotopy M i ≫ eqToHom (by subst h) else 0
  zero' i j h := dif_neg h
  comm i :=
    by
    simp only [HomologicalComplex.id_f, Homotopy.dNext_cochainComplex,
      HomologicalComplex.zero_f_apply, add_zero]
    rcases i with (_ | _ | i)
    · rw [← covariant_is_contracting_homotopy_zero, Homotopy.dNext_zero_chainComplex]
      simp only [eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true,
        Homotopy.prevD_chainComplex, category.comp_id, zero_add]
    · rw [← covariant_is_contracting_homotopy_one, Homotopy.dNext_succ_chainComplex]
      simp only [simplicial_object.augmented.to_complex_d_2, eq_self_iff_true, eq_to_hom_refl,
        category.id_comp, dite_eq_ite, if_true, category.comp_id, Homotopy.prevD_chainComplex]
      rw [add_comm]
    · rw [← covariant_is_contracting_homotopy, Homotopy.dNext_succ_chainComplex]
      simp only [simplicial_object.augmented.to_complex_d_2, eq_self_iff_true, eq_to_hom_refl,
        category.id_comp, dite_eq_ite, if_true, category.comp_id, Homotopy.prevD_chainComplex]
      rw [add_comm]

variable [HasEqualizers N] [HasCokernels N] [HasImages N] [HasImageMaps N]

theorem nerve_toComplex_homology'_isZero (i : ℕ) : IsZero ((f.nerve M).toComplex.homology' i) :=
  by
  rw [is_zero_iff_id_eq_zero]
  simpa only [CategoryTheory.Functor.map_id, functor.map_zero] using
    homology'_map_eq_of_homotopy (f.covariant_contracting_homotopy' M) i

end Covariant

end Arrow

end CategoryTheory

