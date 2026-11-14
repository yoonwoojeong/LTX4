import Mathlib.GroupTheory.FreeAbelianGroupFinsupp
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup

#align_import for_mathlib.free_abelian_group2

namespace FreeAbelianGroup

theorem lift_map {A B C : Type _} [AddCommGroup C] (f : A → B) (g : B → C) (x) :
    FreeAbelianGroup.lift g (FreeAbelianGroup.map f x) = FreeAbelianGroup.lift (g ∘ f) x :=
  by
  rw [← AddMonoidHom.comp_apply]; congr 1; clear x; ext x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_of_apply, FreeAbelianGroup.lift.of,
    id.def]

theorem lift_id_map {A B : Type _} [AddCommGroup B] (f : A → B) (x) :
    FreeAbelianGroup.lift id (FreeAbelianGroup.map f x) = FreeAbelianGroup.lift f x :=
  FreeAbelianGroup.lift_map _ _ _

open scoped BigOperators

theorem coeff_of_not_mem_support {X : Type _} (a : FreeAbelianGroup X) (x : X) (h : x ∉ a.support) :
    FreeAbelianGroup.coeff x a = 0 :=
  by
  dsimp [FreeAbelianGroup.coeff]
  rwa [← Finsupp.not_mem_support_iff]

theorem lift_eq_sum {A B : Type _} [AddCommGroup B] (f : A → B) (x) :
    FreeAbelianGroup.lift f x = ∑ a in x.support, FreeAbelianGroup.coeff a x • f a :=
  by
  apply FreeAbelianGroup.induction_on'' x <;> clear x
  · simp only [AddMonoidHom.map_zero, zero_smul, Finset.sum_const_zero]
  · intro n hn a
    simp only [map_zsmul, smul_assoc, ← Finset.smul_sum, FreeAbelianGroup.lift.of,
      support_zsmul n hn, support_of, Finset.sum_singleton, coeff_of_self, one_smul]
  · intro x n hn a hax IH1 IH2; specialize IH2 n
    simp only [AddMonoidHom.map_add, map_zsmul, smul_assoc, FreeAbelianGroup.lift.of,
      support_add_smul_of x n hn a hax, support_zsmul n hn, support_of, Finset.sum_singleton] at IH2
      ⊢
    rw [Finset.sum_insert]; swap; exact hax
    simp only [IH1, coeff_of_self, smul_assoc, one_smul, add_smul, Finset.sum_add_distrib,
      coeff_of_not_mem_support _ _ hax, zero_smul, zero_add]
    rw [add_comm]; refine' congr_arg₂ _ rfl _; symm; convert add_zero _
    rw [Finset.sum_eq_zero]
    intro z hz
    rw [coeff_of_not_mem_support, zero_smul, smul_zero]
    rw [support_of, Finset.mem_singleton]; rintro rfl; exact hax hz

end FreeAbelianGroup

