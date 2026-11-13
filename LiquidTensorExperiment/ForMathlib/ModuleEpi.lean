import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.Category.ModuleCat.Basic

#align_import for_mathlib.module_epi

namespace Module

variable {A : Type _} [Ring A] {M N L : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module A M] [Module A N] [Module A L] (f : M →ₗ[A] N) (g : M →ₗ[A] L)

def compareInProd : M →ₗ[A] N × L where
  toFun m := ⟨f m, -g m⟩
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' r x := by ext <;> simp

def Pushout :=
  (N × L) ⧸ (compareInProd f g).range
deriving AddCommGroup

instance : Module A (Pushout f g) :=
  show Module A ((N × L) ⧸ (compareInProd f g).range) by infer_instance

def Pushout.π : N × L →ₗ[A] Pushout f g :=
  (compareInProd f g).range.mkQ

-- mkq?
def Pushout.inl : N →ₗ[A] Pushout f g
    where
  toFun n := Pushout.π _ _ (n, 0)
  map_add' x y := by rw [← (pushout.π f g).map_add]; congr 1; ext <;> simp
  map_smul' r x := by rw [← (pushout.π f g).map_smul]; congr 1; ext <;> simp

def Pushout.inr : L →ₗ[A] Pushout f g
    where
  toFun l := Pushout.π _ _ (0, l)
  map_add' x y := by rw [← (pushout.π f g).map_add]; congr 1; ext <;> simp
  map_smul' r x := by rw [← (pushout.π f g).map_smul]; congr 1; ext <;> simp

theorem surjective_of_comp_inl_eq_comp_inr (f : M →ₗ[A] N)
    (h :
      Pushout.inl f.range.Subtype f.range.Subtype = Pushout.inr f.range.Subtype f.range.Subtype) :
    Function.Surjective f := by
  intro b
  apply_fun fun e => e b at h 
  dsimp [pushout.inl, pushout.inr, pushout.π] at h 
  rw [Submodule.Quotient.eq] at h 
  simp at h 
  obtain ⟨⟨a, ⟨a, rfl⟩⟩, ht⟩ := h
  dsimp [compare_in_prod] at ht 
  apply_fun fun e => e.fst at ht 
  use a
  exact ht

end Module

open CategoryTheory

namespace ModuleCat

universe u

theorem surjective_of_epi {A : Type u} [Ring A] {M N : ModuleCat.{u} A} (f : M ⟶ N) [Epi f] :
    Function.Surjective f :=
  by
  apply Module.surjective_of_comp_inl_eq_comp_inr
  apply_fun ModuleCat.ofHom
  swap; · tidy
  erw [← cancel_epi f]
  change LinearMap.comp _ _ = LinearMap.comp _ _
  ext
  dsimp [ModuleCat.ofHom, Module.Pushout.inl, Module.Pushout.inr, Module.Pushout.π]
  rw [Submodule.Quotient.eq]
  simp
  use⟨_, ⟨x, rfl⟩⟩
  rfl

end ModuleCat

