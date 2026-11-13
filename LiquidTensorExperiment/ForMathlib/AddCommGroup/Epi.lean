import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.EpiMono

#align_import for_mathlib.AddCommGroup.epi

-- TODO: This should be integrated in the category theory library with a construction of an
-- TODO: This should be integrated in the category theory library with a construction of an
-- explicit pushout cocone, etc.
-- explicit pushout cocone, etc.
variable {A B C : Type _} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

def compareInProd (f : A →+ B) (g : A →+ C) : A →+ B × C
    where
  toFun a := (f a, -g a)
  map_zero' := by simp
  map_add' x y := by ext; simp; simp [add_comm]

def AddMonoidHom.Pushout (f : A →+ B) (g : A →+ C) : Type _ :=
  (B × C) ⧸ (compareInProd f g).range
deriving AddCommGroup

abbrev AddMonoidHom.pushoutπ (f : A →+ B) (g : A →+ C) : B × C →+ f.Pushout g :=
  QuotientAddGroup.mk' _

def AddMonoidHom.pushoutInl (f : A →+ B) (g : A →+ C) : B →+ f.Pushout g
    where
  toFun b := f.pushoutπ g (b, 0)
  map_zero' := by simp; use 0; simpa
  map_add' x y := by erw [QuotientAddGroup.eq_iff_sub_mem]; simp; use 0; simpa

def AddMonoidHom.pushoutInr (f : A →+ B) (g : A →+ C) : C →+ f.Pushout g
    where
  toFun b := f.pushoutπ g (0, b)
  map_zero' := by simp; use 0; simpa
  map_add' x y := by erw [QuotientAddGroup.eq_iff_sub_mem]; simp; use 0; simpa

theorem surjective_of_comp_inl_eq_comp_inr (f : A →+ B)
    (h : f.range.subtype.pushoutInl f.range.subtype = f.range.subtype.pushoutInr f.range.subtype) :
    Function.Surjective f := by
  intro b
  apply_fun fun e => e b at h 
  dsimp [AddMonoidHom.pushoutInl, AddMonoidHom.pushoutInr] at h 
  rw [QuotientAddGroup.eq_iff_sub_mem] at h 
  simp at h 
  obtain ⟨⟨a, ⟨a, rfl⟩⟩, ht⟩ := h
  dsimp [compareInProd] at ht 
  apply_fun fun e => e.fst at ht 
  use a
  exact ht

open CategoryTheory

theorem AddCommGroupCat.surjective_of_epi {A B : AddCommGroupCat} (f : A ⟶ B) [Epi f] :
    Function.Surjective f := by
  apply surjective_of_comp_inl_eq_comp_inr
  apply_fun AddCommGroupCat.ofHom
  swap; · tidy
  erw [← cancel_epi f]
  change AddMonoidHom.comp _ _ = AddMonoidHom.comp _ _
  ext
  dsimp [AddCommGroupCat.ofHom, AddMonoidHom.pushoutInl, AddMonoidHom.pushoutInr]
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp
  use⟨_, ⟨x, rfl⟩⟩
  rfl

universe u

open CategoryTheory CategoryTheory.Preadditive

namespace AddCommGroupCat

variable {X Y : AddCommGroupCat.{u}} (f : X ⟶ Y)

-- move this (also, it doesn't seem to be used any longer)
theorem AddMonoidHom.range_eq_top_iff {A B : Type _} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) : f.range = ⊤ ↔ Function.Surjective f :=
  by
  rw [eq_top_iff]
  constructor
  · rintro h x; exact h (AddSubgroup.mem_top x)
  · rintro h x -; exact h x

-- instance mono_as_hom'_subtype (U : add_subgroup X) : mono ↑U.subtype :=
-- (mono_iff_ker_eq_bot _).mpr (submodule.ker_subtype U)
-- instance epi_as_hom''_mkq (U : submodule R X) : epi ↿U.mkq :=
-- (epi_iff_range_eq_top _).mpr $ submodule.range_mkq _
end AddCommGroupCat

