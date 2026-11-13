import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

#align_import for_mathlib.is_biprod

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {𝒜 ℬ : Type _} [Category 𝒜] [Category ℬ]

variable [Preadditive 𝒜] [Preadditive ℬ]

variable (F : 𝒜 ⥤ ℬ)

variable {A B : 𝒜} (C : 𝒜)

section IsBiprodVars

variable (inl : A ⟶ C) (inr : B ⟶ C) (fst : C ⟶ A) (snd : C ⟶ B)

structure IsBiprod where
  inl_fst : inl ≫ fst = 𝟙 _
  inr_snd : inr ≫ snd = 𝟙 _
  inl_snd : inl ≫ snd = 0
  inr_fst : inr ≫ fst = 0
  Total : fst ≫ inl + snd ≫ inr = 𝟙 _

variable {inl inr fst snd}

namespace IsBiprod

@[simps]
noncomputable def isoBiprod [HasBinaryBiproduct A B] (h : IsBiprod C inl inr fst snd) : C ≅ A ⊞ B
    where
  hom := biprod.lift fst snd
  inv := biprod.desc inl inr
  hom_inv_id' := by rw [biprod.lift_desc, h.total]
  inv_hom_id' := by
    ext <;>
      simp only [h.inl_fst, h.inl_snd, h.inr_fst, h.inr_snd, biprod.inl_fst, biprod.inl_snd,
        biprod.inr_fst, biprod.inr_snd, biprod.lift_fst, biprod.lift_snd, category.comp_id,
        biprod.inl_desc_assoc, biprod.inr_desc_assoc, category.assoc]

end IsBiprod

namespace Functor

def mapIsBiprod [F.Additive] (h : IsBiprod C inl inr fst snd) :
    IsBiprod (F.obj C) (F.map inl) (F.map inr) (F.map fst) (F.map snd)
    where
  inl_fst := by rw [← F.map_comp, h.inl_fst, F.map_id]
  inr_snd := by rw [← F.map_comp, h.inr_snd, F.map_id]
  inl_snd := by rw [← F.map_comp, h.inl_snd, F.map_zero]
  inr_fst := by rw [← F.map_comp, h.inr_fst, F.map_zero]
  Total := by rw [← F.map_comp, ← F.map_comp, ← F.map_add, h.total, F.map_id]

end Functor

end IsBiprodVars

namespace Biprod

variable (A B)

@[simps]
def isBiprod [HasBinaryBiproduct A B] : IsBiprod (A ⊞ B) biprod.inl biprod.inr biprod.fst biprod.snd
    where
  inl_fst := biprod.inl_fst
  inr_snd := biprod.inr_snd
  inl_snd := biprod.inl_snd
  inr_fst := biprod.inr_fst
  Total := biprod.total

end Biprod

end CategoryTheory

