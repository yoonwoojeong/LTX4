import Mathlib.CategoryTheory.Abelian.Opposite

#align_import for_mathlib.sum_str

noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐]

structure SumStr (A B X : 𝓐) where
  inl : A ⟶ X
  inr : B ⟶ X
  fst : X ⟶ A
  snd : X ⟶ B
  inl_fst : inl ≫ fst = 𝟙 _
  inr_snd : inr ≫ snd = 𝟙 _
  inl_snd : inl ≫ snd = 0
  inr_fst : inr ≫ fst = 0
  Total : fst ≫ inl + snd ≫ inr = 𝟙 _

namespace SumStr

variable {A B X : 𝓐}

attribute [simp, reassoc] SumStr.inl_fst SumStr.inr_snd SumStr.inl_snd SumStr.inr_fst

@[simps]
def biprod (A B : 𝓐) : SumStr A B (A ⊞ B)
    where
  inl := biprod.inl
  inr := biprod.inr
  fst := biprod.fst
  snd := biprod.snd
  inl_fst := biprod.inl_fst
  inr_snd := biprod.inr_snd
  inl_snd := biprod.inl_snd
  inr_fst := biprod.inr_fst
  Total := biprod.total

@[simps]
def symm (sum : SumStr A B X) : SumStr B A X
    where
  inl := Sum.inr
  inr := Sum.inl
  fst := Sum.snd
  snd := Sum.fst
  inl_fst := Sum.inr_snd
  inr_snd := Sum.inl_fst
  inl_snd := Sum.inr_fst
  inr_fst := Sum.inl_snd
  Total := by rw [add_comm, sum.total]

open CategoryTheory.Preadditive Opposite

section Iso

variable {X₁ X₂ : 𝓐} (S₁ : SumStr A B X₁) (S₂ : SumStr A B X₂)

@[simps]
def iso : X₁ ≅ X₂ where
  Hom := S₁.fst ≫ S₂.inl + S₁.snd ≫ S₂.inr
  inv := S₂.fst ≫ S₁.inl + S₂.snd ≫ S₁.inr
  hom_inv_id' := by
    simp only [comp_add, add_comp_assoc, category.assoc, add_comp, inl_fst_assoc, inl_snd_assoc,
      zero_comp, comp_zero, add_zero, inr_fst_assoc, inr_snd_assoc, zero_add, Total]
  inv_hom_id' := by
    simp only [comp_add, add_comp_assoc, category.assoc, add_comp, inl_fst_assoc, inl_snd_assoc,
      zero_comp, comp_zero, add_zero, inr_fst_assoc, inr_snd_assoc, zero_add, Total]

end Iso

@[simps]
protected def op (sum : SumStr A B X) : SumStr (op A) (op B) (op X)
    where
  inl := Sum.fst.op
  inr := Sum.snd.op
  fst := Sum.inl.op
  snd := Sum.inr.op
  inl_fst := by rw [← op_comp, sum.inl_fst, op_id]
  inr_snd := by rw [← op_comp, sum.inr_snd, op_id]
  inl_snd := by rw [← op_comp, sum.inr_fst, op_zero]
  inr_fst := by rw [← op_comp, sum.inl_snd, op_zero]
  Total := by rw [← op_comp, ← op_comp, ← op_add, sum.total, op_id]

@[simps]
protected def unop {A B X : 𝓐ᵒᵖ} (sum : SumStr A B X) : SumStr (unop A) (unop B) (unop X)
    where
  inl := Sum.fst.unop
  inr := Sum.snd.unop
  fst := Sum.inl.unop
  snd := Sum.inr.unop
  inl_fst := by rw [← unop_comp, sum.inl_fst, unop_id]
  inr_snd := by rw [← unop_comp, sum.inr_snd, unop_id]
  inl_snd := by rw [← unop_comp, sum.inr_fst, unop_zero]
  inr_fst := by rw [← unop_comp, sum.inl_snd, unop_zero]
  Total := by rw [← unop_comp, ← unop_comp, ← unop_add, sum.total, unop_id]

theorem symm_symm (sum : SumStr A B X) : Sum.symm.symm = Sum := by cases Sum; rfl

theorem op_symm (sum : SumStr A B X) : Sum.symm.op = Sum.op.symm := by cases Sum; rfl

theorem unop_symm {A B X : 𝓐ᵒᵖ} (sum : SumStr A B X) : Sum.symm.unop = Sum.unop.symm := by
  cases Sum; rfl

theorem unop_op (sum : SumStr A B X) : Sum.op.unop = Sum := by cases Sum; rfl

theorem op_unop {A B X : 𝓐ᵒᵖ} (sum : SumStr A B X) : Sum.unop.op = Sum := by cases Sum; rfl

end SumStr

