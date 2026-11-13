import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitProducts

#align_import for_mathlib.AddCommGroup.direct_sum_colimit

open CategoryTheory

open CategoryTheory.Limits

namespace AddCommGroupCat

universe u

variable {J : Type u} [SmallCategory J] (F : J ⥤ AddCommGroupCat.{u})

open scoped Classical

noncomputable section

def explicitCoconePointKernel : AddSubgroup (DirectSum J fun i => F.obj i) :=
  AddSubgroup.closure
    {x |
      ∃ (i j : J) (f : i ⟶ j) (t : F.obj i), x = DirectSum.of _ j (F.map f t) - DirectSum.of _ i t}

def asSmallSucc (i : AsSmall.{u} ℕ) : AsSmall ℕ :=
  AsSmall.up.obj (AsSmall.down.obj i + 1)

def toAsSmallSucc (i : AsSmall.{u} ℕ) : i ⟶ asSmallSucc i :=
  AsSmall.up.map (homOfLE <| Nat.le_succ _)

theorem explicitCoconePointKernel_eq_of_asSmall_nat (F : AsSmall.{u} ℕ ⥤ AddCommGroupCat.{u}) :
    explicitCoconePointKernel F =
      AddSubgroup.closure
        {x |
          ∃ (i : _) (t : F.obj i),
            x =
              DirectSum.of (fun i => F.obj i) (asSmallSucc i) (F.map (toAsSmallSucc i) t) -
                DirectSum.of _ i t} :=
  by
  apply le_antisymm
  · erw [AddSubgroup.closure_le]
    rintro x ⟨⟨i⟩, ⟨j⟩, f, t, rfl⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = i + k :=
      haveI : i ≤ j := le_of_hom (as_small.down.map f)
      le_iff_exists_add.mp this
    induction' k with k hk
    · have : f = 𝟙 _; ext; rw [this]
      simp only [CategoryTheory.Functor.map_id, id_apply, SetLike.mem_coe]
      erw [sub_self]
      exact AddSubgroup.zero_mem _
    · let f₁ : as_small.up.obj i ⟶ as_small.up.obj (i + k) :=
        as_small.up.map (hom_of_le <| le_self_add)
      let f₂ : as_small.up.obj (i + k) ⟶ as_small.up.obj (i + (k + 1)) :=
        as_small.up.map (hom_of_le <| by nlinarith)
      have hf : f = f₁ ≫ f₂ := by ext; rw [hf]; clear hf
      specialize hk f₁
      let t' := _; change t' ∈ _; let s := _; change s ∈ _ at hk 
      rw [show t' = t' - s + s by simp]
      let A :=
        AddSubgroup.closure
          {x : DirectSum (as_small ℕ) fun i : as_small ℕ => ↥(F.obj i) |
            ∃ (i : as_small ℕ) (t : ↥(F.obj i)),
              x =
                (DirectSum.of (fun i : as_small ℕ => ↥(F.obj i)) (as_small_succ i))
                    ((F.map (to_as_small_succ i)) t) -
                  (DirectSum.of (fun i : as_small ℕ => ↥(F.obj i)) i) t}
      change _ ∈ A
      suffices t' - s ∈ A by exact A.add_mem this hk
      dsimp [t', s]; simp only [functor.map_comp, comp_apply, sub_sub_sub_cancel_right]
      apply AddSubgroup.subset_closure
      use as_small.up.obj (i + k)
      let tt : F.obj (as_small.up.obj (i + k)) := F.map f₁ t
      use tt
      congr
  · rw [AddSubgroup.closure_le]
    rintro x ⟨i, t, rfl⟩
    apply AddSubgroup.subset_closure
    refine' ⟨i, as_small_succ i, to_as_small_succ i, t, _⟩
    congr

def explicitCoconePoint : AddCommGroupCat.{u} :=
  AddCommGroupCat.of ((DirectSum J fun i => F.obj i) ⧸ explicitCoconePointKernel F)

def explicitCocone : Cocone F where
  pt := explicitCoconePoint F
  ι :=
    { app := fun j => AddMonoidHom.comp (QuotientAddGroup.mk' _) (DirectSum.of _ j)
      naturality' := by
        intro i j f; ext t
        dsimp
        simp only [comp_apply, AddMonoidHom.coe_comp, QuotientAddGroup.coe_mk', Function.comp_apply,
          id_apply]
        rw [QuotientAddGroup.eq_iff_sub_mem]
        apply AddSubgroup.subset_closure
        dsimp; refine' ⟨i, j, f, t, rfl⟩ }

def isColimitExplicitCocone : IsColimit (explicitCocone F)
    where
  desc S :=
    QuotientAddGroup.lift _ (DirectSum.toAddMonoid fun i => S.ι.app _)
      (by
        intro t ht
        apply AddSubgroup.closure_induction ht
        · rintro x ⟨i, j, f, t, rfl⟩
          simp only [map_sub, DirectSum.toAddMonoid_of, cocone.w_apply, sub_self]
        · simp only [map_zero]
        · intro x y hx hy; simp only [hx, hy, map_add, add_zero]
        · intro x hx; simp only [hx, map_neg, neg_zero])
  fac := by
    intro S j; ext t; dsimp [explicit_cocone]
    simp only [DirectSum.toAddMonoid_of, comp_apply, AddMonoidHom.coe_comp,
      QuotientAddGroup.coe_mk', QuotientAddGroup.lift_mk]
  uniq := by
    intro S m hm; ext j t
    simp only [DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp, QuotientAddGroup.coe_mk',
      Function.comp_apply, QuotientAddGroup.lift_mk]
    rw [← hm]; rfl

end AddCommGroupCat

