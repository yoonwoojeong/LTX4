import Mathlib.CategoryTheory.Limits.ConcreteCategory

#align_import for_mathlib.types

namespace CategoryTheory.types

open CategoryTheory

open CategoryTheory.Limits

universe u

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Type u)

def filteredColimitSetoid : Setoid (Σ j : J, F.obj j)
    where
  R x y := ∃ (e : J) (i : x.1 ⟶ e) (j : y.1 ⟶ e), F.map i x.2 = F.map j y.2
  iseqv := by
    refine' ⟨_, _, _⟩
    · intro x; use x.1, 𝟙 _, 𝟙 _
    · rintro ⟨x, a⟩ ⟨y, b⟩ ⟨e, i, j, h⟩; use e, j, i, h.symm
    · rintro ⟨x, a⟩ ⟨y, b⟩ ⟨z, c⟩ ⟨e₁, i₁, j₁, h₁⟩ ⟨e₂, i₂, j₂, h₂⟩
      let e₀ := is_filtered.max e₁ e₂; dsimp at *
      let e :=
        is_filtered.coeq (j₁ ≫ is_filtered.left_to_max e₁ e₂) (i₂ ≫ is_filtered.right_to_max e₁ e₂)
      let t : e₀ ⟶ e := is_filtered.coeq_hom _ _
      use e
      use i₁ ≫ is_filtered.left_to_max _ _ ≫ t
      use j₂ ≫ is_filtered.right_to_max _ _ ≫ t
      simp only [← h₂, h₁, functor_to_types.map_comp_apply]
      -- This is really annoying...
      change (F.map _ ≫ F.map _ ≫ F.map _) _ = (F.map _ ≫ F.map _ ≫ F.map _) _
      dsimp only [t]
      simp only [← F.map_comp, ← category.assoc, is_filtered.coeq_condition]

def filteredColimitCocone : Cocone F
    where
  pt := Quotient (filteredColimitSetoid F)
  ι :=
    { app := fun j t => Quotient.mk'' ⟨j, t⟩
      naturality' := by
        intro i j f; ext; dsimp; apply Quotient.sound'
        use j, 𝟙 _, f; simp }

def filteredColimitCoconeIsColimit (F : J ⥤ Type u) : IsColimit (filteredColimitCocone F)
    where
  desc S
    t :=-- ARRGH
      @Quotient.liftOn'
      (Σ j : J, F.obj j) S.pt _ t (fun x => S.ι.app x.1 x.2)
      (by
        rintro ⟨i, a⟩ ⟨j, b⟩ ⟨e, f, g, h⟩; dsimp at *
        rw [← S.w f]; rw [← S.w g]; simp only [types_comp_apply, h])
  fac S j := by ext; rfl
  uniq := by
    intro S m hm; ext ⟨⟨i, t⟩⟩; specialize hm i
    apply_fun fun e => e t at hm ; exact hm

end CategoryTheory.types

