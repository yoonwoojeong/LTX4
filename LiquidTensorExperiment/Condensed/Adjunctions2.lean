import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.Condensed.TopComparison

#align_import condensed.adjunctions2

noncomputable section

universe u

open CategoryTheory

namespace Sheaf

@[simps]
def homEquiv {C D : Type _} [Category C] [Category D] {J : GrothendieckTopology C}
    (F G : Sheaf J D) : (F ⟶ G) ≃ (F.val ⟶ G.val)
    where
  toFun f := f.val
  invFun f := ⟨f⟩
  left_inv f := by cases f; rfl
  right_inv f := rfl

end Sheaf

namespace Condensed

variable (M : Condensed.{u} Ab.{u + 1}) (S T : Profinite.{u}ᵒᵖ) (f : S ⟶ T)

def profiniteFreeAdjAux₁ :
    (condensedSetToCondensedAb.obj (Opposite.unop S).toCondensed ⟶ M) ≃
      ((Opposite.unop S).toCondensed ⟶ condensedAbToCondensedSet.obj M) :=
  condensedAbCondensedSetAdjunction.homEquiv S.unop.toCondensed M

theorem profiniteFreeAdjAux₁_naturality (x : condensedSetToCondensedAb.obj S.unop.toCondensed ⟶ M) :
    profiniteFreeAdjAux₁ _ _ (condensedSetToCondensedAb.map (profiniteToCondensed.map f.unop) ≫ x) =
      profiniteToCondensed.map f.unop ≫ profiniteFreeAdjAux₁ _ _ x :=
  by
  dsimp only [profinite_free_adj_aux₁]
  simpa only [adjunction.hom_equiv_naturality_left]

def profiniteFreeAdjAux₂ (M : Condensed.{u} Ab.{u + 1}) (S : Profinite.{u}ᵒᵖ) :
    ((Opposite.unop S).toCondensed ⟶ condensedAbToCondensedSet.obj M) ≃
      ((Opposite.unop S).toCondensed.val ⟶ (condensedAbToCondensedSet.obj M).val) :=
  Sheaf.homEquiv _ _

theorem profiniteFreeAdjAux₂_naturality (x : S.unop.toCondensed ⟶ condensedAbToCondensedSet.obj M) :
    profiniteFreeAdjAux₂ _ _ (profiniteToCondensed.map f.unop ≫ x) =
      (profiniteToCondensed.map f.unop).val ≫ profiniteFreeAdjAux₂ _ _ x :=
  rfl

def profiniteFreeAdjAux₃ (M : Condensed.{u} Ab.{u + 1}) (S : Profinite.{u}ᵒᵖ) :
    ((Opposite.unop S).toCondensed.val ⟶ (condensedAbToCondensedSet.obj M).val) ≃ M.val.obj S :=
  yoneda'Equiv _ _

theorem profiniteFreeAdjAux₃_naturality
    (x : (Opposite.unop S).toCondensed.val ⟶ (condensedAbToCondensedSet.obj M).val) :
    profiniteFreeAdjAux₃ _ _ ((profiniteToCondensed.map f.unop).val ≫ x) =
      (M.val.map f) (profiniteFreeAdjAux₃ _ _ x) :=
  by
  have := x.naturality f
  apply_fun fun e => e (ULift.up (𝟙 S.unop)) at this 
  exact this

def profiniteFreeAdjAux (M : Condensed.{u} Ab.{u + 1}) (S : Profinite.{u}ᵒᵖ) :
    AddCommGroupCat.of (condensedSetToCondensedAb.obj (Opposite.unop S).toCondensed ⟶ M) ≃+
      M.val.obj S :=
  {
    (profiniteFreeAdjAux₁ M S).trans
      ((profiniteFreeAdjAux₂ _ _).trans (profiniteFreeAdjAux₃ _ _)) with
    map_add' := fun f g => rfl }

def profiniteFreeAdj (M : Condensed.{u} Ab.{u + 1}) :
    (profiniteToCondensed ⋙ condensedSetToCondensedAb).op ⋙ preadditiveYoneda.obj M ≅ M.val :=
  NatIso.ofComponents
    (fun S => by
      apply AddEquiv.toAddCommGroupCatIso
      apply profinite_free_adj_aux)
    (by
      intro S T f; ext t
      change
        ((profinite_free_adj_aux₁ M T).trans
              ((profinite_free_adj_aux₂ M T).trans (profinite_free_adj_aux₃ M T)))
            _ =
          _
      dsimp only [Equiv.trans_apply, functor.comp_map, functor.op_map, preadditive_yoneda]
      erw [profinite_free_adj_aux₁_naturality]
      erw [profinite_free_adj_aux₂_naturality]
      erw [profinite_free_adj_aux₃_naturality]
      rfl)

end Condensed

