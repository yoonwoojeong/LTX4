import LiquidTensorExperiment.FreePfpng.Basic
import LiquidTensorExperiment.Condensed.ProjectiveResolution
import LiquidTensorExperiment.Condensed.Condensify
import LiquidTensorExperiment.Condensed.Adjunctions
import LiquidTensorExperiment.Condensed.SheafificationMono
import LiquidTensorExperiment.Condensed.Coproducts
import LiquidTensorExperiment.FreePfpng.Lemmas
import LiquidTensorExperiment.Condensed.Exact
import LiquidTensorExperiment.ForMathlib.Int
import LiquidTensorExperiment.ForMathlib.AddCommGroupInstances

#align_import free_pfpng.setup

noncomputable section

open scoped Classical

open CategoryTheory

open Opposite

universe u

def Profinite.condensedFreePfpng (S : Profinite.{u}) : Condensed Ab :=
  CompHausFiltPseuNormGrp.toCondensed.obj <|
    cHFPNG₁ToCHFPNGₑₗ.obj (pFPNG₁ToCHFPNG₁ₑₗ.obj S.FreePfpng)

def Profinite.toFreePfpngLevel (S : Profinite.{u}) :
    S.toCondensed ⟶ ((ProFiltPseuNormGrp₁.level.obj 1).obj S.FreePfpng).toCondensed :=
  profiniteToCondensed.map <| S.toFreePfpng

def Profinite.toCondensedFreePfpng (S : Profinite.{u}) :
    S.toCondensed ⟶ condensedAbToCondensedSet.obj S.condensedFreePfpng :=
  S.toFreePfpngLevel ≫
    (CompHausFiltPseuNormGrp.levelCondensedDiagramCocone
            (cHFPNG₁ToCHFPNGₑₗ.obj (pFPNG₁ToCHFPNG₁ₑₗ.obj S.FreePfpng))).ι.app
      ⟨1⟩

@[simp]
theorem Profinite.toCondensedFreePfpng_app (S T : Profinite.{u}) (f) :
    S.toCondensedFreePfpng.val.app (op T) f =
      ULift.up
        ⟨_, 1, S.toFreePfpng ∘ (ULift.down f).1, S.toFreePfpng.2.comp (ULift.down f).2, rfl⟩ :=
  rfl

/-
def profinite_to_condensed_unit :
  Profinite_to_Condensed ⟶
  Profinite.extend free_pfpng_functor ⋙
  PFPNG₁_to_CHFPNG₁ₑₗ ⋙
  CHFPNG₁_to_CHFPNGₑₗ ⋙
  CompHausFiltPseuNormGrp.to_Condensed ⋙
  Condensed_Ab_to_CondensedSet :=
{ app := λ S, S.to_condensed_free_pfpng,
  naturality' := λ S T f, begin
    ext X s x, induction X using opposite.rec,
    dsimp at x,
    admit
  end }
-/
def Profinite.free' (S : Profinite.{u}) : Condensed.{u} Ab.{u + 1} :=
  condensedSetToCondensedAb'.obj S.toCondensed

def Profinite.free'Lift (S : Profinite.{u}) {A : Condensed.{u} Ab.{u + 1}}
    (η : S.toCondensed ⟶ condensedAbToCondensedSet.obj A) : S.free' ⟶ A :=
  (condensedAbCondensedSetAdjunction'.homEquiv _ _).symm η

def free'Lift {X : Type (u + 1)} {A : Ab.{u + 1}} (f : X → A) : AddCommGroupCat.free'.obj X ⟶ A :=
  (AddCommGroupCat.adj'.homEquiv _ _).symm f

-- TODO: Consider redefining `AddCommGroup.free'` so that this is true by rfl.
theorem free'Lift_eq_finsupp_lift {X : Type (u + 1)} {A : Ab.{u + 1}} (f : X → A) :
    free'Lift f = (Finsupp.lift _ _ _ f).toAddMonoidHom :=
  by
  dsimp [free'Lift]
  apply_fun AddCommGroup.adj'.hom_equiv X A
  rw [Equiv.apply_symm_apply]
  dsimp [AddCommGroupCat.adj', adjunction.of_nat_iso_left, AddCommGroupCat.freeIsoFree']
  simp only [adjunction.hom_equiv_unit, forget_map_eq_coe]
  dsimp [AddCommGroupCat.adj, AddCommGroupCat.free]
  ext i
  simp only [types_comp_apply, comp_apply, AddEquiv.coe_toAddMonoidHom,
    FreeAbelianGroup.equivFinsupp_apply, LinearMap.toAddMonoidHom_coe, Finsupp.lift_apply]
  change _ = (FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of i)).Sum _
  simp only [FreeAbelianGroup.toFinsupp_of, Finsupp.sum_single_index, zero_smul, one_zsmul]

open CategoryTheory.GrothendieckTopology

theorem Profinite.free'Lift_val_eq_sheafification_lift (S : Profinite.{u})
    {A : Condensed.{u} Ab.{u + 1}} (η : S.toCondensed ⟶ condensedAbToCondensedSet.obj A)
    (T : Profinite.{u}) :
    (S.free'Lift η).val.app (Opposite.op T) =
      (sheafifyLift _ (((AddCommGroupCat.adj'.whiskeringRight _).homEquiv _ _).symm η.val)
            A.cond).app
        (Opposite.op T) :=
  rfl

def Profinite.free'ToCondensedFreePfpng (S : Profinite.{u}) : S.free' ⟶ S.condensedFreePfpng :=
  S.free'Lift S.toCondensedFreePfpng

--instance : limits.has_limits_of_size.{u u} Ab.{u+1} :=
--category_theory.limits.has_limits_of_size_shrink.{u u (u+1) (u+1)} Ab.{u+1}
/-- the limit `lim_i ℤ[S_i]`. -/
def Profinite.limitFree (S : Profinite.{u}) : Ab.{u + 1} :=
  Limits.limit <| (S.fintypeDiagram ⋙ forget FintypeCat ⋙ AddCommGroupCat.free') ⋙ Ab.ulift.{u + 1}

-- move me
theorem Finsupp.mapDomain_equiv_fun_on_fintype_symm {α β R : Type _} [Fintype α] [Semiring R]
    (f : α → β) (g : α → R) :
    Finsupp.mapDomain f (finsupp.equiv_fun_on_fintype.symm g) =
      Finset.univ.Sum fun x : α => Finsupp.single (f x) (g x) :=
  by
  dsimp [Finsupp.mapDomain]
  rw [Finsupp.sum_fintype]; swap; · intro; apply Finsupp.single_zero
  simp only [finsupp.equiv_fun_on_fintype_symm_apply_to_fun]

-- move me
theorem Finsupp.mapDomain_equiv_fun_on_fintype_symm_apply {α β R : Type _} [Fintype α] [Semiring R]
    (f : α → β) (g : α → R) (b : β) [DecidablePred fun a : α => f a = b] :
    Finsupp.mapDomain f (finsupp.equiv_fun_on_fintype.symm g) b =
      (Finset.filter (fun a : α => f a = b) Finset.univ).Sum g :=
  by
  rw [Finsupp.mapDomain_equiv_fun_on_fintype_symm, Finset.sum_apply']
  classical simp only [Finsupp.single_apply, ← Finset.sum_filter]

def Profinite.condensedFreePfpngSpecializeCone (S B : Profinite.{u}) (b : B) :
    Limits.Cone ((S.fintypeDiagram ⋙ forget FintypeCat ⋙ AddCommGroupCat.free') ⋙ Ab.ulift.{u + 1})
    where
  pt := S.condensedFreePfpng.val.obj (op B)
  π :=
    { app := fun T =>
        AddMonoidHom.mk'
          (fun t => ⟨finsupp.equiv_fun_on_fintype.symm (S.freePfpngπ T (t.down.1 b))⟩)
          (by
            intro f g
            ext x
            simp only [ULift.add_down, Subtype.val_eq_coe,
              finsupp.equiv_fun_on_fintype_symm_apply_to_fun, Finsupp.coe_add, Pi.add_apply]
            erw [StrictComphausFilteredPseudoNormedGroupHom.map_add]
            rfl)
      naturality' := fun T₁ T₂ f => by
        ext g x
        rw [← Profinite.freePfpngπ_w _ f]
        simp only [Subtype.val_eq_coe, finsupp.equiv_fun_on_fintype_symm_apply_to_fun,
          functor.const_obj_map, comp_apply, id_apply, AddMonoidHom.mk'_apply, functor.comp_map,
          forget_map_eq_coe, concrete_category.has_coe_to_fun_Type, AddCommGroupCat.free'_map,
          Ab.uLift_map_apply_down, Finsupp.mapDomain.addMonoidHom_apply, FreePfpng.map,
          freePfpngFunctor_map, StrictComphausFilteredPseudoNormedGroupHom.coe_mk]
        classical
        rw [Finsupp.mapDomain_equiv_fun_on_fintype_symm_apply]
        congr }

def Profinite.condensedFreePfpngSpecialize (S B : Profinite.{u}) (b : B) :
    S.condensedFreePfpng.val.obj (op B) ⟶ S.limitFree :=
  Limits.limit.lift _ (S.condensedFreePfpngSpecializeCone B b)

theorem Finsupp.fun_ext {α γ : Type _} [AddCommGroup γ] (f g : (α →₀ ℤ) → γ)
    (haddf : ∀ x y, f (x + y) = f x + f y) (haddg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ x : α, f (Finsupp.single x 1) = g (Finsupp.single x 1)) : f = g :=
  congr_arg AddMonoidHom.toFun <|
    @Finsupp.addHom_ext α ℤ γ _ _ (AddMonoidHom.mk' f haddf) (AddMonoidHom.mk' g haddg)
      (by
        intro x n
        apply Int.induction_on_iff n <;> clear n
        · simp only [Finsupp.single_zero, map_zero]
        · intro n
          · simp only [Finsupp.single_add, map_add]
            simp only [h, AddMonoidHom.mk'_apply, add_left_inj])

def ProFiltPseuNormGrp₁.limit_π_coe_eq {r : NNReal} {J : Type u} [SmallCategory J]
    (F : J ⥤ ProFiltPseuNormGrp₁.{u}) (k : (ProFiltPseuNormGrp₁.level.obj r).obj (Limits.limit F))
    (j) :
    Limits.limit.π F j (k.1 : Limits.limit F) =
      (((ProFiltPseuNormGrp₁.level.obj r).map (Limits.limit.π F j)) k).1 :=
  rfl

