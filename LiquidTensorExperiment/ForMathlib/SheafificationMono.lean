import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Group.ULift
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Kernels
import LiquidTensorExperiment.ForMathlib.AddCommGroup.ExplicitLimits
import LiquidTensorExperiment.ForMathlib.AbelianCategory
import LiquidTensorExperiment.ForMathlib.AbelianSheaves.Main

#align_import for_mathlib.sheafification_mono

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe u

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)

variable {F : Cᵒᵖ ⥤ Ab.{u + 1}} {G : Sheaf J Ab.{u + 1}}

@[simps]
def kernelForkPoint (η : F ⟶ G.val) : Cᵒᵖ ⥤ Ab.{u + 1}
    where
  obj X := AddCommGroupCat.of (η.app X).ker
  map X Y f :=
    { toFun := fun t =>
        ⟨F.map f t.1, by
          change (_ ≫ η.app Y) _ = 0; rw [nat_trans.naturality]
          rcases t with ⟨t, ht : η.app X t = 0⟩; dsimp
          simp [comp_apply, ht]⟩
      map_zero' := by ext; apply AddMonoidHom.map_zero
      map_add' := by intros; ext; apply AddMonoidHom.map_add }
  map_id' X := by ext; simp
  map_comp' X Y Z f g := by ext; simp

@[simps]
def kernelForkι (η : F ⟶ G.val) : kernelForkPoint J η ⟶ F
    where
  app T := (η.app _).ker.Subtype
  naturality' := by
    intro X Y f; ext
    simp only [comp_apply, AddSubgroup.coeSubtype, kernel_fork_point_map_apply_coe,
      Subtype.val_eq_coe]

@[simps]
def kernelFork (η : F ⟶ G.val) : KernelFork η :=
  KernelFork.ofι (kernelForkι _ η) (by ext X ⟨x, hx⟩; simpa using hx)

def isLimitKernelFork (η : F ⟶ G.val) : IsLimit (kernelFork J η) :=
  Fork.IsLimit.mk _
    (fun S =>
      { app := fun X =>
          { toFun := fun t =>
              ⟨S.ι.app _ t, by
                change (_ ≫ η.app _) _ = _; rw [← nat_trans.comp_app]
                rw [S.condition]
                simp only [comp_zero, nat_trans.app_zero, AddCommGroupCat.zero_apply]⟩
            map_zero' := by ext; apply AddMonoidHom.map_zero
            map_add' := by intros; ext; apply AddMonoidHom.map_add }
        naturality' := by
          intro X Y f; ext
          simp only [comp_apply, AddMonoidHom.coe_mk, AddSubgroup.coe_mk,
            kernel_fork_X_map_apply_coe]
          simpa only [← comp_apply, nat_trans.naturality] })
    (by
      intro s
      ext X t
      delta kernel_fork
      rw [kernel_fork.ι_of_ι, nat_trans.comp_app, kernel_fork_ι_app]
      rfl)
    (by
      delta kernel_fork kernel_fork.of_ι
      dsimp only [fork.of_ι_X, fork.of_ι_π_app]
      intro s m H
      simp only [← H]
      ext; rfl)

noncomputable instance : Abelian (Cᵒᵖ ⥤ Ab.{u + 1}) :=
  CategoryTheory.functorCategoryIsAbelian.{u + 2, u, u + 1}

noncomputable instance : PreservesLimits (forget Ab.{u + 1}) :=
  inferInstance

noncomputable instance : PreservesFilteredColimits (forget Ab.{u + 1}) :=
  inferInstance

noncomputable instance sheafificationPreservesFiniteLimits :
    PreservesFiniteLimits (J.sheafification Ab.{u + 1}) :=
  @sheafification.CategoryTheory.Limits.preservesFiniteLimits.{u + 2, u, u + 1} _ _ _ _ _ _ _ _
    (fun _ => inferInstance) _ _ _

theorem sheafifyLift_mono_iff (η : F ⟶ G.val) (K : Limits.KernelFork η) (hK : IsLimit K) :
    Mono (J.sheafifyLift η G.cond) ↔ IsZero (J.sheafify K.pt) :=
  by
  rw [mono_iff_is_zero_kernel]
  suffices E : kernel (J.sheafify_lift η G.cond) ≅ J.sheafify K.X
  · constructor
    · intro h; exact is_zero_of_iso_of_zero h E
    · intro h; exact is_zero_of_iso_of_zero h E.symm
  refine'
    _ ≪≫ (limit.is_limit _).conePointUniqueUpToIso (is_limit_of_preserves (J.sheafification _) hK)
  refine' has_limit.iso_of_nat_iso _
  symm
  refine' nat_iso.of_components _ _
  rintro (_ | _) <;> dsimp
  exact iso.refl _
  have : is_iso (J.to_sheafify G.val) := by apply is_iso_to_sheafify; exact G.2
  symm
  exact as_iso (J.to_sheafify G.val)
  rintro (_ | _) (_ | _) (_ | _)
  · dsimp; simp; erw [J.sheafify_map_id]; rfl
  · dsimp; rw [is_iso.comp_inv_eq]; simp
    apply J.sheafify_hom_ext
    apply (config := { instances := false }) J.sheafify_is_sheaf
    any_goals infer_instance
    intro X; infer_instance
    simp only [to_sheafify_naturality_assoc]
    rw [← J.sheafify_map_comp, J.to_sheafify_sheafify_lift]
  · dsimp
    simp only [comp_zero, preadditive.is_iso.comp_right_eq_zero]
    apply J.sheafify_hom_ext
    apply (config := { instances := false }) J.sheafify_is_sheaf
    any_goals infer_instance
    intro x; infer_instance
    simp only [comp_zero]
    rw [← J.to_sheafify_naturality, zero_comp]
  · dsimp; simp only [is_iso.comp_inv_eq]
    simp only [category.assoc, is_iso.eq_inv_comp]
    erw [(parallel_pair _ _).map_id, J.sheafify_map_id]
    dsimp; simp only [category.id_comp, category.comp_id]

open scoped ZeroObject

theorem isZero_ab (X : Ab) (hX : ∀ t : X, t = 0) : IsZero X := by rw [is_zero_iff_id_eq_zero]; ext;
  apply hX

theorem isZero_colimit_of_isZero {C A : Type _} [Category C] [Category A] [Abelian A] (F : C ⥤ A)
    [HasColimitsOfShape C A] (hF : IsZero F) : IsZero (colimit F) :=
  by
  let G : C ⥤ A := (CategoryTheory.Functor.const C).obj (⊥_ _)
  have hG : is_zero G := functor.is_zero _ fun X => is_zero_initial
  let e : G ≅ F := hG.iso hF
  refine' is_zero_of_iso_of_zero _ (colim.map_iso e)
  refine' is_zero_of_iso_of_zero is_zero_initial colimit_const_initial.symm

theorem isZero_limit_of_isZero {C A : Type _} [Category C] [Category A] [Abelian A] (F : C ⥤ A)
    [HasLimitsOfShape C A] (hF : IsZero F) : IsZero (limit F) :=
  by
  let G : C ⥤ A := (CategoryTheory.Functor.const C).obj (⊤_ _)
  have hG : is_zero G := functor.is_zero _ fun X => is_zero_terminal
  let e : G ≅ F := hG.iso hF
  refine' is_zero_of_iso_of_zero _ (lim.map_iso e)
  refine' is_zero_of_iso_of_zero is_zero_terminal limit_const_terminal.symm

theorem isZero_plus_of_isZero (F : Cᵒᵖ ⥤ Ab.{u + 1}) (hF : IsZero F) : IsZero (J.plusObj F) :=
  by
  rw [functor.is_zero_iff]; intro X
  apply is_zero_colimit_of_is_zero
  rw [functor.is_zero_iff] at hF ⊢
  intro W
  apply is_zero_limit_of_is_zero
  rw [functor.is_zero_iff]; intro P
  cases P <;> apply hF

theorem eq_zero_of_exists {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Ab.{u}) (j)
    (t : F.obj j) (ht : ∃ (e : J) (q : j ⟶ e), F.map q t = 0) : colimit.ι F j t = 0 :=
  by
  rcases ht with ⟨e, q, hq⟩
  rw [← colimit.w F q, comp_apply, hq, map_zero]

theorem eq_zero_of_forall {J : Type u} [SmallCategory J] (F : J ⥤ Ab.{u}) (t : limit F)
    (ht : ∀ j, limit.π F j t = 0) : t = 0 :=
  by
  let t' : AddCommGroupCat.of (FreeAbelianGroup PUnit) ⟶ limit F :=
    AddCommGroupCat.ofHom (FreeAbelianGroup.lift fun _ => t)
  suffices t' = 0 by
    simpa only [t', AddCommGroupCat.ofHom, FreeAbelianGroup.lift.of] using
      FunLike.congr_fun this (FreeAbelianGroup.of PUnit.unit)
  apply limit.hom_ext
  intro j
  ext x; cases x
  simpa only [t', AddCommGroupCat.ofHom, FreeAbelianGroup.lift.of, comp_apply, map_zero,
    AddMonoidHom.zero_apply] using ht j

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic tactic.op_induction' -/
theorem isZero_of_exists_cover (F : Cᵒᵖ ⥤ Ab.{u + 1})
    (h : ∀ (B : C) (t : F.obj (op B)), ∃ W : J.cover B, ∀ f : W.arrow, F.map f.f.op t = 0) :
    IsZero (J.sheafify F) :=
  by
  -- This proof is a mess...
  apply is_zero_plus_of_is_zero
  rw [functor.is_zero_iff]
  intro B;
  run_tac
    tactic.op_induction'
  apply is_zero_Ab
  intro t
  obtain ⟨W, y, rfl⟩ := concrete.is_colimit_exists_rep _ (colimit.is_colimit _) t
  apply eq_zero_of_exists
  let z := concrete.multiequalizer_equiv _ y
  choose Ws hWs using fun i => h _ (z.1 i)
  let T : J.cover B := W.unop.bind Ws; use op T
  use(W.unop.bind_to_base _).op
  apply_fun concrete.multiequalizer_equiv _; swap; infer_instance
  ext
  dsimp; rw [AddMonoidHom.map_zero]
  dsimp [diagram]
  simp only [← comp_apply, multiequalizer.lift_ι]
  dsimp [cover.index] at x 
  dsimp only [cover.index] at hWs 
  dsimp [cover.arrow.map]
  cases' x with Z x hx; rcases hx with ⟨A, g, f, hf, hA, rfl⟩
  dsimp at hA ⊢
  specialize hWs ⟨_, f, hf⟩ ⟨_, g, hA⟩
  convert hWs
  dsimp [z]
  simp only [← comp_apply]; congr 2
  rw [←
    category.comp_id
      (multiequalizer.ι ((unop W).index F)
        { y := Z
          f := g ≫ f
          hf := _ })]
  let R : W.unop.relation := ⟨_, _, _, g, 𝟙 _, f, g ≫ f, _, _, _⟩
  symm
  convert multiequalizer.condition (W.unop.index F) R
  dsimp [cover.index]; rw [F.map_id]; rw [category.id_comp]

theorem sheafifyLift_mono_of_exists_cover (η : F ⟶ G.val)
    (h :
      ∀ (B : C) (t : F.obj (op B)) (ht : η.app _ t = 0),
        ∃ W : J.cover B, ∀ f : W.arrow, F.map f.f.op t = 0) :
    Mono (J.sheafifyLift η G.cond) :=
  by
  rw [sheafify_lift_mono_iff J η (kernel_fork J η) (is_limit_kernel_fork J η)]
  apply is_zero_of_exists_cover
  rintro B ⟨t, ht⟩
  specialize h B t ht
  obtain ⟨W, hW⟩ := h
  use W; intro f
  ext; apply hW

end CategoryTheory.GrothendieckTopology

