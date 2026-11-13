import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import LiquidTensorExperiment.ForMathlib.Cech.Split
import LiquidTensorExperiment.ForMathlib.Profinite.ArrowLimit
import LiquidTensorExperiment.ForMathlib.Profinite.ClopenLimit
import LiquidTensorExperiment.ForMathlib.Simplicial.Complex
import LiquidTensorExperiment.LocallyConstant.Vhat
import LiquidTensorExperiment.Prop819.Completion

#align_import prop819

--import prop819.locally_constant
--import prop819.locally_constant
open scoped NNReal

noncomputable section

open CategoryTheory Opposite

open SemiNormedGroupCat

universe u v

-- We have a surjective morphism of profinite sets.
variable (F : Arrow Profinite.{u}) (surj : Function.Surjective F.Hom)

variable (M : SemiNormedGroupCat.{v})

/-- The cochain complex built out of the cosimplicial object obtained by applying
  `LocallyConstant.obj M` to the augmented Cech nerve of `F`. -/
abbrev fL : CochainComplex SemiNormedGroupCat ℕ :=
  (((CosimplicialObject.Augmented.whiskering _ _).obj (locallyConstant.obj M)).obj
      F.augmentedCechNerve.rightOp).toCocomplex

/-- The cochain complex built out of the cosimplicial object obtained by applying
  `LCC.obj M` to the augmented Cech nerve of `F`. -/
abbrev fLC : CochainComplex SemiNormedGroupCat ℕ :=
  (((CosimplicialObject.Augmented.whiskering _ _).obj (lCC.obj M)).obj
      F.augmentedCechNerve.rightOp).toCocomplex

--def Rop : (simplicial_object.augmented Profinite)ᵒᵖ ⥤ cosimplicial_object.augmented Profiniteᵒᵖ :=
--{ obj := λ X, X.unop.right_op,
--  map := λ X Y f,
--  { left := quiver.hom.op (comma_morphism.right f.unop),
--    right := nat_trans.right_op (comma_morphism.left f.unop),
--    w' := by { ext, exact congr_arg (λ η, (nat_trans.app η (op x)).op) f.unop.w.symm, } } }
/-- A functorial version of `FL`. -/
def fLFunctor : (Arrow Profinite.{u})ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ :=
  SimplicialObject.augmentedCechNerve.op ⋙
    simplicialToCosimplicialAugmented _ ⋙
      (CosimplicialObject.Augmented.whiskering _ _).obj (locallyConstant.obj M) ⋙
        CosimplicialObject.Augmented.cocomplex

/-- The functor sending an augmented cosimplicial object `X` to
  the cochain complex associated to the composition of `X` with `LCC.obj M`. -/
@[simps obj map]
def fLCFunctor' :
    (SimplicialObject.Augmented Profinite.{u})ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ :=
  simplicialToCosimplicialAugmented _ ⋙
    (CosimplicialObject.Augmented.whiskering _ _).obj (SemiNormedGroupCat.lCC.obj M) ⋙
      CosimplicialObject.Augmented.cocomplex

/-- A functorial version of `FLC`. -/
def fLCFunctor : (Arrow Profinite.{u})ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ :=
  SimplicialObject.augmentedCechNerve.op ⋙ fLCFunctor' M

-- Sanity checks
example : fL F M = (fLFunctor M).obj (op F) :=
  rfl

example : fLC F M = (fLCFunctor M).obj (op F) :=
  rfl

theorem CosimplicialObject.Augmented.cocomplex_map_normNoninc
    {C₁ C₂ : CosimplicialObject.Augmented SemiNormedGroupCat} (f : C₁ ⟶ C₂)
    (hf1 : f.left.NormNoninc) (hf2 : ∀ n, (f.right.app n).NormNoninc) (i : ℕ) :
    ((CosimplicialObject.Augmented.cocomplex.map f).f i).NormNoninc :=
  by
  cases i
  · exact hf1
  · exact hf2 _

theorem fLCFunctor_map_normNoninc {f g : (Arrow Profinite.{u})ᵒᵖ} (α : f ⟶ g) (i : ℕ) :
    (((fLCFunctor M).map α).f i).NormNoninc :=
  by
  refine' CosimplicialObject.Augmented.cocomplex_map_normNoninc _ _ _ _
  · exact SemiNormedGroupCat.lCC_obj_map_normNoninc _ _
  · intro n
    exact SemiNormedGroupCat.lCC_obj_map_normNoninc _ _

--⊢ cosimplicial_object.δ
--      (functor.right_op F.cech_nerve ⋙ (curry.obj (uncurry.obj LocallyConstant ⋙ Completion)).obj M)
--      k =
--    Completion.map (cosimplicial_object.δ (functor.right_op F.cech_nerve ⋙ LocallyConstant.obj M) k)
theorem FLC_iso_helper {x y : SimplexCategory} (f : x ⟶ y) :
    (F.cechNerve.rightOp ⋙ lCC.obj M).map f =
      completion.map ((F.cechNerve.rightOp ⋙ locallyConstant.obj M).map f) :=
  by
  change Completion.map _ = _
  congr 1
  dsimp [uncurry]
  erw [LocallyConstant.mapHom_id]
  change 𝟙 _ ≫ _ = _
  rw [category.id_comp]

/-- This is a strict (i.e. norm-preserving) isomorphism between `FLC F M` and
the cochain complex obtained by mapping `FL F M` along the `Completion` functor.
-/
def fLCIso : StrictIso ((completion.mapHomologicalComplex _).obj (fL F M)) (fLC F M)
    where
  Iso :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => Nat.recOn i (eqToIso rfl) fun _ _ => eqToIso rfl)
      (by
        rintro (_ | i) (_ | j) (_ | ⟨i, w⟩) <;> ext
        · dsimp only
          delta fLC fL
          dsimp only [cosimplicial_object.augmented.whiskering,
            cosimplicial_object.augmented.whiskering_obj,
            cosimplicial_object.augmented.to_cocomplex,
            cosimplicial_object.augmented.to_cocomplex_obj, CochainComplex.of,
            functor.map_homological_complex]
          rw [dif_pos rfl]
          rw [dif_pos rfl]
          erw [category.id_comp, category.comp_id, category.comp_id, category.comp_id]
          dsimp only [cosimplicial_object.augmented.to_cocomplex_d,
            cosimplicial_object.augmented.drop, comma.snd, cosimplicial_object.whiskering,
            whiskering_right, cosimplicial_object.coboundary, functor.const_comp, LCC]
          simp only [Quiver.Hom.unop_op, arrow.augmented_cech_nerve_hom_app, whisker_right_app,
            nat_trans.comp_app, curry_obj_obj_map, category.id_comp, nat_trans.right_op_app,
            uncurry_obj_map, nat_trans.id_app, simplicial_object.augmented.right_op_hom,
            CategoryTheory.Functor.map_id, CategoryTheory.Functor.comp_map,
            SemiNormedGroupCat.locallyConstant_obj_map, SemiNormedGroupCat.completion_map]
        · dsimp only
          delta fLC fL
          dsimp only [cosimplicial_object.augmented.whiskering,
            cosimplicial_object.augmented.whiskering_obj,
            cosimplicial_object.augmented.to_cocomplex,
            cosimplicial_object.augmented.to_cocomplex_obj, CochainComplex.of,
            functor.map_homological_complex]
          rw [dif_pos rfl]
          rw [dif_pos rfl]
          erw [category.id_comp, category.comp_id, category.comp_id, category.comp_id]
          dsimp only [cosimplicial_object.augmented.to_cocomplex_d,
            cosimplicial_object.augmented.drop, comma.snd, cosimplicial_object.whiskering,
            whiskering_right, cosimplicial_object.coboundary, LCC]
          rw [Completion.map_sum]
          congr
          funext k
          rw [Completion.map_zsmul]
          congr 1
          apply FLC_iso_helper)
  isStrict i := { strict_hom' := fun a => by cases i <;> rfl }

open scoped Simplicial

-- TODO: Move this to mathlib (also relax the has_limits condition).
/-- the isomorphism between the 0-th term of the Cech nerve and F.left-/
@[simps]
def cechIsoZero {C : Type _} [Category C] (F : Arrow C) [Limits.HasLimits C] :
    F.cechNerve _[0] ≅ F.left where
  Hom := Limits.WidePullback.π _ 0
  inv := Limits.WidePullback.lift F.Hom (fun _ => 𝟙 _) (by simp)
  hom_inv_id' := by
    apply limits.wide_pullback.hom_ext
    · intro i
      simp only [limits.wide_pullback.lift_π, category.id_comp, category.comp_id, category.assoc]
      congr
      tidy
    · simp

theorem augmentation_zero {C : Type _} [Category C] (F : Arrow C) [Limits.HasLimits C] :
    (cechIsoZero F).inv ≫ F.augmentedCechNerve.Hom.app _ = F.Hom := by tidy

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem locally_constant_norm_empty (X : Profinite) [IsEmpty X]
    (g : (locallyConstant.obj M).obj (op X)) : «expr∥ ∥» g = 0 :=
  by
  rw [LocallyConstant.norm_def]
  dsimp [iSup]
  suffices (Set.range fun x : ↥X => «expr∥ ∥» (g.to_fun x)) = ∅ by erw [this, Real.sSup_empty]
  simp only [Set.range_eq_empty]

theorem Profinite.coe_comp_apply {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  rfl

theorem locallyConstant_toFun_eq {X : Profinite} (f : LocallyConstant X M) : f.toFun = f :=
  rfl

theorem locallyConstant_eq {X : Profinite} (f g : LocallyConstant X M) :
    f.toFun = g.toFun ↔ f = g := by
  constructor
  · intro h; ext; change f.to_fun _ = _; rw [h]; rfl
  · intro h; rw [h]

theorem locallyConstant_eq_zero {X : Profinite} (f : LocallyConstant X M) :
    f = 0 ↔ Set.range f.toFun ⊆ {0} := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext x
    dsimp
    apply h
    use x
    rfl

theorem prop819_degree_zero_helper :
    Function.Surjective (Limits.WidePullback.base fun i : Fin 1 => F.Hom) :=
  by
  intro x
  obtain ⟨x, rfl⟩ := surj x
  dsimp at *
  refine' ⟨(cechIsoZero F).inv x, _⟩
  dsimp
  change (limits.wide_pullback.lift F.hom _ _ ≫ limits.wide_pullback.base _) _ = _
  simp

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem prop819_zero_norm_le (g : (locallyConstant.obj M).obj (op F.right)) :
    «expr∥ ∥» g ≤
      «expr∥ ∥»
        ((locallyConstant.obj M).map (Limits.WidePullback.base fun i : Fin 1 => F.Hom).op g) :=
  by
  cases isEmpty_or_nonempty F.right
  · simp only [locally_constant_norm_empty, norm_nonneg]
  · apply csSup_le
    · inhabit ↥F.right
      dsimp only [unop_op]
      refine' ⟨«expr∥ ∥» (g.to_fun _), default, rfl⟩
    · rintro z ⟨z, rfl⟩
      obtain ⟨z, rfl⟩ := (prop819_degree_zero_helper _ surj) z
      change «expr∥ ∥» (g.to_fun _) ≤ _
      erw [← LocallyConstant_map_apply M _ F.right (limits.wide_pullback.base fun i => F.hom) g z]
      apply LocallyConstant.norm_apply_le

open scoped ZeroObject

theorem prop819_degree_zero (f : (fLC F M).pt 0) (hf : (fLC F M).d 0 1 f = 0) : f = 0 :=
  by
  apply injective_of_strictIso _ _ (fLCIso F M) _ _ hf
  intro f hf
  have :=
    @controlled_exactness ((fL F M).pt 0) (0 : SemiNormedGroupCat) ((fL F M).pt 1) _ _ _ 0 1
      zero_lt_one 1 ((fL F M).d _ _) _ _ 1 zero_lt_one f _
  · rcases this with ⟨g, h1, h2⟩
    rw [← h1]
    simp
  · intro g hg
    refine' ⟨0, _, by simp⟩
    change (fL F M).d 0 1 g = 0 at hg 
    dsimp
    symm
    delta fL at hg 
    dsimp only [cosimplicial_object.augmented.whiskering,
      cosimplicial_object.augmented.whiskering_obj, cosimplicial_object.augmented.to_cocomplex,
      CochainComplex.of] at hg 
    rw [dif_pos] at hg 
    swap; · simp
    dsimp [cosimplicial_object.augmented.to_cocomplex_d] at hg 
    ext x
    obtain ⟨x, rfl⟩ := (prop819_degree_zero_helper F surj) x
    apply_fun fun e => e x at hg 
    rw [LocallyConstant.coe_comap] at hg 
    swap; · continuity
    exact hg
  · rintro g ⟨g, rfl⟩
    refine' ⟨g, rfl, _⟩
    dsimp [cosimplicial_object.augmented.to_cocomplex_d]
    simp only [LocallyConstant.comapHom_apply, one_mul, if_true, eq_self_iff_true, category.id_comp,
      category.comp_id]
    apply prop819_zero_norm_le _ surj
  · exact hf

/-- Any discrete quotient `S` of `F.left` yields a cochain complex, as follows.
First, let `T` be the maximal quotient of `F.right` such that `F.hom : F.left ⟶ F.right`
descends to `S → T`. Next construct the augmented Cech nerve of `S → T`, and finally
apply `FL_functor M` to this augmented Cech nerve.
-/
def fLF : (DiscreteQuotient F.left)ᵒᵖ ⥤ CochainComplex SemiNormedGroupCat ℕ :=
  (Profinite.arrowDiagram F surj).op ⋙ fLFunctor M

/-- The diagram of cochain complexes given by `FLF F surj` fits together into a cocone
whose cocone point is defeq to `FL F M`. This is precisely this cocone.
-/
def fLFCocone : Limits.Cocone (fLF F surj M) :=
  (fLFunctor M).mapCocone <| (Profinite.arrowCone F surj).op

open Profinite

theorem exists_locally_constant_fLF (n : ℕ) (f : (fL F M).pt (n + 1)) :
    ∃ (S : DiscreteQuotient F.left) (g : ((fLF F surj M).obj (op S)).pt (n + 1)),
      ((fLFCocone F surj M).ι.app (op S)).f _ g = f :=
  by
  have hC := Cech_cone_is_limit F surj n
  obtain ⟨i, g, hg⟩ := Profinite.exists_locallyConstant _ hC f
  use i, g
  exact hg.symm

theorem fLFCocone_app_coe_eq (n : ℕ) (S : DiscreteQuotient F.left)
    (g : ((fLF F surj M).obj (op S)).pt (n + 1)) :
    (((fLFCocone F surj M).ι.app (op S)).f _ g).toFun = g.toFun ∘ (cechCone F surj n).π.app _ :=
  by
  ext x
  change LocallyConstant.comap _ _ _ = _
  rw [LocallyConstant.coe_comap]
  swap; · continuity
  rfl

theorem fLF_map_coe_eq (n : ℕ) (S T : DiscreteQuotient F.left) (hh : T ≤ S)
    (g : ((fLF F surj M).obj (op S)).pt (n + 1)) :
    (((fLF F surj M).map (homOfLE hh).op).f _ g).toFun =
      g.toFun ∘ (cechConeDiagram F surj n).map (homOfLE hh) :=
  by
  ext x
  change LocallyConstant.comap _ _ _ = _
  rw [LocallyConstant.coe_comap]
  swap; · continuity
  rfl

theorem eq_zero_fLF (n : ℕ) (S : DiscreteQuotient F.left)
    (g : ((fLF F surj M).obj (op S)).pt (n + 1))
    (hg : ((fLFCocone F surj M).ι.app (op S)).f _ g = 0) :
    ∃ (T : DiscreteQuotient F.left) (hT : T ≤ S), ((fLF F surj M).map (homOfLE hT).op).f _ g = 0 :=
  by
  have :=
    exists_image (Cech_cone_diagram F surj n) (Cech_cone F surj n) (Cech_cone_is_limit F surj n) S
  obtain ⟨T, hT, hh⟩ := this
  use T; use hT
  rw [locallyConstant_eq_zero, fLF_map_coe_eq]
  rw [locallyConstant_eq_zero, fLFCocone_app_coe_eq] at hg 
  rintro x ⟨x, rfl⟩
  apply hg
  let P : (Cech_cone F surj n).pt ⟶ (Cech_cone_diagram F surj n).obj S :=
    (Cech_cone F surj n).π.app _
  let p : (Cech_cone_diagram F surj n).obj T ⟶ (Cech_cone_diagram F surj n).obj S :=
    (Cech_cone_diagram F surj n).map (hom_of_le hT)
  change ↥((Cech_cone_diagram F surj n).obj T) at x 
  have : p x ∈ Set.range p; use x
  erw [← hh] at this 
  obtain ⟨y, hy⟩ := this
  dsimp only [p] at hy 
  use y
  dsimp only [Function.comp_apply]
  erw [hy]

theorem d_eq_zero_fLF (n : ℕ) (S : DiscreteQuotient F.left)
    (g : ((fLF F surj M).obj (op S)).pt (n + 1))
    (hg : (fL F M).d (n + 1) (n + 2) (((fLFCocone F surj M).ι.app (op S)).f _ g) = 0) :
    ∃ (T : DiscreteQuotient F.left) (hT : T ≤ S),
      ((fLF F surj M).obj (op T)).d (n + 1) (n + 2)
          (((fLF F surj M).map <| (homOfLE hT).op).f _ g) =
        0 :=
  by
  have := ((fLFCocone F surj M).ι.app (op S)).comm (n + 1) (n + 2)
  apply_fun fun e => e g at this 
  erw [this] at hg 
  dsimp only [SemiNormedGroupCat.coe_comp] at hg 
  have := eq_zero_fLF F surj M (n + 1) S _ hg
  obtain ⟨T, hT, h⟩ := this
  use T; use hT
  have hh := ((fLF F surj M).map (hom_of_le hT).op).comm (n + 1) (n + 2)
  apply_fun fun e => e g at hh 
  erw [← hh] at h 
  exact h

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem norm_eq_fLF (n : ℕ) (S : DiscreteQuotient F.left)
    (g : ((fLF F surj M).obj (op S)).pt (n + 1)) :
    ∃ (T : DiscreteQuotient F.left) (hT : T ≤ S),
      «expr∥ ∥₊» (((fLFCocone F surj M).ι.app (op S)).f _ g) =
        «expr∥ ∥₊» (((fLF F surj M).map (homOfLE hT).op).f _ g) :=
  by
  have :=
    exists_image (Cech_cone_diagram F surj n) (Cech_cone F surj n) (Cech_cone_is_limit F surj n) S
  obtain ⟨T, hT, hh⟩ := this
  use T; use hT
  ext
  dsimp
  change Sup _ = Sup _
  congr 1
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    dsimp only
    change ↥(Cech_cone F surj n).pt at x 
    use(Cech_cone F surj n).π.app T x
    dsimp only
    rw [← locallyConstant_toFun_eq, fLF_map_coe_eq, Function.comp_apply, ← Profinite.coe_comp_apply,
      (Cech_cone F surj n).w, ← locallyConstant_toFun_eq, fLFCocone_app_coe_eq]
    rfl
  · rintro ⟨x, rfl⟩
    dsimp only
    change ↥((Cech_cone_diagram F surj n).obj T) at x 
    have :
      (Cech_cone_diagram F surj n).map (hom_of_le hT) x ∈
        Set.range ((Cech_cone_diagram F surj n).map (hom_of_le hT))
    use x
    rw [← hh] at this 
    obtain ⟨y, hy⟩ := this
    change ↥(Cech_cone F surj n).pt at y 
    use y
    dsimp only
    simp_rw [← locallyConstant_toFun_eq]
    rw [fLF_map_coe_eq, fLFCocone_app_coe_eq]
    dsimp only [Function.comp_apply]
    erw [hy]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem exists_locally_constant (n : ℕ) (f : (fL F M).pt (n + 1))
    (hf : (fL F M).d _ (n + 2) f = 0) :-- TODO: ∃ ..., true looks a bit fuuny
    ∃ (S : DiscreteQuotient F.left) (g : ((fLF F surj M).obj (op S)).pt (n + 1)) (hgf :
      ((fLFCocone F surj M).ι.app (op S)).f _ g = f) (hgd :
      ((fLF F surj M).obj (op S)).d _ (n + 2) g = 0) (hgnorm : «expr∥ ∥₊» f = «expr∥ ∥₊» g), True :=
  by
  obtain ⟨S, f, rfl⟩ := exists_locally_constant_fLF F surj M n f
  obtain ⟨T1, hT1, h1⟩ := d_eq_zero_fLF F surj M n S f hf
  obtain ⟨T2, hT2, h2⟩ := norm_eq_fLF F surj M n S f
  let T := T1 ⊓ T2
  have hT : T ≤ S := le_trans inf_le_left hT1
  have hhT1 : T ≤ T1 := inf_le_left
  have hhT2 : T ≤ T2 := inf_le_right
  let g := ((fLF F surj M).map (hom_of_le hT).op).f _ f
  let g1 := ((fLF F surj M).map (hom_of_le hT1).op).f _ f
  let g2 := ((fLF F surj M).map (hom_of_le hT2).op).f _ f
  have hg1 : ((fLF F surj M).map (hom_of_le hhT1).op).f _ g1 = g :=
    by
    dsimp only [g, g1]
    have : (hom_of_le hT).op = (hom_of_le hT1).op ≫ (hom_of_le hhT1).op; rfl
    rw [this, functor.map_comp]
    rfl
  have hg2 : ((fLF F surj M).map (hom_of_le hhT2).op).f _ g2 = g :=
    by
    dsimp only [g, g2]
    have : (hom_of_le hT).op = (hom_of_le hT2).op ≫ (hom_of_le hhT2).op; rfl
    rw [this, functor.map_comp]
    rfl
  refine' ⟨T, g, _, _, _, trivial⟩
  · rw [← (fLFCocone F surj M).w (hom_of_le hT).op]
    rfl
  · rw [← hg1]
    have := ((fLF F surj M).map (hom_of_le hhT1).op).comm (n + 1) (n + 2)
    apply_fun fun e => e g1 at this 
    erw [this]; clear this
    dsimp only [g1, SemiNormedGroupCat.coe_comp, Function.comp_apply]
    rw [h1, map_zero]
  · apply le_antisymm
    · dsimp only [g]
      have := (fLFCocone F surj M).w (hom_of_le hT).op
      rw [← this]; clear this
      apply LocallyConstant_obj_map_norm_noninc
    · rw [← hg2, h2]
      apply LocallyConstant_obj_map_norm_noninc

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem fLF_norm_noninc (n : ℕ) (S : DiscreteQuotient F.left)
    (f : ((fLF F surj M).obj (op S)).pt n) :
    «expr∥ ∥₊» (((fLFCocone F surj M).ι.app (op S)).f _ f) ≤ «expr∥ ∥₊» f :=
  by
  cases n
  apply LocallyConstant_obj_map_norm_noninc
  apply LocallyConstant_obj_map_norm_noninc

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥₊» -/
theorem prop819 {m : ℕ} (ε : ℝ≥0) (hε : 0 < ε) (f : (fLC F M).pt (m + 1))
    (hf : (fLC F M).d (m + 1) (m + 2) f = 0) :
    ∃ g : (fLC F M).pt m, (fLC F M).d m (m + 1) g = f ∧ «expr∥ ∥₊» g ≤ (1 + ε) * «expr∥ ∥₊» f :=
  by
  apply exact_of_strictIso _ _ (fLCIso F M) ε hε _ _ _ hf
  apply cmpl_exact_of_exact _ _ hε
  clear hf f m hε ε
  intro n f hf
  -- We've reduced to the non-completed case.
  have := exists_locally_constant F surj M _ f hf
  rcases this with ⟨S, g, rfl, h2, h3, -⟩
  --let gg := ((FLF_cocone F surj M).ι.app (op S)).f _ g,
  let CC : ∀ n : ℕ, ((fLF F surj M).obj (op S)).pt (n + 1) ⟶ ((fLF F surj M).obj (op S)).pt n :=
    ((Profinite.arrowDiagram F surj).obj S).contractingHomotopy (LocallyConstant.obj M)
  let gc := CC _ g
  let GG := ((fLFCocone F surj M).ι.app (op S)).f _ gc
  refine' ⟨GG, _, _⟩
  · dsimp only [GG]
    have := ((fLFCocone F surj M).ι.app (op S)).comm n (n + 1)
    apply_fun fun e => e gc at this 
    erw [this]; clear this
    change ((fLFCocone F surj M).ι.app (op S)).f (n + 1) _ = _
    congr 1
    change (CC n ≫ _) g = g
    cases n
    · have hh :=
        arrow.is_contracting_homotopy_one (LocallyConstant.obj M)
          ((Profinite.arrowDiagram F surj).obj S)
      apply_fun fun e => e g at hh 
      change CC 1 _ + _ = g at hh 
      conv at hh =>
        congr
        congr
        erw [h2]
      rw [map_zero, zero_add] at hh 
      exact hh
    · have hh :=
        arrow.is_contracting_homotopy (LocallyConstant.obj M)
          ((Profinite.arrowDiagram F surj).obj S) _
      apply_fun fun e => e g at hh 
      change CC _ _ + _ = g at hh 
      conv at hh =>
        congr
        congr
        erw [h2]
      rw [map_zero, zero_add] at hh 
      exact hh
  · rw [h3]
    suffices «expr∥ ∥₊» GG ≤ «expr∥ ∥₊» gc
      by
      apply le_trans this _
      cases n
      apply LocallyConstant_obj_map_norm_noninc
      apply LocallyConstant_obj_map_norm_noninc
    apply fLF_norm_noninc

