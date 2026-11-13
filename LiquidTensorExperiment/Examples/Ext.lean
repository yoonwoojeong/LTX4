import LiquidTensorExperiment.ChallengeNotations
import LiquidTensorExperiment.ChallengePrerequisites
import LiquidTensorExperiment.ForMathlib.UniversalDeltaFunctor.Ext

#align_import examples.Ext

/-!

This file discusses the various Ext groups appearing in our project.
We also discuss the computation `Ext^1(ℤ/nℤ, ℤ/nℤ) = ℤ/nℤ`.

-/


noncomputable section

open scoped LiquidTensorExperiment NNReal

open CategoryTheory CategoryTheory.Limits Opposite

open BoundedHomotopyCategory BoundedDerivedCategory

section Ext

namespace LiquidTensorExperiment

/-!
The `Ext i (ℳ_{p'} S) V` which appears in the main statement of the challenge
is just an alias for `Ext' i (op (ℳ_{p'} S)) (Condensed.of_top_ab V)`.
The notation `Ext'` will be explained below, while `ℳ_{p'} S` is discussed in the file
`examples/radon_measures.lean` and `(Condensed.of_top_ab V)` is discussed in the file
`examples/pBanach.lean`.
-/


example (p' p : ℝ≥0) [Fact (0 < p')] [Fact (p' < p)] [Fact (p ≤ 1)] (S : Profinite.{0})
    (V : PBanachCat.{0} p) :
    ∀ i > 0, ext i (ℳ_{p'}S) V = ext' i (op (ℳ_{p'}S)) (Condensed.ofTopAb V) := by intros; rfl

end LiquidTensorExperiment

universe v u

/-!
We fix an abelian category with enough projectives.
-/


variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐] [EnoughProjectives 𝓐]

/-!
The functor from `𝓐` to the bounded above homotopy category, sending `X` to `X[0]`,
is denoted by `single 𝓐 0`.
-/


example : 𝓐 ⥤ BoundedHomotopyCategory 𝓐 :=
  single 𝓐 0

/-!
We introduced a coercion to simplify the notation.
-/


example (X : 𝓐) : BoundedHomotopyCategory 𝓐 :=
  X

example (X : 𝓐) : (X : BoundedHomotopyCategory 𝓐) = (single _ 0) X :=
  rfl

/-!
Our Ext functor `Ext n`, for `n : ℤ`, is defined for arbitrary objects in the bounded above
homotopy category.
It is a bifunctor which is contravariant in the first component and covariant in the second.
-/


example (n : ℤ) : (BoundedHomotopyCategory 𝓐)ᵒᵖ ⥤ BoundedHomotopyCategory 𝓐 ⥤ Ab :=
  ext n

/-!
`Ext' n (X, B)` is defined to be `Ext n (X, B)`, modulo the coercion mentioned above.
We have to manually tell Lean that a coercion is involved in this case using `↑`.
-/


example (n : ℕ) (X Y : 𝓐) : ext' n (op X) Y = ext n (op ↑X) ↑Y :=
  rfl

/-!
The `Ext' n` can be assembled into a δ-functor, which is denoted `Ext_δ_functor 𝓐 Y`.
To be precise, this is considering `Ext' n (X, Y)` as functors in `X`, with `Y` fixed.
-/


example (Y : 𝓐) : 𝓐ᵒᵖ ⥤δ Ab.{v} :=
  extδFunctor 𝓐 Y

/-!
The `n-th` component of this delta functor is denoted `Ext_δ_functor 𝓐 Y n`,
and it is defined on objects as `Ext' n (op X) Y`. -/


example (n : ℕ) (Y : 𝓐) : 𝓐ᵒᵖ ⥤ Ab.{v} :=
  extδFunctor 𝓐 Y n

example (n : ℕ) (X Y : 𝓐) : (extδFunctor 𝓐 Y n) (op X) = ext' n (op X) Y :=
  rfl

/-!
`Ext' 0 (X, Y) ≅ Hom(X,Y)`.
-/


example (X Y : 𝓐) : ext' 0 (op X) Y ≅ AddCommGroupCat.of (X ⟶ Y) :=
  (ext'ZeroFlipIso 𝓐 Y).app (op X)

/-!
The isomorphism above is functorial in the first variable, and the isomorphism of functors
is denoted `Ext'_zero_flip_iso 𝓐 Y`. This isomorphism will be used in the example below.
-/


example (Y : 𝓐) : (ext' 0).flip.obj Y ≅ preadditiveYoneda.obj Y :=
  ext'ZeroFlipIso 𝓐 Y

/-!
Any natural transformation `Hom(-,B) ⟶ F 0` to the zeroth-component of some
delta functor `F` extends in a unique way to a morphism of delta functors
`Ext_δ_functor A B ⟶ F`.

Note that `Ext' 0 (X,B)` is not definitionally equal to `Hom(X,B)`,
so we must compose with the isomorphism `Ext'_zero_flip_iso` from the previous example.
-/


theorem extδFunctor_is_universal_for_Hom (Y : 𝓐)
    -- Let `F` be a contravariant delta functor on `𝓐`,
    (F : 𝓐ᵒᵖ ⥤δ Ab.{v})
    -- and `e0` a morphism from `Hom(-,Y)` to `F 0`.
    (e0 :
      preadditiveYoneda Y ⟶
        F 0) :-- Then there exists a unique morphism of δ-functors `e : Ext_δ_functor 𝓐 Y ⟶ F`
    ∃! e :
      extδFunctor 𝓐 Y ⟶
        F,-- such that `e0` is the composition of the zero-th component of `e` with the isomorphism
        -- `Hom(-,Y) ≅ Ext' 0 (-,Y)`.
        e0 =
        (ext'ZeroFlipIso 𝓐 Y).inv ≫ (e : extδFunctor 𝓐 Y ⟶ F) 0 :=
  by
  let e0' : extδFunctor 𝓐 Y 0 ⟶ F 0 := (Ext'_zero_flip_iso _ _).hom ≫ e0
  obtain ⟨e, he1, he2⟩ := delta_functor.universal.cond F e0'
  refine' ⟨e, _, _⟩
  · dsimp; simp only [e0', he1, iso.inv_hom_id_assoc]
  · intro η hη; specialize he2 η
    apply he2; rw [iso.eq_inv_comp] at hη 
    exact hη.symm

open AddCommGroupCat

/-!
An explicit computation: `Ext^1(ℤ/n,ℤ/n) = ℤ/n`.
The notation `AddCommGroup.of A` considers an abelian group `A` as an object of
`AddCommGroup`, the category of abelian groups.
-/


example (n : ℕ) (hn : n ≠ 0) :
    ext' 1 (op (AddCommGroupCat.of (ZMod n))) (AddCommGroupCat.of (ZMod n)) ≅
      AddCommGroupCat.of (ZMod n) :=
  by
  refine'
    ext'Iso (op <| of <| ZMod n) (of <| ZMod n) 1 (zmod_resolution n) (zmod_resolution_pi n)
        (zmod_resolution_is_resolution n hn) ≪≫
      CategoryTheory.homologyIso _ 0 (-1) (-2) rfl rfl ≪≫ _
  refine' AddCommGroupCat.homologyIso _ _ _ ≪≫ _
  refine' add_equiv_iso_AddCommGroup_iso.hom _
  refine'
    AddEquiv.surjectiveCongr _ (QuotientAddGroup.mk' _) (AddMonoidHom.id _) (Quot.mk_surjective _)
      Function.surjective_id _
  refine' (AddEquiv.addSubgroupCongr _).trans _
  · exact ⊤
  · convert AddMonoidHom.ker_zero using 2
    refine' is_zero.eq_of_tgt _ _ _
    refine' AddCommGroupCat.isZero_of_eq _ _
    intro f g
    apply CategoryTheory.Limits.HasZeroObject.from_zero_ext
  · refine' (add_subgroup.equiv_top _).symm.trans (zmultiplesAddHom _).symm
  · simp only [AddMonoidHom.ker_zero, QuotientAddGroup.ker_mk',
      functor.map_homological_complex_obj_d, HomologicalComplex.op_d]
    ext ⟨f, hf⟩
    simp only [AddSubgroup.mem_comap, AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_trans,
      Function.comp_apply, zmultiplesAddHom_symm_apply, AddSubgroup.coeSubtype, AddSubgroup.coe_mk,
      AddMonoidHom.mem_range]
    simp only [add_subgroup.equiv_top_symm_apply, AddMonoidHom.mem_ker]
    dsimp [AddEquiv.addSubgroupCongr, zmod_resolution]
    constructor
    · intro hf1; refine' ⟨0, comp_zero.trans _⟩; ext1; exact hf1.symm
    · intro H; cases' H with g hg; rw [← hg, coe_comp]
      convert g.map_nsmul _ _ using 1
      simp only [eq_to_hom_refl, id_apply, zmod.nsmul_eq_zero]

end Ext

