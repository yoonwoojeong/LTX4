import LiquidTensorExperiment.BreenDeligne.Eval2
import LiquidTensorExperiment.BreenDeligne.ApplyPow
import LiquidTensorExperiment.ForMathlib.Derived.KProjective
import LiquidTensorExperiment.ForMathlib.Endomorphisms.Ext
import LiquidTensorExperiment.ForMathlib.Endomorphisms.Functor
import LiquidTensorExperiment.ForMathlib.TruncationExt
import LiquidTensorExperiment.ForMathlib.SingleCoproducts
import Mathlib.CategoryTheory.Limits.Opposites
import LiquidTensorExperiment.ForMathlib.FreeAbelianGroup2
import LiquidTensorExperiment.ForMathlib.HasHomologyAux
import LiquidTensorExperiment.ForMathlib.ExactFunctor
import LiquidTensorExperiment.ForMathlib.Derived.ExtLemmas
import LiquidTensorExperiment.ForMathlib.Endomorphisms.Homology
import LiquidTensorExperiment.ForMathlib.YonedaLeftExact
import LiquidTensorExperiment.ForMathlib.HomotopyCategoryFunctorCompatibilities
import LiquidTensorExperiment.ForMathlib.PreservesExact
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Tensor

#align_import breen_deligne.main

noncomputable section

universe v u

open scoped BigOperators

open scoped ZeroObject

open CategoryTheory CategoryTheory.Limits Opposite

open BoundedHomotopyCategory (ext single)

namespace BreenDeligne

namespace Package

variable (BD : Package)

variable {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐]

variable (F : 𝓐 ⥤ 𝓐)

--[preserves_filtered_colimits F]
namespace MainLemma

variable (A : 𝓐) (B : 𝓐) (j : ℤ)

def IH [EnoughProjectives 𝓐] : Prop :=
  (∀ i ≤ j, IsZero <| ((ext' i).obj (op A)).obj B) ↔
    ∀ i ≤ j, IsZero <| ((ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)

theorem iH_neg [EnoughProjectives 𝓐] (j : ℤ) (hj : j ≤ 0) : IH BD F A B (j - 1) :=
  by
  constructor <;> intro _ _ hij
  · apply ext_single_right_isZero _ _ 1 _ _ (ChainComplex.boundedByOne _)
    linarith only [hj, hij]
  · apply ext'_isZero_of_neg; linarith only [hj, hij]

/-- the assumption hC is very suboptimal! -/
def homologyIsoDeg0OfBoundedBy1 (C : HomologicalComplex 𝓐 (ComplexShape.up ℤ))
    (hC : ∀ i : ℤ, 1 ≤ i → IsZero (C.pt i)) : C.homology' 0 ≅ cokernel (C.dTo 0) :=
  by
  refine'
    (ShortComplex.homologyFunctorIso 𝓐 _ 0).app C ≪≫ (HomologyIsoDatum.ofGIsZero _ _ _).Iso.symm
  dsimp
  rw [C.d_from_eq (zero_add 1)]
  suffices C.d 0 1 = 0 by rw [this, zero_comp]
  apply IsZero.eq_of_tgt
  exact hC 1 (by rfl)

def homologyIsoDeg0OfBoundedBy1Down (C : HomologicalComplex 𝓐 (ComplexShape.down ℤ))
    (hC : ∀ i : ℤ, 1 ≤ i → IsZero (C.pt i)) : C.homology' 0 ≅ kernel (C.dFrom 0) :=
  by
  refine'
    (ShortComplex.homologyFunctorIso 𝓐 _ 0).app C ≪≫ (HomologyIsoDatum.ofFIsZero _ _ _).Iso.symm
  dsimp
  rw [C.d_to_eq (zero_add 1)]
  suffices C.d 1 0 = 0 by rw [this, comp_zero]
  apply IsZero.eq_of_src
  exact hC 1 (by rfl)

variable [EnoughProjectives 𝓐]

def iH0Aux (C : BoundedHomotopyCategory 𝓐) (hC : C.val.BoundedBy 1) :
    ((ext' 0).flip.obj B).obj (op (C.val.as.homology' 0)) ≅
      ((ext 0).obj (op C)).obj ((single 𝓐 0).obj B) :=
  by
  refine' (BoundedDerivedCategory.ext'ZeroFlipIso _ _).app _ ≪≫ _
  refine' _ ≪≫ (bounded_homotopy_category.Ext0.obj (op C)).mapIso (shift_zero _ _).symm
  refine' _ ≪≫ (BoundedHomotopyCategory.homSingleIso _ _ _).symm
  dsimp only [unop_op]
  have h := HomotopyCategory.exists_bounded_K_projective_replacement_of_bounded 1 C.val hC
  let P₁ := h.some
  have hP₁ : P₁.bounded_by 1 := h.choose_spec.choose_spec.some
  haveI : P₁.is_bounded_above := ⟨⟨1, hP₁⟩⟩
  let P : BoundedHomotopyCategory 𝓐 := ⟨P₁⟩
  haveI : P.val.isKProjective := h.choose_spec.some
  let ψ : P ⟶ C := h.choose_spec.choose_spec.choose_spec.some
  haveI hψ : HomotopyCategory.IsQuasiIso ψ := h.choose_spec.choose_spec.choose_spec.choose_spec.1
  let e : C.replace.val ≅ P.val :=
    (BoundedHomotopyCategory.forget _).mapIso
      { hom := BoundedHomotopyCategory.lift C.π ψ
        inv := BoundedHomotopyCategory.lift ψ C.π
        hom_inv_id := by
          simp only [BoundedHomotopyCategory.lift_comp_lift_self, BoundedHomotopyCategory.lift_self]
        inv_hom_id := by
          simp only [BoundedHomotopyCategory.lift_comp_lift_self,
            BoundedHomotopyCategory.lift_self] }
  let e' :
    (((preadditive_yoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
            C.replace.val.as.op).homology'
        0 ≅
      (((preadditive_yoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
            P.val.as.op).homology'
        0 :=
    by
    refine'
      _ ≪≫
        (Functor.mapHomotopyCategory (ComplexShape.down ℤ) (preadditive_yoneda.obj B) ⋙
                HomotopyCategory.homology'Functor _ _ 0).mapIso
            (homotopy_category.op_functor.map_iso e.op.symm) ≪≫
          _
    · symm
      exact (preadditive_yoneda.obj B).quotientOpMapHomologyIso C.replace.val 0
    · exact (preadditive_yoneda.obj B).quotientOpMapHomologyIso P.val 0
  refine'
    _ ≪≫
      (BreenDeligne.Package.MainLemma.homologyIsoDeg0OfBoundedBy1Down
            (((preadditive_yoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
              P.val.as.op)
            fun i hi => by
            dsimp only [Functor.mapHomologicalComplex]
            rw [IsZero.iff_id_eq_zero]; rw [← (preadditive_yoneda.obj B).map_id]
            suffices 𝟙 (P₁.as.op.X i) = 0 by rw [this, Functor.map_zero]
            apply Quiver.Hom.unop_inj; dsimp
            simpa [← IsZero.iff_id_eq_zero] using hP₁ i hi).symm ≪≫
        e'.symm
  refine'
    (preadditive_yoneda.obj B).mapIso _ ≪≫
      CategoryTheory.asIso (CategoryTheory.Limits.kernelComparison (P₁.as.op.d 0 (-1)) (preadditive_yoneda.obj B)) ≪≫
        (kernel.mapIso _
            ((((preadditive_yoneda.obj B).mapHomologicalComplex (ComplexShape.up ℤ).symm).obj
                  P.val.as.op).d
              0 (-(1 : ℤ)))
            (iso.refl _) (HomologicalComplex.xNextIso _ (by dsimp; rfl)) (by simpa)).symm
  refine' Iso.op _ ≪≫ (CategoryTheory.kernelOpOp (P₁.as.d (-1) 0)).symm
  refine'
    (cokernel.mapIso _ _ (P₁.as.xPrevIso rfl) (iso.refl _)
          (by simpa only [Iso.refl_hom, Category.comp_id] using P₁.as.dTo_eq _)).symm ≪≫
      (BreenDeligne.Package.MainLemma.homologyIsoDeg0OfBoundedBy1 P₁.as hP₁).symm ≪≫
        CategoryTheory.asIso ((HomotopyCategory.homology'Functor 𝓐 (ComplexShape.up ℤ) 0).map ψ)

variable (hH0 : ((BD.eval F).obj A).val.as.homology' 0 ≅ A)

theorem iH_0 : IH BD F A B 0 := by
  apply forall_congr'; intro i; apply forall_congr'; intro hi0
  rw [le_iff_lt_or_eq] at hi0 ; rcases hi0 with (hi0 | rfl)
  · constructor <;> intro
    · apply ext_single_right_isZero _ _ 1 _ _ (ChainComplex.boundedByOne _)
      linarith only [hi0]
    · apply ext'_isZero_of_neg; linarith only [hi0]
  apply Iso.isZero_iff
  refine' ((ext' 0).flip.obj B).mapIso hH0.op ≪≫ _
  apply IH_0_aux
  apply ChainComplex.boundedByOne

theorem bdd_step₁ (j : ℤ) :
    (∀ i ≤ j, IsZero <| ((ext' i).obj (op A)).obj B) ↔
      ∀ i ≤ j, IsZero <| ((ext' i).obj (op <| ((BD.eval F).obj A).val.as.homology' 0)).obj B :=
  by
  apply forall_congr'; intro i; apply forall_congr'; intro hi
  apply Iso.isZero_iff
  exact ((ext' _).flip.obj B).mapIso hH0.op

open BoundedHomotopyCategory (of' ext_map_isIso_of_quasi_iso)

theorem bdd_step₂ (j : ℤ) :
    (∀ i ≤ j, IsZero <| ((ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B)) ↔
      ∀ i ≤ j,
        IsZero <|
          ((ext i).obj (op <| of' <| ((BD.eval' F).obj A).truncation 0)).obj ((single _ 0).obj B) :=
  by
  apply forall_congr'; intro i; apply forall_congr'; intro hi
  apply Iso.isZero_iff
  refine' ((Ext _).flip.obj ((single _ 0).obj B)).mapIso _
  refine' Iso.op _
  haveI := CochainComplex.truncation.ι_iso ((BD.eval' F).obj A) 0 _
  swap; · apply ChainComplex.boundedByOne
  let e' := CategoryTheory.asIso <| CochainComplex.truncation.ι ((BD.eval' F).obj A) 0
  let e := (HomotopyCategory.quotient _ _).mapIso e'
  refine' ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

theorem bdd_step₃_aux (i j : ℤ) :
    IsZero
        (((ext i).obj (op <| (single 𝓐 j).obj (((BD.eval F).obj A).val.as.homology' j))).obj
          ((single 𝓐 0).obj B)) ↔
      IsZero (((ext i).obj (op <| of' (((BD.eval' F).obj A).imker j))).obj ((single 𝓐 0).obj B)) :=
  by
  apply Iso.isZero_iff
  let φ :
    of' (((BD.eval' F).obj A).imker j) ⟶
      (single 𝓐 j).obj (((BD.eval F).obj A).val.as.homology' j) :=
    (HomotopyCategory.quotient _ _).map (CochainComplex.imker.toSingle ((BD.eval' F).obj A) _)
  haveI : HomotopyCategory.IsQuasiIso φ :=
    CochainComplex.imker.toSingleQuasiIso ((BD.eval' F).obj A) _
  let e := @CategoryTheory.asIso _ _ _ _ _ (Ext_map_is_iso_of_quasi_iso _ _ ((single 𝓐 0).obj B) φ i)
  exact e

theorem bdd_step₃
    (H :
      ∀ i ≤ j + 1,
        IsZero
          (((ext i).obj (op (of' (((BD.eval' F).obj A).truncation (-1))))).obj
            ((single 𝓐 0).obj B))) :
    (∀ i ≤ j + 1,
        IsZero
          (((ext i).obj (op (of' (((BD.eval' F).obj A).truncation 0)))).obj ((single 𝓐 0).obj B))) ↔
      ∀ i ≤ j + 1, IsZero (((ext' i).obj (op (((BD.eval F).obj A).val.as.homology' 0))).obj B) :=
  by
  apply forall_congr'; intro i; apply forall_congr'; intro hi
  refine' Iff.trans _ (bdd_step₃_aux BD F A B i 0).symm
  obtain ⟨i, rfl⟩ : ∃ k, k + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
  have LES1 :=
    CochainComplex.ext_ιSucc_five_term_exactSeq ((BD.eval' F).obj A) ((single 𝓐 0).obj B) (-1) i
  have LES2 :=
    CochainComplex.ext_ιSucc_five_term_exactSeq ((BD.eval' F).obj A) ((single 𝓐 0).obj B) (-1)
      (i + 1)
  have aux := ((LES1.drop 2).pair.cons LES2).isIso_of_zero_of_zero <;> clear LES1 LES2
  symm
  refine' (@CategoryTheory.asIso _ _ _ _ _ (aux _ _)).isZero_iff <;> clear aux
  · apply (H _ _).eq_of_src; exact (Int.le_add_one le_rfl).trans hi
  · apply (H _ hi).eq_of_tgt

theorem bdd_step₄
    (H :
      ∀ t ≤ (-1 : ℤ),
        ∀ i ≤ j + 1,
          IsZero
            (((ext i).obj (op <| (single _ t).obj (((BD.eval F).obj A).val.as.homology' t))).obj
              ((single 𝓐 0).obj B))) :
    ∀ t ≤ (-1 : ℤ),
      ∀ i ≤ j + 1,
        IsZero
          (((ext i).obj (op (of' (((BD.eval' F).obj A).truncation t)))).obj ((single 𝓐 0).obj B)) :=
  by
  intro t ht i; revert ht
  apply Int.inductionOn' t (-i - 1)
  · intro hi1 hi2
    apply ext_single_right_isZero _ _ (-i - 1 + 1)
    · apply CochainComplex.truncation.boundedBy
    · simp only [sub_add_cancel, add_left_neg]
  · intro k hk ih hk' hij
    have LES :=
      CochainComplex.ext_ιSucc_five_term_exactSeq ((BD.eval' F).obj A) ((single 𝓐 0).obj B) k i
    apply LES.pair.isZero_of_isZero_isZero <;> clear LES
    · erw [← bdd_step₃_aux]
      apply H _ hk' _ hij
    · exact ih ((Int.le_add_one le_rfl).trans hk') hij
  · intro k hk ih hk' hij
    apply ext_single_right_isZero _ _ (k - 1 + 1)
    · apply CochainComplex.truncation.boundedBy
    · linarith only [hk, hk', hij]

open BoundedHomotopyCategory (ext0)

-- move me
def bddStep₅Aux'' {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] (X Y : BoundedHomotopyCategory 𝓐)
    (e : BoundedHomotopyCategory 𝓐 ≌ BoundedHomotopyCategory 𝓐) [e.Functor.Additive] :
    (preadditiveYoneda.obj X).obj (op Y) ≅
      (preadditiveYoneda.obj (e.Functor.obj X)).obj (op (e.Functor.obj Y)) :=
  AddEquiv.toAddCommGroupCatIso <|
    { equivOfFullyFaithful e.Functor with map_add' := fun f g => e.Functor.map_add }

-- move me
instance shiftEquiv_functor_additive {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] (k : ℤ) :
    (shiftEquiv (BoundedHomotopyCategory 𝓐) k).Functor.Additive :=
  BoundedHomotopyCategory.shiftFunctor_additive k

def bddStep₅Aux' {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] (X Y : BoundedHomotopyCategory 𝓐) (k : ℤ) :
    (preadditiveYoneda.obj X).obj (op Y) ≅ (preadditiveYoneda.obj (X⟦k⟧)).obj (op (Y⟦k⟧)) :=
  bddStep₅Aux'' _ _ <| shiftEquiv _ k

def bddStep₅Aux (X Y : BoundedHomotopyCategory 𝓐) (k : ℤ) :
    (ext0.obj (op X)).obj Y ≅ (ext0.obj (op <| X⟦k⟧)).obj (Y⟦k⟧) :=
  by
  delta Ext0; dsimp only
  refine'
    bdd_step₅_aux' _ _ k ≪≫
      (preadditive_yoneda.obj ((shift_functor (BoundedHomotopyCategory 𝓐) k).obj Y)).mapIso _
  refine' Iso.op _
  exact BoundedHomotopyCategory.replacementIso _ _ (X⟦k⟧) X⟦k⟧.π (X.π⟦k⟧')

theorem bdd_step₅ (k i : ℤ) :
    IsZero (((ext i).obj (op ((single 𝓐 k).obj A))).obj ((single 𝓐 0).obj B)) ↔
      IsZero (((ext' (i + k)).obj (op <| A)).obj B) :=
  by
  apply Iso.isZero_iff
  dsimp only [ext', Ext, Functor.comp_obj, Functor.flip_obj_obj, CategoryTheory.whiskeringLeft_obj_obj]
  refine' bdd_step₅_aux _ _ k ≪≫ _
  refine' Functor.mapIso _ _ ≪≫ Iso.app (Functor.mapIso _ _) _
  · refine' (CategoryTheory.shiftAdd _ _ _).symm
  · refine' ((BoundedHomotopyCategory.shiftSingleIso k k).app A).op.symm ≪≫ _
    refine' eq_to_iso _; rw [sub_self]; rfl

-- `T` should be thought of as a tensor product functor,
-- taking tensor products with `A : Condensed Ab`
variable (T : Ab.{v} ⥤ 𝓐)

variable [∀ α : Type v, PreservesColimitsOfShape (Discrete α) T]

variable (hT1 : T.obj (AddCommGroupCat.of <| PUnit →₀ ℤ) ≅ A)

variable
  (hT : ∀ {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z), ShortExact f g → ShortExact (T.map f) (T.map g))

theorem bdd_step₆_free₀ (A : Ab) :
    ∃ (F₁ F₀ : Ab) (h₁ : Module.Free ℤ F₁) (h₀ : Module.Free ℤ F₀) (f : F₁ ⟶ F₀) (g : F₀ ⟶ A),
      ShortExact f g :=
  by
  let g := Finsupp.total A A ℤ id
  let F := g.ker
  let f := F.subtype
  let F₀ : Ab := AddCommGroupCat.of (↥A →₀ ℤ)
  let F₁ : Ab := AddCommGroupCat.of F
  refine' ⟨F₁, F₀, _, _, f.toAddMonoidHom, g.toAddMonoidHom, _⟩
  · dsimp [F₁, F]
    exact Submodule.free_of_pid_of_free
  · exact Module.Free.finsupp _ _ _
  · apply (config := { instances := false }) ShortExact.mk
    · rw [AddCommGroupCat.mono_iff_injective]; apply Subtype.val_injective
    · rw [AddCommGroupCat.epi_iff_surjective]; apply Finsupp.total_id_surjective
    · rw [AddCommGroupCat.exact_iff]
      ext x
      dsimp only [f, F, F₁, AddCommGroupCat.coe_of]
      simp only [AddMonoidHom.mem_range, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
      refine' ⟨_, _⟩
      · rintro ⟨y, rfl⟩; exact y.2
      · intro h; exact ⟨⟨x, h⟩, rfl⟩

variable [HasCoproducts.{v} 𝓐] [AB4 𝓐]

theorem bdd_step₆_free₁ (IH : ∀ i ≤ j, IsZero <| ((ext' i).obj (op A)).obj B) (i : ℤ) (hi : i ≤ j)
    (α : Type v) :
    IsZero (((ext' i).flip.obj B).obj (op (T.obj <| AddCommGroupCat.of <| α →₀ ℤ))) :=
  by
  let D : discrete α ⥤ Ab := Discrete.functor fun a => AddCommGroupCat.of <| PUnit →₀ ℤ
  let c : cocone D :=
    Cofan.mk (AddCommGroupCat.of <| α →₀ ℤ) fun a => Finsupp.mapDomain.addMonoidHom fun _ => a
  let hc : is_colimit c := ⟨fun s => _, _, _⟩
  rotate_left
  · refine' (Finsupp.total _ _ _ fun a => _).toAddMonoidHom
    refine' (s.ι.app ⟨a⟩) (Finsupp.single PUnit.unit 1)
  · rintro s ⟨a⟩; apply Finsupp.addHom_ext'; rintro ⟨⟩; apply AddMonoidHom.ext_int
    simp only [AddMonoidHom.comp_apply, CategoryTheory.comp_apply, LinearMap.toAddMonoidHom_coe,
      Cofan.mk_ι_app, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single,
      Finsupp.singleAddHom_apply, Finsupp.total_single, one_smul]
  · intro s m h
    apply Finsupp.addHom_ext'; intro a; apply AddMonoidHom.ext_int
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Finsupp.singleAddHom_apply,
      Finsupp.total_single, one_smul]
    rw [← h]
    simp only [CategoryTheory.comp_apply, Cofan.mk_ι_app, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_single]
  let c' := T.map_cocone c
  let hc' : is_colimit c' := CategoryTheory.Limits.isColimitOfPreserves T hc
  let c'' := ((ext' i).flip.obj B).rightOp.mapCocone c'
  let hc'' : is_colimit c'' := CategoryTheory.Limits.isColimitOfPreserves _ hc'
  change is_zero c''.X.unop
  apply IsZero.unop
  let e : c''.X ≅ colimit ((D ⋙ T) ⋙ ((ext' i).flip.obj B).rightOp) :=
    hc''.coconePointUniqueUpToIso (colimit.isColimit _)
  apply IsZero.of_iso _ e
  apply CategoryTheory.isZero_colimit
  intro j
  apply IsZero.of_iso _ (((ext' i).flip.obj B).rightOp.mapIso hT1)
  apply (IH i hi).op

theorem bdd_step₆_free (IH : ∀ i ≤ j, IsZero <| ((ext' i).obj (op A)).obj B) (i : ℤ) (hi : i ≤ j)
    (A' : Ab) (hA' : Module.Free ℤ A') : IsZero (((ext' i).flip.obj B).obj (op (T.obj A'))) :=
  by
  let e' := Module.Free.chooseBasis ℤ A'
  let e'' := e'.repr.toAddEquiv
  let e : A' ≅ AddCommGroupCat.of <| Module.Free.ChooseBasisIndex ℤ A' →₀ ℤ := by
    refine' add_equiv_iso_AddCommGroup_iso.hom _; exact e''
  refine' IsZero.of_iso _ (Functor.mapIso _ (T.map_iso e).op.symm)
  apply bdd_step₆_free₁ A B j T hT1 IH i hi

theorem bdd_step₆ (IH : ∀ i ≤ j, IsZero <| ((ext' i).obj (op A)).obj B) (i : ℤ) (hi : i ≤ j)
    (A' : Ab) : IsZero (((ext' i).flip.obj B).obj (op (T.obj A'))) :=
  by
  obtain ⟨F₁, F₀, h₁, h₀, f, g, hfg⟩ := bdd_step₆_free₀ A'
  specialize hT f g hfg
  obtain ⟨i, rfl⟩ : ∃ k, k + 1 = i := ⟨i - 1, sub_add_cancel _ _⟩
  have := ((hT.ext'_five_term_exactSeq B i).drop 2).pair
  apply this.isZero_of_isZero_isZero
  · apply bdd_step₆_free A B j T hT1 IH _ ((Int.le_add_one le_rfl).trans hi) _ h₁
  · apply bdd_step₆_free A B j T hT1 IH _ hi _ h₀

variable (hAT : ∀ t ≤ (-1 : ℤ), ∃ A', Nonempty (T.obj A' ≅ ((BD.eval F).obj A).val.as.homology' t))

theorem bdd_step (j : ℤ) (ih : IH BD F A B j) : IH BD F A B (j + 1) :=
  by
  by_cases ih' : ∀ i ≤ j, is_zero <| ((ext' i).obj (op A)).obj B; swap
  · constructor
    · intro h; refine' (ih' fun i hi => _).elim; apply h _ (Int.le_add_one hi)
    · intro h; refine' (ih' <| ih.mpr fun i hi => _).elim; apply h _ (Int.le_add_one hi)
  refine' (bdd_step₁ BD F _ _ hH0 _).trans ((bdd_step₂ BD F _ _ _).trans _).symm
  apply bdd_step₃
  apply bdd_step₄ BD F A B _ _ _ le_rfl
  intro t ht i hi
  rw [bdd_step₅]
  obtain ⟨A', ⟨e⟩⟩ := hAT t ht
  apply (((ext' (i + t)).flip.obj B).mapIso e.op).isZero_iff.mpr
  apply bdd_step₆ A B _ T hT1 (@hT) ih'
  linarith only [ht, hi]

-- This requires more hypotheses on `BD` and `F`.
-- We'll figure them out while proving the lemma.
-- These extra hypotheses are certainly satisfies by
-- `BD = breen_deligne.package.eg` and
-- `F` = "free condensed abelian group"
-- Also missing: the condition that `A` is torsion free.
theorem bdd (j : ℤ) : IH BD F A B j :=
  by
  apply Int.inductionOn' j
  · exact IH_0 BD F A B hH0
  · intro k hk; exact bdd_step BD F A B hH0 T hT1 (@hT) hAT k
  · intro k hk _; exact IH_neg BD F A B k hk

theorem isZero :
    (∀ i, IsZero <| ((ext' i).obj (op A)).obj B) ↔
      ∀ i, IsZero <| ((ext i).obj (op ((BD.eval F).obj A))).obj ((single _ 0).obj B) :=
  by
  constructor
  · intro H j
    refine' (bdd BD F A B hH0 T hT1 (@hT) hAT j).mp _ j le_rfl
    intro i hij
    apply H
  · intro H j
    refine' (bdd BD F A B hH0 T hT1 (@hT) hAT j).mpr _ j le_rfl
    intro i hij
    apply H

end MainLemma

section

variable [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐]

variable [HasProductsOfShape (ULift.{v} ℕ) 𝓐]

open CategoryTheory.Preadditive

@[simps, nolint unused_arguments]
def powX (X : Endomorphisms 𝓐) (n : ℕ) : ((pow n).obj X).pt ≅ (pow n).obj X.pt :=
  (applyPow (Endomorphisms.forget 𝓐) n).app X

instance eval'BoundedAbove {𝓐 : Type u} [Category 𝓐] [Abelian 𝓐] (F : 𝓐 ⥤ 𝓐) (X : 𝓐) :
    ((HomotopyCategory.quotient 𝓐 (ComplexShape.up ℤ)).obj ((BD.eval' F).obj X)).IsBoundedAbove :=
  ((BD.eval F).obj X).bdd

/-
def mk_bo_ha_ca'_Q (X : 𝓐) (f : X ⟶ X) :
  endomorphisms.mk_bo_ho_ca' ((BD.eval' F).obj X) ((BD.eval' F).map f) ≅
  (BD.eval F.map_endomorphisms).obj ⟨X, f⟩ :=
bounded_homotopy_category.mk_iso $ (homotopy_category.quotient _ _).map_iso
begin
  refine homological_complex.hom.iso_of_components _ _,
  { intro i,
    refine endomorphisms.mk_iso _ _,
    { rcases i with ((_|i)|i),
      { refine F.map_iso _, symmetry, refine (Pow_X _ _) },
      { refine (is_zero_zero _).iso _, apply endomorphisms.is_zero_X, exact is_zero_zero _ },
      { refine F.map_iso _, symmetry, refine (Pow_X _ _) } },
    { rcases i with ((_|i)|i),
      { show F.map _ ≫ F.map _ = F.map _ ≫ F.map _,
        rw [← F.map_comp, ← F.map_comp], congr' 1,
        apply biproduct.hom_ext', intro j,
        dsimp only [Pow, Pow_X_hom, Pow_X_inv, iso.symm_hom],
        rw [biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc, ← endomorphisms.hom.comm], },
      { apply is_zero.eq_of_tgt, apply endomorphisms.is_zero_X, exact is_zero_zero _ },
      { show F.map _ ≫ F.map _ = F.map _ ≫ F.map _,
        rw [← F.map_comp, ← F.map_comp], congr' 1,
        apply biproduct.hom_ext', intro j,
        dsimp only [Pow, Pow_X_hom, Pow_X_inv, iso.symm_hom],
        rw [biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc, ← endomorphisms.hom.comm], } } },
  { rintro i j (rfl : _ = _), ext, rcases i with (i|(_|i)),
    { apply is_zero.eq_of_tgt, apply endomorphisms.is_zero_X, exact is_zero_zero _ },
    { change F.map _ ≫ _ = _ ≫ F.map _,
      dsimp only, erw [eval'_obj_d_0 _ _ _ 0, eval'_obj_d_0 _ _ _ 0],
      simp only [universal_map.eval_Pow, free_abelian_group.lift_eq_sum, ← endomorphisms.forget_map,
        sum_comp, comp_sum, nat_trans.app_sum, functor.map_sum, whisker_right_app,
        zsmul_comp, comp_zsmul, nat_trans.app_zsmul, functor.map_zsmul],
      refine finset.sum_congr rfl _, intros g hg, refine congr_arg2 _ rfl _,
      dsimp only [endomorphisms.forget_map, functor.map_endomorphisms_map_f],
      rw [← functor.map_comp, ← functor.map_comp], congr' 1,
      dsimp only [basic_universal_map.eval_Pow_app, iso.symm_hom, Pow_X_inv],
      ext j : 2,
      rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← endomorphisms.comp_f,
        biproduct.ι_matrix, biproduct.lift_desc],
      have := (endomorphisms.forget _).map_id ⟨X,f⟩, dsimp only [endomorphisms.forget_obj] at this,
      simp only [← endomorphisms.forget_map, ← this, ← functor.map_zsmul, ← functor.map_sum, ← functor.map_comp],
      congr' 1,
      apply biproduct.hom_ext, intro i,
      simp only [biproduct.lift_π, sum_comp, category.assoc],
      rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
      { rw [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, category.comp_id], },
      { rintro k - hk, rw [biproduct.ι_π_ne _ hk, comp_zero], } },
    { change F.map _ ≫ _ = _ ≫ F.map _,
      dsimp only, erw [eval'_obj_d, eval'_obj_d],
      simp only [universal_map.eval_Pow, free_abelian_group.lift_eq_sum, ← endomorphisms.forget_map,
        sum_comp, comp_sum, nat_trans.app_sum, functor.map_sum, whisker_right_app,
        zsmul_comp, comp_zsmul, nat_trans.app_zsmul, functor.map_zsmul],
      refine finset.sum_congr rfl _, intros g hg, refine congr_arg2 _ rfl _,
      dsimp only [endomorphisms.forget_map, functor.map_endomorphisms_map_f],
      rw [← functor.map_comp, ← functor.map_comp], congr' 1,
      dsimp only [basic_universal_map.eval_Pow_app, iso.symm_hom, Pow_X_inv],
      ext j : 2,
      rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← endomorphisms.comp_f,
        biproduct.ι_matrix, biproduct.lift_desc],
      have := (endomorphisms.forget _).map_id ⟨X,f⟩, dsimp only [endomorphisms.forget_obj] at this,
      simp only [← endomorphisms.forget_map, ← this, ← functor.map_zsmul, ← functor.map_sum, ← functor.map_comp],
      congr' 1,
      apply biproduct.hom_ext, intro i,
      simp only [biproduct.lift_π, sum_comp, category.assoc],
      rw finset.sum_eq_single_of_mem i (finset.mem_univ _),
      { rw [biproduct.ι_π, dif_pos rfl, eq_to_hom_refl, category.comp_id], },
      { rintro k - hk, rw [biproduct.ι_π_ne _ hk, comp_zero], } }, }
end
-/
section

def evalMkEnd (A : 𝓐) (f : A ⟶ A) :
    HomologicalComplex.mkEnd (((Data.evalFunctor F).obj BD.data).obj A)
        (((Data.evalFunctor F).obj BD.data).map f) ≅
      ((Data.evalFunctor F.mapEndomorphisms).obj BD.data).obj ⟨A, f⟩ :=
  by
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  · intro i; refine' Endomorphisms.mkIso _ _
    · refine' F.map_iso _; exact (Pow_X ⟨A, f⟩ _).symm
    · dsimp [HomologicalComplex.mkEnd]
      rw [← F.map_comp, ← F.map_comp]; congr 1
      ext j
      simp only [Category.assoc, biproduct.ι_map_assoc, biproduct.map_desc_assoc, biproduct.ι_desc,
        biproduct.ι_desc_assoc]
      rw [← Endomorphisms.Hom.comm]
  · rintro _ i (rfl : _ = _); ext k
    dsimp [HomologicalComplex.mkEnd, Endomorphisms.mkIso]
    simp only [UniversalMap.evalPow, FreeAbelianGroup.lift_eq_sum, ← Endomorphisms.forget_map,
      NatTrans.app_sum, Functor.map_sum, comp_sum, sum_comp, NatTrans.app_zsmul,
      Functor.map_zsmul, comp_zsmul, zsmul_comp]
    refine' Finset.sum_congr rfl _
    intro x hx
    refine' congr_arg₂ _ rfl _
    dsimp only [Endomorphisms.forget_map, Functor.mapEndomorphisms_map_f, CategoryTheory.whiskerRight_app,
      BasicUniversalMap.evalPow_app]
    rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
    ext j : 2
    rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← Endomorphisms.comp_f,
      biproduct.ι_matrix, biproduct.lift_desc]
    have := (Endomorphisms.forget _).map_id ⟨A, f⟩; dsimp only [Endomorphisms.forget_obj] at this 
    simp only [← Endomorphisms.forget_map, ← this, ← Functor.map_zsmul, ← Functor.map_sum, ←
      Functor.map_comp]
    congr 1
    apply biproduct.hom_ext; intro i
    simp only [biproduct.lift_π, sum_comp, Category.assoc]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · rw [biproduct.ι_π, dif_pos rfl, CategoryTheory.eqToHom_refl, Category.comp_id]
    · rintro k - hk; rw [biproduct.ι_π_ne _ hk, comp_zero]

variable (hH0 : (Data.evalFunctor F).obj BD.data ⋙ homology'Functor _ _ 0 ≅ 𝟭 _)

variable (X : Endomorphisms 𝓐)

def forgetEval :
    Endomorphisms.forget _ ⋙ (Data.evalFunctor F).obj BD.data ≅
      (Data.evalFunctor F.mapEndomorphisms).obj BD.data ⋙
        (Endomorphisms.forget 𝓐).mapHomologicalComplex _ :=
  NatIso.ofComponents
    (fun X =>
      HomologicalComplex.Hom.isoOfComponents (fun n => F.mapIso (powX _ _).symm)
        (by
          rintro _ i (rfl : _ = _)
          dsimp only [Functor.comp_obj, Data.evalFunctor_obj_obj_d,
            Functor.mapHomologicalComplex_obj_d, UniversalMap.evalPow]
          simp only [FreeAbelianGroup.lift_eq_sum, sum_comp, comp_sum, NatTrans.app_sum,
            Functor.map_sum, CategoryTheory.whiskerRight_app, zsmul_comp, comp_zsmul, NatTrans.app_zsmul,
            Functor.map_zsmul]
          refine' Finset.sum_congr rfl _
          intro x hx
          refine' congr_arg₂ _ rfl _
          dsimp only [Endomorphisms.forget_map, Functor.mapEndomorphisms_map_f,
            Functor.mapIso_hom, CategoryTheory.whiskerRight_app, BasicUniversalMap.evalPow_app, Pow_X_inv,
            Iso.symm_hom]
          rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
          ext j : 2
          rw [biproduct.ι_desc_assoc, biproduct.ι_matrix_assoc, ← Endomorphisms.comp_f,
            biproduct.ι_matrix, biproduct.lift_desc]
          have := (Endomorphisms.forget _).map_id X
          simp only [← Endomorphisms.forget_map, ← this, ← Functor.map_zsmul, ← Functor.map_sum, ←
            Functor.map_comp]
          congr 1
          apply biproduct.hom_ext; intro i
          simp only [biproduct.lift_π, sum_comp, Category.assoc]
          rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
          · rw [biproduct.ι_π, dif_pos rfl, CategoryTheory.eqToHom_refl, Category.comp_id]
          · rintro k - hk; rw [biproduct.ι_π_ne _ hk, comp_zero]))
    (by
      intro X Y f
      ext n
      dsimp only [HomologicalComplex.Hom.isoOfComponents_hom_f, HomologicalComplex.comp_f,
        Iso.symm_hom, Pow_X_inv, Functor.comp_map, Functor.mapIso_hom,
        Functor.mapHomologicalComplex_map_f, Data.evalFunctor_obj_map_f,
        Endomorphisms.forget_map, Functor.mapEndomorphisms_map_f]
      rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
      ext j : 2
      rw [biproduct.ι_desc_assoc, biproduct.ι_map_assoc, ← Endomorphisms.comp_f, biproduct.ι_map,
        biproduct.ι_desc, Endomorphisms.comp_f])

def eval'Homology {𝓐 : Type _} [Category 𝓐] [Abelian 𝓐] (F : 𝓐 ⥤ 𝓐) (i : ℕ) :
    BD.eval' F ⋙ homology'Functor 𝓐 (ComplexShape.up ℤ) (-i) ≅
      (Data.evalFunctor F).obj BD.data ⋙ homology'Functor 𝓐 (ComplexShape.down ℕ) i :=
  by
  calc
    ((Data.evalFunctor F).obj BD.data ⋙
            HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp) ⋙
          homology'Functor 𝓐 (ComplexShape.up ℤ) (-i) ≅
        (Data.evalFunctor F).obj BD.data ⋙
          HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
            homology'Functor 𝓐 (ComplexShape.up ℤ) (-i) :=
      Functor.associator _ _ _
    _ ≅ (Data.evalFunctor F).obj BD.data ⋙ homology'Functor 𝓐 (ComplexShape.down ℕ) i :=
      CategoryTheory.isoWhiskerLeft _ _
  refine' HomologicalComplex.homologyEmbedNatIso 𝓐 ComplexShape.Embedding.natDownIntUp _ _ _
  · cases i <;> rfl

def hHEndo₁A (i : ℕ) :
    BD.eval' F.mapEndomorphisms ⋙ homology'Functor _ _ (-i) ⋙ Endomorphisms.forget 𝓐 ≅
      (Data.evalFunctor F.mapEndomorphisms).obj BD.data ⋙
        homology'Functor _ _ i ⋙ Endomorphisms.forget 𝓐 :=
  ((whiskeringRight _ _ _).obj (Endomorphisms.forget 𝓐)).mapIso (eval'Homology _ _ _)

def hHEndo₁B (i : ℕ) :
    (Data.evalFunctor F.mapEndomorphisms).obj BD.data ⋙
        homology'Functor _ _ i ⋙ Endomorphisms.forget 𝓐 ≅
      (Data.evalFunctor F.mapEndomorphisms).obj BD.data ⋙
        (Endomorphisms.forget 𝓐).mapHomologicalComplex _ ⋙ homology'Functor _ _ i :=
  ((whiskeringLeft _ _ _).obj ((Data.evalFunctor _).obj BD.data)).mapIso
    ((Endomorphisms.forget 𝓐).homology'FunctorIso _ i)

def hHEndo₁C (i : ℕ) :
    (Data.evalFunctor F.mapEndomorphisms).obj BD.data ⋙
        (Endomorphisms.forget 𝓐).mapHomologicalComplex _ ⋙ homology'Functor _ _ i ≅
      Endomorphisms.forget _ ⋙ (Data.evalFunctor F).obj BD.data ⋙ homology'Functor _ _ i :=
  (((whiskeringRight _ _ _).obj (homology'Functor 𝓐 (ComplexShape.down ℕ) i)).mapIso
      (forgetEval BD F).symm :
    _)

def hHEndo₁ (i : ℕ) :
    BD.eval' F.mapEndomorphisms ⋙
        homology'Functor (Endomorphisms 𝓐) _ (-i) ⋙ Endomorphisms.forget 𝓐 ≅
      Endomorphisms.forget _ ⋙ (Data.evalFunctor F).obj BD.data ⋙ homology'Functor 𝓐 _ i :=
  hHEndo₁A _ _ i ≪≫ hHEndo₁B _ _ i ≪≫ hHEndo₁C _ _ i

theorem hHEndo₁_natural (X : Endomorphisms 𝓐) (i : ℕ) :
    ((BD.eval' F.mapEndomorphisms ⋙ homology'Functor _ _ (-i)).obj X).e ≫
        (BD.hHEndo₁ F i).hom.app X =
      (BD.hHEndo₁ F i).hom.app X ≫
        ((Data.evalFunctor F).obj BD.data ⋙ homology'Functor 𝓐 _ i).map X.e :=
  by
  let φ : X ⟶ X := ⟨X.e, rfl⟩
  have := (hH_endo₁ BD F i).hom.naturality φ; erw [← this]; clear this
  refine' congr_arg₂ _ _ rfl
  dsimp only [Functor.comp_map, Endomorphisms.forget_map]
  erw [Endomorphisms.homology'Functor_obj_e ((BD.eval' F.map_endomorphisms).obj X) (-i)]
  congr 2
  dsimp only [Package.eval']
  ext i
  rcases hi : complex_shape.embedding.natDownIntUp.r i with (_ | j)
  · apply IsZero.eq_of_src
    dsimp [HomologicalComplex.embed, HomologicalComplex.Embed.obj]
    simp only [hi]
    let zero : endomorphisms 𝓐 := ⟨0, 0⟩
    have h : is_zero zero := by rw [IsZero.iff_id_eq_zero]; ext
    have e' := (Endomorphisms.forget 𝓐).mapIso (IsZero.iso h (is_zero_zero _))
    refine' IsZero.of_iso _ e'.symm
    rw [IsZero.iff_id_eq_zero]
    rw [← (Endomorphisms.forget 𝓐).map_id]
    convert (Endomorphisms.forget 𝓐).map_zero _ _
    ext
  · apply Endomorphisms.congr_f
    dsimp [HomologicalComplex.embed, HomologicalComplex.Embed.map, HomologicalComplex.Embed.obj]
    rw [HomologicalComplex.Embed.f_of_some _ hi]
    rw [←
      cancel_mono
        (HomologicalComplex.Embed.xIsoOfSome
            (((Data.evalFunctor F.map_endomorphisms).obj BD.data).obj X) hi).hom]
    rw [←
      cancel_epi
        (HomologicalComplex.Embed.xIsoOfSome
            (((Data.evalFunctor F.map_endomorphisms).obj BD.data).obj X) hi).inv]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    dsimp only [HomologicalComplex.tautologicalEndomorphism]
    ext
    simp only [Endomorphisms.comp_f, Endomorphisms.Hom.comm]
    slice_lhs 1 2 => rw [← Endomorphisms.comp_f, Iso.inv_hom_id, Endomorphisms.id_f]
    rw [Category.id_comp]
    dsimp
    congr
    rw [← Endomorphisms.endOfE_f]
    apply Endomorphisms.congr_f
    apply biproduct.hom_ext
    intro a
    simpa only [biproduct.map_π, Endomorphisms.endOfE_comm]

def hH0Endo₂ :
    ((BD.eval' F.mapEndomorphisms ⋙ homology'Functor (Endomorphisms 𝓐) (ComplexShape.up ℤ) 0).obj
          X).pt ≅
      X.pt :=
  (hHEndo₁ _ _ 0).app _ ≪≫ hH0.app _

def hH0Endo :
    (BD.eval' F.mapEndomorphisms ⋙ homology'Functor (Endomorphisms 𝓐) (ComplexShape.up ℤ) 0).obj X ≅
      X :=
  Endomorphisms.mkIso (hH0Endo₂ _ _ hH0 X)
    (by
      dsimp only [hH0_endo₂, Iso.trans_hom, CategoryTheory.isoWhiskerLeft_hom, Iso.app_hom, CategoryTheory.whiskerLeft_app]
      have := hH0.hom.naturality X.e; simp only [Functor.id_map] at this 
      simp only [Category.assoc]; erw [← this]; clear this; simp only [← Category.assoc]
      rw [← hH_endo₁_natural BD F X 0]; rfl)

end

variable [EnoughProjectives 𝓐]

variable [HasCoproducts.{v} (Endomorphisms 𝓐)]

variable [AB4 (Endomorphisms 𝓐)]

theorem main_lemma_general (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
    (hH0 : ((BD.eval F.mapEndomorphisms).obj ⟨A, f⟩).val.as.homology' 0 ≅ ⟨A, f⟩)
    (T : Ab.{v} ⥤ Endomorphisms 𝓐) [∀ α : Type v, PreservesColimitsOfShape (Discrete α) T]
    (hT0 : T.obj (AddCommGroupCat.of (PUnit →₀ ℤ)) ≅ ⟨A, f⟩)
    (hT : ∀ {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z), ShortExact f g → ShortExact (T.map f) (T.map g))
    (hTA :
      ∀ t ≤ (-1 : ℤ),
        ∃ A' : Ab,
          Nonempty (T.obj A' ≅ ((BD.eval F.mapEndomorphisms).obj ⟨A, f⟩).val.as.homology' t)) :
    (∀ i, IsIso <| ((ext' i).map f.op).app B - ((ext' i).obj (op A)).map g) ↔
      ∀ i,
        IsIso <|
          ((ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
            ((ext i).obj (op <| (BD.eval F).obj A)).map ((single _ 0).map g) :=
  by
  rw [← Endomorphisms.ext'_isZero_iff A B f g]
  erw [← Endomorphisms.ext_isZero_iff]
  refine' (MainLemma.isZero BD F.map_endomorphisms _ _ hH0 T hT0 (@hT) hTA).trans _
  apply forall_congr'; intro i
  apply Iso.isZero_iff
  refine' Functor.mapIso _ _ ≪≫ Iso.app (Functor.mapIso _ _) _
  · exact iso.refl _
  · refine' Iso.op _; apply Functor.mapIso
    apply BreenDeligne.Package.evalMkEnd

theorem main_lemma (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
    (hH0 : (Data.evalFunctor F).obj BD.data ⋙ homology'Functor _ _ 0 ≅ 𝟭 _)
    (T : Ab.{v} ⥤ Endomorphisms 𝓐) [∀ α : Type v, PreservesColimitsOfShape (Discrete α) T]
    (hT0 : T.obj (AddCommGroupCat.of (PUnit →₀ ℤ)) ≅ ⟨A, f⟩)
    (hT : ∀ {X Y Z : Ab} (f : X ⟶ Y) (g : Y ⟶ Z), ShortExact f g → ShortExact (T.map f) (T.map g))
    (hTA :
      ∀ t ≤ (-1 : ℤ),
        ∃ A' : Ab,
          Nonempty (T.obj A' ≅ ((BD.eval F.mapEndomorphisms).obj ⟨A, f⟩).val.as.homology' t)) :
    (∀ i, IsIso <| ((ext' i).map f.op).app B - ((ext' i).obj (op A)).map g) ↔
      ∀ i,
        IsIso <|
          ((ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
            ((ext i).obj (op <| (BD.eval F).obj A)).map ((single _ 0).map g) :=
  by
  rw [← Endomorphisms.ext'_isZero_iff A B f g]
  erw [← Endomorphisms.ext_isZero_iff]
  refine' (MainLemma.isZero BD F.map_endomorphisms _ _ _ T hT0 (@hT) hTA).trans _
  · exact hH0_endo _ _ hH0 _
  apply forall_congr'; intro i
  apply Iso.isZero_iff
  refine' Functor.mapIso _ _ ≪≫ Iso.app (Functor.mapIso _ _) _
  · exact iso.refl _
  · refine' Iso.op _; apply Functor.mapIso
    apply BreenDeligne.Package.evalMkEnd

@[simps]
def endoT {𝓐 : Type _} [Category 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) :
    Endomorphisms 𝓐 ⥤ Ab.{v} ⥤ Endomorphisms 𝓐 :=
  Functor.flip
    { obj := fun A => (T.flip.obj A).mapEndomorphisms
      map := fun A B f => NatTrans.mapEndomorphisms <| T.flip.map f
      map_id := by intro X; simp only [CategoryTheory.Functor.map_id]; rfl
      map_comp := by intro X Y Z f g; simp only [Functor.map_comp]; rfl }

def endoTCompForget {𝓐 : Type _} [Category 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (M : Endomorphisms 𝓐) :
    (endoT T).obj M ⋙ Endomorphisms.forget _ ≅ T.obj M.pt :=
  (NatIso.ofComponents fun _ => Iso.refl _) <| by intros; dsimp;
    simp only [Category.comp_id, Category.id_comp]

instance endoT_additive {𝓐 : Type _} [Category 𝓐] [Preadditive 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐)
    (A : Endomorphisms 𝓐) [(T.obj A.pt).Additive] : ((endoT T).obj A).Additive
    where map_add' X Y f g := by ext; dsimp; rw [Functor.map_add]

instance endoTPreservesFiniteLimits {𝓐 : Type _} [Category 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐)
    (A : Endomorphisms 𝓐) [PreservesFiniteLimits (T.obj A.pt)] :
    PreservesFiniteLimits ((endoT T).obj A) :=
  by
  constructor; intro J hJ1 hJ2
  haveI : reflects_limits_of_shape J (Endomorphisms.forget 𝓐) := { }
  have : preserves_limits_of_shape J ((endo_T T).obj A ⋙ Endomorphisms.forget 𝓐) :=
    by
    apply CategoryTheory.Limits.preservesLimitsOfShapeOfNatIso (endo_T_comp_forget T A).symm
    infer_instance
  exact
    CategoryTheory.Limits.preservesLimitsOfShapeOfReflectsOfPreserves ((endo_T T).obj A) (Endomorphisms.forget _)

/- ./././Mathport/Syntax/Translate/Basic.lean:339:40: warning: unsupported option pp.universes -/
set_option pp.universes true

instance endoTPreservesFiniteColimits {𝓐 : Type u} [Category.{v} 𝓐] (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐)
    (A : Endomorphisms 𝓐) [PreservesFiniteColimits (T.obj A.pt)] :
    PreservesFiniteColimits ((endoT T).obj A) :=
  by
  constructor; intro J hJ1 hJ2
  -- Move this
  have : reflects_colimits_of_shape J (Endomorphisms.forget 𝓐) :=
    by
    let E : J ≌ AsSmall.{v} J := AsSmall.equiv
    suffices reflects_colimits_of_shape (AsSmall.{v} J) (Endomorphisms.forget 𝓐) by skip;
      apply CategoryTheory.Limits.reflectsColimitsOfShapeOfEquiv E.symm
    constructor
  have : preserves_colimits_of_shape J ((endo_T T).obj A ⋙ Endomorphisms.forget 𝓐) :=
    by
    apply CategoryTheory.Limits.preservesColimitsOfShapeOfNatIso (endo_T_comp_forget T A).symm
    infer_instance
  exact
    CategoryTheory.Limits.preservesColimitsOfShapeOfReflectsOfPreserves ((endo_T T).obj A) (Endomorphisms.forget _)

instance endoTPreservesColimitsOfShapeDiscrete {𝓐 : Type u} [Category.{v} 𝓐] (α : Type v)
    (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) (M : Endomorphisms 𝓐)
    [PreservesColimitsOfShape (Discrete α) (T.obj M.pt)] :
    PreservesColimitsOfShape (Discrete α) ((endoT T).obj M) :=
  by
  letI : reflects_colimits_of_shape (discrete α) (Endomorphisms.forget 𝓐) := { }
  let this.1 :
    preserves_colimits_of_shape (discrete α) ((endo_T T).obj M ⋙ Endomorphisms.forget 𝓐) :=
    by
    apply CategoryTheory.Limits.preservesColimitsOfShapeOfNatIso (endo_T_comp_forget T M).symm
    infer_instance
  exact
    CategoryTheory.Limits.preservesColimitsOfShapeOfReflectsOfPreserves ((endo_T T).obj M) (Endomorphisms.forget _)

theorem endoT_shortExact {𝓐 : Type u} [Category.{v} 𝓐] [Abelian 𝓐]
    [HasProductsOfShape (ULift.{v} ℕ) 𝓐] [HasCoproductsOfShape (ULift.{v} ℕ) 𝓐]
    (A : Endomorphisms 𝓐) (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐) [(T.obj A.pt).Additive]
    [PreservesFiniteLimits (T.obj A.pt)] [PreservesFiniteColimits (T.obj A.pt)] {X Y Z : Ab}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfg : ShortExact f g) :
    ShortExact (((endoT T).obj A).map f) (((endoT T).obj A).map g) := by
  apply Functor.map_shortExact; exact hfg

theorem main_lemma' (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B)
    (hH0 : (Data.evalFunctor F).obj BD.data ⋙ homology'Functor _ _ 0 ≅ 𝟭 _) (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐)
    [(T.obj A).Additive] [PreservesFiniteLimits (T.obj A)] [PreservesFiniteColimits (T.obj A)]
    [∀ α : Type v, PreservesColimitsOfShape (Discrete α) (T.obj A)]
    (hT0 : T.flip.obj (AddCommGroupCat.of (PUnit →₀ ℤ)) ≅ 𝟭 _)
    (hTA :
      ∀ t : ℤ,
        t ≤ -1 →
          ∃ A' : Ab,
            Nonempty
              (((endoT T).obj ⟨A, f⟩).obj A' ≅
                ((BD.eval F.mapEndomorphisms).obj ⟨A, f⟩).val.as.homology' t)) :
    (∀ i, IsIso <| ((ext' i).map f.op).app B - ((ext' i).obj (op A)).map g) ↔
      ∀ i,
        IsIso <|
          ((ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
            ((ext i).obj (op <| (BD.eval F).obj A)).map ((single _ 0).map g) :=
  by
  let M : endomorphisms 𝓐 := ⟨A, f⟩
  apply BD.main_lemma F A B f g hH0 ((endo_T T).obj M)
  · exact Endomorphisms.mkIso (hT0.app _) (NatTrans.naturality _ _)
  · intro X Y Z _ _ hfg; refine' endo_T_short_exact _ T _ _ hfg
  · exact hTA

theorem main_lemma_general' (A : 𝓐) (B : 𝓐) (f : A ⟶ A) (g : B ⟶ B) (T : 𝓐 ⥤ Ab.{v} ⥤ 𝓐)
    [(T.obj A).Additive] [PreservesFiniteLimits (T.obj A)] [PreservesFiniteColimits (T.obj A)]
    [∀ α : Type v, PreservesColimitsOfShape (Discrete α) (T.obj A)]
    (hT0 : T.flip.obj (AddCommGroupCat.of (PUnit →₀ ℤ)) ≅ 𝟭 _) (A' : ℕ → Ab)
    (hA'0 : T.flip.obj (A' 0) ≅ 𝟭 _)
    (hTA :
      ∀ n,
        ((endoT T).obj ⟨A, f⟩).obj (A' n) ≅
          ((BD.eval F.mapEndomorphisms).obj ⟨A, f⟩).val.as.homology' (-n)) :
    (∀ i, IsIso <| ((ext' i).map f.op).app B - ((ext' i).obj (op A)).map g) ↔
      ∀ i,
        IsIso <|
          ((ext i).map ((BD.eval F).map f).op).app ((single _ 0).obj B) -
            ((ext i).obj (op <| (BD.eval F).obj A)).map ((single _ 0).map g) :=
  by
  let M : endomorphisms 𝓐 := ⟨A, f⟩
  -- let h
  apply BD.main_lemma_general F A B f g _ ((endo_T T).obj M)
  · exact Endomorphisms.mkIso (hT0.app _) (NatTrans.naturality _ _)
  · intro X Y Z _ _ hfg; refine' endo_T_short_exact _ T _ _ hfg
  · intro t ht
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = -n :=
      by
      lift -t to ℕ with n hn; swap; · rw [neg_nonneg]; refine' ht.trans _; decide
      refine' ⟨n, _⟩; rw [hn, neg_neg]
    refine' ⟨A' n, ⟨hTA n⟩⟩
  · refine' (hTA 0).symm ≪≫ _
    refine' Endomorphisms.mkIso (hA'0.app _) (hA'0.hom.naturality f)

end

end Package

end BreenDeligne

