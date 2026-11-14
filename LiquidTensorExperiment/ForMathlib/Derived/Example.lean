import Mathlib.Data.ZMod.Basic
import LiquidTensorExperiment.ForMathlib.ComplexExtend
import LiquidTensorExperiment.ForMathlib.Projectives
import LiquidTensorExperiment.ForMathlib.TwoStepResolution
import LiquidTensorExperiment.ForMathlib.HomSingleIso
import LiquidTensorExperiment.ForMathlib.HomologicalComplexOp

#align_import for_mathlib.derived.example

universe v u

open CategoryTheory HomotopyCategory

variable {C : Type u} {ι : Type _} [Category.{v} C] [Abelian C] {c : ComplexShape ι}

open scoped ZeroObject

instance projective_zero : Projective (0 : C) where Factors E X f e he := ⟨0, by ext⟩

theorem CategoryTheory.isIso_of_nat_iso {C D : Type _} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ≅ G) {X Y : C} (f : X ⟶ Y) (h : IsIso (F.map f)) : IsIso (G.map f) :=
  by
  rw [← NatIso.naturality_1 α f]
  infer_instance

theorem CategoryTheory.NatIso.isIso_iff {C D : Type _} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ≅ G) {X Y : C} (f : X ⟶ Y) : IsIso (F.map f) ↔ IsIso (G.map f) :=
  ⟨CategoryTheory.isIso_of_nat_iso α _, CategoryTheory.isIso_of_nat_iso α.symm _⟩

open CategoryTheory

theorem ChainComplex.boundedByOne (P : ChainComplex C ℕ) :
    ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
              Quotient C (ComplexShape.up ℤ)).obj
          P).BoundedBy
      1 :=
  by
  rintro ((_ | i) | i) h
  · exfalso; revert h; decide
  · exact Limits.isZero_zero _
  · exfalso; revert h; decide

instance ChainComplex.isBoundedAbove (P : ChainComplex C ℕ) :
    ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
            Quotient C (ComplexShape.up ℤ)).obj
        P).IsBoundedAbove :=
  ⟨⟨1, ChainComplex.boundedByOne _⟩⟩

/-- The functor from ℕ-indexed chain complexes to bounded-above ℤ-indexed cochain complexes
sending `C₀ ← C₁ ← ...` to `... ⟶ C₁ ⟶ C₀ ⟶ 0 ⟶ ...` -/
@[simps obj obj_val map]
noncomputable def ChainComplex.toBoundedHomotopyCategory :
    ChainComplex C ℕ ⥤ BoundedHomotopyCategory C
    where
  obj P :=
    { val :=
        (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
              HomotopyCategory.quotient C _).obj
          P
      bdd := by apply ChainComplex.isBoundedAbove }
  map P Q f :=
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
          HomotopyCategory.quotient C _).map
      f
  map_id P :=
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
          HomotopyCategory.quotient C _).map_id
      P
  map_comp P Q R f g :=
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
          HomotopyCategory.quotient C _).map_comp
      f g

theorem ChainComplex.toBoundedHomotopyCategory.isKProjective [EnoughProjectives C]
    (P : ChainComplex C ℕ) (A : C) (π : P ⟶ (ChainComplex.single₀ C).obj A)
    (hP : P.IsProjectiveResolution A π) :
    IsKProjective (ChainComplex.toBoundedHomotopyCategory.obj P).val :=
  by
  constructor
  intro Y hY f
  rw [← quotient_map_out f]
  apply eq_of_homotopy
  refine' Projective.nullHomotopicOfProjectiveToAcyclic _ 1 _ _ hY.cond
  · rintro ((_ | i) | i)
    · exact hP.projective 0
    · exact projective_zero
    · exact hP.projective _
  · rintro ((_ | i) | i)
    · intro h; exfalso; revert h; decide
    · intro h; exact Limits.isZero_zero _
    · intro h; exfalso; revert h; decide

noncomputable def HomologicalComplex.homologyFunctorSingle [DecidableEq ι] (i : ι) :
    HomologicalComplex.single C c i ⋙ homology'Functor C c i ≅ 𝟭 C :=
  by
  refine' NatIso.ofComponents _ _
  · intro X
    refine' homology'.congr _ _ _ _ ≪≫ homology'ZeroZero ≪≫ _
    · rfl
    · rfl
    · exact eq_to_iso (if_pos rfl)
  · intro X Y f
    apply homology'.ext
    dsimp
    simpa only [Category.comp_id, HomologicalComplex.Hom.sqFrom_left, CategoryTheory.eqToHom_refl,
      HomologicalComplex.singleObjXSelf_hom, homology'.map_desc_assoc, CategoryTheory.eqToHom_trans,
      HomologicalComplex.singleObjXSelf_inv, HomologicalComplex.single_map_f_self, Category.assoc,
      Limits.kernelSubobjectMap_arrow, homology'.π_desc_assoc]

instance {X Y Z : C} (f : X ⟶ Y) : IsIso (homology'.ι f (0 : Y ⟶ Z) Limits.comp_zero) :=
  by
  suffices Limits.cokernel.desc f 0 Limits.comp_zero = 0 by
    exact @IsIso.comp_isIso _ _ (show _ by convert Limits.kernel.ι_zero_is_iso)
  ext
  simp

theorem homology'.desc_zero_isIso_of_exact_of_epi {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Exact f g) [Epi g] :
    IsIso
      (homology'.desc' f (0 : Y ⟶ W) Limits.comp_zero (Limits.kernelZeroIsoSource.hom ≫ g)
        (by simp [h.w])) :=
  by
  convert_to
    is_iso
      (homology'.ι _ _ _ ≫
        (Limits.colimit.isoColimitCocone ⟨_, Abelian.isColimitOfExactOfEpi f g h⟩).hom)
  · ext; simp
  · infer_instance

theorem ChainComplex.IsProjectiveResolution.isQuasiIsoEmbed {P : ChainComplex C ℕ} {A : C}
    {π : P ⟶ (ChainComplex.single₀ C).obj A} (hP : P.IsProjectiveResolution A π) :
    IsQuasiIso
      ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
            HomotopyCategory.quotient C _).map
        π) :=
  by
  constructor
  intro i
  rw [← Functor.comp_map,
    CategoryTheory.NatIso.isIso_iff
      (Functor.associator _ _ _ ≪≫ CategoryTheory.isoWhiskerLeft _ (HomotopyCategory.homology'Factors _ _ _))]
  rcases i with ((_ | i) | i)
  · apply (config := { instances := false }) IsIso.of_isIso_comp_right
    show
      is_iso
        (Functor.mapIso _ (chain_complex.single₀CompEmbedIsoSingle.app A) ≪≫
            ((HomologicalComplex.homologyFunctorSingle (0 : ℤ)).app A : _)).hom
    · infer_instance
    apply (config := { instances := false }) IsIso.of_isIso_comp_left
    swap; convert @homology'.desc_zero_isIso_of_exact_of_epi _ _ _ _ hP.exact₀ hP.epi using 1
    pick_goal 4
    · refine' (homology'.mapIso _ _ (Arrow.isoMk _ _ _) (Arrow.isoMk _ (iso.refl _) _) rfl).hom
      ·
        exact
          ((HomologicalComplex.Embed.obj ComplexShape.Embedding.natDownIntUp P).xPrevIso
              (show (ComplexShape.up ℤ).Rel -[0+1] 0 from neg_add_self 1)).symm
      · exact iso.refl _
      · dsimp
        rw [eq_comm, Iso.eq_inv_comp, Category.comp_id, eq_comm]
        apply HomologicalComplex.dTo_eq
      · dsimp
        rw [Category.comp_id, Category.id_comp]
        erw [HomologicalComplex.dFrom_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
        exact Limits.zero_comp
    · ext
      dsimp only [homology'.mapIso, HomologicalComplex.homologyFunctorSingle]
      rw [← cancel_epi (Limits.kernelSubobjectIso _).hom, homology'.π'_eq_π_assoc]
      simp only [homology'.π'_desc', Category.comp_id, HomologicalComplex.Hom.sqFrom_left,
        Limits.kernelSubobject_arrow_assoc, homology'.π_desc, homology'.map_desc,
        Limits.kernelSubobjectMap_arrow_assoc, Arrow.isoMk_hom_left,
        Limits.kernelSubobjectMap_arrow]
      dsimp only [ChainComplex.single₀CompEmbedIsoSingle,
        ChainComplex.single₀CompEmbedIsoSingleComponent]
      simp only [Limits.kernelSubobjectMap_arrow, Limits.kernelSubobjectMap_arrow_assoc,
        HomologicalComplex.Hom.sqFrom_left, HomologicalComplex.Hom.isoOfComponents_hom_f,
        Functor.comp_map, homology'Functor_map, NatIso.ofComponents.app, eq_to_iso_refl,
        Iso.trans_refl, Iso.trans_hom, Functor.mapIso_hom, homology'.congr_hom,
        homology'ZeroZero_hom, homology'.map_desc, homology'.π_map_assoc,
        Limits.kernelZeroIsoSource_hom, Limits.kernelSubobject_arrow_assoc]
      erw [homology'.π_desc, Limits.kernelSubobjectMap_arrow_assoc]
      simp only [HomologicalComplex.Hom.sqFrom_left, Limits.kernelSubobjectMap_arrow_assoc,
        Arrow.isoMk_hom_left]
      dsimp only [ChainComplex.single₀CompEmbedIsoSingleComponent]
      erw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.id_comp, Category.comp_id]; rfl
      infer_instance
    · infer_instance
  · refine' Limits.IsZero.isIso _ _ _ <;> refine' Exact.homology'_isZero _ _ (exact_of_zero _ _)
  · refine' Limits.IsZero.isIso _ _ _
    · refine' Limits.isZero_of_iso_of_zero _ (homology_iso _ (-[i.succ+1] : ℤ) _ (-i : ℤ) _ _).symm
      rotate_left
      · dsimp; rfl
      · dsimp; simp only [Int.negSucc_eq', sub_add_cancel]
      refine' Exact.homology'_isZero _ _ _
      cases i <;> exact hP.exact _
    · refine' Limits.isZero_of_iso_of_zero _ (homology_iso _ (-[i.succ+1] : ℤ) _ (-i : ℤ) _ _).symm
      rotate_left
      · dsimp; rfl
      · dsimp; simp only [Int.negSucc_eq', sub_add_cancel]
      refine' Exact.homology'_isZero _ _ (exact_of_zero _ _)

open Opposite

open CategoryTheory.Limits

@[simp]
theorem CategoryTheory.Equivalence.symm_toAdjunction_counit {C D : Type _} [Category C] [Category D]
    (e : C ≌ D) : e.symm.toAdjunction.counit = e.unitInv :=
  rfl

@[simp]
theorem HomologicalComplex.shiftEquiv_unit_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).Unit.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [CategoryTheory.shiftEquiv, CategoryTheory.unitOfTensorIsoUnit]
  simp only [HomologicalComplex.xEqToIso, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app, eqToIso.hom,
    HomologicalComplex.eqToHom_f, CategoryTheory.eqToHom_trans, HomologicalComplex.shift_μ_inv_app_f]

@[simp]
theorem HomologicalComplex.shiftEquiv_unitInv_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).unitInv.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [CategoryTheory.shiftEquiv, CategoryTheory.unitOfTensorIsoUnit]
  simp only [HomologicalComplex.xEqToIso, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app, eqToIso.hom,
    HomologicalComplex.eqToHom_f, HomologicalComplex.shift_ε_inv_app_f, CategoryTheory.eqToHom_trans]

@[simp]
theorem CategoryTheory.Equivalence.symm_toAdjunction_unit {C D : Type _} [Category C] [Category D]
    (e : C ≌ D) : e.symm.toAdjunction.Unit = e.counitInv :=
  rfl

@[simp]
theorem HomologicalComplex.shiftEquiv_counit_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).counit.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [CategoryTheory.shiftEquiv, CategoryTheory.unitOfTensorIsoUnit]
  simp only [HomologicalComplex.xEqToIso, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app, eqToIso.hom,
    HomologicalComplex.eqToHom_f, HomologicalComplex.shift_ε_inv_app_f, CategoryTheory.eqToHom_trans]

@[simp]
theorem HomologicalComplex.shiftEquiv_counitInv_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).counitInv.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [CategoryTheory.shiftEquiv, CategoryTheory.unitOfTensorIsoUnit]
  simpa only [HomologicalComplex.xEqToIso, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_app, eqToIso.hom,
    add_neg_equiv_counit_iso_inv, NatTrans.comp_app, HomologicalComplex.comp_f,
    HomologicalComplex.shift_ε_hom_app_f, HomologicalComplex.eqToHom_f,
    HomologicalComplex.shift_μ_inv_app_f, CategoryTheory.eqToHom_trans]

variable [EnoughProjectives C]

noncomputable def ext'Iso (A : Cᵒᵖ) (B : C) (i : ℤ) (P : ChainComplex C ℕ)
    (π : P ⟶ (ChainComplex.single₀ C).obj A.unop) (hP : P.IsProjectiveResolution A.unop π) :
    ((ext' i).obj A).obj B ≅
      (((preadditiveYoneda.obj B).mapHomologicalComplex _).obj
            ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj P).op).homology'
        (-i) :=
  by
  dsimp only [ext', Functor.comp_obj, Functor.op_obj, Functor.flip_obj_obj]
  haveI := ChainComplex.toBoundedHomotopyCategory.isKProjective P A.unop π hP
  haveI : is_quasi_iso (chain_complex.toBoundedHomotopyCategory.map π) := hP.isQuasiIsoEmbed
  refine'
    BoundedHomotopyCategory.extIso i (chain_complex.toBoundedHomotopyCategory.obj P) _ _
        (chain_complex.toBoundedHomotopyCategory.map π ≫ _) ≪≫
      (preadditive_yoneda.map_iso _).app (op (chain_complex.toBoundedHomotopyCategory.obj P)) ≪≫
        BoundedHomotopyCategory.homSingleIso _ B (-i)
  ·
    exact
      ((HomotopyCategory.quotient _ _).mapIso <|
          ChainComplex.single₀CompEmbedIsoSingle.app A.unop).hom
  · infer_instance
  · exact (BoundedHomotopyCategory.shiftSingleIso 0 i).app B ≪≫ eq_to_iso (by rw [zero_sub])

theorem AddCommGroupCat.isZero_of_eq (A : AddCommGroupCat) (h : ∀ x y : A, x = y) : IsZero A :=
  by
  rw [CategoryTheory.Limits.isZero_iff_id_eq_zero]
  ext
  apply h

theorem CategoryTheory.ProjectiveResolution.isProjectiveResolution {A : C}
    (P : ProjectiveResolution A) : P.complex.IsProjectiveResolution _ P.π :=
  { Projective := P.Projective
    exact₀ := P.exact₀
    exact := P.exact
    Epi := ProjectiveResolution.F.CategoryTheory.epi P 0 }

theorem ext'_isZero_of_neg (A : Cᵒᵖ) (B : C) (i : ℤ) (hi : i < 0) :
    IsZero (((ext' i).obj A).obj B) :=
  by
  let P := ProjectiveResolution.of A.unop
  refine' CategoryTheory.Limits.isZero_of_iso_of_zero _ (ext'Iso _ _ i P.complex P.π P.is_projective_resolution).symm
  rcases i with (i | i)
  · exfalso; revert hi; decide
  refine' IsZero.homology'_isZero _ _ _ _
  refine' AddCommGroupCat.isZero_of_eq _ _
  intro f g
  ext

section

open BoundedHomotopyCategory

theorem ext_single_right_isZero (A : HomotopyCategory C (ComplexShape.up ℤ)) (B : C) (i j k : ℤ)
    (hA : A.BoundedBy i) [A.IsBoundedAbove] (hijk : i + j ≤ k) :
    IsZero (((ext j).obj (op ⟨A⟩)).obj ((BoundedHomotopyCategory.single _ k).obj B)) :=
  by
  obtain ⟨P, H1, H2, f, H3, H4⟩ := exists_bounded_K_projective_replacement_of_bounded _ _ hA
  have H5 : P.is_bounded_above := ⟨⟨i, H2⟩⟩
  skip
  refine' CategoryTheory.Limits.isZero_of_iso_of_zero _ (Ext_iso j ⟨P⟩ _ _ _).symm
  swap; · exact f; swap; · exact H3
  refine' AddCommGroupCat.isZero_of_eq _ _
  rintro (φ ψ : P ⟶ _)
  rw [← quotient_map_out φ, ← quotient_map_out ψ]
  congr 1
  ext n
  by_cases hn : i ≤ n
  · apply (H2 n hn).eq_of_src
  · apply IsZero.eq_of_tgt
    dsimp [BoundedHomotopyCategory.single]
    rw [if_neg]; · exact is_zero_zero _
    linarith only [hijk, hn]

end

namespace AddCommGroupCat

-- We only need `G` to preserve epimorphisms, but we don't have such a class.
theorem preserves_projectives {C D : Type _} [Category C] [Category.{v} D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) [PreservesColimitsOfShape WalkingSpan G] (P : C) [Projective P] :
    Projective (F.obj P) := by
  constructor
  intros
  skip
  use(adj.homEquiv _ _).symm (Projective.factorThru (adj.homEquiv _ _ f) (G.map e))
  rw [← adj.homEquiv_naturality_right_symm, Projective.factorThru_comp, Equiv.symm_apply_apply]

instance {C D : Type _} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [Faithful G]
    (X : D) : Epi (adj.counit.app X) :=
  by
  have H : split_epi (G.map (adj.counit.app X)) := ⟨_, adj.right_triangle_components⟩
  haveI := H.epi
  exact G.epi_of_epi_map inferInstance

theorem enoughProjectives_of_adjoint {C D : Type _} [Category C] [Category.{v} D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) [PreservesColimitsOfShape WalkingSpan G] [Faithful G]
    [EnoughProjectives C] : EnoughProjectives D :=
  by
  haveI : CategoryTheory.IsLeftAdjoint F := ⟨_, adj⟩
  constructor
  intro X
  refine' ⟨⟨_, preserves_projectives adj _, (adj.homEquiv _ _).symm (projective.π (G.obj X)), _⟩⟩
  dsimp
  rw [Adjunction.homEquiv_counit]
  exact epi_comp _ _

instance : EnoughProjectives AddCommGroupCat.{u} :=
  enoughProjectives_of_adjoint
    (Functor.asEquivalence (forget₂ (ModuleCat ℤ) AddCommGroupCat)).toAdjunction

theorem Ext_isZero_of_one_lt (A : AddCommGroupCat.{u}ᵒᵖ) (B : AddCommGroupCat.{u}) (i : ℤ)
    (hi : i > 1) : IsZero (((ext' i).obj A).obj B) :=
  by
  induction A
  rcases A with ⟨A, _Ainst⟩; skip
  let this.1 := ext'Iso (op <| AddCommGroupCat.of A) B i
  dsimp at this 
  refine' CategoryTheory.Limits.isZero_of_iso_of_zero _ (this _ _ (twoStepResolutionAbProjective A)).symm
  rcases i with ((_ | _ | i) | i)
  · exfalso; revert hi; decide
  · exfalso; revert hi; decide
  swap
  · exfalso; revert hi; decide
  refine' IsZero.homology'_isZero _ _ _ _
  refine' AddCommGroupCat.isZero_of_eq _ _
  intro f g
  apply CategoryTheory.Limits.HasZeroObject.from_zero_ext

noncomputable section

variable (n : ℕ)

-- move me (the rest of the file)
def zmodResolution : ChainComplex AddCommGroupCat ℕ :=
  ChainComplex.mk' (of ℤ) (of ℤ) (n • 𝟙 _) fun _ => ⟨0, 0, zero_comp⟩

example : (zmodResolution n).pt 0 = of ℤ :=
  rfl

def zmodResolutionPiF :
    ∀ i : ℕ,
      (zmodResolution n).pt i ⟶ ((ChainComplex.single₀ AddCommGroupCat).obj (of <| ZMod n)).pt i
  | 0 => show of ℤ ⟶ of (ZMod n) from (Int.castRingHom (ZMod n)).toAddMonoidHom
  | i + 1 => 0

def zmodResolutionPi : zmodResolution n ⟶ (ChainComplex.single₀ AddCommGroupCat).obj (of <| ZMod n)
    where
  f := zmodResolutionPiF n
  comm' := by
    rintro i ⟨_ | j⟩ (rfl : _ = _)
    · ext k; dsimp [AddCommGroupCat.zmodResolutionPiF, AddCommGroupCat.zmodResolution]
      simp only [zero_apply, Fin.val_zero, comp_apply, Int.coe_castAddHom]
      simp only [ChainComplex.mk'_d_1_0, AddMonoidHom.coe_smul, Pi.smul_apply, id_apply, nsmul_one,
        Int.ofNat_bit0, Int.ofNat_succ, Int.ofNat_zero, zero_add, Int.cast_bit0, Int.cast_one,
        map_nsmul]
      simp only [RingHom.coe_addMonoidHom, eq_intCast, Int.cast_one, nsmul_one, ZMod.nat_cast_self]
    · exact comp_zero.trans comp_zero.symm

attribute [-instance] Limits.hasSmallestColimitsOfHasColimits

instance : Projective (AddCommGroupCat.of ℤ) :=
  preserves_projectives (Functor.asEquivalence (forget₂ (ModuleCat ℤ) AddCommGroupCat)).toAdjunction
    (ModuleCat.of ℤ ℤ)

theorem exact_zMod_nsmul_cast :
    Exact (n • 𝟙 (of ℤ)) (AddCommGroupCat.ofHom <| Int.castAddHom (ZMod n)) :=
  by
  rw [AddCommGroupCat.exact_iff]
  erw [ZMod.ker_int_castAddHom]
  ext
  apply exists_congr
  rintro (a : ℤ)
  change n • a = x ↔ a * (n : ℤ) = x
  rw [mul_comm]
  norm_num

theorem zmodResolutionIsResolution (hn : n ≠ 0) :
    (zmodResolution n).IsProjectiveResolution (of (ZMod n)) (zmodResolutionPi n) :=
  by
  constructor
  · rintro (_ | _ | _ | _)
    · show projective (AddCommGroupCat.of ℤ); · infer_instance
    · show projective (AddCommGroupCat.of ℤ); · infer_instance
    · show projective (0 : AddCommGroupCat); · infer_instance
    · show projective (0 : AddCommGroupCat); · infer_instance
  · dsimp [AddCommGroupCat.zmodResolutionPi, AddCommGroupCat.zmodResolutionPiF, AddCommGroupCat.zmodResolution]
    rw [ChainComplex.mk'_d_1_0]
    exact AddCommGroupCat.exact_zMod_nsmul_cast n
  · intro i
    dsimp [AddCommGroupCat.zmodResolution, ChainComplex.mk', ChainComplex.mk, ChainComplex.of]
    rw [if_pos rfl, if_pos rfl, Category.id_comp, Category.id_comp]
    rcases i with (_ | _ | _)
    · show exact 0 (n • 𝟙 (of ℤ))
      rw [(Abelian.tfae_mono 0 (n • 𝟙 (of ℤ))).out 2 0, AddCommGroupCat.mono_iff_injective]
      rintro (x : ℤ) (y : ℤ) (e : n • x = n • y)
      norm_num at e 
      exact e.resolve_right hn
    · show exact 0 0; apply exact_of_zero
    · show exact 0 0; apply exact_of_zero
  · dsimp [AddCommGroupCat.zmodResolutionPi, AddCommGroupCat.zmodResolutionPiF]
    rw [AddCommGroupCat.epi_iff_surjective]
    rintro (x : ZMod n)
    exact ⟨(x : ℤ), by norm_num⟩

theorem Zmod.nsmul_eq_zero (k : ZMod n) : n • k = 0 := by norm_num

@[simps]
def AddSubgroup.equivTop (A : Type _) [AddCommGroup A] : A ≃+ (⊤ : AddSubgroup A)
    where
  toFun x := ⟨x, AddSubgroup.mem_top _⟩
  invFun x := x
  left_inv x := rfl
  right_inv := by rintro ⟨x, hx⟩; rfl
  map_add' x y := rfl

end AddCommGroupCat

