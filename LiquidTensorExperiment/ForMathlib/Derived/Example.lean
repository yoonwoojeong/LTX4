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
  rw [← nat_iso.naturality_1 α f]
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
  · exact limits.is_zero_zero _
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
  map_id' P :=
    (HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp ⋙
          HomotopyCategory.quotient C _).map_id
      P
  map_comp' P Q R f g :=
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
  refine' projective.null_homotopic_of_projective_to_acyclic _ 1 _ _ hY.cond
  · rintro ((_ | i) | i)
    · exact hP.projective 0
    · exact projective_zero
    · exact hP.projective _
  · rintro ((_ | i) | i)
    · intro h; exfalso; revert h; decide
    · intro h; exact limits.is_zero_zero _
    · intro h; exfalso; revert h; decide

noncomputable def HomologicalComplex.homologyFunctorSingle [DecidableEq ι] (i : ι) :
    HomologicalComplex.single C c i ⋙ homology'Functor C c i ≅ 𝟭 C :=
  by
  refine' nat_iso.of_components _ _
  · intro X
    refine' homology'.congr _ _ _ _ ≪≫ homology'ZeroZero ≪≫ _
    · rfl
    · rfl
    · exact eq_to_iso (if_pos rfl)
  · intro X Y f
    apply homology'.ext
    dsimp
    simpa only [category.comp_id, HomologicalComplex.Hom.sqFrom_left, eq_to_hom_refl,
      HomologicalComplex.singleObjXSelf_hom, homology'.map_desc_assoc, eq_to_hom_trans,
      HomologicalComplex.singleObjXSelf_inv, HomologicalComplex.single_map_f_self, category.assoc,
      limits.kernel_subobject_map_arrow, homology'.π_desc_assoc]

instance {X Y Z : C} (f : X ⟶ Y) : IsIso (homology'.ι f (0 : Y ⟶ Z) Limits.comp_zero) :=
  by
  suffices limits.cokernel.desc f 0 limits.comp_zero = 0 by
    exact @is_iso.comp_is_iso _ _ (show _ by convert limits.kernel.ι_zero_is_iso)
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
        (limits.colimit.iso_colimit_cocone ⟨_, abelian.is_colimit_of_exact_of_epi f g h⟩).hom)
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
  rw [← functor.comp_map,
    CategoryTheory.NatIso.isIso_iff
      (functor.associator _ _ _ ≪≫ iso_whisker_left _ (homology_factors _ _ _))]
  rcases i with ((_ | i) | i)
  · apply (config := { instances := false }) is_iso.of_is_iso_comp_right
    show
      is_iso
        (functor.map_iso _ (chain_complex.single₀_comp_embed_iso_single.app A) ≪≫
            ((HomologicalComplex.homologyFunctorSingle (0 : ℤ)).app A : _)).hom
    · infer_instance
    apply (config := { instances := false }) is_iso.of_is_iso_comp_left
    swap; convert @homology'.desc_zero_isIso_of_exact_of_epi _ _ _ _ hP.exact₀ hP.epi using 1
    pick_goal 4
    · refine' (homology'.mapIso _ _ (arrow.iso_mk _ _ _) (arrow.iso_mk _ (iso.refl _) _) rfl).hom
      ·
        exact
          ((HomologicalComplex.Embed.obj ComplexShape.Embedding.natDownIntUp P).xPrevIso
              (show (ComplexShape.up ℤ).Rel -[0+1] 0 from neg_add_self 1)).symm
      · exact iso.refl _
      · dsimp
        rw [eq_comm, iso.eq_inv_comp, category.comp_id, eq_comm]
        apply HomologicalComplex.dTo_eq
      · dsimp
        rw [category.comp_id, category.id_comp]
        erw [HomologicalComplex.dFrom_eq _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
        exact limits.zero_comp
    · ext
      dsimp only [homology'.mapIso, HomologicalComplex.homologyFunctorSingle]
      rw [← cancel_epi (limits.kernel_subobject_iso _).hom, homology'.π'_eq_π_assoc]
      simp only [homology'.π'_desc', category.comp_id, HomologicalComplex.Hom.sqFrom_left,
        limits.kernel_subobject_arrow_assoc, homology'.π_desc, homology'.map_desc,
        limits.kernel_subobject_map_arrow_assoc, arrow.iso_mk_hom_left,
        limits.kernel_subobject_map_arrow]
      dsimp only [ChainComplex.single₀CompEmbedIsoSingle,
        ChainComplex.single₀CompEmbedIsoSingleComponent]
      simp only [limits.kernel_subobject_map_arrow, limits.kernel_subobject_map_arrow_assoc,
        HomologicalComplex.Hom.sqFrom_left, HomologicalComplex.Hom.isoOfComponents_hom_f,
        functor.comp_map, homology'Functor_map, nat_iso.of_components.app, eq_to_iso_refl,
        iso.trans_refl, iso.trans_hom, functor.map_iso_hom, homology'.congr_hom,
        homology'ZeroZero_hom, homology'.map_desc, homology'.π_map_assoc,
        limits.kernel_zero_iso_source_hom, limits.kernel_subobject_arrow_assoc]
      erw [homology'.π_desc, limits.kernel_subobject_map_arrow_assoc]
      simp only [HomologicalComplex.Hom.sqFrom_left, limits.kernel_subobject_map_arrow_assoc,
        arrow.iso_mk_hom_left]
      dsimp only [ChainComplex.single₀CompEmbedIsoSingleComponent]
      erw [iso.refl_hom, iso.refl_hom, category.id_comp, category.id_comp, category.comp_id]; rfl
      infer_instance
    · infer_instance
  · refine' limits.is_zero.is_iso _ _ _ <;> refine' exact.homology_is_zero _ _ (exact_of_zero _ _)
  · refine' limits.is_zero.is_iso _ _ _
    · refine' limits.is_zero_of_iso_of_zero _ (homology_iso _ (-[i.succ+1] : ℤ) _ (-i : ℤ) _ _).symm
      rotate_left
      · dsimp; rfl
      · dsimp; simp only [Int.negSucc_eq', sub_add_cancel]
      refine' exact.homology_is_zero _ _ _
      cases i <;> exact hP.exact _
    · refine' limits.is_zero_of_iso_of_zero _ (homology_iso _ (-[i.succ+1] : ℤ) _ (-i : ℤ) _ _).symm
      rotate_left
      · dsimp; rfl
      · dsimp; simp only [Int.negSucc_eq', sub_add_cancel]
      refine' exact.homology_is_zero _ _ (exact_of_zero _ _)

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
  dsimp [shift_equiv, unit_of_tensor_iso_unit]
  simp only [HomologicalComplex.xEqToIso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    HomologicalComplex.eqToHom_f, eq_to_hom_trans, HomologicalComplex.shift_μ_inv_app_f]

@[simp]
theorem HomologicalComplex.shiftEquiv_unitInv_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).unitInv.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [shift_equiv, unit_of_tensor_iso_unit]
  simp only [HomologicalComplex.xEqToIso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    HomologicalComplex.eqToHom_f, HomologicalComplex.shift_ε_inv_app_f, eq_to_hom_trans]

@[simp]
theorem CategoryTheory.Equivalence.symm_toAdjunction_unit {C D : Type _} [Category C] [Category D]
    (e : C ≌ D) : e.symm.toAdjunction.Unit = e.counitInv :=
  rfl

@[simp]
theorem HomologicalComplex.shiftEquiv_counit_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).counit.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [shift_equiv, unit_of_tensor_iso_unit]
  simp only [HomologicalComplex.xEqToIso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    HomologicalComplex.eqToHom_f, HomologicalComplex.shift_ε_inv_app_f, eq_to_hom_trans]

@[simp]
theorem HomologicalComplex.shiftEquiv_counitInv_app (i j : ℤ) (X : CochainComplex C ℤ) :
    HomologicalComplex.Hom.f ((shiftEquiv _ i).counitInv.app X) j = (X.xEqToIso <| by simp).hom :=
  by
  dsimp [shift_equiv, unit_of_tensor_iso_unit]
  simpa only [HomologicalComplex.xEqToIso, eq_to_hom_map, eq_to_hom_app, eq_to_iso.hom,
    add_neg_equiv_counit_iso_inv, nat_trans.comp_app, HomologicalComplex.comp_f,
    HomologicalComplex.shift_ε_hom_app_f, HomologicalComplex.eqToHom_f,
    HomologicalComplex.shift_μ_inv_app_f, eq_to_hom_trans]

variable [EnoughProjectives C]

noncomputable def ext'Iso (A : Cᵒᵖ) (B : C) (i : ℤ) (P : ChainComplex C ℕ)
    (π : P ⟶ (ChainComplex.single₀ C).obj A.unop) (hP : P.IsProjectiveResolution A.unop π) :
    ((ext' i).obj A).obj B ≅
      (((preadditiveYoneda.obj B).mapHomologicalComplex _).obj
            ((HomologicalComplex.embed ComplexShape.Embedding.natDownIntUp).obj P).op).homology'
        (-i) :=
  by
  dsimp only [ext', functor.comp_obj, functor.op_obj, functor.flip_obj_obj]
  haveI := ChainComplex.toBoundedHomotopyCategory.isKProjective P A.unop π hP
  haveI : is_quasi_iso (chain_complex.to_bounded_homotopy_category.map π) := hP.is_quasi_iso_embed
  refine'
    BoundedHomotopyCategory.extIso i (chain_complex.to_bounded_homotopy_category.obj P) _ _
        (chain_complex.to_bounded_homotopy_category.map π ≫ _) ≪≫
      (preadditive_yoneda.map_iso _).app (op (chain_complex.to_bounded_homotopy_category.obj P)) ≪≫
        BoundedHomotopyCategory.homSingleIso _ B (-i)
  ·
    exact
      ((HomotopyCategory.quotient _ _).mapIso <|
          ChainComplex.single₀CompEmbedIsoSingle.app A.unop).hom
  · infer_instance
  · exact (BoundedHomotopyCategory.shiftSingleIso 0 i).app B ≪≫ eq_to_iso (by rw [zero_sub])

theorem AddCommGroupCat.isZero_of_eq (A : AddCommGroupCat) (h : ∀ x y : A, x = y) : IsZero A :=
  by
  rw [is_zero_iff_id_eq_zero]
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
  refine' is_zero_of_iso_of_zero _ (ext'Iso _ _ i P.complex P.π P.is_projective_resolution).symm
  rcases i with (i | i)
  · exfalso; revert hi; decide
  refine' is_zero.homology_is_zero _ _ _ _
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
  refine' is_zero_of_iso_of_zero _ (Ext_iso j ⟨P⟩ _ _ _).symm
  swap; · exact f; swap; · exact H3
  refine' AddCommGroupCat.isZero_of_eq _ _
  rintro (φ ψ : P ⟶ _)
  rw [← quotient_map_out φ, ← quotient_map_out ψ]
  congr 1
  ext n
  by_cases hn : i ≤ n
  · apply (H2 n hn).eq_of_src
  · apply is_zero.eq_of_tgt
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
  use(adj.hom_equiv _ _).symm (projective.factor_thru (adj.hom_equiv _ _ f) (G.map e))
  rw [← adj.hom_equiv_naturality_right_symm, projective.factor_thru_comp, Equiv.symm_apply_apply]

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
  haveI : is_left_adjoint F := ⟨_, adj⟩
  constructor
  intro X
  refine' ⟨⟨_, preserves_projectives adj _, (adj.hom_equiv _ _).symm (projective.π (G.obj X)), _⟩⟩
  dsimp
  rw [adjunction.hom_equiv_counit]
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
  refine' is_zero_of_iso_of_zero _ (this _ _ (twoStepResolutionAbProjective A)).symm
  rcases i with ((_ | _ | i) | i)
  · exfalso; revert hi; decide
  · exfalso; revert hi; decide
  swap
  · exfalso; revert hi; decide
  refine' is_zero.homology_is_zero _ _ _ _
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
    · ext k; dsimp [zmod_resolution_pi_f, zmod_resolution]
      simp only [zero_apply, Fin.val_zero, comp_apply, Int.coe_castAddHom]
      simp only [ChainComplex.mk'_d_1_0, AddMonoidHom.coe_smul, Pi.smul_apply, id_apply, nsmul_one,
        Int.ofNat_bit0, Int.ofNat_succ, Int.ofNat_zero, zero_add, Int.cast_bit0, Int.cast_one,
        map_nsmul]
      simp only [RingHom.coe_addMonoidHom, eq_intCast, Int.cast_one, nsmul_one, ZMod.nat_cast_self]
    · exact comp_zero.trans comp_zero.symm

attribute [-instance] limits.has_smallest_colimits_of_has_colimits

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
  · dsimp [zmod_resolution_pi, zmod_resolution_pi_f, zmod_resolution]
    rw [ChainComplex.mk'_d_1_0]
    exact AddCommGroupCat.exact_zMod_nsmul_cast n
  · intro i
    dsimp [zmod_resolution, ChainComplex.mk', ChainComplex.mk, ChainComplex.of]
    rw [if_pos rfl, if_pos rfl, category.id_comp, category.id_comp]
    rcases i with (_ | _ | _)
    · show exact 0 (n • 𝟙 (of ℤ))
      rw [(abelian.tfae_mono 0 (n • 𝟙 (of ℤ))).out 2 0, AddCommGroupCat.mono_iff_injective]
      rintro (x : ℤ) (y : ℤ) (e : n • x = n • y)
      norm_num at e 
      exact e.resolve_right hn
    · show exact 0 0; apply exact_of_zero
    · show exact 0 0; apply exact_of_zero
  · dsimp [zmod_resolution_pi, zmod_resolution_pi_f]
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

