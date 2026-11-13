import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.GroupTheory.FreeAbelianGroupFinsupp
import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Category.GroupCat.Biproducts
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.LinearAlgebra.FreeModule.PID
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi
import Mathlib.Algebra.Group.ULift

#align_import for_mathlib.AddCommGroup

open CategoryTheory

universe v u

namespace AddCommGroupCat

noncomputable section

@[simps]
def free' : Type u ⥤ AddCommGroupCat.{u}
    where
  obj X := AddCommGroupCat.of <| X →₀ ℤ
  map X Y f := Finsupp.mapDomain.addMonoidHom f
  map_id' := by intro X; ext; dsimp; simp
  map_comp' := by intro X Y Z f g; ext; dsimp; simp

@[simps]
def ofIso {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) : of A ≅ of B
    where
  Hom := e.toAddMonoidHom
  inv := e.symm.toAddMonoidHom
  hom_inv_id' := by ext; dsimp; simp
  inv_hom_id' := by ext; dsimp; simp

@[simps]
def freeIsoFree' : free.{u} ≅ free'.{u} :=
  CategoryTheory.NatIso.ofComponents (fun X => ofIso (FreeAbelianGroup.equivFinsupp X))
    (by intro X Y f; ext; dsimp; simp)

def adj' : free'.{u} ⊣ forget AddCommGroupCat.{u} :=
  AddCommGroupCat.adj.ofNatIsoLeft <| freeIsoFree'.{u}

end AddCommGroupCat

def Types.pt {α : Type u} (a : α) : ⊤_ _ ⟶ α := fun x => a

def Types.punitIso : (PUnit : Type u) ≅ ⊤_ _
    where
  Hom := Limits.terminal.from _
  inv := Types.pt PUnit.unit

namespace AddCommGroupCat

def tunit : AddCommGroupCat.{u} :=
  AddCommGroupCat.free'.obj (⊤_ _)

def tunit.lift {A : AddCommGroupCat.{u}} (e : ⊤_ _ ⟶ (forget _).obj A) : tunit ⟶ A :=
  (AddCommGroupCat.adj'.homEquiv _ _).symm e

-- Do we really not have this?!
def Finsupp.punitAddEquiv (M : Type _) [AddMonoid M] : ((PUnit : Type u) →₀ M) ≃+ M
    where
  toFun f := f PUnit.unit
  invFun m := Finsupp.single PUnit.unit m
  left_inv x := by ext; dsimp; simp
  right_inv x := by dsimp; simp
  map_add' f g := by simp

-- Do we really not have this?!
def addEquivOfIso (A B : AddCommGroupCat.{u}) (e : A ≅ B) : A ≃+ B
    where
  toFun := e.Hom
  invFun := e.inv
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := e.Hom.map_add _ _

def tunitAddEquiv : tunit.{u} ≃+ ℤ :=
  AddEquiv.trans (addEquivOfIso _ _ <| AddCommGroupCat.free'.mapIso Types.punitIso.symm)
    (Finsupp.punitAddEquiv ℤ)

def tunit.gen : tunit.{u} :=
  AddCommGroupCat.adj'.Unit.app _ <|
    (Limits.terminal.from (PUnit : Type u) : PUnit → ⊤_ Type u) PUnit.unit

open scoped Classical

def coproductCoconeOfBasis {ι : Type v} {A : AddCommGroupCat.{u}} (𝓑 : Basis ι ℤ A) :
    Limits.Cofan fun i : ι => tunit.{u} :=
  Limits.Cofan.mk A fun i =>
    AddCommGroupCat.ofHom ((zmultiplesAddHom A.α (𝓑 i)).comp tunitAddEquiv.toAddMonoidHom)

def coproductCoconeOfBasisIsColimit {ι : Type v} {A : AddCommGroupCat.{u}} (𝓑 : Basis ι ℤ A) :
    Limits.IsColimit (coproductCoconeOfBasis 𝓑)
    where
  desc s :=
    AddCommGroupCat.ofHom
      ((Finsupp.total ι s.pt.α ℤ fun i => s.ι.app ⟨i⟩ (tunitAddEquiv.symm 1)).comp
          𝓑.repr.toLinearMap).toAddMonoidHom
  fac := by
    rintro s ⟨j⟩
    apply Finsupp.addHom_ext
    intro x y
    dsimp [coproduct_cocone_of_basis]
    simp [← map_zsmul]
  uniq := by
    intro s m e
    apply (addMonoidHomLequivInt ℤ).Injective
    swap; · infer_instance
    apply 𝓑.ext
    intro i
    convert concrete_category.congr_hom (e ⟨i⟩) (tunit_add_equiv.symm 1) using 1
    · dsimp [coproduct_cocone_of_basis]; simp
    · dsimp; simp

-- set_option pp.universes true
-- Of course this is true without the fintype assumption...
def isoOfBasis {ι : Type v} [Limits.HasCoproduct fun i : ι => tunit.{u}] {A : AddCommGroupCat.{u}}
    (𝓑 : Basis ι ℤ A) : (∐ fun i : ι => tunit.{u}) ≅ A :=
  Limits.IsColimit.coconePointUniqueUpToIso (Limits.coproductIsCoproduct _)
    (coproductCoconeOfBasisIsColimit 𝓑)

-- begin
--   -- This is very messy...
--   let e : (∐ (λ i : ι, tunit.{u})) ≅ (⨁ (λ i, tunit.{u})) :=
--     (limits.colimit.is_colimit _).cocone_point_unique_up_to_iso
--       (limits.biproduct.is_bilimit _).is_colimit,
--   refine e ≪≫ _,
--   refine biproduct_iso_pi _ ≪≫ _,
--   let e : A ≃+ ulift.{u} (ι →₀ ℤ) := 𝓑.repr.to_add_equiv.trans add_equiv.ulift.symm,
--   refine AddCommGroup.of_iso _ ≪≫ (AddCommGroup.of_iso e).symm ≪≫
--     ⟨add_monoid_hom.id _, add_monoid_hom.id _, by { ext, refl }, by { ext, refl }⟩,
--   refine add_equiv.trans _ add_equiv.ulift.symm,
--   let q : tunit.{u} ≃+ ℤ := tunit_add_equiv,
--   let e : (ι →₀ ℤ) ≃+ (ι → ℤ),
--   { fconstructor,
--     exact finsupp.equiv_fun_on_fintype,
--     exact finsupp.equiv_fun_on_fintype.symm,
--     exact finsupp.equiv_fun_on_fintype.left_inverse_symm,
--     exact finsupp.equiv_fun_on_fintype.right_inverse_symm,
--     intros x y, refl },
--   refine add_equiv.trans _ e.symm,
--   fconstructor,
--   { intros f i, exact q (f i) },
--   { intros f i, exact q.symm (f i) },
--   { intros f, ext, dsimp, simp },
--   { intros f, ext, dsimp, simp },
--   { intros f g, ext i, simp, },
-- end
def IndexCat (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] : Type u :=
  { H : AddSubgroup A // H.FG }
deriving PartialOrder

-- Is this the condition we want?
instance nonempty_indexCat (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] :
    Nonempty A.IndexCat :=
  ⟨⟨⊥, ∅, by simp⟩⟩

instance semilatticeSupIndexCat (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] :
    SemilatticeSup A.IndexCat :=
  {
    (inferInstance :
      PartialOrder
        _) with
    sup := fun I J =>
      ⟨I.1 ⊔ J.1, by
        obtain ⟨S, hS⟩ := I.2
        obtain ⟨T, hT⟩ := J.2
        rw [← hS, ← hT]
        use S ∪ T
        simp only [Finset.coe_union, AddSubgroup.closure_union]⟩
    le_sup_left := fun I J => @le_sup_left (AddSubgroup A) _ _ _
    le_sup_right := fun I J => @le_sup_right (AddSubgroup A) _ _ _
    sup_le := fun I J K h1 h2 => @sup_le (AddSubgroup A) _ _ _ _ h1 h2 }

def diagram (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] : A.IndexCat ⥤ AddCommGroupCat.{u}
    where
  obj I := AddCommGroupCat.of I.1
  map I J h := AddSubgroup.inclusion h.le

def cocone (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] : Limits.Cocone A.diagram
    where
  pt := A
  ι := { app := fun I => I.1.Subtype }

def isColimitCocone (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] : Limits.IsColimit A.Cocone
    where
  desc S :=
    { toFun := fun a =>
        S.ι.app ⟨AddSubgroup.closure {a}, {a}, by simp⟩ ⟨a, AddSubgroup.subset_closure rfl⟩
      map_zero' := AddMonoidHom.map_zero _
      map_add' := fun x y =>
        by
        let I : A.index_cat := ⟨AddSubgroup.closure {x}, {x}, by simp⟩
        let J : A.index_cat := ⟨AddSubgroup.closure {y}, {y}, by simp⟩
        let K : A.index_cat := ⟨AddSubgroup.closure {x + y}, {x + y}, by simp⟩
        let IJ : A.index_cat := ⟨AddSubgroup.closure {x, y}, {x, y}, by simp⟩
        let iI : I ⟶ IJ := hom_of_le (AddSubgroup.closure_mono <| by simp)
        let iJ : J ⟶ IJ := hom_of_le (AddSubgroup.closure_mono <| by simp)
        let iK : K ⟶ IJ := hom_of_le ((AddSubgroup.closure_le _).2 _)
        swap
        · rintro a (rfl : a = _); change x + y ∈ IJ.1; apply IJ.1.add_mem
          · apply AddSubgroup.subset_closure; simp
          · apply AddSubgroup.subset_closure; simp
        rw [← S.w iI, ← S.w iJ, ← S.w iK, comp_apply, comp_apply, comp_apply, ←
          AddMonoidHom.map_add]
        rfl }
  fac := by
    rintro S J; ext ⟨x, hx⟩
    let I : A.index_cat := ⟨AddSubgroup.closure {x}, {x}, by simp⟩
    let e : I ⟶ J := hom_of_le ((AddSubgroup.closure_le _).2 _)
    · rw [comp_apply]; dsimp [cocone]; rw [← S.w e]; rfl
    rintro x (rfl : x = _); exact hx
  uniq := by
    intro S m hm; ext x; dsimp [cocone] at x ⊢
    let I : A.index_cat := ⟨AddSubgroup.closure {x}, {x}, by simp⟩
    specialize hm I
    let y : I.1 := ⟨x, AddSubgroup.subset_closure rfl⟩
    apply_fun fun e => e y at hm ; exact hm

def colimitComparison (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] :
    Limits.colimit A.diagram ≅ A :=
  (Limits.colimit.isColimit A.diagram).coconePointUniqueUpToIso A.isColimitCocone

theorem exists_basis_of_index (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] (I : A.IndexCat) :
    ∃ (ι : Type v) (_ : Fintype ι) (𝓑 : Basis ι ℤ (AddCommGroupCat.of I.1)), True :=
  by
  obtain ⟨S, hS⟩ := I.2
  let e : S → I.1 := fun s => ⟨s, _⟩
  swap; · rw [← hS]; apply AddSubgroup.subset_closure; exact s.2
  have : NoZeroSMulDivisors ℤ I.1 := by
    constructor; rintro c ⟨x, hx⟩ h; apply_fun fun e => e.val at h 
    dsimp at h 
    cases NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h
    left; assumption
    right; ext; assumption
  obtain ⟨n, B⟩ := @Module.free_of_finite_type_torsion_free S ℤ _ _ _ I.1 _ _ _ e _ _
  · use ULift (Fin n), inferInstance
    refine' ⟨_, trivial⟩
    apply B.reindex
    exact equiv.ulift.symm
  · apply le_antisymm; · intro x hx; trivial
    rintro ⟨x, hx⟩ -
    let J := (Submodule.span ℤ (Set.range e)).toAddSubgroup
    change _ ∈ J
    have hJ : J = (J.map I.1.Subtype).comap I.1.Subtype :=
      by
      -- is this not a lemma?!
      apply le_antisymm
      · exact AddSubgroup.le_comap_map I.val.subtype J
      · intro t ht
        simpa using ht
    rw [hJ, AddSubgroup.mem_comap]; clear hJ
    dsimp [J]
    convert hx
    rw [← hS, Submodule.span_int_eq_addSubgroup_closure, AddMonoidHom.map_closure]; congr 1
    ext t
    constructor
    · rintro ⟨t, ⟨t, rfl⟩, rfl⟩; exact t.2
    · intro ht; refine' ⟨⟨t, _⟩, ⟨⟨t, ht⟩, rfl⟩, rfl⟩

theorem exists_sigma_iso_of_index (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A]
    (I : A.IndexCat) :
    ∃ (ι : Type v) (_ : Fintype ι) (e : (∐ fun i : ι => tunit.{u}) ≅ AddCommGroupCat.of I.1),
      True :=
  by
  obtain ⟨ι, hι, 𝓑, -⟩ := exists_basis_of_index.{v} A I
  skip
  exact ⟨ι, hι, iso_of_basis 𝓑, trivial⟩

instance (priority := 100) {C J : Type _} [Fintype J] [Category C] [Limits.HasZeroMorphisms C]
    [Limits.HasFiniteBiproducts C] : Limits.HasBiproductsOfShape J C :=
  ⟨fun F =>
    by
    have : F = (F ∘ (Fintype.equivFin J).invFun) ∘ (Fintype.equivFin J).toFun := by ext; dsimp;
      rw [Equiv.symm_apply_apply]
    rw [this]
    exact
      ⟨⟨⟨_,
            (limits.bicone.whisker_is_bilimit_iff _ (Fintype.equivFin J)).symm
              (limits.biproduct.is_bilimit <| F ∘ (Fintype.equivFin J).invFun)⟩⟩⟩⟩

theorem exists_biprod_iso_of_index (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A]
    (I : A.IndexCat) :
    ∃ (ι : Type v) (_ : Fintype ι) (e : (⨁ fun i : ι => tunit.{u}) ≅ AddCommGroupCat.of I.1),
      True :=
  by
  obtain ⟨ι, hι, e, -⟩ := exists_sigma_iso_of_index A I
  skip; use ι, hι
  use(limits.biproduct.is_bilimit _).IsColimit.coconePointUniqueUpToIso
        (limits.colimit.is_colimit _) ≪≫
      e

universe u'

theorem isIso_of_preserves {𝓐 : Type u'} [Category.{u} 𝓐] [Preadditive 𝓐]
    (F G : AddCommGroupCat ⥤ 𝓐) [F.Additive] [G.Additive] [Limits.PreservesFilteredColimits F]
    [Limits.PreservesFilteredColimits G] (η : F ⟶ G) [hη : IsIso (η.app tunit)]
    (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] : IsIso (η.app A) :=
  by
  let T := (limits.cocones.precompose (whisker_left A.diagram η)).obj (G.map_cocone A.cocone)
  let S := F.map_cocone A.cocone
  let hS : limits.is_colimit S := limits.is_colimit_of_preserves F A.is_colimit_cocone
  have : η.app A = hS.desc T := by
    apply hS.hom_ext; intro j; rw [hS.fac]
    dsimp; apply η.naturality
  rw [this]; clear this
  suffices ∀ I : A.index_cat, is_iso (η.app (A.diagram.obj I))
    by
    skip
    have : is_iso (whisker_left A.diagram η) :=
      by
      apply (config := { instances := false }) nat_iso.is_iso_of_is_iso_app
      intro I; exact this I
    let hT : limits.is_colimit T :=
      (limits.is_colimit.precompose_hom_equiv (as_iso (whisker_left A.diagram η))
            (G.map_cocone A.cocone)).symm
        (limits.is_colimit_of_preserves G A.is_colimit_cocone)
    use hT.desc S
    constructor
    · apply hS.hom_ext
      intro j
      erw [hS.fac_assoc, hT.fac, category.comp_id]
    · apply hT.hom_ext
      intro j
      erw [hT.fac_assoc, hS.fac, category.comp_id]
  --^ general colimit nonsense..., but I can't find applicable lemmas :-(
  intro I
  obtain ⟨ι : Type, hι, e, -⟩ := A.exists_biprod_iso_of_index I
  -- now use the fact that the functors are additive and that there exists some iso with a biproduct
  skip
  let eF : F.obj (⨁ fun i : ι => tunit.{u}) ≅ ⨁ fun i : ι => F.obj tunit :=
    (limits.is_bilimit_of_preserves F
            (limits.biproduct.is_bilimit fun i : ι => tunit.{u})).IsColimit.coconePointUniqueUpToIso
      (limits.biproduct.is_bilimit fun i : ι => F.obj tunit).IsColimit
  let eG : G.obj (⨁ fun i : ι => tunit.{u}) ≅ ⨁ fun i : ι => G.obj tunit :=
    (limits.is_bilimit_of_preserves G
            (limits.biproduct.is_bilimit fun i : ι => tunit.{u})).IsColimit.coconePointUniqueUpToIso
      (limits.biproduct.is_bilimit fun i : ι => G.obj tunit).IsColimit
  have :
    η.app (A.diagram.obj I) =
      F.map e.inv ≫ eF.hom ≫ (limits.biproduct.map fun i => η.app _) ≫ eG.inv ≫ G.map e.hom :=
    by
    rw [← functor.map_iso_inv, iso.eq_inv_comp, ← iso.inv_comp_eq]
    apply limits.biproduct.hom_ext'; intro i
    simp only [functor.map_iso_hom, nat_trans.naturality, limits.biproduct.ι_map_assoc,
      category.assoc]
    erw [limits.biproduct.ι_desc_assoc, limits.biproduct.ι_desc_assoc]
    dsimp; rw [η.naturality_assoc]
  rw [this]
  apply (config := { instances := false }) is_iso.comp_is_iso
  infer_instance
  apply (config := { instances := false }) is_iso.comp_is_iso
  infer_instance
  apply (config := { instances := false }) is_iso.comp_is_iso
  swap
  infer_instance
  use limits.biproduct.desc fun i => inv (η.app _) ≫ limits.biproduct.ι _ i
  constructor
  · ext; simp
  · ext; simp

def IsTensorUnit (A : AddCommGroupCat.{u}) : Prop :=
  ∃ a : A, ∀ B : AddCommGroupCat.{u}, Function.Bijective fun f : A ⟶ B => (f : A → B) a

def IsTensorUnit.gen {A : AddCommGroupCat.{u}} (h : A.IsTensorUnit) : A :=
  h.some

def IsTensorUnit.asHom {A B : AddCommGroupCat.{u}} (h : A.IsTensorUnit) (b : B) : A ⟶ B :=
  ((h.choose_spec B).2 b).some

@[simp]
theorem IsTensorUnit.eval_asHom {A B : AddCommGroupCat.{u}} (h : A.IsTensorUnit) (b : B) :
    h.asHom b h.gen = b :=
  ((h.choose_spec B).2 b).choose_spec

theorem IsTensorUnit.ext {A B : AddCommGroupCat.{u}} (h : A.IsTensorUnit) (f g : A ⟶ B)
    (hh : f h.gen = g h.gen) : f = g :=
  (h.choose_spec B).1 hh

def IsTensorUnit.iso {A B : AddCommGroupCat.{u}} (hA : A.IsTensorUnit) (hB : B.IsTensorUnit) : A ≅ B
    where
  Hom := hA.asHom hB.gen
  inv := hB.asHom hA.gen
  hom_inv_id' := by
    apply hA.ext
    simp
  inv_hom_id' := by
    apply hB.ext
    simp

theorem isTensorUnit_tunit : tunit.{u}.IsTensorUnit :=
  by
  use tunit.gen
  intro B
  constructor
  · intro f g h
    dsimp [tunit.gen] at h 
    change (adj'.unit.app _ ≫ (forget _).map f) _ = (adj'.unit.app _ ≫ (forget _).map g) _ at h 
    apply_fun adj'.hom_equiv _ _
    simp only [adjunction.hom_equiv_unit]
    ext t
    let e := limits.terminal.from (PUnit : Type u)
    suffices t = e PUnit.unit by rw [this]; exact h
    apply_fun types.punit_iso.inv
    · simp
    intro i j h; apply_fun types.punit_iso.hom at h 
    simpa using h
  · intro t
    use tunit.lift (Types.pt t)
    dsimp only [tunit.lift, Types.pt, tunit.gen]
    simp only [adjunction.hom_equiv_counit]
    change
      (adj'.unit.app _ ≫ (forget _).map ((free'.map fun x : ⊤_ Type u => t) ≫ adj'.counit.app B))
          _ =
        _
    simp only [functor.map_comp, adjunction.unit_naturality_assoc]
    erw [adj'.right_triangle_components]; rfl

theorem isIso_of_preserves_of_isTensorUnit {𝓐 : Type u'} [Category.{u} 𝓐] [Preadditive 𝓐]
    (F G : AddCommGroupCat ⥤ 𝓐) [F.Additive] [G.Additive] [Limits.PreservesFilteredColimits F]
    [Limits.PreservesFilteredColimits G] (η : F ⟶ G) (U : AddCommGroupCat) (hU : U.IsTensorUnit)
    [hη : IsIso (η.app U)] (A : AddCommGroupCat.{u}) [NoZeroSMulDivisors ℤ A] : IsIso (η.app A) :=
  by
  suffices is_iso (η.app tunit) by skip; apply is_iso_of_preserves
  let e : tunit ≅ U := is_tensor_unit_tunit.iso hU
  suffices η.app tunit = F.map e.hom ≫ η.app U ≫ G.map e.inv by rw [this]; apply is_iso.comp_is_iso
  rw [← η.naturality, ← F.map_comp_assoc, e.hom_inv_id, F.map_id, category.id_comp]

end AddCommGroupCat

