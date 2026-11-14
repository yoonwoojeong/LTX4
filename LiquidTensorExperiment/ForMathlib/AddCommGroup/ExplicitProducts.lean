import Mathlib.Algebra.Category.GroupCat.Biproducts
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi

#align_import for_mathlib.AddCommGroup.explicit_products

open CategoryTheory

open CategoryTheory.Limits

def DFinsupp.addEquivPiOnFintype {α : Type _} [Fintype α] (X : α → Type _)
    [∀ i, AddCommGroup (X i)] : (Π₀ i, X i) ≃+ ∀ i, X i :=
  { DFinsupp.equivFunOnFintype with map_add' := fun x y => by ext; simp }

namespace AddCommGroupCat

universe v u

def piπ {α : Type v} (X : α → AddCommGroupCat.{max v u}) (i) :
    AddCommGroupCat.of (∀ i, X i) ⟶ X i :=
  Pi.evalAddMonoidHom _ _

def piFan {α : Type v} (X : α → AddCommGroupCat.{max v u}) : Fan X :=
  Fan.mk (AddCommGroupCat.of <| ∀ i, X i) fun b => piπ _ _

def piLift {α : Type v} {Y : AddCommGroupCat.{max v u}} (X : α → AddCommGroupCat.{max v u})
    (f : ∀ a, Y ⟶ X a) : Y ⟶ AddCommGroupCat.of (∀ i, X i)
    where
  toFun y i := f _ y
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[reassoc (attr := simp)]
theorem piLift_π {α : Type v} {Y : AddCommGroupCat.{max v u}} (X : α → AddCommGroupCat.{max v u})
    (f : ∀ a, Y ⟶ X a) (i) : piLift X f ≫ piπ _ i = f _ := by ext; rfl

theorem pi_hom_ext {α : Type v} {Y : AddCommGroupCat.{max v u}} (X : α → AddCommGroupCat.{max v u})
    (f g : Y ⟶ AddCommGroupCat.of (∀ i, X i)) (h : ∀ i, f ≫ piπ _ i = g ≫ piπ _ i) : f = g := by
  ext y a; specialize h a; apply_fun fun e => e y at h ; exact h

def isLimitPiFan {α : Type v} (X : α → AddCommGroupCat.{max v u}) : IsLimit (piFan X)
    where
  lift S := piLift _ fun a => S.π.app ⟨_⟩
  fac := by
    rintro S ⟨j⟩
    apply pi_lift_π
  uniq := by
    intro S m hm
    apply pi_hom_ext
    intro i
    erw [hm ⟨i⟩, pi_lift_π]

noncomputable def homProductComparison {α : Type v} (A : AddCommGroupCat.{max v u})
    (X : α → AddCommGroupCat.{max v u}) :
    AddCommGroupCat.of (A ⟶ ∏ X) ⟶ ∏ fun i => AddCommGroupCat.of (A ⟶ X i) :=
  Limits.Pi.lift fun a => (preadditiveYoneda.flip.obj (Opposite.op A)).map (Limits.Pi.π _ _)

instance isIso_homProductComparison {α : Type v} (A : AddCommGroupCat.{max v u})
    (X : α → AddCommGroupCat.{max v u}) : IsIso (homProductComparison A X) :=
  by
  --haveI : balanced Ab.{max v u} := AddcommGroup.abelian
  let t :
    (∏ fun i : α => AddCommGroupCat.of (A ⟶ X i)) ≅
      AddCommGroupCat.of (∀ i, AddCommGroupCat.of (A ⟶ X i)) :=
    (Limits.limit.isLimit _).conePointUniqueUpToIso (AddCommGroupCat.isLimitPiFan fun i => of (A ⟶ X i))
  suffices is_iso (A.hom_product_comparison X ≫ t.hom) by apply IsIso.of_isIso_comp_right _ t.hom;
    exact this
  have ht :
    A.hom_product_comparison X ≫ t.hom =
      (AddCommGroupCat.isLimitPiFan fun i => of (A ⟶ X i)).lift
        ⟨_,
          Discrete.natTrans fun i =>
            (preadditive_yoneda.flip.obj (Opposite.op A)).map (limits.pi.π _ _)⟩ :=
    by
    apply (AddCommGroupCat.isLimitPiFan _).hom_ext; intro j
    simp [AddCommGroupCat.homProductComparison]
  rw [ht]; clear ht
  apply (config := { instances := false }) is_iso_of_mono_of_epi
  infer_instance
  · rw [mono_iff_injective]
    intro f g h
    ext1 ⟨j⟩
    apply_fun fun e => e j at h 
    exact h
  · rw [epi_iff_surjective]
    intro f
    use Limits.Pi.lift fun i => f i
    dsimp [AddCommGroupCat.isLimitPiFan, pi_lift]
    simp [pi_lift_π]

def directSumπ {α : Type v} (X : α → AddCommGroupCat.{max v u}) (i) :
    AddCommGroupCat.of (DirectSum α fun i => X i) ⟶ X i
    where
  toFun f :=
    let e : Π₀ i : α, X i := f
    e i
  map_zero' := by simp
  map_add' x y := by dsimp; simp

def directSumFan {α : Type v} (X : α → AddCommGroupCat.{max v u}) : Fan X :=
  Fan.mk (AddCommGroupCat.of (DirectSum α fun i => X i)) fun b => directSumπ _ _

open scoped Classical

def directSumLift {α : Type v} [Fintype α] {Y : AddCommGroupCat.{max v u}}
    (X : α → AddCommGroupCat.{max v u}) (f : ∀ a, Y ⟶ X a) :
    Y ⟶ AddCommGroupCat.of (DirectSum α fun i => X i)
    where
  toFun y := (DFinsupp.addEquivPiOnFintype _).symm fun i => f i y
  map_zero' := by
    simp_rw [map_zero]
    change (DFinsupp.addEquivPiOnFintype fun i : α => ↥(X i)).symm 0 = _
    simp
  map_add' := by
    intro x y
    simp_rw [map_add]
    change
      (DFinsupp.addEquivPiOnFintype fun i : α => ↥(X i)).symm
          ((fun i : α => (f i) x) + fun i : α => (f i) y) =
        _
    simp

@[reassoc (attr := simp)]
theorem directSumLift_π {α : Type v} [Fintype α] {Y : AddCommGroupCat.{max v u}}
    (X : α → AddCommGroupCat.{max v u}) (f : ∀ a, Y ⟶ X a) (i) :
    directSumLift X f ≫ directSumπ _ i = f i := by ext; rfl

theorem directSum_hom_ext {α : Type v} [Fintype α] {Y : AddCommGroupCat.{max v u}}
    (X : α → AddCommGroupCat.{max v u}) (f g : Y ⟶ AddCommGroupCat.of (DirectSum α fun i => X i))
    (h : ∀ i, f ≫ directSumπ _ i = g ≫ directSumπ _ i) : f = g :=
  by
  ext
  specialize h i
  apply_fun fun e => e x at h ; exact h

def isLimitDirectSumFan {α : Type v} [Fintype α] (X : α → AddCommGroupCat.{max v u}) :
    IsLimit (directSumFan X)
    where
  lift S := directSumLift _ fun a => S.π.app ⟨a⟩
  -- S.π.app,
  fac := by
    rintro S ⟨j⟩
    apply direct_sum_lift_π
  uniq := by
    intro S m hm
    apply AddCommGroupCat.directSum_hom_ext
    intro i
    specialize hm ⟨i⟩
    erw [hm, direct_sum_lift_π]

noncomputable section

def toDirectSum {α : Type v} (X : α → AddCommGroupCat.{max v u}) (i : α) :
    X i ⟶ AddCommGroupCat.of (DirectSum α fun i => X i) :=
  DirectSum.of (fun i => X i) i

def directSumPunitIso (A : AddCommGroupCat.{max v u}) :
    AddCommGroupCat.of (DirectSum _ fun i : PUnit.{v + 1} => A) ≅ A
    where
  hom := directSumπ _ PUnit.unit
  inv := toDirectSum (fun i => A) PUnit.unit
  hom_inv_id := by
    ext ⟨⟩ ⟨⟩
    ext t ⟨⟩
    -- WAT?
    dsimp [direct_sum_π, to_direct_sum]
    simp
  inv_hom_id := by
    ext a
    dsimp [direct_sum_π, to_direct_sum]
    simp

def directSumι {α : Type v} (X : α → AddCommGroupCat.{max v u}) (i : α) :
    X i ⟶ AddCommGroupCat.of (DirectSum α fun i => X i) :=
  DirectSum.of _ i

def directSumDesc {α : Type v} {Y : AddCommGroupCat.{max v u}} (X : α → AddCommGroupCat.{max v u})
    (f : ∀ i, X i ⟶ Y) : AddCommGroupCat.of (DirectSum α fun i => X i) ⟶ Y :=
  DirectSum.toAddMonoid f

@[reassoc (attr := simp)]
theorem directSumι_desc {α : Type v} {Y : AddCommGroupCat.{max v u}}
    (X : α → AddCommGroupCat.{max v u}) (f : ∀ i, X i ⟶ Y) (i) :
    directSumι X i ≫ directSumDesc X f = f _ := by ext; dsimp [direct_sum_ι, AddCommGroupCat.directSumDesc]; simp

theorem directSum_hom_ext' {α : Type v} {Y : AddCommGroupCat.{max v u}}
    (X : α → AddCommGroupCat.{max v u}) (f g : AddCommGroupCat.of (DirectSum α fun i => X i) ⟶ Y)
    (h : ∀ i, directSumι X i ≫ f = directSumι X i ≫ g) : f = g :=
  by
  have hf : f = AddCommGroupCat.directSumDesc X fun i => direct_sum_ι X i ≫ f := by ext t;
    apply DirectSum.toAddMonoid.unique
  have hg : g = AddCommGroupCat.directSumDesc X fun i => direct_sum_ι X i ≫ g := by ext t;
    apply DirectSum.toAddMonoid.unique
  rw [hf, hg]
  congr 1; ext i; rw [h]

def directSumCofan {α : Type v} (X : α → AddCommGroupCat.{max v u}) : Cofan X :=
  Cofan.mk _ (directSumι _)

def isColimitDirectSumCofan {α : Type v} (X : α → AddCommGroupCat.{max v u}) :
    IsColimit (directSumCofan X)
    where
  desc S := directSumDesc X fun a => S.ι.app ⟨a⟩
  -- S.ι.app,
  fac := by
    rintro X ⟨j⟩
    apply direct_sum_ι_desc
  uniq := by
    intro S m hm
    apply AddCommGroupCat.directSum_hom_ext'
    intro i
    specialize hm ⟨i⟩
    erw [hm]; rw [direct_sum_ι_desc]

theorem directSumι_π {α : Type v} (X : α → AddCommGroupCat.{max v u}) (i : α) :
    directSumι.{v, u} X i ≫ directSumπ.{v, u} X i = 𝟙 _ :=
  by
  ext
  dsimp [direct_sum_ι, direct_sum_π, DirectSum.of]
  simp only [comp_apply, DFinsupp.singleAddHom_apply, AddMonoidHom.coe_mk, DFinsupp.single_apply]
  split_ifs; rfl; rfl

theorem directSumι_π_of_ne {α : Type v} (X : α → AddCommGroupCat.{max v u}) (i j : α) (h : i ≠ j) :
    directSumι.{v, u} X i ≫ directSumπ.{v, u} X j = 0 :=
  by
  ext
  dsimp [direct_sum_ι, direct_sum_π, DirectSum.of]
  simp only [comp_apply, DFinsupp.singleAddHom_apply, AddMonoidHom.coe_mk, DFinsupp.single_apply]
  split_ifs; contradiction; rfl

-- `bicone` is not sufficiently universe polymorphic.
def directSumBicone {α : Type u} [Fintype α] (X : α → AddCommGroupCat.{u}) : Bicone X
    where
  pt := AddCommGroupCat.of (DirectSum α fun i => X i)
  π := directSumπ.{u, u} _
  ι := directSumι.{u, u} _
  ι_π i j := by
    ext t
    dsimp [direct_sum_ι, direct_sum_π, DirectSum.of]
    simp only [comp_apply, DFinsupp.singleAddHom_apply, AddMonoidHom.coe_mk, DFinsupp.single_apply]
    split_ifs; subst h; rfl; rfl

def isBilimitDirectSumBicone {α : Type u} [Fintype α] (X : α → AddCommGroupCat.{u}) :
    Bicone.IsBilimit (directSumBicone X)
    where
  IsLimit := isLimitDirectSumFan.{u, u} X
  IsColimit := isColimitDirectSumCofan.{u, u} X

end AddCommGroupCat

