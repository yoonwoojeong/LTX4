import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.RingTheory.Int.Basic
import LiquidTensorExperiment.PolyhedralLattice.Finsupp
import LiquidTensorExperiment.PolyhedralLattice.Category
import LiquidTensorExperiment.PolyhedralLattice.Quotient

#align_import polyhedral_lattice.cech

/-!
# The Čech conerve attached to `Λ → Λ'`

Let `f : Λ → Λ'` be a morphism of polyhedral lattices.
(We probably need to assume that the cokernel is torsion-free...)

In this file we construct the Čech conerve attached to `f`.

Concretely, but in pseudo-code:
it consists of the objects `Λ'^(m)` defined as `(Λ')^m/L`,
where `L` is the sublattice `Λ ⊗ {x : ℤ^m | ∑ x = 0}`.
-/


noncomputable section

open scoped BigOperators

namespace PolyhedralLattice

variable {Λ Λ' : Type _} [PolyhedralLattice Λ] [PolyhedralLattice Λ']

variable (f : PolyhedralLatticeHom Λ Λ')

namespace Conerve

section Objects

/-!
## The objects
-/


variable (m : ℕ)

def l : AddSubgroup (Fin m →₀ Λ')
    where
  carrier := {l' | ∑ i, l' i = 0 ∧ ∀ i, ∃ l, f l = l' i}
  zero_mem' := ⟨Finset.sum_const_zero, fun i => ⟨0, f.map_zero⟩⟩
  add_mem' := by
    rintro l'₁ l'₂ ⟨hl'₁, Hl'₁⟩ ⟨hl'₂, Hl'₂⟩
    refine' ⟨_, _⟩
    · simp only [Finsupp.add_apply, Finset.sum_add_distrib, hl'₁, hl'₂, add_zero]
    · intro i
      obtain ⟨l₁, hl₁⟩ := Hl'₁ i
      obtain ⟨l₂, hl₂⟩ := Hl'₂ i
      refine' ⟨l₁ + l₂, _⟩
      rw [f.map_add, hl₁, hl₂, Finsupp.add_apply]
  neg_mem' := by
    rintro l' ⟨hl', Hl'⟩
    refine' ⟨_, _⟩
    · simp only [Finsupp.neg_apply, Finset.sum_neg_distrib, hl', neg_zero]
    · intro i
      obtain ⟨l, hl⟩ := Hl' i
      refine' ⟨-l, _⟩
      rw [f.map_neg, hl, Finsupp.neg_apply]

instance l_saturated [hf : Fact f.toAddMonoidHom.range.saturated] : Fact (l f m).saturated :=
  by
  constructor
  rw [AddSubgroup.saturated_iff_nsmul]
  rintro n l' ⟨hl', Hl'⟩
  simp only [zsmul_eq_smul, Finsupp.smul_apply, ← Finset.smul_sum, smul_eq_zero] at hl' Hl' 
  rw [Classical.or_iff_not_imp_left]
  intro hn
  refine' ⟨hl'.resolve_left hn, fun i => _⟩
  obtain ⟨li, hli⟩ := Hl' i
  have hl'i : n • l' i ∈ f.to_add_monoid_hom.range := by rw [← hli, AddMonoidHom.mem_range];
    refine' ⟨li, rfl⟩
  have Hf := hf.1
  exact (Hf hl'i).resolve_left hn

section

open Finsupp

theorem l_le_comap {n} (g : Fin (n + 1) → Fin (m + 1)) :
    l f (n + 1) ≤ (l f (m + 1)).comap (mapDomain.addMonoidHom g) :=
  by
  rintro l' ⟨hl', Hl'⟩
  rw [AddSubgroup.mem_comap]
  refine' ⟨_, _⟩
  · have aux1 : (l'.sum fun _ => AddMonoidHom.id _) = ∑ i, l' i :=
      Finsupp.sum_fintype _ _ fun _ => rfl
    have aux2 := @sum_map_domain_index_add_monoid_hom _ _ _ _ _ _ g l' fun _ => AddMonoidHom.id _
    dsimp only at aux2 
    rw [aux1, Finsupp.sum_fintype, hl'] at aux2 
    · simpa only [AddMonoidHom.id_apply] using aux2
    · intro; rfl
  · intro i
    choose l hl using Hl'
    simp only [map_domain.add_monoid_hom_apply, map_domain]
    refine' ⟨∑ j, if g j = i then l j else 0, _⟩
    rw [Finsupp.sum_apply, Finsupp.sum_fintype]
    swap; · intro; simp only [coe_zero, Pi.zero_apply, single_zero]
    simp only [f.map_sum, single_apply, ← hl]
    apply Fintype.sum_congr
    intro j; split_ifs
    · rfl
    · exact f.map_zero

@[simp]
theorem l_one : l f 1 = ⊥ := by
  rw [eq_bot_iff]
  rintro l' ⟨hl', Hl'⟩
  simp only [Fin.default_eq_zero, Finset.univ_unique, Finset.sum_singleton] at hl' 
  simp only [AddSubgroup.mem_bot, Finsupp.ext_iff, coe_zero, Pi.zero_apply]
  intro i; fin_cases i; exact hl'

end

def Obj :=
  (Fin m →₀ Λ') ⧸ l f m

instance : NormedAddCommGroup (Obj f m) :=
  AddSubgroup.normedAddCommGroupQuotient _

def π : NormedAddGroupHom (Fin m →₀ Λ') (Obj f m) :=
  (l f m).normedMk

theorem π_apply_eq_zero_iff (x : Fin m →₀ Λ') : π f m x = 0 ↔ x ∈ l f m :=
  QuotientAddGroup.eq_zero_iff _

theorem π_surjective : Function.Surjective (π f m) :=
  Quotient.surjective_Quotient_mk''

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem norm_π_one_eq (l : Fin 1 →₀ Λ') : «expr∥ ∥» ((π f 1) l) = «expr∥ ∥» l :=
  by
  delta π; dsimp
  show «expr∥ ∥» ((QuotientAddGroup.mk' (L f 1)) l) = «expr∥ ∥» l
  rw [quotient_norm_mk_eq (L f 1) l]
  simp only [L_one, Set.image_singleton, add_zero, csInf_singleton, AddSubgroup.coe_bot]

theorem π_isQuotient : (π f m).IsQuotient :=
  NormedAddGroupHom.isQuotientQuotient _

instance [Fact f.toAddMonoidHom.range.saturated] : PolyhedralLattice (Obj f m) := by delta obj;
  infer_instance

end Objects

section Maps

/-!
## The simplicial maps
-/


open Finsupp

variable {n m k : ℕ} (g : Fin (n + 1) → Fin (m + 1)) (g' : Fin (m + 1) → Fin (k + 1))

-- the underlying morphism of additive groups
def mapAddHom : Obj f (n + 1) →+ Obj f (m + 1) :=
  QuotientAddGroup.map _ _ (mapDomain.addMonoidHom g) (l_le_comap f _ g)

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem map_domain_addMonoidHom_strict (x : Fin (n + 1) →₀ Λ) :
    «expr∥ ∥» (mapDomain.addMonoidHom g x) ≤ «expr∥ ∥» x :=
  by
  simp only [norm_def, map_domain.add_monoid_hom_apply]
  dsimp [map_domain]
  rw [sum_fintype]; swap; · intro; exact norm_zero
  simp only [sum_apply]
  rw [sum_fintype]; swap; · intro; exact norm_zero
  calc
    ∑ i, «expr∥ ∥» (x.sum fun j l => single (g j) l i) ≤
        ∑ i, ∑ j, «expr∥ ∥» (single (g j) (x j) i) :=
      _
    _ ≤ ∑ j, «expr∥ ∥» (x j) := _
  · apply Finset.sum_le_sum
    rintro i -
    rw [sum_fintype]; swap; · intro; rw [single_zero, zero_apply]
    exact norm_sum_le _ _
  · rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    rintro j -
    simp only [single_apply, norm_zero, apply_ite norm]
    apply le_of_eq
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
theorem mapAddHom_strict (x : Obj f (n + 1)) : «expr∥ ∥» (mapAddHom f g x) ≤ «expr∥ ∥» x :=
  by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, rfl, h⟩ := norm_mk_lt x hε
  calc
    _ ≤ «expr∥ ∥» (map_domain.add_monoid_hom g x) := quotient_norm_mk_le _ _
    _ ≤ «expr∥ ∥» x := (map_domain_add_monoid_hom_strict _ _)
    _ ≤ _ := h.le

theorem mapAddHom_mk (x : Fin (n + 1) →₀ Λ') :
    (mapAddHom f g) (QuotientAddGroup.mk x) = QuotientAddGroup.mk (mapDomain.addMonoidHom g x) :=
  rfl

@[simp]
theorem mapAddHom_π (x : Fin (n + 1) →₀ Λ') :
    (mapAddHom f g) (π _ _ x) = π _ _ (mapDomain.addMonoidHom g x) :=
  rfl

variable [Fact f.toAddMonoidHom.range.saturated]

@[simps]
def map : PolyhedralLatticeHom (Obj f (n + 1)) (Obj f (m + 1)) :=
  { mapAddHom f g with strict' := mapAddHom_strict f g }

theorem map_id : map f (id : Fin (m + 1) → Fin (m + 1)) = PolyhedralLatticeHom.id :=
  by
  ext x
  apply QuotientAddGroup.induction_on x <;> clear x
  intro x
  simp only [AddMonoidHom.toFun_eq_coe, map_apply, PolyhedralLatticeHom.id_apply, map_add_hom_mk,
    map_domain.add_monoid_hom_apply, map_domain_id]

theorem map_comp : map f (g' ∘ g) = (map f g').comp (map f g) :=
  by
  ext x
  apply QuotientAddGroup.induction_on x <;> clear x
  intro x
  simp only [AddMonoidHom.toFun_eq_coe, map_apply, PolyhedralLatticeHom.comp_apply, map_add_hom_mk,
    map_domain.add_monoid_hom_apply, ← map_domain_comp]

end Maps

theorem lift'_w {M : Type _} [AddCommGroup M] (m : ℕ) (g₀ : Λ →+ M) (g : Fin (m + 1) → Λ' →+ M)
    (hg : ∀ i l, (g i) (f l) = g₀ l) (hf : Function.Injective f) :
    ∀ (l : Fin (m + 1) →₀ Λ') (hl : l ∈ l f (m + 1)), Finsupp.liftAddHom g l = 0 :=
  by
  rintro l ⟨h1, h2⟩
  choose l₀ hl₀ using h2
  dsimp only [Finsupp.liftAddHom_apply]
  rw [Finsupp.sum_fintype]
  swap; · intro j; exact (g j).map_zero
  simp only [← hl₀, hg, ← g₀.map_sum, ← f.map_sum] at h1 ⊢
  rw [← PolyhedralLatticeHom.coe_toAddMonoidHom] at h1 hf 
  rw [injective_iff_map_eq_zero] at hf 
  rw [hf _ h1, g₀.map_zero]

def lift' {M : Type _} [AddCommGroup M] (m : ℕ) (g₀ : Λ →+ M) (g : Fin (m + 1) → Λ' →+ M)
    (hg : ∀ i l, (g i) (f l) = g₀ l) (hf : Function.Injective f) : Obj f (m + 1) →+ M :=
  by
  let Ψ :=
    QuotientAddGroup.lift (PolyhedralLattice.Conerve.l f (m + 1)) (Finsupp.liftAddHom g)
      (lift'_w f m g₀ g hg hf)
  exact Ψ

end Conerve

end PolyhedralLattice

namespace PolyhedralLatticeCat

universe u

open PolyhedralLattice SimplexCategory _Root_.CategoryTheory

variable {Λ Λ' : PolyhedralLatticeCat.{u}} (f : Λ ⟶ Λ') [Fact f.toAddMonoidHom.range.saturated]

namespace CechConerve

def obj (m : ℕ) : PolyhedralLatticeCat :=
  of (Conerve.Obj f (m + 1))

section

open Finsupp

def mapSuccZeroAux (m : ℕ) (g : Fin (m + 2) →o Fin 1) : obj f (m + 1) →+ Λ' :=
  (applyAddHom (0 : Fin 1)).comp <|
    by
    -- TODO: this is very ugly
    let foo := QuotientAddGroup.lift (conerve.L f (m + 1 + 1)) (map_domain.add_monoid_hom g)
    refine' foo _
    rintro l' ⟨hl', Hl'⟩
    ext i
    simp only [map_domain.add_monoid_hom_apply, map_domain, sum_apply, single_apply, zero_apply]
    rw [Finsupp.sum_fintype]
    swap; · simp only [forall_const, if_true, eq_iff_true_of_subsingleton]
    convert hl'
    ext; rw [if_pos]; exact Subsingleton.elim _ _

end

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr∥ ∥» -/
def mapSuccZero (m : ℕ) (g : Fin (m + 2) →o Fin 1) : obj f (m + 1) ⟶ Λ' :=
  { mapSuccZeroAux f m g with
    strict' := by
      intro x
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨x, rfl, h⟩ := norm_mk_lt x hε
      calc
        «expr∥ ∥» (Finsupp.mapDomain.addMonoidHom g x 0) ≤
            «expr∥ ∥» (Finsupp.mapDomain.addMonoidHom g x) :=
          _
        _ ≤ «expr∥ ∥» x := (conerve.map_domain_add_monoid_hom_strict g x)
        _ ≤ _ := h.le
      rw [Finsupp.norm_def, Finsupp.sum_fintype, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      intro; exact norm_zero }

def finsuppFinOneIso : of (Fin 1 →₀ Λ') ≅ Λ' :=
  Iso.symm <|
    PolyhedralLatticeCat.isoMk (Finsupp.singleAddHom 0) (Finsupp.applyAddHom 0)
      (fun l => by dsimp [Finsupp.norm_def]; simp only [norm_zero, Finsupp.sum_single_index])
      (by ext l; dsimp; simp only [Finsupp.single_eq_same])
      (by ext f; dsimp; simp only [Finsupp.single_eq_same])

@[simp]
theorem finsuppFinOneIso_hom (l') :
    (@finsuppFinOneIso Λ').Hom l' = Finsupp.applyAddHom (0 : Fin 1) l' :=
  rfl

@[simp]
theorem finsuppFinOneIso_inv (l') :
    (@finsuppFinOneIso Λ').inv l' = Finsupp.singleAddHom (0 : Fin 1) l' :=
  rfl

/-- the left hand side is by definition the quotient of the right hand side
by a subgroup that is provably trivial -/
def objZeroIso' : obj f 0 ≅ of (Fin 1 →₀ Λ') :=
  Iso.symm <|
    PolyhedralLatticeCat.isoMk (PolyhedralLattice.Conerve.π _ _).toAddMonoidHom
      (QuotientAddGroup.lift _ (AddMonoidHom.id _)
        (by intro x hx; rwa [PolyhedralLattice.Conerve.l_one, AddSubgroup.mem_bot] at hx ))
      (PolyhedralLattice.Conerve.norm_π_one_eq _) (by ext <;> rfl) (by ext ⟨x⟩ <;> rfl)

-- @[simp] lemma obj_zero_iso'_hom (l') :
--   (obj_zero_iso' f).hom l' = _ := rfl
@[simp]
theorem objZeroIso'_inv (l') : (objZeroIso' f).inv l' = PolyhedralLattice.Conerve.π _ _ l' :=
  rfl

def objZeroIso : obj f 0 ≅ Λ' :=
  objZeroIso' _ ≪≫ finsuppFinOneIso

def πHom (m : ℕ) : of (Fin (m + 1) →₀ Λ') ⟶ obj f m :=
  { Conerve.π f (m + 1) with
    toFun := Conerve.π f (m + 1)
    strict' := (Conerve.π_isQuotient f (m + 1)).norm_le }

instance (m : ℕ) : Epi (πHom f m) :=
  ConcreteCategory.epi_of_surjective _ <| Conerve.π_surjective f (m + 1)

theorem map_const_objZeroIso (m : ℕ) (i : Fin (m + 1)) (l : Λ') :
    Conerve.map f (fun _ => i) ((objZeroIso f).inv l) = Conerve.π f (m + 1) (Finsupp.single i l) :=
  by
  dsimp only [conerve.map_apply, AddMonoidHom.toFun_eq_coe, conerve.map_add_hom, obj_zero_iso,
    iso.trans_inv, Finsupp.singleAddHom_apply]
  simp only [comp_apply, finsupp_fin_one_iso_inv, obj_zero_iso'_inv, conerve.π]
  delta QuotientAddGroup.map
  erw [QuotientAddGroup.lift_mk']
  simp only [AddMonoidHom.comp_apply]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.singleAddHom_apply,
    Finsupp.mapDomain_single, AddSubgroup.normedMk.apply]

end CechConerve

open CechConerve

@[simps]
def cechConerve : CosimplicialObject PolyhedralLatticeCat
    where
  obj n := obj f n.len
  map n m g := Conerve.map f g.toOrderHom
  map_id' _ := Conerve.map_id f
  map_comp' _ _ _ _ _ := Conerve.map_comp f _ _

@[simps]
def cechAugmentationMap : Λ ⟶ (cechConerve f).obj (mk 0) :=
  f ≫ (objZeroIso f).inv

def augmentedCechConerve : CosimplicialObject.Augmented PolyhedralLatticeCat :=
  (cechConerve f).augment Λ (cechAugmentationMap f)
    (by
      intro n g₁ g₂
      ext l : 2
      simp only [comp_apply, Cech_augmentation_map_apply, Cech_conerve_map, conerve.map_apply,
        AddMonoidHom.toFun_eq_coe, obj_zero_iso, iso.trans_inv, Finsupp.singleAddHom_apply,
        finsupp_fin_one_iso_inv, obj_zero_iso'_inv]
      have H1 := conerve.map_add_hom_π f g₁.to_order_hom (Finsupp.single 0 (f l))
      have H2 := conerve.map_add_hom_π f g₂.to_order_hom (Finsupp.single 0 (f l))
      refine' H1.trans (Eq.trans _ H2.symm); clear H1 H2
      simp only [Finsupp.mapDomain_single, Finsupp.mapDomain.addMonoidHom_apply]
      rw [← sub_eq_zero, ← _root_.map_sub, conerve.π_apply_eq_zero_iff]
      refine' ⟨_, fun i => _⟩
      ·
        simp only [Finsupp.sub_apply, Finset.sum_sub_distrib, sub_eq_zero, Finsupp.single_apply,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
      · by_cases H : g₁.to_order_hom 0 = g₂.to_order_hom 0
        · refine' ⟨0, _⟩; simp only [H, sub_self, f.map_zero, Finsupp.zero_apply]
        simp only [Finsupp.sub_apply, Finsupp.single_apply]
        by_cases h₁ : i = g₁.to_order_hom 0
        · refine' ⟨l, _⟩; subst i
          simp only [if_neg (Ne.symm H), if_true, eq_self_iff_true, sub_zero]
        by_cases h₂ : i = g₂.to_order_hom 0
        · refine' ⟨-l, _⟩; subst i
          simp only [if_neg H, if_true, eq_self_iff_true, zero_sub, f.map_neg]
        · refine' ⟨0, _⟩; simp only [if_false, Ne.symm h₁, Ne.symm h₂, f.map_zero, sub_zero])

theorem augmentation_map_equalizes :
    cechAugmentationMap f ≫ (cechConerve f).map (δ 0) =
      cechAugmentationMap f ≫ (cechConerve f).map (δ 1) :=
  by
  ext l
  simp only [conerve.map_apply, AddMonoidHom.toFun_eq_coe, Cech_augmentation_map_apply,
    Cech_conerve_map, comp_apply, Finsupp.singleAddHom_apply, obj_zero_iso, iso.trans_inv,
    finsupp_fin_one_iso_inv, obj_zero_iso'_inv]
  have H1 := conerve.map_add_hom_π f (@hom.to_order_hom (mk 0) _ (δ 0)) (Finsupp.single 0 (f l))
  have H2 := conerve.map_add_hom_π f (@hom.to_order_hom (mk 0) _ (δ 1)) (Finsupp.single 0 (f l))
  refine' H1.trans (Eq.trans _ H2.symm); clear H1 H2
  show (conerve.π f 2) _ = (conerve.π f 2) _
  simp only [Finsupp.mapDomain_single, Finsupp.mapDomain.addMonoidHom_apply]
  rw [← sub_eq_zero, ← _root_.map_sub, conerve.π_apply_eq_zero_iff]
  have hδ0 : hom.to_order_hom (δ (0 : Fin 2)) 0 = 1 := rfl
  have hδ1 : hom.to_order_hom (δ (1 : Fin 2)) 0 = 0 := rfl
  erw [hδ0, hδ1]
  refine' ⟨_, fun i => _⟩
  ·
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Finsupp.sub_apply, len_mk,
      Finsupp.single_apply, Fin.one_eq_zero_iff, if_true, zero_sub, Fin.zero_eq_one_iff,
      eq_self_iff_true, sub_zero, Fin.succ_zero_eq_one', add_left_neg, if_false, one_ne_zero]
  fin_cases i <;>
    simp only [Finsupp.sub_apply, len_mk, Finsupp.single_apply, eq_self_iff_true, if_true, if_false,
      Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, Fin.succ_zero_eq_one', one_ne_zero, sub_zero,
      zero_sub, ← f.map_neg, exists_apply_eq_apply]

end PolyhedralLatticeCat

