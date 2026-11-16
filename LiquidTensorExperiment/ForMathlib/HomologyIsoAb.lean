import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.CategoryTheory.Abelian.Homology
import LiquidTensorExperiment.ForMathlib.HomologyExact
import LiquidTensorExperiment.ForMathlib.HomologyMap
import LiquidTensorExperiment.ForMathlib.HasHomology
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Exact

#align_import for_mathlib.homology_iso_Ab

noncomputable section

universe v u

open CategoryTheory

@[to_additive]
theorem Subgroup.comap_eq_iff {A B : Type _} [CommGroup A] [CommGroup B] (f : A ≃* B)
    (C : Subgroup A) (D : Subgroup B) :
    D.comap f.toMonoidHom = C ↔ C.comap f.symm.toMonoidHom = D :=
  by
  constructor <;> rintro rfl <;> ext
  · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

@[to_additive]
noncomputable def MulEquiv.surjectiveCongr {A B C D : Type _} [CommGroup A] [CommGroup B]
    [CommGroup C] [CommGroup D] (e : A ≃* B) (f : A →* C) (g : B →* D) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (he : g.ker.comap e.toMonoidHom = f.ker) : C ≃* D
    where
  toFun := f.liftOfSurjective hf ⟨g.comp e.toMonoidHom, fun x hx => by rw [← he] at hx ; exact hx⟩
  invFun :=
    g.liftOfSurjective hg
      ⟨f.comp e.symm.toMonoidHom, fun x hx => by rw [Subgroup.comap_eq_iff] at he ;
        rw [← he] at hx ; exact hx⟩
  left_inv x := by
    obtain ⟨x, rfl⟩ := hf x
    delta MonoidHom.liftOfSurjective
    simp only [MonoidHom.liftOfRightInverse_comp_apply, Subtype.coe_mk, MonoidHom.comp_apply]
    convert MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ (e.toMonoidHom x) using 1
    exact f.congr_arg (e.symm_apply_apply x).symm
  right_inv x := by
    obtain ⟨x, rfl⟩ := hg x
    delta MonoidHom.liftOfSurjective
    simp only [MonoidHom.liftOfRightInverse_comp_apply, Subtype.coe_mk, MonoidHom.comp_apply]
    convert MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ (e.symm.toMonoidHom x) using 1
    exact g.congr_arg (e.apply_symm_apply x).symm
  map_mul' x y := MonoidHom.map_mul _ _ _

@[to_additive]
def MulEquiv.quotientCongr {A B : Type _} [CommGroup A] [CommGroup B] (f : A ≃* B) (C : Subgroup A)
    (D : Subgroup B) (h : D.comap f.toMonoidHom = C) : A ⧸ C ≃* B ⧸ D
    where
  toFun := QuotientGroup.map _ _ f.toMonoidHom h.ge
  invFun :=
    QuotientGroup.map _ _ f.symm.toMonoidHom
      (by
        refine' le_of_eq _; subst h; ext
        simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply])
  left_inv x := by
    induction x using QuotientGroup.induction_on
    erw [QuotientGroup.map_mk, f.symm_apply_apply]
    rfl
  right_inv x := by
    induction x using QuotientGroup.induction_on
    erw [QuotientGroup.map_mk, f.apply_symm_apply]
    rfl
  map_mul' x y := MonoidHom.map_mul _ _ _

namespace AddCommGroupCat

open CategoryTheory.Limits

-- move this
attribute [elementwise] AddCommGroupCat.kernelIsoKer_hom_comp_subtype
  AddCommGroupCat.kernelIsoKer_inv_comp_ι

variable {A B C : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)

protected noncomputable def homology {A B C : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    AddCommGroupCat :=
  AddCommGroupCat.of (g.ker ⧸ f.range.comap g.ker.Subtype)

def hasHomology : HasHomology f g (AddCommGroupCat.homology f g) :=
  { w
    π := (AddCommGroupCat.kernelIsoKer _).hom ≫ ofHom (QuotientAddGroup.mk' _)
    ι :=
      QuotientAddGroup.lift _ ((cokernel.π f).comp <| AddSubgroup.subtype _)
        (by
          rintro ⟨y, hx : g y = 0⟩ ⟨x, rfl : f x = y⟩
          dsimp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, Subtype.coe_mk,
            AddSubgroup.coeSubtype]
          rw [← comp_apply, cokernel.condition, zero_apply])
    π_ι := by rw [← AddCommGroupCat.kernelIsoKer_hom_comp_subtype]; rfl
    ex_π := by
      rw [← exact_comp_hom_inv_comp_iff (kernel_iso_ker g), Iso.inv_hom_id_assoc]
      rw [AddCommGroupCat.exact_iff']
      constructor
      · ext; simp
      · rintro ⟨x, hx : _ = _⟩ (hh : _ = _)
        dsimp at hh 
        rw [QuotientAddGroup.eq_zero_iff] at hh 
        obtain ⟨t, ht⟩ := hh
        use t
        ext
        simp_rw [comp_apply]
        dsimp [kernel_iso_ker]
        rw [← comp_apply, kernel.lift_ι, ht]
        rfl
    ι_ex := by
      rw [AddCommGroupCat.exact_iff']
      constructor
      · ext ⟨t⟩
        simpa only [comp_apply, AddMonoidHom.coe_comp, QuotientAddGroup.coe_mk',
          Function.comp_apply, QuotientAddGroup.lift_mk, AddSubgroup.coeSubtype, AddSubgroup.coe_mk,
          cokernel.π_desc_apply, AddMonoidHom.zero_comp, AddMonoidHom.zero_apply]
      · rintro x (hx : _ = _)
        change ∃ e, _
        have : Function.Surjective (cokernel.π f) := surjective_of_epi (cokernel.π f)
        obtain ⟨y, rfl⟩ := this x
        rw [← comp_apply, cokernel.π_desc] at hx 
        let yy : g.ker := ⟨y, hx⟩
        use QuotientAddGroup.mk yy
        simp only [QuotientAddGroup.lift_mk', AddMonoidHom.coe_comp, AddSubgroup.coeSubtype,
          Function.comp_apply, Subtype.coe_mk]
    epi_π := by
      apply (config := { instances := false }) epi_comp; · infer_instance
      rw [AddCommGroupCat.epi_iff_surjective]; exact QuotientAddGroup.mk'_surjective _
    mono_ι := by
      rw [AddCommGroupCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨⟨y, hy'⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk] at hy 
      rw [AddSubgroup.mem_comap]
      dsimp at hy ⊢
      have : exact f (cokernel.π f) := Abelian.exact_cokernel f
      rw [AddCommGroupCat.exact_iff'] at this 
      exact this.2 hy }

protected noncomputable def homologyIso {A B C : AddCommGroupCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) : homology' f g w ≅ AddCommGroupCat.of (g.ker ⧸ f.range.comap g.ker.Subtype) :=
  (homology'.has f g w).Iso (hasHomology f g w)

-- begin
--   refine homology_iso_cokernel_lift f g w ≪≫
--     AddCommGroup.cokernel_iso_quotient _ ≪≫
--     add_equiv_iso_AddCommGroup_iso.hom _,
--   refine add_equiv.quotient_congr _ _ _ _,
--   { exact add_equiv_iso_AddCommGroup_iso.inv (AddCommGroup.kernel_iso_ker _) },
--   rw add_subgroup.comap_eq_iff,
--   show add_subgroup.comap (AddCommGroup.kernel_iso_ker g).inv
--     (add_monoid_hom.range (limits.kernel.lift g f w)) =
--     add_subgroup.comap (add_monoid_hom.ker g).subtype (add_monoid_hom.range f),
--   dsimp only [AddCommGroup.kernel_iso_ker],
--   have : function.injective (λ x, limits.kernel.ι g x),
--   { rw [← AddCommGroup.kernel_iso_ker_hom_comp_subtype, coe_comp],
--     have : function.injective (g.ker.subtype) := subtype.val_injective,
--     refine this.comp _,
--     refine function.has_left_inverse.injective _,
--     refine ⟨(AddCommGroup.kernel_iso_ker _).inv, _⟩,
--     intro y, refine category_theory.iso.hom_inv_id_apply (AddCommGroup.kernel_iso_ker g) y, },
--   ext ⟨x, hx⟩,
--   simp only [add_subgroup.mem_comap, add_monoid_hom.mem_range, add_subgroup.coe_subtype,
--     subtype.coe_mk, ← this.eq_iff, category_theory.limits.kernel.lift_ι_apply],
-- end
-- lemma homology_iso_hom_eq {A B C : AddCommGroup.{u}} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) :
--   (AddCommGroup.homology_iso f g w).hom =
--   homology.desc' _ _ _ ((AddCommGroup.kernel_iso_ker _).hom ≫ quotient_add_group.mk' _)
--   (by { ext x, simp only [comp_apply, quotient_add_group.mk'_apply, zero_apply, quotient_add_group.eq_zero_iff], refine ⟨x, _⟩, rw [kernel_iso_ker_hom_comp_subtype_apply, ← comp_apply, limits.kernel.lift_ι], }) :=
-- begin
--   ext1,
--   dsimp only [AddCommGroup.homology_iso, iso.trans_hom],
--   rw [homology.π'_desc'],
--   admit
-- end
variable {A₁ B₁ C₁ A₂ B₂ C₂ : AddCommGroupCat.{u}}

variable {f₁ : A₁ ⟶ B₁} {g₁ : B₁ ⟶ C₁} (w₁ : f₁ ≫ g₁ = 0)

variable {f₂ : A₂ ⟶ B₂} {g₂ : B₂ ⟶ C₂} (w₂ : f₂ ≫ g₂ = 0)

variable {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂} {γ : C₁ ⟶ C₂}

variable (sq1 : Commsq f₁ α β f₂) (sq2 : Commsq g₁ β γ g₂)

@[simps apply]
def kerMap : ↥(AddMonoidHom.ker f₁) →+ ↥(AddMonoidHom.ker f₂) :=
  (AddMonoidHom.mk' fun x =>
      ⟨α x, by rw [f₂.mem_ker, ← comp_apply, ← sq1.w, comp_apply]; convert β.map_zero;
        exact x.2⟩) <|
    by rintro ⟨a, _⟩ ⟨b, _⟩; ext; apply α.map_add

noncomputable def homologyMap : AddCommGroupCat.homology f₁ g₁ ⟶ AddCommGroupCat.homology f₂ g₂ :=
  (hasHomology f₁ g₁ w₁).map (hasHomology f₂ g₂ w₂) sq1 sq2

@[simp]
theorem homologyMap_apply_mk (t) :
    homologyMap w₁ w₂ sq1 sq2 (QuotientAddGroup.mk t) = QuotientAddGroup.mk (kerMap sq2 t) :=
  by
  dsimp [AddCommGroupCat.homologyMap, HasHomology.map, HasHomology.desc]
  generalize_proofs _ h _ _ h1 h2
  have := h.comp_epiDesc ((HasHomology f₂ g₂ w₂).lift (kernel.ι g₁ ≫ β ≫ cokernel.π f₂) h1) h2
  let e : kernel g₁ ≅ AddCommGroupCat.of (AddMonoidHom.ker g₁) := AddCommGroupCat.kernelIsoKer _
  let s := e.inv t
  let p := (HasHomology f₁ g₁ w₁).π
  have ht : QuotientAddGroup.mk t = p s := by
    dsimp [s, p]; rw [← comp_apply]
    let pp : AddCommGroupCat.of g₁.ker ⟶ AddCommGroupCat.homology f₁ g₁ := QuotientAddGroup.mk' _
    suffices : pp = e.inv ≫ p; rw [← this]; rfl
    rw [Iso.eq_inv_comp]
    ext t; rfl
  rw [ht, ← comp_apply, this]
  dsimp [s]
  rw [← comp_apply]
  dsimp [e, HasHomology.desc, HasHomology.lift]
  generalize_proofs hh
  let q := (kernel_iso_ker g₁).inv ≫ hh.monoLift (kernel.ι g₁ ≫ β ≫ cokernel.π f₂) h1
  let pp : AddCommGroupCat.of g₂.ker ⟶ AddCommGroupCat.homology f₂ g₂ := QuotientAddGroup.mk' _
  let tt : AddCommGroupCat.of g₁.ker ⟶ AddCommGroupCat.of g₂.ker := ker_map sq2
  have hq : (kernel_iso_ker g₁).inv ≫ hh.monoLift (kernel.ι g₁ ≫ β ≫ cokernel.π f₂) h1 = tt ≫ pp :=
    by
    rw [Iso.inv_comp_eq]
    have := hh.monoLift_comp (kernel.ι g₁ ≫ β ≫ cokernel.π f₂) h1
    rw [← cancel_mono (HasHomology f₂ g₂ w₂).ι, this]
    ext; rfl
  rw [hq]; rfl

noncomputable def homologyIso_hom_homologyMap :
    (AddCommGroupCat.homologyIso f₁ g₁ w₁).hom ≫ homologyMap w₁ w₂ sq1 sq2 =
      homology'.map' w₁ w₂ sq1 sq2 ≫ (AddCommGroupCat.homologyIso f₂ g₂ w₂).hom :=
  by
  erw [HasHomology.map_comp_map]
  erw [HasHomology.map_comp_map]
  rfl

noncomputable def homologyIso_inv_homologyMap :
    (AddCommGroupCat.homologyIso f₁ g₁ w₁).inv ≫ homology'.map' w₁ w₂ sq1 sq2 =
      homologyMap w₁ w₂ sq1 sq2 ≫ (AddCommGroupCat.homologyIso f₂ g₂ w₂).inv :=
  by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, AddCommGroupCat.homologyIso_hom_homologyMap]

end AddCommGroupCat

