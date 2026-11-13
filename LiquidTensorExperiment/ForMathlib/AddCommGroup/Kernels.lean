/-
Credit to Markus Himmel for the corresponding file about `Module` in mathlib
-/
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi

#align_import for_mathlib.AddCommGroup.kernels

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe u

namespace AddCommGroupCat

variable {M N : AddCommGroupCat.{u}} (f : M ⟶ N)

#print AddCommGroupCat.kernelCone /-
/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  @KernelFork.ofι AddCommGroupCat _ _ M N f (of f.ker) (f.ker.Subtype : of f.ker ⟶ M) <| by ext1;
    cases x; assumption
-/

#print AddCommGroupCat.kernelIsLimit /-
/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s : Fork f 0 =>
      AddMonoidHom.codRestrict (Fork.ι s) f.ker fun c =>
        (AddMonoidHom.mem_ker _).2 <|
          by
          rw [← @Function.comp_apply _ _ _ f s.ι c, ← coe_comp, fork.condition,
            has_zero_morphisms.comp_zero (fork.ι s) N]
          rfl)
    (fun s => by ext; simp only [comp_apply, AddMonoidHom.codRestrict_apply]; rfl) fun s m h =>
    AddMonoidHom.ext fun x =>
      Subtype.ext_iff_val.2 <|
        by
        have h₁ : (m ≫ (kernelCone f).π.app zero).toFun = (s.π.app zero).toFun := by congr; exact h
        convert @congr_fun _ _ _ _ h₁ x
-/

#print AddCommGroupCat.cokernelCocone /-
/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  @CokernelCofork.ofπ AddCommGroupCat _ _ M N f (of <| N ⧸ f.range)
      (QuotientAddGroup.mk' f.range) <|
    by ext1;
    simp only [comp_apply, QuotientAddGroup.mk'_apply, zero_apply, QuotientAddGroup.eq_zero_iff,
      AddMonoidHom.mem_range, exists_apply_eq_apply]
-/

#print AddCommGroupCat.cokernelIsColimit /-
/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s : Cofork f 0 =>
      QuotientAddGroup.lift _ s.π <| by
        rintro _ ⟨x, rfl⟩; have := AddMonoidHom.congr_fun s.condition x
        simpa only [comp_apply, zero_apply, map_zero] using this)
    (fun s => by ext; simp only [comp_apply]; rfl) fun s m h =>
    by
    let g : N ⟶ of <| N ⧸ f.range := QuotientAddGroup.mk' f.range
    haveI : epi g := (epi_iff_range_eq_top _).mpr _
    swap;
    · ext ⟨x⟩;
      simp only [AddMonoidHom.mem_range, QuotientAddGroup.mk'_apply, AddSubgroup.mem_top,
        iff_true_iff]
      exact ⟨x, rfl⟩
    apply (cancel_epi g).1
    convert h
    ext; rfl
-/

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
-- TODO: the next two already exist: add `elementwise` to those lemmas in mathlib
@[simp, elementwise]
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f = f.ker.Subtype :=
  kernelIsoKer_inv_comp_ι _

@[simp, elementwise]
theorem kernelIsoKer_hom_ker_subtype : (kernelIsoKer f).hom ≫ f.ker.Subtype = kernel.ι f :=
  kernelIsoKer_hom_comp_subtype _

/-- The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient : cokernel f ≅ of (N ⧸ f.range) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = QuotientAddGroup.mk' f.range := by
  convert colimit.iso_colimit_cocone_ι_hom _ _ <;> rfl

@[simp, elementwise]
theorem range_mkq_cokernelIsoRangeQuotient_inv :
    (QuotientAddGroup.mk' f.range : _) ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f := by
  convert colimit.iso_colimit_cocone_ι_inv ⟨_, cokernel_is_colimit f⟩ _ <;> rfl

end AddCommGroupCat

