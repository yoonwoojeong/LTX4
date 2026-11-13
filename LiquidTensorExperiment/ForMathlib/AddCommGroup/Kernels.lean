/-
Credit to Markus Himmel for the corresponding file about `Module` in mathlib
-/
import LiquidTensorExperiment.ForMathlib.AddCommGroup.Epi
import Mathlib.Algebra.Category.GroupCat.Kernels

#align_import for_mathlib.AddCommGroup.kernels

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.WalkingParallelPair

universe u

namespace AddCommGroupCat

variable {M N : AddCommGroupCat.{u}} (f : M ⟶ N)

/-!
Porting note: LTE's `AddCommGroup.kernel_cone`, `kernel_is_limit`, `cokernel_cocone` and
`cokernel_is_colimit` were later added to mathlib with the same names and the same data
(the cone point `of f.ker` with `f.ker.subtype`, and the cocone point `of (N ⧸ f.range)`
with `QuotientAddGroup.mk' f.range`); in Lean 4 they are
`AddCommGroupCat.kernelCone` etc. in `Mathlib.Algebra.Category.GroupCat.Kernels`, which is
imported here, so they are not redeclared.
-/

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
-- TODO: the next two already exist: add `elementwise` to those lemmas in mathlib
@[elementwise (attr := simp)]
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f = f.ker.subtype :=
  kernelIsoKer_inv_comp_ι _

@[elementwise (attr := simp)]
theorem kernelIsoKer_hom_ker_subtype : (kernelIsoKer f).hom ≫ f.ker.subtype = kernel.ι f :=
  kernelIsoKer_hom_comp_subtype _

/-- The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient : cokernel f ≅ of (N ⧸ f.range) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[elementwise (attr := simp)]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = QuotientAddGroup.mk' f.range := by
  convert colimit.isoColimitCocone_ι_hom _ _ <;> rfl

@[elementwise (attr := simp)]
theorem range_mkq_cokernelIsoRangeQuotient_inv :
    -- Porting note: Lean 3's `(_ : _)` ascription is spelled with `show` so that the
    -- `→+` is elaborated as a morphism of `AddCommGroupCat`
    (show N ⟶ of (N ⧸ f.range) from QuotientAddGroup.mk' f.range) ≫ (cokernelIsoRangeQuotient f).inv =
      cokernel.π f := by
  -- Porting note: the walking-parallel-pair object is given explicitly
  convert colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one <;> rfl

end AddCommGroupCat

