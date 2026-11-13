import LiquidTensorExperiment.Rescale.Basic
import LiquidTensorExperiment.LocallyConstant.Vhat
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import LiquidTensorExperiment.Facts.Nnreal

#align_import rescale.normed_group

noncomputable section

open scoped BigOperators Classical NNReal

namespace Rescale

variable {N : ℝ≥0} {V : Type _}

instance [Norm V] : Norm (Rescale N V) where norm v := ‖of.symm v‖ / N

theorem norm_def [Norm V] (v : Rescale N V) : ‖v‖ = ‖of.symm v‖ / N :=
  rfl

instance [hN : Fact (0 < N)] [SeminormedAddCommGroup V] : SeminormedAddCommGroup (Rescale N V) :=
  seminormed_add_comm_group.of_core (Rescale N V)
    { norm_zero := show ‖0 : V‖ / N = 0 by rw [norm_zero, zero_div]
      triangle := fun v w => by
        simp only [norm_def, ← add_div]
        exact div_le_div_of_le hN.out.le (norm_add_le _ _)
      -- defeq abuse
      norm_neg := fun v => by simp only [norm_def]; congr 1; exact norm_neg _ }

-- defeq abuse
instance [hN : Fact (0 < N)] [NormedAddCommGroup V] : NormedAddCommGroup (Rescale N V) :=
  normed_add_comm_group.of_core (Rescale N V)
    { norm_eq_zero_iff := fun v =>
        by
        have aux : (N : ℝ) ≠ 0 := ne_of_gt hN.out
        simp only [norm_def, div_eq_zero_iff, aux, or_false_iff]
        exact norm_eq_zero
      -- defeq abuse
      triangle := fun v w => by
        simp only [norm_def, ← add_div]
        exact div_le_div_of_le hN.out.le (norm_add_le _ _)
      -- defeq abuse
      norm_neg := fun v => by simp only [norm_def]; congr 1; exact norm_neg _ }

-- defeq abuse
theorem nnnorm_def [hN : Fact (0 < N)] [SeminormedAddCommGroup V] (v : Rescale N V) :
    ‖v‖₊ = ‖of.symm v‖₊ / N :=
  rfl

end Rescale

namespace SemiNormedGroupCat

variable (r r₁ r₂ : ℝ≥0) [Fact (0 < r₁)] [Fact (0 < r₂)]

@[simps]
def rescale (r : ℝ≥0) [hr : Fact (0 < r)] : SemiNormedGroupCat ⥤ SemiNormedGroupCat
    where
  obj V := of <| Rescale r V
  map V₁ V₂ f :=
    { toFun := fun v => @Rescale.of r V₂ <| f ((@Rescale.of r V₁).symm v)
      map_add' := f.map_add'
      -- defeq abuse
      bound' := by
        obtain ⟨C, C_pos, hC⟩ := f.bound
        use C
        intro v
        have := hC ((@Rescale.of r V₁).symm v)
        rw [← div_le_div_right (show 0 < (r : ℝ) from hr.1), mul_div_assoc] at this 
        exact this }
  map_id' V := rfl
  -- defeq abuse
  map_comp' V₁ V₂ V₃ f g := rfl

-- defeq abuse
instance rescale.additive [Fact (0 < r)] : (rescale r).Additive where map_add' V W f g := rfl

-- defeq abuse
theorem norm_rescale_map_le [Fact (0 < r)] {V₁ V₂ : SemiNormedGroupCat} {f : V₁ ⟶ V₂} {C : ℝ}
    (hf : ‖f‖ ≤ C) : ‖((rescale r).map f)‖ ≤ C :=
  by
  refine' NormedAddGroupHom.opNorm_le_bound _ (le_trans (norm_nonneg _) hf) fun v => _
  dsimp
  erw [Rescale.norm_def, Rescale.norm_def, Equiv.symm_apply_apply, ← mul_div_assoc]
  refine'
    div_le_div (mul_nonneg (le_trans (norm_nonneg _) hf) (norm_nonneg _))
      (NormedAddGroupHom.le_of_opNorm_le _ hf _) _ le_rfl
  rw [NNReal.coe_pos]; exact ‹Fact (0 < r)›.out

theorem rescale_map_isometry [Fact (0 < r)] {V₁ V₂ : SemiNormedGroupCat} {f : V₁ ⟶ V₂}
    (hf : Isometry f) : Isometry ((rescale r).map f) :=
  by
  rw [AddMonoidHomClass.isometry_iff_norm] at hf ⊢
  intro v
  erw [Rescale.norm_def, Rescale.norm_def, hf ((@Rescale.of r _).symm v)]

theorem rescale_exact [Fact (0 < r)] {V₁ V₂ V₃ : SemiNormedGroupCat} (f : V₁ ⟶ V₂) (g : V₂ ⟶ V₃)
    (hfg : f.range = g.ker) : ((rescale r).map f).range = ((rescale r).map g).ker :=
  by
  ext x
  calc
    x ∈ ((Rescale r).map f).range ↔ x ∈ f.range := Iff.rfl
    _ ↔ x ∈ g.ker := by rw [hfg]
    _ ↔ x ∈ ((Rescale r).map g).ker := Iff.rfl

theorem rescale_exists_norm_le [Fact (0 < r)] {V₁ V₂ : SemiNormedGroupCat} (f : V₁ ⟶ V₂) (C : ℝ≥0)
    (hf : ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖) :
    ∀ y, ∃ x, (rescale r).map f x = y ∧ ‖x‖ ≤ C * ‖y‖ :=
  by
  intro y
  obtain ⟨x, h1, h2⟩ := hf ((@Rescale.of r _).symm y)
  refine' ⟨@Rescale.of r _ x, h1, _⟩
  erw [Rescale.norm_def, Rescale.norm_def]
  simp only [div_eq_mul_inv, ← mul_assoc, Equiv.symm_apply_apply, ← coe_nnnorm]
  norm_cast; exact mul_le_mul' h2 le_rfl

theorem nnnorm_to_rescale {V : SemiNormedGroupCat} (v : V) :
    ‖((@Rescale.of r V) v)‖ ≤ r⁻¹ * ‖v‖ := by rw [← div_eq_inv_mul]; rfl

def toRescale [Fact (0 < r)] : 𝟭 _ ⟶ rescale r
    where
  app V :=
    AddMonoidHom.mkNormedAddGroupHom' (AddMonoidHom.mk' (@Rescale.of r V) fun _ _ => rfl) r⁻¹
      fun v => nnnorm_to_rescale _ v
  naturality' V W f := rfl

-- defeq abuse
def ofRescale [hr : Fact (0 < r)] : rescale r ⟶ 𝟭 _
    where
  app V :=
    AddMonoidHom.mkNormedAddGroupHom' (AddMonoidHom.mk' (@Rescale.of r V).symm fun _ _ => rfl) r
      (by
        intro v
        erw [Rescale.nnnorm_def, mul_div_cancel' _ hr.1.ne']
        exact le_rfl)
  naturality' V W f := rfl

-- defeq abuse
@[simps]
def isoRescale [Fact (0 < r)] : 𝟭 _ ≅ rescale r
    where
  hom := toRescale r
  inv := ofRescale r

open _Root_.CategoryTheory

theorem isoRescale_isometry [Fact (0 < r)] (h : r = 1) (V : SemiNormedGroupCat) :
    Isometry ((isoRescale r).app V).hom := by
  cases h
  dsimp only [nat_iso.app_hom, iso_rescale_hom]
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  erw [Rescale.norm_def]
  simp only [div_one, Subtype.coe_mk]
  rfl

theorem norm_toRescale_le [Fact (0 < r)] (V : SemiNormedGroupCat) :
    ‖((toRescale r).app V)‖ ≤ r⁻¹ :=
  NormedAddGroupHom.mkNormedAddGroupHom_norm_le _ (inv_nonneg.2 NNReal.zero_le_coe) fun v =>
    nnnorm_to_rescale _ v

theorem nnnorm_rescale_rescale_symm {V : SemiNormedGroupCat} (v : (rescale r₁).obj V) :
    ‖((@Rescale.of r₂ V) ((@Rescale.of r₁ V).symm v))‖₊ ≤ r₁ / r₂ * ‖v‖₊ :=
  by
  apply le_of_eq
  show _ = r₁ / r₂ * (‖((@Rescale.of r₁ V).symm v)‖₊ / r₁)
  simp only [AddMonoidHom.mk'_apply, div_eq_inv_mul, Rescale.nnnorm_def]
  rw [mul_assoc, mul_inv_cancel_left₀ (show r₁ ≠ 0 from ne_of_gt <| Fact.out _)]
  rfl

def scale : rescale r₁ ⟶ rescale r₂
    where
  app V :=
    AddMonoidHom.mkNormedAddGroupHom'
      (AddMonoidHom.mk' (fun v => @Rescale.of r₂ V <| (@Rescale.of r₁ V).symm v) fun _ _ => rfl)
      (r₁ / r₂) fun v => nnnorm_rescale_rescale_symm r₁ r₂ v
  naturality' V W f := rfl

-- defeq abuse
theorem norm_scale_le (V : SemiNormedGroupCat) : ‖((scale r₁ r₂).app V)‖ ≤ r₁ / r₂ :=
  NormedAddGroupHom.mkNormedAddGroupHom_norm_le _
    (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) fun v =>
    nnnorm_rescale_rescale_symm r₁ r₂ v

theorem scale_comm {V₁ V₂ W₁ W₂ : SemiNormedGroupCat} (f₁ : V₁ ⟶ W₁) (f₂ : V₂ ⟶ W₂) (φ : V₁ ⟶ V₂)
    (ψ : W₁ ⟶ W₂) (h : f₁ ≫ ψ = φ ≫ f₂) :
    (rescale r₁).map f₁ ≫ (rescale r₁).map ψ ≫ (scale r₁ r₂).app W₂ =
      ((rescale r₁).map φ ≫ (scale r₁ r₂).app V₂) ≫ (rescale r₂).map f₂ :=
  by
  rw [← category.assoc, ← CategoryTheory.Functor.map_comp, nat_trans.naturality,
    nat_trans.naturality, category.assoc, ← CategoryTheory.Functor.map_comp, h]

end SemiNormedGroupCat

