import LiquidTensorExperiment.SystemOfComplexes.Basic
import LiquidTensorExperiment.Rescale.NormedGroup

#align_import system_of_complexes.rescale

/-!

# rescaling norms on a system of complexes

This file defines the `rescale` functor which will take a system of complexes of seminormed groups
and systematically rescale all the norms on all the seminormed groups by a constant factor.

-/


noncomputable section

universe u

open CategoryTheory

open scoped Nat NNReal

namespace NNReal

def mulLeft (κ : ℝ≥0) : ℝ≥0 ⥤ ℝ≥0 where
  obj c := κ * c
  map c₁ c₂ h := homOfLE <| mul_le_mul' le_rfl (leOfHom h)

def mulRight (κ : ℝ≥0) : ℝ≥0 ⥤ ℝ≥0 where
  obj c := c * κ
  map c₁ c₂ h := homOfLE <| mul_le_mul' (leOfHom h) le_rfl

end NNReal

namespace SystemOfComplexes

def rescale (r : ℝ≥0) [Fact (0 < r)] : SystemOfComplexes.{u} ⥤ SystemOfComplexes.{u} :=
  (whiskeringRight _ _ _).obj <| (SemiNormedGroupCat.rescale r).mapHomologicalComplex _

theorem rescale_obj (r c : ℝ≥0) [Fact (0 < r)] (C : SystemOfComplexes) (i : ℕ) :
    ↥(((rescale r).obj C) c i) = Rescale r (C c i) :=
  rfl

theorem rescale_d (r c : ℝ≥0) [Fact (0 < r)] (C : SystemOfComplexes) (i j : ℕ)
    (v : ((rescale r).obj C) c i) :
    (((rescale r).obj C).d i j) v = @Rescale.of r _ ((C.d i j) ((@Rescale.of r _).symm v)) :=
  rfl

instance rescale.additive (r : ℝ≥0) [Fact (0 < r)] : (rescale r).Additive
    where map_add' X Y f g := by ext; rfl

-- a heavy refl
-- can we golf this? speed it up?
def toRescale (r : ℝ≥0) [Fact (0 < r)] : 𝟭 SystemOfComplexes ⟶ rescale r
    where
  app C :=
    { app := fun c =>
        { f := fun _ => (SemiNormedGroupCat.toRescale r).app _
          comm' := by intros; exact ((SemiNormedGroupCat.toRescale r).naturality _).symm }
      naturality' := by intro c₁ c₂ h; ext i : 2; rfl }
  naturality' C₁ C₂ f := by ext; rfl

def scale (i j : ℝ≥0) [Fact (0 < i)] [Fact (0 < j)] : rescale i ⟶ rescale j :=
  (whiskeringRight _ _ _).map <| NatTrans.mapHomologicalComplex (SemiNormedGroupCat.scale i j) _

section ExactAndAdmissible

variable {k K : ℝ≥0} [Fact (1 ≤ k)] {m : ℕ} {c₀ : ℝ≥0}

theorem rescaleIsWeakBoundedExact (r : ℝ≥0) [hr : Fact (0 < r)] (C : SystemOfComplexes)
    (hC : C.IsWeakBoundedExact k K m c₀) : ((rescale r).obj C).IsWeakBoundedExact k K m c₀ :=
  by
  intro c hc i hi x ε hε
  obtain ⟨_, _, rfl, rfl, y, hy⟩ := hC c hc i hi ((@Rescale.of r _).symm x) (ε * r) _
  swap; · exact mul_pos hε hr.out
  refine' ⟨_, _, rfl, rfl, (@Rescale.of r _) y, _⟩
  erw [Rescale.norm_def, Rescale.norm_def]
  rwa [div_le_iff, add_mul, mul_assoc, div_mul_cancel]
  · apply ne_of_gt; exact hr.out
  · exact hr.out

/-- `rescale C` is admissible if `C` is. -/
theorem rescaleAdmissible (r : ℝ≥0) [Fact (0 < r)] (C : SystemOfComplexes) (hC : C.Admissible) :
    ((rescale r).obj C).Admissible :=
  { d_norm_noninc' := by
      rintro c i j h
      rintro (v : _root_.rescale r (C c i))
      -- rw rescale_obj gives motive issues
      rw [rescale_d, Rescale.norm_def, Rescale.norm_def, Equiv.symm_apply_apply]
      refine' div_le_div_of_le_of_nonneg _ _
      · apply hC.d_norm_noninc' c i j h
      · exact NNReal.coe_nonneg r
    res_normNoninc := fun c' c i h v =>
      div_le_div_of_le_of_nonneg (hC.res_normNoninc c' c i h _) (NNReal.coe_nonneg r) }

end ExactAndAdmissible

instance (m : ℕ) : Fact (0 < m !) :=
  ⟨Nat.factorial_pos _⟩

def rescaleFunctor : ℕ → SystemOfComplexes ⥤ SystemOfComplexes
  | 0 => 𝟭 _
  | 1 => 𝟭 _
  | m + 2 => rescale (m + 2)!

instance rescaleFunctor.additive : ∀ m, (rescaleFunctor m).Additive
  | 0 => Functor.id.additive
  | 1 => Functor.id.additive
  | m + 2 => show (rescale (m + 2)!).Additive from rescale.additive _

def rescaleNatTrans : ∀ i j, rescaleFunctor i ⟶ rescaleFunctor j
  | 0, 1 => 𝟙 _
  | 1, j + 2 => toRescale (j + 2)!
  | i + 2, j + 2 => scale (i + 2)! (j + 2)!
  | _, _ => 0

section ScaleIndex

@[simps]
def scaleIndexLeft (κ : ℝ≥0) : SystemOfComplexes ⥤ SystemOfComplexes :=
  (whiskeringLeft _ _ _).obj (NNReal.mulLeft κ).op

@[simp]
theorem scaleIndexLeft_apply (C : SystemOfComplexes) (κ c : ℝ≥0) (i : ℕ) :
    (scaleIndexLeft κ).obj C c i = C (κ * c) i :=
  rfl

/- warning: system_of_complexes.scale_index_left clashes with system_of_complexes.ScaleIndexLeft -> SystemOfComplexes.scaleIndexLeft
Case conversion may be inaccurate. Consider using '#align system_of_complexes.scale_index_left SystemOfComplexes.scaleIndexLeftₓ'. -/
def scaleIndexLeft (C : SystemOfComplexes) (κ : ℝ≥0) :=
  (scaleIndexLeft κ).obj C

theorem Admissible.scaleIndexLeft {C : SystemOfComplexes} (hC : C.Admissible) (κ : ℝ≥0) :
    (C.scaleIndexLeft κ).Admissible :=
  { d_norm_noninc' := fun c i j hij => by apply admissible.d_norm_noninc C hC (κ * c) i j
    res_normNoninc := fun c₁ c₂ i hc => hC.res_normNoninc _ _ i (by skip; dsimp; infer_instance) }

theorem IsWeakBoundedExact.scaleIndexLeft {C : SystemOfComplexes} {k K : ℝ≥0} {m : ℕ} (c₀ c₁ : ℝ≥0)
    [Fact (1 ≤ k)] (hC : C.IsWeakBoundedExact k K m c₀) (κ : ℝ≥0) [hκ : Fact (c₀ ≤ κ * c₁)]
    (C_adm : C.Admissible) : (C.scaleIndexLeft κ).IsWeakBoundedExact k K m c₁ :=
  by
  intro c hc i hi x ε hε
  dsimp [scale_index_left, ScaleIndexLeft_apply] at x 
  haveI aux1 : Fact (k * (κ * c) ≤ κ * (k * c)) := ⟨(mul_left_comm _ _ _).le⟩
  obtain ⟨i₀, j, hi₀, hj, y, hy⟩ := hC (κ * c) _ i hi (res x) ε hε
  swap; · exact ⟨hκ.1.trans <| Fact.out _⟩
  refine' ⟨i₀, j, hi₀, hj, y, _⟩
  simp only [res_res, d_res] at hy 
  refine' hy.trans (add_le_add (mul_le_mul le_rfl _ (norm_nonneg _) K.coe_nonneg) le_rfl)
  apply C_adm.res_norm_noninc

@[simps]
def scaleIndexRight (κ : ℝ≥0) : SystemOfComplexes ⥤ SystemOfComplexes :=
  (whiskeringLeft _ _ _).obj (NNReal.mulRight κ).op

@[simp]
theorem scaleIndexRight_apply (C : SystemOfComplexes) (κ c : ℝ≥0) (i : ℕ) :
    (scaleIndexRight κ).obj C c i = C (c * κ) i :=
  rfl

/- warning: system_of_complexes.scale_index_right clashes with system_of_complexes.ScaleIndexRight -> SystemOfComplexes.scaleIndexRight
Case conversion may be inaccurate. Consider using '#align system_of_complexes.scale_index_right SystemOfComplexes.scaleIndexRightₓ'. -/
def scaleIndexRight (C : SystemOfComplexes) (κ : ℝ≥0) :=
  (scaleIndexRight κ).obj C

theorem Admissible.scaleIndexRight {C : SystemOfComplexes} (hC : C.Admissible) (κ : ℝ≥0) :
    (C.scaleIndexRight κ).Admissible :=
  { d_norm_noninc' := fun c i j hij => by apply admissible.d_norm_noninc C hC (c * κ) i j
    res_normNoninc := fun c₁ c₂ i hc => hC.res_normNoninc _ _ i (by skip; dsimp; infer_instance) }

theorem IsWeakBoundedExact.scaleIndexRight {C : SystemOfComplexes} {k K : ℝ≥0} {m : ℕ} (c₀ c₁ : ℝ≥0)
    [Fact (1 ≤ k)] (hC : C.IsWeakBoundedExact k K m c₀) (κ : ℝ≥0) [hκ : Fact (c₀ ≤ κ * c₁)]
    (C_adm : C.Admissible) : (C.scaleIndexRight κ).IsWeakBoundedExact k K m c₁ :=
  by
  intro c hc i hi x ε hε
  dsimp [scale_index_right, ScaleIndexRight_apply] at x 
  haveI aux1 : Fact (k * (c * κ) ≤ k * c * κ) := ⟨(mul_assoc _ _ _).ge⟩
  obtain ⟨i₀, j, hi₀, hj, y, hy⟩ := hC (c * κ) _ i hi (res x) ε hε
  swap; · rw [mul_comm]; exact ⟨hκ.1.trans <| Fact.out _⟩
  refine' ⟨i₀, j, hi₀, hj, y, _⟩
  simp only [res_res, d_res] at hy 
  refine' hy.trans (add_le_add (mul_le_mul le_rfl _ (norm_nonneg _) K.coe_nonneg) le_rfl)
  apply C_adm.res_norm_noninc

end ScaleIndex

end SystemOfComplexes

namespace Thm95

def rescaleFunctor' : ℕ → (ℝ≥0ᵒᵖ ⥤ SemiNormedGroupCat) ⥤ ℝ≥0ᵒᵖ ⥤ SemiNormedGroupCat
  | 0 => 𝟭 _
  | 1 => 𝟭 _
  | m + 2 => (whiskeringRight _ _ _).obj (SemiNormedGroupCat.rescale (m + 2)!)

instance rescaleFunctor'.additive : ∀ m, (rescaleFunctor' m).Additive
  | 0 => Functor.id.additive
  | 1 => Functor.id.additive
  | m + 2 => { }

def toRescale' (r : ℝ≥0) [Fact (0 < r)] :
    𝟭 (ℝ≥0ᵒᵖ ⥤ SemiNormedGroupCat) ⟶ (whiskeringRight _ _ _).obj (SemiNormedGroupCat.rescale r)
    where
  app V :=
    { app := fun c => (SemiNormedGroupCat.toRescale r).app _
      naturality' := by intro c₁ c₂ h; dsimp; ext i : 2; rfl }
  naturality' C₁ C₂ f := by ext; rfl

@[simps app]
def scale' (i j : ℝ≥0) [Fact (0 < i)] [Fact (0 < j)] :
    (whiskeringRight ℝ≥0ᵒᵖ _ _).obj (SemiNormedGroupCat.rescale i) ⟶
      (whiskeringRight ℝ≥0ᵒᵖ _ _).obj (SemiNormedGroupCat.rescale j) :=
  (whiskeringRight ℝ≥0ᵒᵖ _ _).map <| SemiNormedGroupCat.scale i j

def rescaleNatTrans' : ∀ i j, rescaleFunctor' i ⟶ rescaleFunctor' j
  | 0, 1 => 𝟙 _
  | 1, j + 2 => toRescale' (j + 2)!
  | i + 2, j + 2 => scale' (i + 2)! (j + 2)!
  | _, _ => 0

end Thm95

