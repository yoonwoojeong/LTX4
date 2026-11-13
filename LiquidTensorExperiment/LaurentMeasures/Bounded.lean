import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Analysis.NormedSpace.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Basic
import LiquidTensorExperiment.PseudoNormedGroup.Category.Default

#align_import laurent_measures.bounded

universe u

noncomputable section

open scoped BigOperators NNReal Classical

open Set

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
/-- `laurent_measures_bdd r S T c` is functions from `S` to the space of Laurent polynomials
  whose coefficients are supported in the `finset` T, and whose `r`-norm is at most `c`.
  Note that this is a finite type.  -/
structure LaurentMeasuresBdd (r : ℝ≥0) (S : FintypeCat) (T : Finset ℤ) (c : ℝ≥0) where
  toFun : S → T → ℤ
  bound' : ∑ (s) (i), ‖to_fun s i‖₊ * r ^ (i : ℤ) ≤ c

namespace LaurentMeasuresBdd

variable {r : ℝ≥0} {S S' S'' : FintypeCat.{u}} {T : Finset ℤ} {c : ℝ≥0}

instance : CoeFun (LaurentMeasuresBdd r S T c) fun _ => S → T → ℤ :=
  ⟨fun F => F.1⟩

@[ext]
theorem ext (F G : LaurentMeasuresBdd r S T c) : (F : S → T → ℤ) = G → F = G := by intro h; cases F;
  cases G; simpa

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
instance : NNNorm (LaurentMeasuresBdd r S T c) :=
  ⟨fun F => ∑ (s) (i), ‖F s i‖₊ * r ^ (i : ℤ)⟩

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (s i) -/
@[simp]
theorem nnnorm_def (F : LaurentMeasuresBdd r S T c) :
    ‖F‖₊ = ∑ (s) (i), ‖F s i‖₊ * r ^ (i : ℤ) :=
  rfl

theorem bound (F : LaurentMeasuresBdd r S T c) : ‖F‖₊ ≤ c :=
  F.2

def map (f : S ⟶ S') : LaurentMeasuresBdd r S T c → LaurentMeasuresBdd r S' T c := fun F =>
  { toFun := fun s' k => ∑ s in Finset.univ.filterₓ fun t => f t = s', F s k
    bound' :=
      calc
        ∑ (s : S') (i : T),
              ‖∑ s : S.α in Finset.univ.filterₓ fun t : S => f t = s, F s i‖₊ *
                r ^ (i : ℤ) ≤
            ∑ (s' : S') (i : T),
              ∑ s in Finset.univ.filterₓ fun t => f t = s', ‖F s i‖₊ * r ^ (i : ℤ) :=
          by
          apply Finset.sum_le_sum
          intro s' hs'
          apply Finset.sum_le_sum
          intro i hi
          rw [← Finset.sum_mul]
          exact mul_le_mul' (nnnorm_sum_le _ _) (le_refl _)
        _ =
            ∑ s' : S',
              ∑ s in Finset.univ.filterₓ fun t => f t = s', ∑ i, ‖F s i‖₊ * r ^ (i : ℤ) :=
          by
          apply Finset.sum_congr rfl
          intro s' hs'
          rw [Finset.sum_comm]
        _ = ∑ s, ∑ i, ‖F s i‖₊ * r ^ (i : ℤ) :=
          by
          rw [← Finset.sum_biUnion]
          · apply Finset.sum_congr
            · ext e
              constructor
              · simp
              · intro h
                simp only [true_and_iff, Finset.mem_univ, Finset.mem_biUnion, exists_true_left,
                  Finset.mem_filter]
                use f e
            · tauto
          · intro x hx y hy h i hi
            apply h
            simp at hi 
            rw [← hi.1, ← hi.2]
        _ ≤ c := F.bound }

@[simp]
theorem map_apply (f : S ⟶ S') (F : LaurentMeasuresBdd r S T c) (s' : S') (t : T) :
    map f F s' t = ∑ s in Finset.univ.filterₓ fun i => f i = s', F s t :=
  rfl

@[simp]
theorem map_id : (map (𝟙 S) : LaurentMeasuresBdd r S T c → LaurentMeasuresBdd r S T c) = id :=
  by
  ext F s t
  dsimp
  change ∑ s in finset.univ.filter fun i => i = s, F s t = _
  simp [Finset.sum_filter]

@[simp]
theorem map_comp (f : S ⟶ S') (g : S' ⟶ S'') :
    (map (f ≫ g) : LaurentMeasuresBdd r S T c → LaurentMeasuresBdd r S'' T c) = map g ∘ map f :=
  by
  ext F s t
  simp
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_congr
    · ext x
      constructor
      · intro h; simpa using h
      · intro h; simpa using h
    · tauto
  · intro i hi j hj h e he
    simp at he 
    apply h
    rw [← he.1, ← he.2]

theorem coeff_bound (F : LaurentMeasuresBdd r S T c) [hr : Fact (0 < r)] (s : S) (i : T) :
    ‖F s i‖₊ ≤ c * (r ^ (i : ℤ))⁻¹ :=
  by
  suffices ‖F s i‖₊ * r ^ (i : ℤ) ≤ c
    by
    convert mul_le_mul' this le_rfl using 1
    have hh : 0 < (r ^ (i : ℤ))⁻¹ := by rw [nnreal.inv_pos]; exact NNReal.zpow_pos hr.out.ne' _
    have hh' : r ^ (i : ℤ) ≠ 0 := zpow_ne_zero _ hr.out.ne'
    field_simp [this]
  calc
    ‖F s i‖₊ * r ^ (i : ℤ) ≤ ∑ i, ‖F s i‖₊ * r ^ (i : ℤ) :=
      @Finset.single_le_sum T _ _ (fun i => ‖F s i‖₊ * r ^ (i : ℤ)) _ _ _ _
    _ ≤ ‖F‖₊ :=
      (@Finset.single_le_sum S _ _ (fun s => ∑ i, ‖F s i‖₊ * r ^ (i : ℤ)) _ _ _ _)
    _ ≤ c := F.bound
  all_goals
    first
    | exact Finset.mem_univ _
    | · intros; exact zero_le'

open scoped Classical

instance (r : ℝ≥0) [Fact (0 < r)] (S : FintypeCat) (T : Finset ℤ) :
    Fintype (LaurentMeasuresBdd r S T c) :=
  by
  let lb : T → ℤ := fun i => Int.floor (-((c : ℝ) * ((r : ℝ) ^ (i : ℤ))⁻¹))
  let ub : T → ℤ := fun i => Int.ceil ((c : ℝ) * ((r : ℝ) ^ (i : ℤ))⁻¹)
  let ι : LaurentMeasuresBdd r S T c → ∀ (s : S) (i : T), Icc (lb i) (ub i) := fun F s i =>
    ⟨F s i, _⟩
  apply Fintype.ofInjective ι _
  · intro F G h
    ext s i
    apply_fun fun e => (e s i : ℤ) at h 
    exact h
  · have := F.coeff_bound s i
    change (abs (F s i) : ℝ) ≤ _ at this 
    simp only [abs_le, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_zpow] at this 
    constructor
    · replace := le_trans (Int.floor_le _) this.1
      rwa [Int.cast_le] at this 
    · replace := le_trans this.2 (Int.le_ceil _)
      rwa [Int.cast_le] at this 

instance : TopologicalSpace (LaurentMeasuresBdd r S T c) :=
  ⊥

example [Fact (0 < r)] : CompactSpace (LaurentMeasuresBdd r S T c) := by infer_instance

example : T2Space (LaurentMeasuresBdd r S T c) := by infer_instance

example : TotallyDisconnectedSpace (LaurentMeasuresBdd r S T c) := by infer_instance

end LaurentMeasuresBdd

