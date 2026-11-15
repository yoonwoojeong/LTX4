import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Analysis.Normed.Group.SemiNormedGroupCat.Completion

#align_import for_mathlib.SemiNormedGroup

noncomputable section

universe u

open CategoryTheory Opposite

variable (V : SemiNormedGroupCat.{u}) [CompleteSpace V] [SeparatedSpace V]

-- move me
instance SemiNormedGroupCat.forget₂ : HasForget₂ SemiNormedGroupCat.{u} Ab.{u}
    where
  forget₂ :=
    { obj := fun V => AddCommGroupCat.of V
      map := fun {X Y} (f : X ⟶ Y) =>
        -- Porting note: explicit types needed since `⟶` in `SemiNormedGroupCat` is not unfolded
        (NormedAddGroupHom.toAddMonoidHom (V₁ := X) (V₂ := Y) f : (X : Type u) →+ (Y : Type u))
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  forget_comp := rfl

-- move me
instance SemiNormedGroupCat.forget₂_additive :
    (CategoryTheory.forget₂ SemiNormedGroupCat.{u} Ab.{u}).Additive where
  map_add := by
    intros
    apply AddMonoidHom.ext
    intro x
    rfl

instance SemiNormedGroupCat.metricSpace : MetricSpace V :=
  MetricSpace.ofT0PseudoMetricSpace _

instance SemiNormedGroupCat.normedAddCommGroup : NormedAddCommGroup V :=
  { (by infer_instance : SeminormedAddCommGroup V) with
    dist_eq := SeminormedAddCommGroup.dist_eq
    -- Porting note: in Lean 4 the `MetricSpace` field `eq_of_dist_eq_zero` must be supplied
    eq_of_dist_eq_zero := fun {x y} h => (SemiNormedGroupCat.metricSpace V).eq_of_dist_eq_zero h }

