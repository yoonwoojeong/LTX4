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
      map := fun V W f => f.toAddMonoidHom
      map_id' := fun V => rfl
      map_comp' := fun _ _ _ f g => rfl }
  forget_comp := rfl

-- move me
instance SemiNormedGroupCat.forget₂_additive : (forget₂ SemiNormedGroupCat.{u} Ab.{u}).Additive
    where map_add' := by intros; rfl

instance SemiNormedGroupCat.metricSpace : MetricSpace V :=
  metric.of_t0_pseudo_metric_space _

instance SemiNormedGroupCat.normedAddCommGroup : NormedAddCommGroup V :=
  { (by infer_instance : SeminormedAddCommGroup V) with dist_eq := SeminormedAddCommGroup.dist_eq }

