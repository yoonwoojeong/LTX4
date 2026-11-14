import Mathlib.Algebra.Group.ULift
import LiquidTensorExperiment.ForMathlib.SemiNormedGroup
import LiquidTensorExperiment.NormedGroup.NormedWithAut

#align_import for_mathlib.SemiNormedGroup_ulift

universe v u

namespace SeminormedAddCommGroup

variable (V : Type u) [SeminormedAddCommGroup V]

instance : SeminormedAddCommGroup (ULift.{v} V) :=
  @SeminormedAddCommGroup.induced V _ (ULift.{v} V) _ <| AddEquiv.toAddMonoidHom AddEquiv.ulift

end SeminormedAddCommGroup

namespace SemiNormedGroupCat

def ulift : SemiNormedGroupCat.{u} ⥤ SemiNormedGroupCat.{max u v}
    where
  obj V := of (ULift.{v} V)
  map V W f :=
    { toFun := fun v => ⟨f v.down⟩
      map_add' := by rintro ⟨x⟩ ⟨y⟩; congr; apply f.map_add'
      bound' := by obtain ⟨C, h1, h2⟩ := f.bound; refine' ⟨C, _⟩; rintro ⟨x⟩; apply h2 }
  map_id V := by ext; rfl
  map_comp := by intros; ext; rfl

open scoped NNReal

noncomputable instance ulift.normedWithAut (r : ℝ≥0) (V : SemiNormedGroupCat.{u})
    [NormedWithAut r V] : NormedWithAut r (SemiNormedGroupCat.ulift.{v, u}.obj V)
    where
  t := ulift.mapIso NormedWithAut.t
  norm_t v := NormedWithAut.norm_t _

end SemiNormedGroupCat

