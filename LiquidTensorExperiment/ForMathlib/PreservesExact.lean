import Mathlib.CategoryTheory.Abelian.Exact
import LiquidTensorExperiment.ForMathlib.SplitExact

#align_import for_mathlib.preserves_exact

universe v u u'

namespace CategoryTheory

namespace Functor

open CategoryTheory.Limits

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem map_shortExact (h : ShortExact f g) : ShortExact (F.map f) (F.map g) :=
  by
  rcases h with ⟨hf, hg, hfg⟩
  have : mono (F.map f) := by
    rw [(abelian.tfae_mono X f).out 0 2] at hf 
    rw [(abelian.tfae_mono (F.obj X) (F.map f)).out 0 2]
    have := F.map_exact _ _ hf; rwa [F.map_zero] at this 
  have : epi (F.map g) := by
    rw [(abelian.tfae_epi Z g).out 0 2] at hg 
    rw [(abelian.tfae_epi (F.obj Z) (F.map g)).out 0 2]
    have := F.map_exact _ _ hg; rwa [F.map_zero] at this 
  refine' ⟨F.map_exact f g hfg⟩

end Functor

end CategoryTheory

