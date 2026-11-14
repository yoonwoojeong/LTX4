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
  -- Porting note: `rcases h with ⟨hf, hg, hfg⟩` destructs the instance fields too deeply
  have hf := h.mono
  have hg := h.epi
  have hfg := h.exact
  have : Mono (F.map f) := by
    -- Porting note: `List.TFAE.out` needs the statement to be given explicitly in Lean 4
    rw [((Abelian.tfae_mono X f).out 0 2 : Mono f ↔ Exact (0 : X ⟶ X) f)] at hf 
    rw [((Abelian.tfae_mono (F.obj X) (F.map f)).out 0 2 :
      Mono (F.map f) ↔ Exact (0 : F.obj X ⟶ F.obj X) (F.map f))]
    have := F.map_exact _ _ hf; rwa [F.map_zero] at this 
  have : Epi (F.map g) := by
    rw [((Abelian.tfae_epi Z g).out 0 2 : Epi g ↔ Exact g (0 : Z ⟶ Z))] at hg 
    rw [((Abelian.tfae_epi (F.obj Z) (F.map g)).out 0 2 :
      Epi (F.map g) ↔ Exact (F.map g) (0 : F.obj Z ⟶ F.obj Z))]
    have := F.map_exact _ _ hg; rwa [F.map_zero] at this 
  refine' ⟨F.map_exact f g hfg⟩

end Functor

end CategoryTheory

