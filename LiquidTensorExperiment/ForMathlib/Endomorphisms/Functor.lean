import LiquidTensorExperiment.ForMathlib.Endomorphisms.Basic

#align_import for_mathlib.endomorphisms.functor

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]

namespace Functor

@[simps]
def mapEndomorphisms (F : C ⥤ D) : Endomorphisms C ⥤ Endomorphisms D
    where
  obj X := ⟨F.obj X.pt, F.map X.e⟩
  map X Y f := ⟨F.map f.f, by rw [← F.map_comp, ← F.map_comp, f.comm]⟩
  map_id' X := by ext; exact F.map_id _
  map_comp' X Y Z f g := by ext; exact F.map_comp _ _

end Functor

@[simps]
def NatTrans.mapEndomorphisms {F G : C ⥤ D} (η : F ⟶ G) : F.mapEndomorphisms ⟶ G.mapEndomorphisms
    where app T := ⟨η.app _, by tidy⟩

end CategoryTheory

