import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive

#align_import for_mathlib.homological_complex_map_d_to_d_from

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D]

variable {M : Type _} {c : ComplexShape M}

namespace CategoryTheory

namespace Functor

variable [Preadditive C] [Preadditive D]

variable (F : C ⥤ D) [Functor.Additive F] (X Y : HomologicalComplex C c)

def objXPrev (i : M) : F.obj (X.xPrev i) ≅ ((F.mapHomologicalComplex c).obj X).xPrev i :=
  Iso.refl _

theorem objXPrev_hom_eq (i : M) : (F.objXPrev X i).Hom = 𝟙 _ :=
  rfl

theorem map_prev_iso_hom (j i : M) (hij : c.Rel j i) :
    F.map (X.xPrevIso hij).Hom = (((F.mapHomologicalComplex c).obj X).xPrevIso hij).Hom := by
  obtain rfl := c.prev_eq' hij; exact F.map_id _

def objXNext {M : Type _} {c : ComplexShape M} (X : HomologicalComplex C c) (i : M) :
    F.obj (X.xNext i) ≅ ((F.mapHomologicalComplex c).obj X).xNext i :=
  Iso.refl _

theorem objXNext_hom_eq (i : M) : (F.objXNext X i).Hom = 𝟙 _ :=
  rfl

theorem map_next_iso_inv (i j : M) (hij : c.Rel i j) :
    F.map (X.xNextIso hij).inv = (((F.mapHomologicalComplex c).obj X).xNextIso hij).inv := by
  obtain rfl := c.next_eq' hij; exact F.map_id _

theorem map_dTo (i : M) : F.map (X.dTo i) = ((F.mapHomologicalComplex c).obj X).dTo i :=
  rfl

theorem dFrom_map (i : M) : F.map (X.dFrom i) = ((F.mapHomologicalComplex c).obj X).dFrom i :=
  rfl

variable {X Y}

theorem map_prev (f : X ⟶ Y) (i : M) :
    F.map (HomologicalComplex.Hom.prev f i) =
      HomologicalComplex.Hom.prev ((F.mapHomologicalComplex c).map f) i :=
  rfl

theorem map_next (f : X ⟶ Y) (i : M) :
    F.map (HomologicalComplex.Hom.next f i) =
      HomologicalComplex.Hom.next ((F.mapHomologicalComplex c).map f) i :=
  rfl

end Functor

namespace NatTrans

variable [Preadditive C] [Preadditive D] {F G : C ⥤ D} [Functor.Additive F] [Functor.Additive G]
  (φ : F ⟶ G) (X : HomologicalComplex C c)

theorem map_prev (i : M) :
    φ.app (X.xPrev i) =
      HomologicalComplex.Hom.prev ((NatTrans.mapHomologicalComplex φ c).app X) i :=
  rfl

theorem map_next (i : M) :
    φ.app (X.xNext i) =
      HomologicalComplex.Hom.next ((NatTrans.mapHomologicalComplex φ c).app X) i :=
  rfl

end NatTrans

end CategoryTheory

