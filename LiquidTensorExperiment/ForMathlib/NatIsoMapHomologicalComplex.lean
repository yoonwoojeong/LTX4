import Mathlib.Algebra.Homology.Additive

#align_import for_mathlib.nat_iso_map_homological_complex

namespace CategoryTheory

open Category

#print CategoryTheory.NatIso.mapHomologicalComplex /-
def NatIso.mapHomologicalComplex {ι V W : Type _} [Category V] [Category W] [Preadditive V]
    [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (e : F ≅ G) (c : ComplexShape ι) :
    F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c
    where
  Hom := NatTrans.mapHomologicalComplex e.Hom c
  inv := NatTrans.mapHomologicalComplex e.inv c
  hom_inv_id' := by ext X i; dsimp; simp only [iso.hom_inv_id_app]
  inv_hom_id' := by ext X i; dsimp; simp only [iso.inv_hom_id_app]
-/

end CategoryTheory

