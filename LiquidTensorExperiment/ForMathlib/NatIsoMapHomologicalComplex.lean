import Mathlib.Algebra.Homology.Additive

#align_import for_mathlib.nat_iso_map_homological_complex

/-!
Porting note: LTE's `category_theory.nat_iso.map_homological_complex` was upstreamed to
mathlib with the same name and the same definition (`hom`/`inv` are
`nat_trans.map_homological_complex e.hom c` / `... e.inv c`); in Lean 4 it is
`CategoryTheory.NatIso.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive`, so it is
not redeclared here. (mathport also replaced it by a reference to the mathlib declaration.)
-/
