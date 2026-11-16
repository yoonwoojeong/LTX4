import Mathlib.Data.Setoid.Basic
import Mathlib.Topology.Homeomorph
-- Porting note: provides `QuotientMap.homeomorph`, see below
import Mathlib.Topology.ContinuousFunction.Basic

#align_import for_mathlib.quotient_map

/-! Porting note: LTE's `quotient_map.homeomorph` (`Quotient (Setoid.ker f) ≃ₜ β` for a quotient map
`f`) was upstreamed to mathlib as `QuotientMap.homeomorph` with the same statement, so LTE's copy is
removed; files importing this one get mathlib's declaration. -/
