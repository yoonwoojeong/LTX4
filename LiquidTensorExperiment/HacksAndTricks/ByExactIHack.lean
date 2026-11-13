import Mathlib.Tactic.Basic
import Mathlib.Mathport.Rename

#align_import hacks_and_tricks.by_exactI_hack

/-!
# The zero-width-space `by exactI` hack

Porting note: in Lean 3 this file (a "brilliant hack by Gabriel Ebner") defined a user notation
so that a zero-width space before an expression `e` meant `by exactI e`, i.e. elaborate `e`
after resetting the type-class instance cache. Lean 4 always uses the current local instances,
so no such device is needed: `by exactI e` is just `e`. The LTE call sites were expanded to
`(by exactI e)` before porting (`scripts/port/lean3_premathport.py`; the resulting Lean 3
declarations were checked to be identical up to bound-variable names), which mathport
translates to `e`. This module therefore defines nothing.
-/
