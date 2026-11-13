import Mathlib.Mathport.Rename

/-! Explicit name alignments for LTE declarations whose default mathport translation
collides with another LTE declaration (Lean 3 `condensed.*` and `Condensed.*`
both map to Lean 4 `Condensed.*`). -/

set_option align.precheck false

#align condensed.evaluation_additive Condensed.evaluation_additive'
