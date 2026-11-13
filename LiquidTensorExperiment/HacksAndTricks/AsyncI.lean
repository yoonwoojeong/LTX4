import Mathlib.Tactic.Basic
import Mathlib.Mathport.Rename

#align_import hacks_and_tricks.asyncI

/-!
# `asyncI`

Porting note: in Lean 3, `asyncI { tac }` (a `meta def` by LTE) proved the first goal with
`tac` as a separate, asynchronously elaborated auxiliary lemma — purely a performance device.
Lean 3 metaprograms cannot be translated by mathport; all LTE call sites were rewritten to the
equivalent `{ tac }` before porting (`scripts/port/lean3_premathport.py`). For completeness the
tactic is provided here with the same meaning: run `tac` on the main goal.
-/

/-- Proves the main goal with the given tactics (Lean 3 did this asynchronously). -/
macro "asyncI " tac:tacticSeq : tactic => `(tactic| focus $tac)
