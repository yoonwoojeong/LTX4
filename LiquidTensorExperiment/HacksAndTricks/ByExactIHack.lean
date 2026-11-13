-- brilliant hack by Gabriel Ebner

#align_import hacks_and_tricks.by_exactI_hack

-- thanks!!
-- files that import this file can use the zero-width space char
-- to reset the TC instance cache, and avoid `by exactI` kludges
open Tactic Expr

open Lean

open Lean.Parser

open Interactive

open Tactic

-- zero-width space Unicode char
@[user_notation]
unsafe def exact_notation (_ : parse <| tk "​") (e : parse (lean.parser.pexpr 0)) : parser pexpr :=
  do
  let expr.macro d [_] ← pure ``(by skip)
  pure <| expr.macro d [const `tactic.interactive.exactI [] (cast undefined e)]

