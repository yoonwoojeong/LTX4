import Mathlib
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    if n.isInternal then none else some n.toString
  IO.FS.writeFile ".lake/mathlib-names.txt" ("\n".intercalate names)
