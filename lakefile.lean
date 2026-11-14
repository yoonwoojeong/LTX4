import Lake
open Lake DSL

/-!
Lean 4 port of the Liquid Tensor Experiment, produced with mathport.

mathlib4 is pinned to `79254c9790` (2023-11-29), the revision paired with mathport
`nightly-2023-11-30-10`. It is the latest mathlib4 that still contains the old
homology API (`Algebra.Homology.Exact`, `CategoryTheory.Abelian.Homology`, old
`Functor.LeftDerived`) on which LTE is built; later mathlib4 (including `v3-eol`)
removed it. Upgrading mathlib is a separate, later step.
-/

package liquid_tensor_experiment

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "79254c9790cbd7c5f682271eb9f951c6fc60ecd5"

@[default_target]
lean_lib LiquidTensorExperiment
