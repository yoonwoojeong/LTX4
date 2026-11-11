import Lake
open Lake DSL

/-!
Lean 4 port of the Liquid Tensor Experiment, produced with mathport (`v3-eol`).

The mathlib4 revision is pinned to `v3-eol`, the last mathlib4 release that still
carries the `#align` data mathport relies on. Upgrading to a modern mathlib4 is a
separate, later step (`lake update` after changing the `require` below).
-/

package «liquid-tensor-experiment» where
  leanOptions := #[⟨`autoImplicit, true⟩, ⟨`relaxedAutoImplicit, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v3-eol"

@[default_target]
lean_lib LiquidTensorExperiment
