import Lake

open Lake DSL

package sharpSwitchGap where
  version := v!"1.0.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI where
  srcDir := "vendor"

@[default_target] lean_lib SharpSwitchGap
