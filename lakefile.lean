/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Lake
open Lake DSL

package «finite-markov-processes» where
  weakLeanArgs := #["-j2"]
  moreGlobalServerArgs := #["-j2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

require «finite-markov-kernels» from git
  "https://github.com/abenenson/finite-markov-kernels" @
    "6f3c409965c1a9d23f870ec4f9f2de9b5b79a0f3"

require «measure-discrimination» from git
  "https://github.com/abenenson/measure-discrimination" @
    "a975df146d5dae2e60338eaad5e4e612828c8805"

@[default_target]
lean_lib FiniteMarkovProcesses

@[default_target]
lean_lib FiniteMarkovProcessesExamples
