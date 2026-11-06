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
    "de78502c3f191840bc6b3ff55d2be5e9d66ca122"

require «measure-discrimination» from git
  "https://github.com/abenenson/measure-discrimination" @
    "549acb4aa11ac99656db832ab2a08fbc1df5a5e3"

@[default_target]
lean_lib FiniteMarkovProcesses

@[default_target]
lean_lib FiniteMarkovProcessesExamples
