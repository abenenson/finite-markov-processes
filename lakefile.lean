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
    "56a005855ea17e0b0958f73ec801ae140b0a1679"

require «finite-markov-kernels» from git
  "https://github.com/abenenson/finite-markov-kernels" @
    "e37ed564fcc193ace7c48a94cf8f7090c2a31390"

require «measure-discrimination» from git
  "https://github.com/abenenson/measure-discrimination" @
    "723fcf3128700035d6a23d2891970491ac03f392"

@[default_target]
lean_lib FiniteMarkovProcesses

@[default_target]
lean_lib FiniteMarkovProcessesExamples
