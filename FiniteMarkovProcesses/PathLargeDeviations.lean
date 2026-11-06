/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVTheoremFourOneLargeDeviationRepresentation
import
FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVCorollaryFourSixteenLargeDeviationRepresentation
import FiniteMarkovProcesses.Probability.FiniteStateMarkovIIDHybridExponential

/-!
# Finite-state Markov path large deviations

The terminal constructors for Renger (2018), Theorems 4.1 and 4.2 and Corollary 4.16, retain
actual microscopic laws, measurable hybrid-BV observations, complete rates, and both LDP bounds.
The initial-data contracts of the three results remain distinct. Theorem 4.2 is available through
Theorem 4.1's dependency; its initial LDP is a supplied premise, not a consequence of a label.

The IID exponential confidence theorem is a separate finite-particle estimate for the strong-L1
norm of the total hybrid observation around its unconditional generated mean.

See `docs/path-large-deviations.md` and `docs/theorem-map.md` for assumptions and conventions.
-/
