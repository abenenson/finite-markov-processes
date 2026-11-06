/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteIIDEmpiricalProbabilityDensityLargeDeviation

/-!
# Sanov's theorem for a finite alphabet

The public entry point for exact positive-sample empirical laws and their finite-alphabet
large-deviation bounds. The speed is `finiteIIDPositiveSampleSpeed n = n + 1`; the rate is
`finiteStateProbabilityDensityRelativeEntropy reference` on the closed simplex. The reference
must satisfy `reference.IsInterior`. See `docs/sanov.md` and `FiniteMarkovProcessesExamples.Sanov`.
-/
