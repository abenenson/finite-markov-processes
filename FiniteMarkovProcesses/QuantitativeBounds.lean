/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVRateStability
import FiniteMarkovProcesses.RelativeEntropy.LargeDeviationConcentration
import FiniteMarkovProcesses.RelativeEntropy.PoissonRateBudgetCoercivity
import FiniteMarkovProcesses.Probability.FiniteStateMarkovIIDHybridExponential
import FiniteMarkovProcesses.Probability.FiniteSampleConfidence

/-!
# Quantitative stability and particle probability bounds

A finite dynamic-rate budget controls the integrated flow residual and the distance to an
admissible same-generator-flow reference, retaining the actual initial-density error.
The deterministic estimates include strong-L1 distance, terminal-left traces, and derivative
variation. They do not assume that sampled finite-particle paths have finite action.

A closed-event rate gap and an existing LDP upper bound give an eventual exponential mass bound
with strict exponent slack. Its cutoff remains existential. Separately, the original-IID
strong-L1 Chernoff estimate holds for every positive particle count and supplied capped tilt.
Rational particle budgets turn supplied polynomial or exponential envelopes into confidence bounds.

The scalar entropy/Hellinger, finite-state contraction, and Chernoff arguments are classical;
the density/ordered-flow action is due to Renger (2018). See the theorem map and path guide for
exact hypotheses and the distinctions between these conclusions.
-/
