/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.RelativeEntropy.RengerHybridBVZeroRateEvolution

/-!
# Complete-rate zero sets and actual Markov mean evolution

For a finite constant nonnegative generator and positive horizon, the complete hybrid-BV rate
vanishes exactly on actual generated mean paths whose initial density has zero supplied initial
cost. The initial cost is arbitrary and extended nonnegative. The mean-path map is injective;
a singleton initial zero set yields a singleton path zero set.

This deterministic classification retains the full hybrid path and its recovered boundary data.
It does not supply a probability estimate. The finite-state forward uniqueness and scalar entropy
equality arguments are classical; the density/ordered-flux action is due to Renger (2018).
-/

@[expose] public section
