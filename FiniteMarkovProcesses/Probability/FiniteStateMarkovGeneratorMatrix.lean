/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpLaw

/-!
# Matrix convention for finite-state Markov generators

This module relates the repository's zero-diagonal nonnegative jump-rate convention with a
separately stored escape rate to the standard signed generator-matrix convention.  Off-diagonal
entries are the jump rates, diagonal entries are negative escape rates, and every row sums to zero.

## Main results

- `FiniteStateMarkovGenerator.matrixEntry_self`: the diagonal is negative escape rate.
- `FiniteStateMarkovGenerator.matrixEntry_of_ne`: off-diagonal matrix entries are jump rates.
- `FiniteStateMarkovGenerator.sum_matrixEntry`: every matrix row sums to zero.
-/

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Signed generator-matrix entry corresponding to the repository's nonnegative off-diagonal rate
and separate escape-rate convention. -/
def FiniteStateMarkovGenerator.matrixEntry
    (generator : FiniteStateMarkovGenerator State) (source target : State) : ℝ :=
  if source = target then -(generator.escapeRate source : ℝ)
  else generator.rate source target

/-- A signed generator-matrix diagonal is the negative escape rate. -/
theorem FiniteStateMarkovGenerator.matrixEntry_self
    (generator : FiniteStateMarkovGenerator State) (state : State) :
    generator.matrixEntry state state = -(generator.escapeRate state : ℝ) := by
  simp [FiniteStateMarkovGenerator.matrixEntry]

/-- Every signed off-diagonal generator-matrix entry is the corresponding nonnegative jump rate. -/
theorem FiniteStateMarkovGenerator.matrixEntry_of_ne
    (generator : FiniteStateMarkovGenerator State) {source target : State}
    (hDistinct : source ≠ target) :
    generator.matrixEntry source target = generator.rate source target := by
  simp [FiniteStateMarkovGenerator.matrixEntry, hDistinct]

/-- Every signed generator-matrix row sums to zero. -/
theorem FiniteStateMarkovGenerator.sum_matrixEntry
    (generator : FiniteStateMarkovGenerator State) (source : State) :
    ∑ target, generator.matrixEntry source target = 0 := by
  classical
  unfold FiniteStateMarkovGenerator.matrixEntry
  calc
    _ = (∑ target, if source = target then
          -(generator.escapeRate source : ℝ) else 0) +
        ∑ target, (generator.rate source target : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro target
      by_cases hTarget : source = target
      · subst target
        simp [generator.rate_self]
      · simp [hTarget]
    _ = -(generator.escapeRate source : ℝ) +
        ∑ target, (generator.rate source target : ℝ) := by
      rw [Fintype.sum_ite_eq source]
    _ = 0 := by
      simp [FiniteStateMarkovGenerator.escapeRate]

end FiniteMarkovProcesses.Probability
