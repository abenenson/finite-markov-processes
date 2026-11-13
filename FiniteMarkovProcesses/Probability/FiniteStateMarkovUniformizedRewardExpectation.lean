/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedStationaryRewards

/-!
# Expected rewards of finite-state uniformized chains

This module defines the dynamic-programming expectation of an additive transition reward over a
fixed number of virtual events. When the initial law is stationary, the expectation is exactly the
event count times the one-event stationary reward.

The definition is an expectation recursion, not yet a timed virtual-history probability law. Its
role is to isolate the finite-chain calculation required by a later Poisson-clock construction and
physical self-event deletion theorem.

## Main Results

- `uniformizedCumulativeTransitionRewardExpectation`: finite-event reward recursion.
- `uniformizedCumulativeTransitionRewardExpectation_stationary`: exact stationary linear growth.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Mean reward of one uniformized event from an arbitrary source-state law. -/
noncomputable def uniformizedTransitionRewardExpectation
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → State → ℝ) : ℝ :=
  ∑ source, ∑ target,
    (law source).toReal * (generator.uniformizedTransitionPMF source target).toReal *
      reward source target

/-- Dynamic-programming expectation of the cumulative transition reward over a fixed number of
uniformized virtual events. -/
noncomputable def uniformizedCumulativeTransitionRewardExpectation
    (generator : FiniteStateMarkovGenerator State) (law : PMF State)
    (reward : State → State → ℝ) : ℕ → ℝ
  | 0 => 0
  | eventCount + 1 =>
      uniformizedTransitionRewardExpectation generator law reward +
        uniformizedCumulativeTransitionRewardExpectation generator
          (generator.uniformizedAdvancePMF law) reward eventCount

/-- The one-event reward from a physical stationary PMF is the named stationary transition
reward. -/
theorem uniformizedTransitionRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ) :
    uniformizedTransitionRewardExpectation generator stationary.pmf reward =
      uniformizedStationaryTransitionReward generator stationary reward := by
  unfold uniformizedTransitionRewardExpectation uniformizedStationaryTransitionReward
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro target _
  simp only [FiniteStateMarkovStationaryDistribution.pmf_apply, ENNReal.coe_toReal]

/-- At stationarity, the expected cumulative reward is exactly the event count times the
one-event stationary reward. -/
theorem uniformizedCumulativeTransitionRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ) (eventCount : ℕ) :
    uniformizedCumulativeTransitionRewardExpectation generator stationary.pmf reward eventCount =
      (eventCount : ℝ) *
        uniformizedStationaryTransitionReward generator stationary reward := by
  induction eventCount with
  | zero => simp [uniformizedCumulativeTransitionRewardExpectation]
  | succ eventCount inductionHypothesis =>
      rw [uniformizedCumulativeTransitionRewardExpectation,
        generator.uniformizedAdvancePMF_stationary stationary,
        uniformizedTransitionRewardExpectation_stationary,
        inductionHypothesis]
      push_cast
      ring

end FiniteMarkovProcesses.Probability
