/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedRewardExpectation
import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Poissonized stationary rewards of finite-state Markov chains

This module integrates the fixed-event dynamic-programming reward expectation against the actual
Poisson count law of the uniformization clock. For rewards that vanish on virtual self-events, the
result is exactly the observation duration times the physical directed-rate reward.

This theorem closes the count-summation part of uniformization. It does not yet construct ordered
event times, delete virtual self-events on a history carrier, or identify the resulting pushforward
with the canonical physical finite-jump law.

## Main Results

- `integrable_uniformizedCumulativeTransitionRewardExpectation_stationary`: integrability under
  the uniform-clock Poisson count.
- `integral_uniformizedCumulativeTransitionRewardExpectation_stationary`: exact physical-rate
  expectation after Poissonization.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- The fixed-event stationary reward expectation is integrable under the uniform-clock Poisson
count law. -/
theorem integrable_uniformizedCumulativeTransitionRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ) (duration : ℝ≥0) :
    Integrable
      (uniformizedCumulativeTransitionRewardExpectation generator stationary.pmf reward)
      (poissonMeasure (generator.uniformizationRate * duration)) := by
  have hFunction :
      uniformizedCumulativeTransitionRewardExpectation generator stationary.pmf reward =
        fun eventCount : ℕ ↦
          (eventCount : ℝ) *
            uniformizedStationaryTransitionReward generator stationary reward := by
    funext eventCount
    exact uniformizedCumulativeTransitionRewardExpectation_stationary
      generator stationary reward eventCount
  rw [hFunction]
  exact (integrable_poissonCount (generator.uniformizationRate * duration)).mul_const _

/-- Poissonizing a stationary uniformized-chain reward that vanishes on virtual self-events gives
exactly duration times its physical directed-rate reward. -/
theorem integral_uniformizedCumulativeTransitionRewardExpectation_stationary
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (reward : State → State → ℝ) (duration : ℝ≥0)
    (hSelf : ∀ state, reward state state = 0) :
    ∫ eventCount : ℕ,
        uniformizedCumulativeTransitionRewardExpectation generator stationary.pmf reward
          eventCount
      ∂poissonMeasure (generator.uniformizationRate * duration) =
      (duration : ℝ) *
        ∑ source, ∑ target,
          (stationary.weight source : ℝ) * (generator.rate source target : ℝ) *
            reward source target := by
  simp_rw [uniformizedCumulativeTransitionRewardExpectation_stationary]
  rw [integral_mul_const, integral_poissonCount]
  rw [NNReal.coe_mul]
  calc
    (generator.uniformizationRate : ℝ) * (duration : ℝ) *
        uniformizedStationaryTransitionReward generator stationary reward =
        (duration : ℝ) *
          ((generator.uniformizationRate : ℝ) *
            uniformizedStationaryTransitionReward generator stationary reward) := by ring
    _ = _ := by
      rw [uniformizationRate_mul_uniformizedStationaryTransitionReward
        generator stationary reward hSelf]

end FiniteMarkovProcesses.Probability
