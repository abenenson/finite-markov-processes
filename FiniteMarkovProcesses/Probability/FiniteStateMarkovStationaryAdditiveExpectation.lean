/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteJumpHistorySelfEventReward
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedDeletionDensity

/-!
# Stationary additive expectations of finite-state Markov histories

This module transports a generic transition-plus-dwell reward through exact deletion of
uniformization self-events. Under a stationary initial law, its expectation on the canonical
physical finite-jump carrier is exactly the observation duration times the sum of its stationary
transition and occupation rates.

The theorem retains both sectors before evaluating their stationary means. It supplies no
thermodynamic interpretation for either reward.

## Main Results

- `finiteStateMarkovAdditiveHistoryReward_deleteSelfEvents_eq`: additive rewards with zero
  diagonal transition reward are invariant under deletion of virtual self-events.
- `integrable_finiteStateMarkovAdditiveHistoryReward_jumpDensity`: every such finite-state reward
  is integrable under the canonical physical history law.
- `integral_finiteStateMarkovAdditiveHistoryReward_eq_stationaryRate`: exact physical-history
  expectation of a stationary additive reward.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

omit [Fintype State] in
/-- Every additive transition-plus-dwell reward with zero diagonal transition reward is invariant
under canonical self-event deletion. -/
theorem finiteStateMarkovAdditiveHistoryReward_deleteSelfEvents_eq
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (hSelf : ∀ state, transitionReward state state = 0)
    (T : ℝ) (history : FiniteJumpHistory State) :
    finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T
        (FiniteJumpHistory.deleteSelfEvents history) =
      finiteStateMarkovAdditiveHistoryReward transitionReward stateReward T history := by
  rcases history with ⟨eventCount, states, times⟩
  change finiteStateMarkovAdditiveSliceReward transitionReward stateReward T
      (FiniteJumpHistory.deleteSelfEventsSlice states times).states
      (FiniteJumpHistory.deleteSelfEventsSlice states times).jumpTimes =
    finiteStateMarkovAdditiveSliceReward transitionReward stateReward T states times
  unfold finiteStateMarkovAdditiveSliceReward
  rw [FiniteJumpHistory.sum_transitionReward_deleteSelfEventsSlice
    states times transitionReward hSelf]
  rw [FiniteJumpHistory.sum_dwellReward_deleteSelfEventsSlice]

/-- Every finite-state transition-plus-dwell reward with zero diagonal transition reward is
integrable under the canonical physical finite-jump law at a nonnegative horizon. -/
theorem integrable_finiteStateMarkovAdditiveHistoryReward_jumpDensity
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) (hSelf : ∀ state, transitionReward state state = 0) :
    Integrable
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration)
      (finiteStateMarkovJumpDensityMeasure initial generator duration) := by
  rw [← map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator duration.coe_nonneg]
  rw [integrable_map_measure
    (measurable_finiteStateMarkovAdditiveHistoryReward
      transitionReward stateReward duration).aestronglyMeasurable
    FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable]
  have hFunction :
      (finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration) ∘
          FiniteJumpHistory.deleteSelfEvents =
        finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration := by
    funext history
    exact finiteStateMarkovAdditiveHistoryReward_deleteSelfEvents_eq
      transitionReward stateReward hSelf duration history
  rw [hFunction]
  exact integrable_finiteStateMarkovAdditiveHistoryReward_uniformizedDensity
    initial generator transitionReward stateReward duration

/-- The expectation of a stationary transition-plus-dwell reward on the canonical physical
finite-jump law is exactly duration times its complete stationary rate. -/
theorem integral_finiteStateMarkovAdditiveHistoryReward_eq_stationaryRate
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (generator : FiniteStateMarkovGenerator State)
    (stationary : FiniteStateMarkovStationaryDistribution generator)
    (transitionReward : State → State → ℝ) (stateReward : State → ℝ)
    (duration : ℝ≥0) (hSelf : ∀ state, transitionReward state state = 0) :
    (∫ history : FiniteJumpHistory State,
        finiteStateMarkovAdditiveHistoryReward
          transitionReward stateReward duration history
      ∂finiteStateMarkovJumpDensityMeasure stationary.pmf generator duration) =
      (duration : ℝ) *
        (∑ source, ∑ target,
            (stationary.weight source : ℝ) * (generator.rate source target : ℝ) *
              transitionReward source target +
          ∑ state, (stationary.weight state : ℝ) * stateReward state) := by
  rw [← map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    stationary.pmf generator duration.coe_nonneg]
  rw [integral_map FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable
    (measurable_finiteStateMarkovAdditiveHistoryReward
      transitionReward stateReward duration).aestronglyMeasurable]
  have hFunction :
      (fun history : FiniteJumpHistory State ↦
        finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration
          (FiniteJumpHistory.deleteSelfEvents history)) =
        finiteStateMarkovAdditiveHistoryReward transitionReward stateReward duration := by
    funext history
    exact finiteStateMarkovAdditiveHistoryReward_deleteSelfEvents_eq
      transitionReward stateReward hSelf duration history
  rw [hFunction]
  have hIntegrable :=
    integrable_finiteStateMarkovAdditiveHistoryReward_uniformizedDensity
      stationary.pmf generator transitionReward stateReward duration
  rw [integral_finiteStateMarkovAdditiveHistoryReward_densityMeasure
    generator stationary transitionReward stateReward duration hIntegrable]
  rw [tsum_finiteStateMarkovUniformizedCountAdditiveRewardIntegral_stationary]
  rw [show ((generator.uniformizationRate : ℝ) * (duration : ℝ)) *
      uniformizedStationaryTransitionReward generator stationary transitionReward =
    (duration : ℝ) * ((generator.uniformizationRate : ℝ) *
      uniformizedStationaryTransitionReward generator stationary transitionReward) by ring]
  rw [uniformizationRate_mul_uniformizedStationaryTransitionReward
    generator stationary transitionReward hSelf]
  ring

end FiniteMarkovProcesses.Probability
