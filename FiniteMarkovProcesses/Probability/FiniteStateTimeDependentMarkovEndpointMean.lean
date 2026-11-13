/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovIntermediateMarginal
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanContinuity

/-!
# Projective mean of bounded time-dependent Markov jump laws

The expected occupied-state coordinate at every nonnegative time within the physical
horizon is exactly the real coordinate of the resummed endpoint PMF at that time.  The result
composes the exact reduced-history projective marginal with the literal state-membership
observable.

The rate compensator remains a separate result.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- The physical source's expected density at any nonnegative time within its horizon is exactly
the resummed endpoint PMF coordinate at that time. -/
theorem finiteStateTimeDependentMarkovMeanDensityAt_eq_endpointPMF
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration time : ℝ≥0) (hTimeDuration : time ≤ duration) (observed : State) :
    finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration time observed =
      (finiteStateTimeDependentMarkovEndpointPMF
        initial rates time observed).toReal := by
  unfold finiteStateTimeDependentMarkovMeanDensityAt
  have hIndicator :
      (fun history : FiniteJumpHistory State ↦
        finiteJumpHistoryStateMembershipAtTime time observed history) =
      ((fun history : FiniteJumpHistory State ↦ history.stateAtTime time) ⁻¹'
          {observed}).indicator
        (1 : FiniteJumpHistory State → ℝ) := by
    funext history
    unfold finiteJumpHistoryStateMembershipAtTime
      FiniteJumpHistory.stateMembershipIndicator Set.indicator
    by_cases hState : history.stateAtTime time = observed
    · simp only [hState, Set.mem_preimage, Set.mem_singleton_iff, ite_true,
        Pi.one_apply]
    · simp only [Set.mem_preimage, Set.mem_singleton_iff, hState, ite_false,
        Pi.one_apply]
  rw [hIndicator]
  rw [integral_indicator_one
    (FiniteJumpHistory.measurable_stateAtTime time
      (measurableSet_singleton observed))]
  unfold Measure.real
  rw [← Measure.map_apply (FiniteJumpHistory.measurable_stateAtTime time)
    (measurableSet_singleton observed)]
  rw [map_stateAtTime_finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial rates duration time hTimeDuration]
  rw [PMF.toMeasure_apply_singleton
    (finiteStateTimeDependentMarkovEndpointPMF initial rates time)
    observed (measurableSet_singleton observed)]

/-- The horizon-only endpoint-mean theorem is the terminal specialization of the projective
mean identity. -/
theorem finiteStateTimeDependentMarkovMeanDensityAt_horizon_eq_endpointPMF
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observed : State) :
    finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration duration observed =
      (finiteStateTimeDependentMarkovEndpointPMF
        initial rates duration observed).toReal := by
  exact finiteStateTimeDependentMarkovMeanDensityAt_eq_endpointPMF
    initial rates duration duration le_rfl observed

end

end FiniteMarkovProcesses.Probability
