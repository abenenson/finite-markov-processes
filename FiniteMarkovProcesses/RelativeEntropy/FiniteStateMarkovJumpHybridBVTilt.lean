/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import FiniteMarkovProcesses.RelativeEntropy.FiniteStateJumpDirectionalFlowLDPBoundary
public import FiniteMarkovProcesses.Probability.FiniteStateMarkovExponentialTimeTilt
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovUniformizedHistoryLaw

/-!
# Exponential jump-rate tilt induced by a hybrid-BV dual test

This module turns the finite family of continuous directional-flow dual tests into the explicit
bounded measurable transition exponent and normalized time-dependent virtual jump law required
by the path-space exponential-moment argument.

The construction preserves zero diagonal physical rates and keeps the finite global test bound
visible. It does not yet identify self-event deletion with an exponentially tilted reduced
physical law or assert the martingale identity.

## Main results

- `rengerDirectionalFlowDualTestTransitionExponent`: the full state-pair exponent.
- `rengerDirectionalFlowDualTestExponentialTimeTilt`: the induced time-dependent rate family.
- `rengerDirectionalFlowDualTestUniformizedHistoryProbabilityMeasure`: its normalized virtual
  finite-history law.
-/

@[expose] public section

namespace FiniteMarkovProcesses.InformationTheory

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction ENNReal NNReal

open FiniteMarkovProcesses.Probability

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  {duration : ℝ}

/-- Bounded-continuous realization of one compactly supported directional dual test. -/
noncomputable def rengerDirectionalFlowDualTestBoundedMap
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) : ℝ →ᵇ ℝ :=
  ofCompactSupport (test transition).1 (test transition).1.continuous
    (test transition).1.hasCompactSupport

/-- Finite explicit upper bound for every channel value in one dual-test family. -/
noncomputable def rengerDirectionalFlowDualTestUpperBound
    (test : RengerDirectionalFlowHybridBVDualTest State duration) : ℝ :=
  ∑ transition : FiniteStateOrderedOffDiagonalTransition State,
    ‖rengerDirectionalFlowDualTestBoundedMap test transition‖

/-- A channel test is pointwise bounded above by the finite family-wide norm sum. -/
theorem rengerDirectionalFlowDualTest_le_upperBound
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (transition : FiniteStateOrderedOffDiagonalTransition State) (time : ℝ) :
    (test transition).1 time ≤ rengerDirectionalFlowDualTestUpperBound test := by
  let boundedTest := rengerDirectionalFlowDualTestBoundedMap test transition
  calc
    (test transition).1 time ≤ |(test transition).1 time| := le_abs_self _
    _ = ‖boundedTest time‖ := by
      change |(test transition).1 time| = |(test transition).1 time|
      rfl
    _ ≤ ‖boundedTest‖ := boundedTest.norm_coe_le_norm time
    _ ≤ ∑ candidate : FiniteStateOrderedOffDiagonalTransition State,
        ‖rengerDirectionalFlowDualTestBoundedMap test candidate‖ := by
      exact Finset.single_le_sum
        (fun candidate _ ↦ norm_nonneg
          (rengerDirectionalFlowDualTestBoundedMap test candidate))
        (Finset.mem_univ transition)

/-- Full state-pair exponent obtained from the ordered off-diagonal dual tests, with a literal
zero diagonal. -/
noncomputable def rengerDirectionalFlowDualTestTransitionExponent
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    FiniteStateTransitionExponent State where
  exponent := fun time source target ↦
    if hNe : source ≠ target then (test ⟨(source, target), hNe⟩).1 time else 0
  measurable_exponent := fun source target ↦ by
    by_cases hNe : source ≠ target
    · simpa [hNe] using
        (test ⟨(source, target), hNe⟩).1.continuous.measurable
    · simp [hNe]
  upperBound := rengerDirectionalFlowDualTestUpperBound test
  exponent_le_upperBound := fun time source target ↦ by
    by_cases hNe : source ≠ target
    · simpa [hNe] using rengerDirectionalFlowDualTest_le_upperBound
        test ⟨(source, target), hNe⟩ time
    · simpa [hNe, rengerDirectionalFlowDualTestUpperBound] using!
        Finset.sum_nonneg fun transition _ ↦
        norm_nonneg (rengerDirectionalFlowDualTestBoundedMap test transition)

/-- Time-dependent physical rates induced by exponential tilting with one hybrid-BV dual test. -/
noncomputable def rengerDirectionalFlowDualTestExponentialTimeTilt
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration) :
    FiniteStateTimeDependentMarkovRate State :=
  generator.exponentialTimeTilt
    (rengerDirectionalFlowDualTestTransitionExponent test)

/-- The induced nonnegative rate is exactly the generic exponential time tilt. -/
theorem rengerDirectionalFlowDualTestExponentialTimeTilt_rate
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (time : ℝ) (source target : State) :
    (rengerDirectionalFlowDualTestExponentialTimeTilt generator test).rate
        time source target =
      generator.rate source target *
        (rengerDirectionalFlowDualTestTransitionExponent test).exponentialMultiplier
          time source target :=
  rfl

/-- Real-valued off-diagonal form of the dual-test tilted rate. -/
theorem coe_rengerDirectionalFlowDualTestExponentialTimeTilt_rate_of_ne_real
    (generator : FiniteStateMarkovGenerator State)
    (test : RengerDirectionalFlowHybridBVDualTest State duration)
    (time : ℝ) {source target : State} (hNe : source ≠ target) :
    ((rengerDirectionalFlowDualTestExponentialTimeTilt generator test).rate
        time source target : ℝ) =
      (generator.rate source target : ℝ) *
        Real.exp ((test ⟨(source, target), hNe⟩).1 time) := by
  unfold rengerDirectionalFlowDualTestExponentialTimeTilt
  rw [generator.coe_exponentialTimeTilt_rate]
  simp [rengerDirectionalFlowDualTestTransitionExponent, hNe]

/-- Normalized virtual finite-history law generated by the dual-test exponential rate tilt. -/
noncomputable def rengerDirectionalFlowDualTestUniformizedHistoryProbabilityMeasure
    [MeasurableSpace State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (durationNNReal : ℝ≥0)
    (test : RengerDirectionalFlowHybridBVDualTest State durationNNReal) :
    ProbabilityMeasure (FiniteJumpHistory State) :=
  finiteStateTimeDependentMarkovUniformizedHistoryProbabilityMeasure initial
    (rengerDirectionalFlowDualTestExponentialTimeTilt generator test) durationNNReal

end

end FiniteMarkovProcesses.InformationTheory
