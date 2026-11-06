/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpTrajectory

/-!
# Fixed-state slices of finite-state jump-process steps

This module computes the waiting-time measures obtained by fixing the state coordinate of the
initial timed state or one subsequent timed transition. These one-coordinate disintegrations are
the induction steps for finite state-word trajectory laws.

## Main results

- `finiteStateInitialTimedStateMeasure_stateSlice`: fixing the initial state leaves its PMF mass
  times the corresponding holding-time law.
- `finiteStateTimedStepKernel_stateSlice`: fixing one jump destination leaves its transition
  probability times that destination's holding-time law.
- `finiteStateInitialTimedStateMeasure_stateWaitSet`: exact initial state/wait cylinder mass.
- `finiteStateTimedStepKernel_stateWaitSet`: exact transition state/wait cylinder mass.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {State : Type u} [Fintype State] [MeasurableSpace State]
  [MeasurableSingletonClass State]

/-- Fixing the state coordinate of the initial timed-state law leaves the initial point mass
times the state-dependent holding-time measure. -/
theorem finiteStateInitialTimedStateMeasure_stateSlice
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (state : State) :
    Measure.map Prod.snd
        ((finiteStateInitialTimedStateMeasure initial generator T).restrict
          {timedState | timedState.1 = state}) =
      (initial state) • finiteStateHoldingTimeMeasure generator T state := by
  ext waits hWaits
  rw [Measure.map_apply measurable_snd hWaits]
  rw [Measure.restrict_apply (hWaits.preimage measurable_snd)]
  rw [finiteStateInitialTimedStateMeasure]
  have hEvent : MeasurableSet
      (Prod.snd ⁻¹' waits ∩ {timedState : State × ℝ | timedState.1 = state}) :=
    (hWaits.preimage measurable_snd).inter
      ((measurableSet_singleton state).preimage measurable_fst)
  rw [Measure.compProd_apply hEvent]
  rw [lintegral_fintype]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change (∑ x, (finiteStateHoldingTimeMeasure generator T x)
      (Prod.mk x ⁻¹' (Prod.snd ⁻¹' waits ∩
        {timedState : State × ℝ | timedState.1 = state})) * initial x) =
    initial state * finiteStateHoldingTimeMeasure generator T state waits
  classical
  rw [Finset.sum_eq_single state]
  · have hPreimage :
        Prod.mk state ⁻¹' (Prod.snd ⁻¹' waits ∩
          {timedState : State × ℝ | timedState.1 = state}) = waits := by
        ext wait
        simp
    rw [hPreimage, mul_comm]
  · intro x hx hNe
    simp [hNe]
  · simp

/-- Fixing the destination-state coordinate of one timed transition leaves the physical
destination probability times that destination's holding-time measure. -/
theorem finiteStateTimedStepKernel_stateSlice
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (source target : State) :
    Measure.map Prod.snd
        ((finiteStateTimedStepKernel generator T source).restrict
          {timedState | timedState.1 = target}) =
      (finiteStateJumpDestinationPMF generator source target) •
        finiteStateHoldingTimeMeasure generator T target := by
  ext waits hWaits
  rw [Measure.map_apply measurable_snd hWaits]
  rw [Measure.restrict_apply (hWaits.preimage measurable_snd)]
  rw [finiteStateTimedStepKernel]
  have hEvent : MeasurableSet
      (Prod.snd ⁻¹' waits ∩ {timedState : State × ℝ | timedState.1 = target}) :=
    (hWaits.preimage measurable_snd).inter
      ((measurableSet_singleton target).preimage measurable_fst)
  rw [Kernel.compProd_apply hEvent]
  change (∫⁻ x, (finiteStateHoldingTimeKernel generator T x)
      (Prod.mk x ⁻¹' (Prod.snd ⁻¹' waits ∩
        {timedState : State × ℝ | timedState.1 = target}))
      ∂(finiteStateJumpDestinationPMF generator source).toMeasure) =
    finiteStateJumpDestinationPMF generator source target *
      finiteStateHoldingTimeMeasure generator T target waits
  rw [lintegral_fintype]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change (∑ x, (finiteStateHoldingTimeMeasure generator T x)
      (Prod.mk x ⁻¹' (Prod.snd ⁻¹' waits ∩
        {timedState : State × ℝ | timedState.1 = target})) *
        finiteStateJumpDestinationPMF generator source x) =
    finiteStateJumpDestinationPMF generator source target *
      finiteStateHoldingTimeMeasure generator T target waits
  classical
  rw [Finset.sum_eq_single target]
  · have hPreimage :
        Prod.mk target ⁻¹' (Prod.snd ⁻¹' waits ∩
          {timedState : State × ℝ | timedState.1 = target}) = waits := by
        ext wait
        simp
    rw [hPreimage, mul_comm]
  · intro x hx hNe
    simp [hNe]
  · simp

/-- Exact mass of an initial state-and-wait cylinder. -/
theorem finiteStateInitialTimedStateMeasure_stateWaitSet
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (T : ℝ) (state : State) (waits : Set ℝ) (hWaits : MeasurableSet waits) :
    finiteStateInitialTimedStateMeasure initial generator T
        {timedState | timedState.1 = state ∧ timedState.2 ∈ waits} =
      initial state * finiteStateHoldingTimeMeasure generator T state waits := by
  have hSlice := congrArg (fun measure : Measure ℝ => measure waits)
    (finiteStateInitialTimedStateMeasure_stateSlice initial generator T state)
  change Measure.map Prod.snd
      ((finiteStateInitialTimedStateMeasure initial generator T).restrict
        {timedState | timedState.1 = state}) waits =
    initial state * finiteStateHoldingTimeMeasure generator T state waits at hSlice
  rw [Measure.map_apply measurable_snd hWaits] at hSlice
  rw [Measure.restrict_apply (hWaits.preimage measurable_snd)] at hSlice
  convert hSlice using 1
  congr 1
  ext timedState
  simp [and_comm]

/-- Exact mass of a destination state-and-wait cylinder for one timed transition. -/
theorem finiteStateTimedStepKernel_stateWaitSet
    (generator : FiniteStateMarkovGenerator State) (T : ℝ)
    (source target : State) (waits : Set ℝ) (hWaits : MeasurableSet waits) :
    finiteStateTimedStepKernel generator T source
        {timedState | timedState.1 = target ∧ timedState.2 ∈ waits} =
      finiteStateJumpDestinationPMF generator source target *
        finiteStateHoldingTimeMeasure generator T target waits := by
  have hSlice := congrArg (fun measure : Measure ℝ => measure waits)
    (finiteStateTimedStepKernel_stateSlice generator T source target)
  change Measure.map Prod.snd
      ((finiteStateTimedStepKernel generator T source).restrict
        {timedState | timedState.1 = target}) waits =
    finiteStateJumpDestinationPMF generator source target *
      finiteStateHoldingTimeMeasure generator T target waits at hSlice
  rw [Measure.map_apply measurable_snd hWaits] at hSlice
  rw [Measure.restrict_apply (hWaits.preimage measurable_snd)] at hSlice
  convert hSlice using 1
  congr 1
  ext timedState
  simp [and_comm]

end FiniteMarkovProcesses.Probability
