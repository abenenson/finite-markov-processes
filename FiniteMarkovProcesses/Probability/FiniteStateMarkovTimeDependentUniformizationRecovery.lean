/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateMarkovUniformizedDeletionDensity
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovUniformizedHistoryLaw

/-!
# Recovery of homogeneous finite-state jump uniformization

This module embeds a homogeneous finite-state Markov jump generator into the bounded
time-dependent rate interface and proves literal recovery of the existing uniformized virtual
history measure. Consequently, deleting virtual self-events recovers the existing normalized
physical jump law.

The result is a regression theorem for the time-dependent construction. It does not identify a
genuinely time-dependent reduced law; that requires the variable-rate self-event resummation.

## Main results

- `FiniteStateMarkovGenerator.toTimeDependentMarkovRate`: constant-time embedding.
- `finiteStateTimeDependentMarkovUniformizedHistoryMeasure_constant`: exact virtual-law recovery.
- `map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure_constant`:
  exact physical-law recovery after self-event deletion.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

variable {State : Type u} [Fintype State] [DecidableEq State]

namespace FiniteStateMarkovGenerator

/-- A homogeneous generator regarded as a constant bounded time-dependent jump-rate family. -/
noncomputable def toTimeDependentMarkovRate
    (generator : FiniteStateMarkovGenerator State) :
    FiniteStateTimeDependentMarkovRate State where
  rate := fun _time ↦ generator.rate
  rate_self := fun _time state ↦ generator.rate_self state
  measurable_rate := fun _source _target ↦ measurable_const
  escapeBound := finiteStateTotalEscapeBound generator
  escapeRate_le_bound := fun _time source ↦ by
    rw [show (∑ target ∈ Finset.univ.erase source, generator.rate source target) =
        generator.escapeRate source by
      rw [Finset.sum_erase (s := Finset.univ) (generator.rate_self source)]
      rfl]
    exact escapeRate_le_finiteStateTotalEscapeBound generator source

/-- The constant embedding recovers the homogeneous escape rate. -/
theorem toTimeDependentMarkovRate_escapeRate
    (generator : FiniteStateMarkovGenerator State) (time : ℝ) (source : State) :
    generator.toTimeDependentMarkovRate.escapeRate time source =
      generator.escapeRate source := by
  unfold FiniteStateTimeDependentMarkovRate.escapeRate escapeRate
    toTimeDependentMarkovRate
  rw [Finset.sum_erase (s := Finset.univ) (generator.rate_self source)]

/-- The constant embedding uses exactly the existing homogeneous uniformization clock. -/
theorem toTimeDependentMarkovRate_uniformizationRate
    (generator : FiniteStateMarkovGenerator State) :
    generator.toTimeDependentMarkovRate.uniformizationRate =
      generator.uniformizationRate := by
  rfl

/-- Every constant embedded virtual transition weight is the existing homogeneous weight. -/
theorem toTimeDependentMarkovRate_uniformizedTransitionWeight
    (generator : FiniteStateMarkovGenerator State)
    (time : ℝ) (source target : State) :
    generator.toTimeDependentMarkovRate.uniformizedTransitionWeight time source target =
      generator.uniformizedTransitionWeight source target := by
  by_cases hEq : source = target
  · subst target
    rw [FiniteStateTimeDependentMarkovRate.uniformizedTransitionWeight_self,
      generator.uniformizedTransitionWeight_self,
      generator.toTimeDependentMarkovRate_escapeRate,
      generator.toTimeDependentMarkovRate_uniformizationRate]
  · rw [generator.toTimeDependentMarkovRate.uniformizedTransitionWeight_of_ne time hEq,
      generator.uniformizedTransitionWeight_of_ne hEq,
      generator.toTimeDependentMarkovRate_uniformizationRate]
    rfl

/-- Every constant embedded transition PMF is the existing homogeneous virtual row. -/
theorem toTimeDependentMarkovRate_uniformizedTransitionPMF
    (generator : FiniteStateMarkovGenerator State)
    (time : ℝ) (source : State) :
    generator.toTimeDependentMarkovRate.uniformizedTransitionPMF time source =
      generator.uniformizedTransitionPMF source := by
  ext target
  rw [FiniteStateTimeDependentMarkovRate.uniformizedTransitionPMF_apply,
    generator.uniformizedTransitionPMF_apply]
  exact_mod_cast generator.toTimeDependentMarkovRate_uniformizedTransitionWeight
    time source target

end FiniteStateMarkovGenerator

/-- The constant time-dependent continuation weight is the existing homogeneous continuation
weight, independently of the supplied event-time vector. -/
theorem finiteStateTimeDependentMarkovUniformizedContinuationWeight_constant
    (generator : FiniteStateMarkovGenerator State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ)
    (source : State) (future : Fin eventCount → State) :
    finiteStateTimeDependentMarkovUniformizedContinuationWeight
        generator.toTimeDependentMarkovRate times source future =
      finiteStateUniformizedContinuationWeight generator source future := by
  unfold finiteStateTimeDependentMarkovUniformizedContinuationWeight
    finiteStateTimeDependentMarkovContinuationWeight
    finiteStateUniformizedContinuationWeight
  apply Finset.prod_congr rfl
  intro index _hIndex
  simpa only using congrArg
    (fun law : PMF State ↦
      (law ((Fin.cons source future : Fin (eventCount + 1) → State) index.succ)).toReal)
    (generator.toTimeDependentMarkovRate_uniformizedTransitionPMF
      (times index)
      ((Fin.cons source future : Fin (eventCount + 1) → State) index.castSucc))

/-- The constant time-dependent state-word weight is the existing homogeneous state-word weight. -/
theorem finiteStateTimeDependentMarkovUniformizedStateWordWeight_constant
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ)
    (states : Fin (eventCount + 1) → State) :
    finiteStateTimeDependentMarkovUniformizedStateWordWeight
        initial generator.toTimeDependentMarkovRate times states =
      finiteStateUniformizedStateWordWeight initial generator states := by
  unfold finiteStateTimeDependentMarkovUniformizedStateWordWeight
    finiteStateUniformizedStateWordWeight
  rw [finiteStateTimeDependentMarkovUniformizedContinuationWeight_constant]

/-- Every constant time-dependent virtual slice density is the existing homogeneous density. -/
theorem finiteStateTimeDependentMarkovUniformizedSliceDensity_constant
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial generator.toTimeDependentMarkovRate duration states times =
      finiteStateMarkovUniformizedSliceDensity
        initial generator duration states times := by
  rw [finiteStateTimeDependentMarkovUniformizedSliceDensity,
    finiteStateMarkovUniformizedSliceDensity_eq_clock_mul_stateWordWeight,
    generator.toTimeDependentMarkovRate_uniformizationRate,
    finiteStateTimeDependentMarkovUniformizedStateWordWeight_constant]

/-- The constant time-dependent virtual history measure is literally the existing uniformized
history density measure. -/
theorem finiteStateTimeDependentMarkovUniformizedHistoryMeasure_constant
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial generator.toTimeDependentMarkovRate duration =
      finiteStateMarkovUniformizedDensityMeasure initial generator duration := by
  rw [finiteStateMarkovUniformizedDensityMeasure_eq_sum_slices]
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    finiteStateTimeDependentMarkovUniformizedCountMeasure
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
  congr 1
  funext eventCount
  congr 1
  funext states
  congr 1
  apply congrArg
  funext times
  rw [finiteStateTimeDependentMarkovUniformizedSliceDensity_constant]

/-- Deleting virtual self-events from the constant time-dependent law recovers the normalized
physical finite-state jump law. -/
theorem map_deleteSelfEvents_finiteStateTimeDependentMarkovUniformizedHistoryMeasure_constant
    [MeasurableSpace State] [MeasurableSingletonClass State]
    (initial : PMF State) (generator : FiniteStateMarkovGenerator State)
    {duration : ℝ} (hDuration : 0 ≤ duration) :
    Measure.map FiniteJumpHistory.deleteSelfEvents
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial generator.toTimeDependentMarkovRate duration) =
      finiteStateMarkovJumpDensityMeasure initial generator duration := by
  rw [finiteStateTimeDependentMarkovUniformizedHistoryMeasure_constant]
  exact map_deleteSelfEvents_finiteStateMarkovUniformizedDensityMeasure
    initial generator hDuration

end FiniteMarkovProcesses.Probability
