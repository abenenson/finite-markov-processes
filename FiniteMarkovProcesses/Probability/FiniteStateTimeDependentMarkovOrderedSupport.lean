/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovReducedHistoryLaw

/-!
# Ordered support of bounded time-dependent Markov jump laws

Every virtual common-clock word is integrated over the strict ordered-time simplex.  This module
propagates that support through the fixed-word, fixed-count, complete virtual, and physical
self-event-deletion laws.  It supplies the exact almost-sure physical ordering premise needed to
integrate microscopic continuity identities under the perturbed source.

## Main results

- `ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedHistoryMeasure`.
- `ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

omit [MeasurableSingletonClass State] in
/-- Every fixed-word virtual time-dependent slice is supported on strict ordered histories. -/
theorem ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ)
    (states : Fin (eventCount + 1) → State) :
    ∀ᵐ history
      ∂finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
        initial rates duration eventCount states,
      history.OrderedBefore duration := by
  apply (ae_map_iff (measurable_embedJumpTimes eventCount states).aemeasurable
    (FiniteJumpHistory.measurableSet_orderedBefore duration)).2
  have hRestricted : ∀ᵐ times
      ∂volume.restrict (orderedJumpTimes eventCount duration),
      times ∈ orderedJumpTimes eventCount duration :=
    ae_restrict_mem (measurableSet_orderedJumpTimes eventCount duration)
  have hDensityAbsoluteContinuous :
      (volume.restrict (orderedJumpTimes eventCount duration)).withDensity
          (fun times ↦ ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times)) ≪
        volume.restrict (orderedJumpTimes eventCount duration) :=
    withDensity_absolutelyContinuous _ _
  exact hDensityAbsoluteContinuous.ae_le <| hRestricted.mono fun times hTimes ↦ hTimes

omit [MeasurableSingletonClass State] in
/-- Every fixed-count virtual time-dependent measure is supported on strict ordered histories. -/
theorem ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedCountMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) :
    ∀ᵐ history
      ∂finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount,
      history.OrderedBefore duration := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [Measure.ae_sum_iff]
  intro states
  exact ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
    initial rates duration eventCount states

omit [MeasurableSingletonClass State] in
/-- The complete virtual bounded time-dependent law is supported on strict ordered histories. -/
theorem ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    ∀ᵐ history
      ∂finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration,
      history.OrderedBefore duration := by
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [Measure.ae_sum_iff]
  intro eventCount
  exact ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedCountMeasure
    initial rates duration eventCount

/-- The normalized physical self-event-deletion law is supported on strict ordered histories. -/
theorem ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    ∀ᵐ history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration,
      history.OrderedBefore duration := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  apply (ae_map_iff FiniteJumpHistory.measurable_deleteSelfEvents.aemeasurable
    (FiniteJumpHistory.measurableSet_orderedBefore duration)).2
  filter_upwards [
    ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
      initial rates duration] with history hOrdered
  exact hOrdered.deleteSelfEvents

end

end FiniteMarkovProcesses.Probability
