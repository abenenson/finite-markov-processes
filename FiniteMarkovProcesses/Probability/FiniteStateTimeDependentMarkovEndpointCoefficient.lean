/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointWordWeight
import FiniteMarkovProcesses.Probability.OrderedJumpTimesLastDisintegration

/-!
# Ordered-time endpoint coefficients for time-dependent uniformized chains

This module integrates the fixed-time-vector endpoint weights of the common-clock source over
the ordered event-time simplex.  The resulting clock-free coefficient has an exact last-event
Volterra recursion.  It is the finite-event sector needed before the Poisson clock is resummed.

No differentiability of the measurable rates, path compensator, or large-deviation statement is
assumed here.

## Main results

- `finiteStateTimeDependentMarkovUniformizedEndpointCoefficient`.
- `finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_succ`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]

/-- Every fixed-time-vector endpoint word weight is nonnegative. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_nonneg
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ) (observed : State) :
    0 ≤ finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
      initial rates times observed := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
  apply Finset.sum_nonneg
  intro states _hStates
  split
  · unfold finiteStateTimeDependentMarkovUniformizedStateWordWeight
      finiteStateTimeDependentMarkovUniformizedContinuationWeight
      finiteStateTimeDependentMarkovContinuationWeight
    positivity
  · exact le_rfl

/-- The endpoint word weight is measurable in its ordered event-time vector. -/
theorem measurable_finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (observed : State) :
    Measurable fun times : Fin eventCount → ℝ ↦
      finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        initial rates times observed := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
  apply Finset.measurable_sum
  intro states _hStates
  by_cases hState : states (Fin.last eventCount) = observed
  · simp only [hState, ite_true]
    unfold finiteStateTimeDependentMarkovUniformizedStateWordWeight
      finiteStateTimeDependentMarkovUniformizedContinuationWeight
      finiteStateTimeDependentMarkovContinuationWeight
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro index _hIndex
    simpa only [Function.comp_def, Fin.cons_self_tail] using
      (rates.measurable_uniformizedTransitionPMF_toReal
        (states index.castSucc) (states index.succ)).comp
          (show Measurable fun times : Fin eventCount → ℝ ↦ times index from
            measurable_pi_apply index)
  · simp only [hState, ite_false]
    exact measurable_const

/-- Summing the endpoint coordinate over all final states recovers the normalized fixed-time
state-word weight. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ) :
    ∑ observed : State,
        finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
          initial rates times observed = 1 := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
  rw [Finset.sum_comm]
  simp_rw [show ∀ states : Fin (eventCount + 1) → State,
      (∑ observed : State,
        if states (Fin.last eventCount) = observed then
          finiteStateTimeDependentMarkovUniformizedStateWordWeight
            initial rates times states
        else 0) =
      finiteStateTimeDependentMarkovUniformizedStateWordWeight
        initial rates times states by
    intro states
    rw [Finset.sum_eq_single (states (Fin.last eventCount))]
    · simp
    · intro observed _hObserved hNe
      simp only [hNe.symm, ite_false]
    · simp]
  exact sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight
    initial rates times

/-- Clock-free mass of one endpoint and one fixed virtual-event count.  The common Poisson
factor `lambda^n * exp (-lambda * T)` is deliberately excluded so that the last-event recursion
has its clean source-level form. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (observed : State) : ℝ≥0∞ :=
  ∫⁻ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
    ENNReal.ofReal
      (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
        initial rates times observed)

/-- The zero-event endpoint coefficient is exactly the supplied initial coordinate. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_zero
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates duration 0 observed =
      initial observed := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
  have hStrict : ∀ times : Fin 0 → ℝ, StrictMono times := by
    intro times index
    exact Fin.elim0 index
  have hOrdered (horizon : ℝ) : orderedJumpTimes 0 horizon = Set.univ := by
    ext times
    simp [orderedJumpTimes, hStrict times]
  rw [hOrdered duration, Measure.restrict_univ]
  simp_rw [finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_zero]
  rw [lintegral_const]
  rw [ENNReal.ofReal_toReal (initial.apply_ne_top observed)]
  have hVolume : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    have hZero := volume_orderedJumpTimes 0 0 (le_refl (0 : ℝ))
    rw [hOrdered 0] at hZero
    simpa using hZero
  rw [hVolume, mul_one]

/-- At every nonnegative horizon, the endpoint coefficients for one event count have exactly the
ordered-simplex volume.  This is the coefficient-level bound needed for Poisson resummation. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (hDuration : 0 ≤ duration) (eventCount : ℕ) :
    ∑ observed : State,
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates duration eventCount observed =
      ENNReal.ofReal (duration ^ eventCount / eventCount.factorial) := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
  rw [← lintegral_finsetSum]
  · calc
      (∫⁻ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
          ∑ observed : State,
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates times observed)) =
          ∫⁻ _times : Fin eventCount → ℝ in
            orderedJumpTimes eventCount duration, 1 := by
        apply lintegral_congr
        intro times
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · rw [sum_finiteStateTimeDependentMarkovUniformizedEndpointWordWeight]
          simp
        · intro observed _hObserved
          exact finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_nonneg
            initial rates times observed
      _ = volume (orderedJumpTimes eventCount duration) := by simp
      _ = ENNReal.ofReal (duration ^ eventCount / eventCount.factorial) :=
        volume_orderedJumpTimes eventCount duration hDuration
  · intro observed _hObserved
    exact (measurable_finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
      initial rates observed).ennreal_ofReal

/-- A nonempty endpoint coefficient is obtained by choosing its last virtual event time,
summing over the state immediately before that event, and applying the corresponding
time-dependent transition row. -/
theorem finiteStateTimeDependentMarkovUniformizedEndpointCoefficient_succ
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (target : State) :
    finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
        initial rates duration (eventCount + 1) target =
      ∫⁻ lastTime : ℝ in Ioo 0 duration,
        ∑ source : State,
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
              initial rates lastTime eventCount source *
            rates.uniformizedTransitionPMF lastTime source target := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
  rw [lintegral_orderedJumpTimes_succ eventCount
    ((measurable_finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
      initial rates target).ennreal_ofReal) duration]
  apply lintegral_congr
  intro lastTime
  rw [show
      (∫⁻ earlierTimes : Fin eventCount → ℝ in
          orderedJumpTimes eventCount lastTime,
        ENNReal.ofReal
          (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
            initial rates
              (orderedJumpTimesLastJoin eventCount (lastTime, earlierTimes)) target)) =
        ∫⁻ earlierTimes : Fin eventCount → ℝ in
          orderedJumpTimes eventCount lastTime,
          ∑ source : State,
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates earlierTimes source) *
              rates.uniformizedTransitionPMF lastTime source target by
    apply lintegral_congr
    intro earlierTimes
    rw [finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_succ]
    simp only [orderedJumpTimesLastJoin_init, orderedJumpTimesLastJoin_last]
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro source _hSource
      rw [ENNReal.ofReal_mul
        (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_nonneg
          initial rates earlierTimes source)]
      rw [ENNReal.ofReal_toReal
        ((rates.uniformizedTransitionPMF lastTime source).apply_ne_top target)]
    · intro source _hSource
      exact mul_nonneg
        (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight_nonneg
          initial rates earlierTimes source)
        ENNReal.toReal_nonneg]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro source _hSource
    rw [lintegral_mul_const'
      (rates.uniformizedTransitionPMF lastTime source target) _
      ((rates.uniformizedTransitionPMF lastTime source).apply_ne_top target)]
  · intro source _hSource
    exact (measurable_finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
      initial rates source).ennreal_ofReal.mul_const _

end

end FiniteMarkovProcesses.Probability
