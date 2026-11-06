/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointEvolution
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovReducedHistoryLaw
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryTimeObservation

/-!
# Endpoint marginal of bounded time-dependent Markov jump laws

The resummed endpoint evolution is identified here with the literal final-state marginal of the
normalized common-clock history law.  Measurable self-event deletion preserves that final state,
so the physical reduced source has the same endpoint PMF.

This theorem is horizon-level source ownership.  Intermediate-time marginals and the
compensator/forward equation remain separate statements.

## Main results

- `map_finalState_finiteStateTimeDependentMarkovUniformizedHistoryMeasure`.
- `map_finalState_finiteStateTimeDependentMarkovReducedHistoryMeasure`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Summing a fixed-count slice density over state words with one final state leaves the common
clock factor times that state's endpoint word weight. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_finalState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (times : Fin eventCount → ℝ)
    (observed : State) :
    (∑ states : Fin (eventCount + 1) → State,
      if states (Fin.last eventCount) = observed then
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
      else 0) =
      ((rates.uniformizationRate : ℝ) ^ eventCount *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
          initial rates times observed := by
  unfold finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro states _hStates
  by_cases hState : states (Fin.last eventCount) = observed
  · simp only [hState, ite_true,
      finiteStateTimeDependentMarkovUniformizedSliceDensity]
  · simp only [hState, ite_false, mul_zero]

/-- One fixed virtual event-count sector has final-state mass equal to its common Poisson clock
factor times the clock-free endpoint coefficient. -/
theorem finiteStateTimeDependentMarkovUniformizedCountMeasure_finalState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (eventCount : ℕ) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount
        (FiniteJumpHistory.finalState ⁻¹' {observed}) =
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ eventCount *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
        finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
          initial rates duration eventCount observed := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_finalState (measurableSet_singleton observed)),
    tsum_fintype]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure]
  simp_rw [Measure.map_apply (measurable_embedJumpTimes eventCount _)
    (FiniteJumpHistory.measurable_finalState (measurableSet_singleton observed))]
  have hPreimage (states : Fin (eventCount + 1) → State) :
      embedJumpTimes eventCount states ⁻¹'
          (FiniteJumpHistory.finalState ⁻¹' {observed}) =
        if states (Fin.last eventCount) = observed then Set.univ else ∅ := by
    by_cases hState : states (Fin.last eventCount) = observed
    · rw [ite_eq_left hState]
      ext times
      change states (Fin.last eventCount) = observed ↔ True
      simp only [hState]
    · rw [ite_eq_right hState]
      ext times
      change states (Fin.last eventCount) = observed ↔ False
      simp only [hState]
  simp_rw [hPreimage]
  have hSlice (states : Fin (eventCount + 1) → State) :
      ((volume.restrict (orderedJumpTimes eventCount duration)).withDensity
          (fun times ↦ ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times)))
          (if states (Fin.last eventCount) = observed then Set.univ else ∅) =
        if states (Fin.last eventCount) = observed then
          ∫⁻ times in orderedJumpTimes eventCount duration,
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times)
        else 0 := by
    by_cases hState : states (Fin.last eventCount) = observed
    · simp only [hState, ite_eq_left]
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
    · simp [hState]
  simp_rw [hSlice]
  have hMoveIndicator (states : Fin (eventCount + 1) → State) :
      (if states (Fin.last eventCount) = observed then
          ∫⁻ times in orderedJumpTimes eventCount duration,
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times)
        else 0) =
      ∫⁻ times in orderedJumpTimes eventCount duration,
        ENNReal.ofReal
          (if states (Fin.last eventCount) = observed then
            finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times
          else 0) := by
    by_cases hState : states (Fin.last eventCount) = observed <;> simp [hState]
  simp_rw [hMoveIndicator]
  rw [← lintegral_finsetSum]
  · have hDensity (times : Fin eventCount → ℝ) :
        (∑ states : Fin (eventCount + 1) → State,
          ENNReal.ofReal
            (if states (Fin.last eventCount) = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)) =
          ENNReal.ofReal
            (((rates.uniformizationRate : ℝ) ^ eventCount *
                Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
              finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates times observed) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_finalState]
      · intro states _hStates
        split
        · exact finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
            initial rates duration states times
        · exact le_rfl
    simp_rw [hDensity]
    simp_rw [show ∀ times : Fin eventCount → ℝ,
        ENNReal.ofReal
          (((rates.uniformizationRate : ℝ) ^ eventCount *
              Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
            finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
              initial rates times observed) =
          ENNReal.ofReal
              ((rates.uniformizationRate : ℝ) ^ eventCount *
                Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedEndpointWordWeight
                initial rates times observed) by
      intro times
      rw [ENNReal.ofReal_mul]
      positivity]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  · intro states _hStates
    by_cases hState : states (Fin.last eventCount) = observed
    · simp only [hState, ite_true]
      exact (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration states).ennreal_ofReal
    · simp only [hState, ite_false]
      exact measurable_const

/-- The normalized virtual time-dependent source has exactly the resummed endpoint PMF as its
final-state marginal. -/
theorem map_finalState_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    Measure.map FiniteJumpHistory.finalState
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration) =
      (finiteStateTimeDependentMarkovEndpointPMF
        initial rates duration).toMeasure := by
  apply Measure.ext_of_singleton
  intro observed
  rw [Measure.map_apply FiniteJumpHistory.measurable_finalState
    (measurableSet_singleton observed)]
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_finalState (measurableSet_singleton observed))]
  simp_rw [finiteStateTimeDependentMarkovUniformizedCountMeasure_finalState]
  rw [PMF.toMeasure_apply_singleton
    (finiteStateTimeDependentMarkovEndpointPMF initial rates duration)
    observed (measurableSet_singleton observed)]
  rw [finiteStateTimeDependentMarkovEndpointPMF_apply]
  unfold finiteStateTimeDependentMarkovEndpointProbability
  unfold finiteStateTimeDependentMarkovUniformizedEndpointSeries
  have hClock (eventCount : ℕ) :
      ENNReal.ofReal
          ((rates.uniformizationRate : ℝ) ^ eventCount *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration))) =
        ENNReal.ofReal
            (Real.exp (-((rates.uniformizationRate : ℝ) * duration))) *
          (rates.uniformizationRate : ℝ≥0∞) ^ eventCount := by
    rw [ENNReal.ofReal_mul (pow_nonneg
      (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity) eventCount)]
    rw [ENNReal.coe_nnreal_eq]
    rw [← ENNReal.ofReal_pow
      (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity)]
    ac_rfl
  simp_rw [hClock, mul_assoc]
  rw [ENNReal.tsum_mul_left]

/-- Measurable self-event deletion preserves the exact resummed endpoint marginal. -/
theorem map_finalState_finiteStateTimeDependentMarkovReducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    Measure.map FiniteJumpHistory.finalState
        (finiteStateTimeDependentMarkovReducedHistoryMeasure
          initial rates duration) =
      (finiteStateTimeDependentMarkovEndpointPMF
        initial rates duration).toMeasure := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  rw [Measure.map_map FiniteJumpHistory.measurable_finalState
    FiniteJumpHistory.measurable_deleteSelfEvents]
  have hFunction :
      (FiniteJumpHistory.finalState : FiniteJumpHistory State → State) ∘
          (FiniteJumpHistory.deleteSelfEvents :
            FiniteJumpHistory State → FiniteJumpHistory State) =
        (FiniteJumpHistory.finalState : FiniteJumpHistory State → State) := by
    funext history
    rcases history with ⟨eventCount, states, times⟩
    exact FiniteJumpHistory.finalState_deleteSelfEventsSlice states times
  rw [hFunction]
  exact map_finalState_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    initial rates duration

end

end FiniteMarkovProcesses.Probability
