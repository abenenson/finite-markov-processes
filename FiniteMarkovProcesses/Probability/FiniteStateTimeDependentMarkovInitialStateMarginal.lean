/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryTimeObservation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovReducedHistoryLaw
import FiniteMarkovProcesses.Probability.PoissonCountExpectation

/-!
# Initial marginal of bounded time-dependent Markov jump laws

The normalized common-clock construction retains its prospectively supplied initial PMF exactly.
The proof is source-level: it first sums every fixed-time continuation word conditional on one
initial state, then integrates the ordered clock and sums its Poisson event count.  Measurable
self-event deletion preserves the initial state, so the physical reduced law has the same
marginal.

## Main results

- `map_initialState_finiteStateTimeDependentMarkovUniformizedHistoryMeasure`.
- `map_initialState_finiteStateTimeDependentMarkovReducedHistoryMeasure`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- At fixed virtual event times, the total weight of words starting from one state is exactly
the supplied initial mass of that state. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_initialState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {eventCount : ℕ} (times : Fin eventCount → ℝ) (observed : State) :
    (∑ states : Fin (eventCount + 1) → State,
      if states 0 = observed then
        finiteStateTimeDependentMarkovUniformizedStateWordWeight
          initial rates times states
      else 0) = (initial observed).toReal := by
  rw [← (Fin.consEquiv (fun _ : Fin (eventCount + 1) ↦ State)).sum_comp]
  rw [Fintype.sum_prod_type]
  change (∑ source : State, ∑ future : Fin eventCount → State,
    if source = observed then
      finiteStateTimeDependentMarkovUniformizedStateWordWeight
        initial rates times (Fin.cons source future)
    else 0) = _
  rw [Finset.sum_eq_single observed]
  · simp only [ite_true]
    unfold finiteStateTimeDependentMarkovUniformizedStateWordWeight
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [← Finset.mul_sum,
      sum_finiteStateTimeDependentMarkovUniformizedContinuationWeight, mul_one]
  · intro source _hSource hNe
    simp only [ite_eq_right hNe]
    exact Finset.sum_const_zero
  · simp

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Summing fixed-count virtual densities over words starting from one state leaves that initial
mass times the common Poisson-clock density. -/
theorem sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_initialState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) (times : Fin eventCount → ℝ)
    (observed : State) :
    (∑ states : Fin (eventCount + 1) → State,
      if states 0 = observed then
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
      else 0) =
      (initial observed).toReal *
        ((rates.uniformizationRate : ℝ) ^ eventCount *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration))) := by
  let clock := (rates.uniformizationRate : ℝ) ^ eventCount *
    Real.exp (-((rates.uniformizationRate : ℝ) * duration))
  calc
    (∑ states : Fin (eventCount + 1) → State,
      if states 0 = observed then
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          initial rates duration states times
      else 0) =
        clock * ∑ states : Fin (eventCount + 1) → State,
          if states 0 = observed then
            finiteStateTimeDependentMarkovUniformizedStateWordWeight
              initial rates times states
          else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro states _hStates
      by_cases hState : states 0 = observed
      · simp only [hState, ite_eq_left, clock,
          finiteStateTimeDependentMarkovUniformizedSliceDensity]
      · simp [hState]
    _ = clock * (initial observed).toReal := by
      rw [sum_finiteStateTimeDependentMarkovUniformizedStateWordWeight_initialState]
    _ = (initial observed).toReal *
        ((rates.uniformizationRate : ℝ) ^ eventCount *
          Real.exp (-((rates.uniformizationRate : ℝ) * duration))) := by
      rw [mul_comm]

/-- One fixed virtual event-count sector assigns the corresponding Poisson mass times the
supplied initial mass to each initial state. -/
theorem finiteStateTimeDependentMarkovUniformizedCountMeasure_initialState
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) (eventCount : ℕ) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount
        (FiniteJumpHistory.initialState ⁻¹' {observed}) =
      poissonCountPMF (rates.uniformizationRate * duration) eventCount * initial observed := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_initialState (measurableSet_singleton observed)),
    tsum_fintype]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure]
  simp_rw [Measure.map_apply (measurable_embedJumpTimes eventCount _)
    (FiniteJumpHistory.measurable_initialState (measurableSet_singleton observed))]
  have hPreimage (states : Fin (eventCount + 1) → State) :
      embedJumpTimes eventCount states ⁻¹'
          (FiniteJumpHistory.initialState ⁻¹' {observed}) =
        if states 0 = observed then Set.univ else ∅ := by
    by_cases hState : states 0 = observed
    · rw [ite_eq_left hState]
      ext times
      change states 0 = observed ↔ True
      simp only [hState]
    · rw [ite_eq_right hState]
      ext times
      change states 0 = observed ↔ False
      simp only [hState]
  simp_rw [hPreimage]
  have hSlice (states : Fin (eventCount + 1) → State) :
      ((volume.restrict (orderedJumpTimes eventCount duration)).withDensity
          (fun times ↦ ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times)))
          (if states 0 = observed then Set.univ else ∅) =
        if states 0 = observed then
          ∫⁻ times in orderedJumpTimes eventCount duration,
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times)
        else 0 := by
    by_cases hState : states 0 = observed
    · simp only [hState, ite_eq_left]
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ]
    · simp [hState]
  simp_rw [hSlice]
  have hMoveIndicator (states : Fin (eventCount + 1) → State) :
      (if states 0 = observed then
          ∫⁻ times in orderedJumpTimes eventCount duration,
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times)
        else 0) =
      ∫⁻ times in orderedJumpTimes eventCount duration,
        if states 0 = observed then
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times)
        else 0 := by
    by_cases hState : states 0 = observed <;> simp [hState]
  simp_rw [hMoveIndicator]
  rw [← lintegral_finsetSum]
  · have hDensity (times : Fin eventCount → ℝ) :
        (∑ states : Fin (eventCount + 1) → State,
          if states 0 = observed then
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times)
          else 0) =
        ENNReal.ofReal
          ((initial observed).toReal *
            ((rates.uniformizationRate : ℝ) ^ eventCount *
              Real.exp (-((rates.uniformizationRate : ℝ) * duration)))) := by
      rw [show (∑ states : Fin (eventCount + 1) → State,
          if states 0 = observed then
            ENNReal.ofReal
              (finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times)
          else 0) =
          ∑ states : Fin (eventCount + 1) → State,
            ENNReal.ofReal
              (if states 0 = observed then
                finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times
              else 0) by
        apply Finset.sum_congr rfl
        intro states _hStates
        by_cases hState : states 0 = observed <;> simp [hState]]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [sum_finiteStateTimeDependentMarkovUniformizedSliceDensity_initialState]
      · intro states _hStates
        split
        · exact finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
            initial rates duration states times
        · exact le_rfl
    simp_rw [hDensity]
    rw [lintegral_const]
    rw [Measure.restrict_apply_univ]
    change ENNReal.ofReal
        ((initial observed).toReal *
          ((rates.uniformizationRate : ℝ) ^ eventCount *
            Real.exp (-((rates.uniformizationRate : ℝ) * duration)))) *
        volume (orderedJumpTimes eventCount duration) = _
    rw [volume_orderedJumpTimes eventCount duration duration.coe_nonneg]
    rw [← ENNReal.ofReal_mul]
    · rw [← ENNReal.ofReal_toReal (initial.apply_ne_top observed)]
      change ENNReal.ofReal _ =
        ENNReal.ofReal (poissonCountMassReal
          (rates.uniformizationRate * duration) eventCount) *
            ENNReal.ofReal (initial observed).toReal
      rw [← ENNReal.ofReal_mul (by
        unfold poissonCountMassReal
        positivity)]
      apply congrArg ENNReal.ofReal
      unfold poissonCountMassReal
      rw [NNReal.coe_mul]
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      ring
    · positivity
  · intro states _hStates
    by_cases hState : states 0 = observed
    · simp only [hState, ite_eq_left]
      exact (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration states).ennreal_ofReal
    · simp only [hState]
      exact measurable_const

/-- The normalized virtual time-dependent source starts from exactly the supplied PMF. -/
theorem map_initialState_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    Measure.map FiniteJumpHistory.initialState
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration) =
      initial.toMeasure := by
  apply Measure.ext_of_singleton
  intro observed
  rw [Measure.map_apply FiniteJumpHistory.measurable_initialState
    (measurableSet_singleton observed)]
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [Measure.sum_apply _
    (FiniteJumpHistory.measurable_initialState (measurableSet_singleton observed))]
  simp_rw [finiteStateTimeDependentMarkovUniformizedCountMeasure_initialState]
  rw [ENNReal.tsum_mul_right]
  rw [(poissonCountPMF (rates.uniformizationRate * duration)).tsum_coe, one_mul]
  exact (PMF.toMeasure_apply_singleton initial observed
    (measurableSet_singleton observed)).symm

/-- Measurable self-event deletion preserves the exact supplied initial-state marginal. -/
theorem map_initialState_finiteStateTimeDependentMarkovReducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    Measure.map FiniteJumpHistory.initialState
        (finiteStateTimeDependentMarkovReducedHistoryMeasure
          initial rates duration) =
      initial.toMeasure := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  rw [Measure.map_map FiniteJumpHistory.measurable_initialState
    FiniteJumpHistory.measurable_deleteSelfEvents]
  have hFunction :
      (FiniteJumpHistory.initialState : FiniteJumpHistory State → State) ∘
          (FiniteJumpHistory.deleteSelfEvents :
            FiniteJumpHistory State → FiniteJumpHistory State) =
        (FiniteJumpHistory.initialState : FiniteJumpHistory State → State) := by
    funext history
    rcases history with ⟨eventCount, states, times⟩
    exact FiniteJumpHistory.initialState_deleteSelfEventsSlice states times
  rw [hFunction]
  exact map_initialState_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    initial rates duration

end

end FiniteMarkovProcesses.Probability
