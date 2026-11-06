/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanContinuity

/-!
# Initial-law mixtures of time-dependent finite-state Markov sources

The normalized virtual and reduced history laws depend linearly on their finite initial PMF.
This module exposes that source property as an exact finite mixture of pure-initial laws.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A fixed virtual word-slice density factors into its initial mass and the corresponding
pure-initial density. -/
theorem finiteStateTimeDependentMarkovUniformizedSliceDensity_eq_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ) :
    finiteStateTimeDependentMarkovUniformizedSliceDensity
        initial rates duration states times =
      (initial (states 0)).toReal *
        finiteStateTimeDependentMarkovUniformizedSliceDensity
          (PMF.pure (states 0)) rates duration states times := by
  unfold finiteStateTimeDependentMarkovUniformizedSliceDensity
    finiteStateTimeDependentMarkovUniformizedStateWordWeight
  simp
  ring

omit [MeasurableSingletonClass State] in
/-- A fixed virtual state-word measure is the initial mass times its pure-initial word measure. -/
theorem finiteStateTimeDependentMarkovUniformizedWordSliceMeasure_eq_initial_smul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ)
    (states : Fin (eventCount + 1) → State) :
    finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
        initial rates duration eventCount states =
      initial (states 0) •
        finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
          (PMF.pure (states 0)) rates duration eventCount states := by
  unfold finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
  rw [← Measure.map_smul _
    (measurable_embedJumpTimes eventCount states).aemeasurable, ← withDensity_smul]
  · apply congrArg (Measure.map (embedJumpTimes eventCount states))
    apply withDensity_congr_ae
    filter_upwards [] with times
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [finiteStateTimeDependentMarkovUniformizedSliceDensity_eq_initial_mul_pure]
    rw [ENNReal.ofReal_mul (initial (states 0)).toReal_nonneg]
    rw [ENNReal.ofReal_toReal (initial.apply_ne_top (states 0))]
  · exact
      (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
        (PMF.pure (states 0)) rates duration states).ennreal_ofReal

omit [MeasurableSingletonClass State] in
/-- A fixed-count virtual history law is the finite initial-PMF mixture of its pure-initial
fixed-count laws. -/
theorem finiteStateTimeDependentMarkovUniformizedCountMeasure_eq_sum_initial_smul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) (eventCount : ℕ) :
    finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount =
      ∑ state, initial state •
        finiteStateTimeDependentMarkovUniformizedCountMeasure
          (PMF.pure state) rates duration eventCount := by
  ext event hEvent
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Measure.sum_apply _ hEvent, tsum_fintype]
  rw [show
      (∑ state, initial state *
        ∑ states,
          (finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
            (PMF.pure state) rates duration eventCount states) event) =
        ∑ states, ∑ state, initial state *
          (finiteStateTimeDependentMarkovUniformizedWordSliceMeasure
            (PMF.pure state) rates duration eventCount states) event by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]]
  apply Finset.sum_congr rfl
  intro states _hStates
  rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure_eq_initial_smul_pure]
  simp only [Measure.coe_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single (states 0)]
  · simp
  · intro state _hState hState
    have hInitialNe : states 0 ≠ state := Ne.symm hState
    rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure_eq_initial_smul_pure]
    simp [hInitialNe]
  · simp

omit [MeasurableSingletonClass State] in
/-- The complete virtual history law is the finite initial-PMF mixture of its pure-initial
history laws. -/
theorem finiteStateTimeDependentMarkovUniformizedHistoryMeasure_eq_sum_initial_smul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ) :
    finiteStateTimeDependentMarkovUniformizedHistoryMeasure initial rates duration =
      ∑ state, initial state •
        finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          (PMF.pure state) rates duration := by
  ext event hEvent
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Measure.sum_apply _ hEvent]
  have hCount (eventCount : ℕ) :
      (finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount) event =
        ∑ state, initial state *
          (finiteStateTimeDependentMarkovUniformizedCountMeasure
            (PMF.pure state) rates duration eventCount) event := by
    rw [finiteStateTimeDependentMarkovUniformizedCountMeasure_eq_sum_initial_smul_pure]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
      Pi.smul_apply, smul_eq_mul]
  simp_rw [hCount]
  rw [Summable.tsum_finsetSum (fun _eventCount _state => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro state _hState
  rw [ENNReal.tsum_mul_left]

/-- The physical reduced-history law is the finite initial-PMF mixture of its pure-initial
physical laws.  Self-event deletion therefore preserves exact initial-law linearity. -/
theorem finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_smul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration =
      ∑ state, initial state •
        finiteStateTimeDependentMarkovReducedHistoryMeasure
          (PMF.pure state) rates duration := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  rw [finiteStateTimeDependentMarkovUniformizedHistoryMeasure_eq_sum_initial_smul_pure]
  ext event hEvent
  rw [Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents hEvent]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro state _hState
  rw [Measure.map_apply FiniteJumpHistory.measurable_deleteSelfEvents hEvent]

/-- Expectations under the physical source are the finite initial-PMF weighted average of the
corresponding pure-initial expectations whenever the observable is integrable in every pure
sector. -/
theorem integral_finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observable : FiniteJumpHistory State → ℝ)
    (hIntegrable : ∀ state, Integrable observable
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure state) rates duration)) :
    (∫ history, observable history
        ∂finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration) =
      ∑ state, (initial state).toReal *
        ∫ history, observable history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure state) rates duration := by
  rw [finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_smul_pure]
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, smul_eq_mul]
  · intro state _hState
    exact (hIntegrable state).smul_measure (initial.apply_ne_top state)

/-- Expected occupied-state density is linear in the finite initial PMF. -/
theorem finiteStateTimeDependentMarkovMeanDensityAt_eq_sum_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (time : ℝ) (observed : State) :
    finiteStateTimeDependentMarkovMeanDensityAt initial rates duration time observed =
      ∑ state, (initial state).toReal *
        finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure state) rates duration time observed := by
  unfold finiteStateTimeDependentMarkovMeanDensityAt
  apply
    integral_finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_mul_pure
  intro state
  let : IsProbabilityMeasure
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure state) rates duration) :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      (PMF.pure state) rates duration⟩
  exact
    (memLp_two_finiteJumpHistoryStateMembershipAtTime
      (PMF.pure state) rates duration time observed).integrable one_le_two

/-- Expected cumulative ordered flow is linear in the finite initial PMF. -/
theorem finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_sum_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (time : ℝ) (source target : State) :
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration time source target =
      ∑ state, (initial state).toReal *
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          (PMF.pure state) rates duration time source target := by
  unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
  apply
    integral_finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_mul_pure
  intro state
  let : IsProbabilityMeasure
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure state) rates duration) :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      (PMF.pure state) rates duration⟩
  exact
    (memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
      (PMF.pure state) rates duration time source target).integrable one_le_two

end

end FiniteMarkovProcesses.Probability
