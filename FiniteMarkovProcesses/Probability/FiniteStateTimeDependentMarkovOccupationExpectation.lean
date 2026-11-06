/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointMean
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovSelfEventDeletion
import FiniteMarkovProcesses.Probability.FiniteJumpHistoryTimeObservation
import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1Path

/-!
# Occupation expectations for bounded time-dependent Markov jump laws

This module turns the dwell-interval representation of a finite jump history into a physical-time
occupation integral and evaluates that integral under the normalized reduced history law.  It is
source-neutral finite-state probability mathematics.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

open FiniteMarkovProcesses

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

private theorem sum_intervalIntegral_adjacent_stateBlocks
    {eventCount : ℕ} (integrand : ℝ → ℝ)
    (hIntegrable : ∀ lower upper,
      IntervalIntegrable integrand volume lower upper)
    (boundaries : Fin (eventCount + 2) → ℝ) :
    (∑ block : Fin (eventCount + 1),
      ∫ time in boundaries block.castSucc..boundaries block.succ,
        integrand time) =
      ∫ time in boundaries 0..boundaries (Fin.last (eventCount + 1)),
        integrand time := by
  induction eventCount with
  | zero =>
      rw [Fin.sum_univ_succ]
      simp
  | succ eventCount inductionHypothesis =>
      rw [Fin.sum_univ_castSucc]
      have hPrefix := inductionHypothesis
        (fun boundary : Fin (eventCount + 2) => boundaries boundary.castSucc)
      simp_rw [← Fin.castSucc_succ]
      rw [hPrefix]
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · simp [Fin.succ_last]
      · exact hIntegrable _ _
      · exact hIntegrable _ _

/-- The instantaneous escape rate of the occupied state is jointly measurable in a complete
history and physical observation time. -/
theorem measurable_finiteStateTimeDependentMarkovEscapeRate_stateAtTime_uncurry
    (rates : FiniteStateTimeDependentMarkovRate State) :
    Measurable fun data : FiniteJumpHistory State × ℝ ↦
      (rates.escapeRate data.2 (data.1.stateAtTime data.2) : ℝ) := by
  have hSum : Measurable fun data : FiniteJumpHistory State × ℝ ↦
      ∑ state : State,
        if data.1.stateAtTime data.2 = state then
          (rates.escapeRate data.2 state : ℝ)
        else 0 := by
    apply Finset.measurable_sum
    intro state _hState
    exact Measurable.ite
      (FiniteJumpHistory.measurable_stateAtTime_uncurry.eq measurable_const).setOf
      ((rates.measurable_escapeRate state).coe_nnreal_real.comp measurable_snd)
      measurable_const
  rw [show (fun data : FiniteJumpHistory State × ℝ ↦
      (rates.escapeRate data.2 (data.1.stateAtTime data.2) : ℝ)) =
      fun data ↦ ∑ state : State,
        if data.1.stateAtTime data.2 = state then
          (rates.escapeRate data.2 state : ℝ)
        else 0 by
    funext data
    rw [Finset.sum_eq_single (data.1.stateAtTime data.2)]
    · simp
    · intro state _hState hStateNe
      simp [Ne.symm hStateNe]
    · simp]
  exact hSum

/-- On an ordered physical history, the dwell-sum integrated escape is exactly the physical-time
integral of the occupied state's instantaneous escape rate. -/
theorem finiteStateTimeDependentMarkovIntegratedEscape_eq_integral_stateAtTime
    (rates : FiniteStateTimeDependentMarkovRate State)
    {duration : ℝ} (hDuration : 0 ≤ duration) {eventCount : ℕ}
    (states : Fin (eventCount + 1) → State) (times : Fin eventCount → ℝ)
    (hTimes : times ∈ orderedJumpTimes eventCount duration) :
    finiteStateTimeDependentMarkovIntegratedEscape
        rates duration states times =
      ∫ time in 0..duration,
        (rates.escapeRate time
          (FiniteJumpHistory.stateAtTimeVector states times time) : ℝ) := by
  let occupiedEscape : ℝ → ℝ := fun time ↦
    rates.escapeRate time
      (FiniteJumpHistory.stateAtTimeVector states times time)
  have hOccupiedMeasurable : Measurable occupiedEscape := by
    have hState : Measurable fun time ↦
        FiniteJumpHistory.stateAtTimeVector states times time := by
      let fixedHistoryTime : ℝ →
          ((Fin (eventCount + 1) → State) × (Fin eventCount → ℝ)) × ℝ :=
        fun time ↦ ((states, times), time)
      have hFixedHistoryTime : Measurable fixedHistoryTime := by
        fun_prop
      exact (FiniteJumpHistory.measurable_stateAtTimeVector_uncurry
        (State := State) (eventCount := eventCount)).comp
        hFixedHistoryTime
    have hSum : Measurable fun time ↦
        ∑ state : State,
          if FiniteJumpHistory.stateAtTimeVector states times time = state then
            (rates.escapeRate time state : ℝ)
          else 0 := by
      apply Finset.measurable_sum
      intro state _hState
      exact Measurable.ite (hState.eq measurable_const).setOf
        (rates.measurable_escapeRate state).coe_nnreal_real measurable_const
    rw [show occupiedEscape = fun time ↦
        ∑ state : State,
          if FiniteJumpHistory.stateAtTimeVector states times time = state then
            (rates.escapeRate time state : ℝ)
          else 0 by
      funext time
      unfold occupiedEscape
      rw [Finset.sum_eq_single
        (FiniteJumpHistory.stateAtTimeVector states times time)]
      · simp
      · intro state _hState hStateNe
        simp [Ne.symm hStateNe]
      · simp]
    exact hSum
  have hOccupiedIntegrable (lower upper : ℝ) :
      IntervalIntegrable occupiedEscape volume lower upper := by
    constructor <;> apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    · exact hOccupiedMeasurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun time ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        exact_mod_cast rates.escapeRate_le_escapeBound time
          (FiniteJumpHistory.stateAtTimeVector states times time)
    · exact hOccupiedMeasurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun time ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
        exact_mod_cast rates.escapeRate_le_escapeBound time
          (FiniteJumpHistory.stateAtTimeVector states times time)
  change finiteStateTimeDependentMarkovIntegratedEscape rates duration states times =
    ∫ time in 0..duration, occupiedEscape time
  have hPartition := sum_intervalIntegral_adjacent_stateBlocks occupiedEscape
    hOccupiedIntegrable (FiniteJumpHistory.boundaryTimeVector duration times)
  have hPartition' :
      (∑ block : Fin (eventCount + 1),
        ∫ time in
            (FiniteJumpHistory.boundaryTimeVector duration times block.castSucc)..
            (FiniteJumpHistory.boundaryTimeVector duration times block.succ),
          occupiedEscape time) =
        ∫ time in 0..duration, occupiedEscape time := by
    simpa only [FiniteJumpHistory.boundaryTimeVector_zero,
      FiniteJumpHistory.boundaryTimeVector_last] using hPartition
  rw [← hPartition']
  unfold finiteStateTimeDependentMarkovIntegratedEscape
  apply Finset.sum_congr rfl
  intro block _hBlock
  apply intervalIntegral.integral_congr_ae
  have hLowerUpper :
      FiniteJumpHistory.boundaryTimeVector duration times block.castSucc ≤
        FiniteJumpHistory.boundaryTimeVector duration times block.succ :=
    FiniteJumpHistory.monotone_boundaryTimeVector_of_mem_orderedJumpTimes
      hDuration hTimes (Fin.castSucc_le_succ block)
  filter_upwards [Measure.ae_ne volume
    (FiniteJumpHistory.boundaryTimeVector duration times block.succ)] with
      time hUpperNe
  intro hTime
  rw [uIoc_of_le hLowerUpper] at hTime
  unfold occupiedEscape
  rw [FiniteJumpHistory.stateAtTimeVector_eq_state_of_mem_dwellInterval
    states times duration time hDuration hTimes block
      hTime.1.le
      (lt_of_le_of_ne hTime.2 hUpperNe)]

/-- Integrated escape is measurable on the complete finite-history carrier. -/
theorem measurable_finiteStateTimeDependentMarkovIntegratedEscape_history
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ) :
    Measurable fun history : FiniteJumpHistory State ↦
      finiteStateTimeDependentMarkovIntegratedEscape rates duration
        history.states history.jumpTimes := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro states
  exact measurable_finiteStateTimeDependentMarkovIntegratedEscape
    rates duration states

/-- Every bounded test-rate family's integrated escape is integrable under every normalized
bounded time-dependent jump source on a finite horizon. -/
theorem integrable_finiteStateTimeDependentMarkovIntegratedEscape
    (initial : PMF State) (sourceRates testRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    Integrable
      (fun history : FiniteJumpHistory State ↦
        finiteStateTimeDependentMarkovIntegratedEscape testRates duration
          history.states history.jumpTimes)
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial sourceRates duration) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial sourceRates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial sourceRates duration⟩
  apply Integrable.of_bound
    (measurable_finiteStateTimeDependentMarkovIntegratedEscape_history
      testRates duration).aestronglyMeasurable
    ((testRates.escapeBound : ℝ) * duration)
  filter_upwards [ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial sourceRates duration] with history hOrdered
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact finiteStateTimeDependentMarkovIntegratedEscape_le_bound_mul_duration_of_ordered
      testRates duration.coe_nonneg history.states history.jumpTimes hOrdered
  · exact finiteStateTimeDependentMarkovIntegratedEscape_nonneg_of_mem_orderedJumpTimes
      testRates duration.coe_nonneg history.states history.jumpTimes hOrdered

/-- The expected integrated escape of any bounded measurable test-rate family under a normalized
time-dependent jump source is its physical-time occupation integral against the exact source
mean density. -/
theorem integral_finiteStateTimeDependentMarkovIntegratedEscape_eq_occupationMean
    (initial : PMF State) (sourceRates testRates : FiniteStateTimeDependentMarkovRate State)
    (duration : NNReal) :
    (∫ history : FiniteJumpHistory State,
        finiteStateTimeDependentMarkovIntegratedEscape testRates duration
          history.states history.jumpTimes
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial sourceRates duration) =
      ∫ time,
        ∑ state,
          finiteStateTimeDependentMarkovMeanDensityAt
              initial sourceRates duration time state *
            (testRates.escapeRate time state : ℝ)
        ∂finiteOpenIntervalVolume (duration : ℝ) := by
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure
    initial sourceRates duration
  let physicalTime := finiteOpenIntervalVolume (duration : ℝ)
  let occupiedEscape : FiniteJumpHistory State × ℝ → ℝ := fun data ↦
    testRates.escapeRate data.2 (data.1.stateAtTime data.2)
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
      initial sourceRates duration⟩
  have hOccupiedMeasurable : Measurable occupiedEscape :=
    measurable_finiteStateTimeDependentMarkovEscapeRate_stateAtTime_uncurry testRates
  have hOccupiedIntegrable : Integrable occupiedEscape (law.prod physicalTime) := by
    apply Integrable.of_bound hOccupiedMeasurable.aestronglyMeasurable
      (testRates.escapeBound : ℝ)
    filter_upwards [] with data
    rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast testRates.escapeRate_le_escapeBound data.2
      (data.1.stateAtTime data.2)
  have hHistoryIntegral : ∀ᵐ history ∂law,
      finiteStateTimeDependentMarkovIntegratedEscape testRates duration
          history.states history.jumpTimes =
        ∫ time, occupiedEscape (history, time) ∂physicalTime := by
    filter_upwards [ae_orderedBefore_finiteStateTimeDependentMarkovReducedHistoryMeasure
      initial sourceRates duration] with history hOrdered
    have hPathwise :=
      finiteStateTimeDependentMarkovIntegratedEscape_eq_integral_stateAtTime
        testRates duration.coe_nonneg history.states history.jumpTimes hOrdered
    change finiteStateTimeDependentMarkovIntegratedEscape testRates duration
        history.states history.jumpTimes =
      ∫ time, occupiedEscape (history, time) ∂physicalTime
    rw [hPathwise]
    rw [intervalIntegral.integral_of_le duration.coe_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rfl
  have hTimeIntegral (time : ℝ) :
      (∫ history, occupiedEscape (history, time) ∂law) =
        ∑ state,
          finiteStateTimeDependentMarkovMeanDensityAt
              initial sourceRates duration time state *
            (testRates.escapeRate time state : ℝ) := by
    have hMembershipIntegrable (state : State) : Integrable
        (fun history : FiniteJumpHistory State ↦
          finiteJumpHistoryStateMembershipAtTime time state history)
        law :=
      (memLp_two_finiteJumpHistoryStateMembershipAtTime
        initial sourceRates duration time state).integrable one_le_two
    rw [show (fun history ↦ occupiedEscape (history, time)) =
        fun history ↦ ∑ state,
          finiteJumpHistoryStateMembershipAtTime time state history *
            (testRates.escapeRate time state : ℝ) by
      funext history
      unfold occupiedEscape finiteJumpHistoryStateMembershipAtTime
        FiniteJumpHistory.stateMembershipIndicator
      rw [Finset.sum_eq_single (history.stateAtTime time)]
      · simp
      · intro state _hState hStateNe
        simp [Ne.symm hStateNe]
      · simp]
    rw [integral_finsetSum Finset.univ fun state _hState ↦
      (hMembershipIntegrable state).mul_const _]
    apply Finset.sum_congr rfl
    intro state _hState
    rw [integral_mul_const]
    rfl
  calc
    (∫ history : FiniteJumpHistory State,
        finiteStateTimeDependentMarkovIntegratedEscape testRates duration
          history.states history.jumpTimes ∂law) =
      ∫ history, ∫ time, occupiedEscape (history, time)
        ∂physicalTime ∂law := integral_congr_ae hHistoryIntegral
    _ = ∫ time, ∫ history, occupiedEscape (history, time)
        ∂law ∂physicalTime := integral_integral_swap hOccupiedIntegrable
    _ = ∫ time,
        ∑ state,
          finiteStateTimeDependentMarkovMeanDensityAt
              initial sourceRates duration time state *
            (testRates.escapeRate time state : ℝ)
        ∂physicalTime := integral_congr_ae
          (Filter.Eventually.of_forall hTimeIntegral)

end

end FiniteMarkovProcesses.Probability
