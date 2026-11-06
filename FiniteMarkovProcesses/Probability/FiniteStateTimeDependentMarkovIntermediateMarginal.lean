/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovCutSectorResummation
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointMarginal
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovOrderedSupport
import FiniteMarkovProcesses.Probability.NatSuccessorIndexSplit
import FiniteMarkovProcesses.Probability.OrderedJumpTimesCutPartition

/-!
# Intermediate-time marginal of bounded time-dependent Markov jump laws

This module transports the cut-sector factorization and future Poisson resummation back to the
literal complete-history source.  It first identifies each fixed total-count state-at-time mass
with an ordered-simplex integral.  The complete projective marginal is assembled only after the
exact observed-count partition, null cut-boundary removal, and total/cut-count reindexing.

## Main results

- `finiteStateTimeDependentMarkovUniformizedCountMeasure_stateAtTime`.
- `map_stateAtTime_finiteStateTimeDependentMarkovUniformizedHistoryMeasure`.
- `map_stateAtTime_finiteStateTimeDependentMarkovReducedHistoryMeasure`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Fixed-total-count mass of one occupied state at one physical observation time, written as a
literal state-word sum over the complete ordered simplex. -/
noncomputable def finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration observationTime : ℝ) (eventCount : ℕ) (observed : State) : ℝ≥0∞ :=
  ∫⁻ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
    ENNReal.ofReal
      (∑ states : Fin (eventCount + 1) → State,
        if FiniteJumpHistory.stateAtTimeVector states times observationTime = observed then
          finiteStateTimeDependentMarkovUniformizedSliceDensity
            initial rates duration states times
        else 0)

/-- One fixed virtual event-count sector has exactly the literal ordered-simplex fixed-time state
mass. -/
theorem finiteStateTimeDependentMarkovUniformizedCountMeasure_stateAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration observationTime : ℝ) (eventCount : ℕ) (observed : State) :
    finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount
        ((fun history : FiniteJumpHistory State ↦
          history.stateAtTime observationTime) ⁻¹' {observed}) =
      finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
        initial rates duration observationTime eventCount observed := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [Measure.sum_apply _
    ((FiniteJumpHistory.measurable_stateAtTime observationTime)
      (measurableSet_singleton observed)), tsum_fintype]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure]
  simp_rw [Measure.map_apply (measurable_embedJumpTimes eventCount _)
    ((FiniteJumpHistory.measurable_stateAtTime observationTime)
      (measurableSet_singleton observed))]
  have hPreimage (states : Fin (eventCount + 1) → State) :
      embedJumpTimes eventCount states ⁻¹'
          ((fun history : FiniteJumpHistory State ↦
            history.stateAtTime observationTime) ⁻¹' {observed}) =
        {times : Fin eventCount → ℝ |
          FiniteJumpHistory.stateAtTimeVector states times observationTime = observed} := by
    rfl
  simp_rw [hPreimage]
  have hStateEvent (states : Fin (eventCount + 1) → State) : MeasurableSet
      {times : Fin eventCount → ℝ |
        FiniteJumpHistory.stateAtTimeVector states times observationTime = observed} := by
    exact ((FiniteJumpHistory.measurable_stateAtTimeVector observationTime).comp
      (measurable_const.prodMk measurable_id))
        (measurableSet_singleton observed)
  simp_rw [withDensity_apply _ (hStateEvent _)]
  simp_rw [← lintegral_indicator (hStateEvent _)]
  rw [← lintegral_finsetSum]
  · unfold finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
    apply lintegral_congr
    intro times
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro states _hStates
      by_cases hObserved :
          FiniteJumpHistory.stateAtTimeVector states times observationTime = observed
      · simp [Set.indicator, hObserved]
      · simp [Set.indicator, hObserved]
    · intro states _hStates
      split
      · exact finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
          initial rates duration states times
      · exact le_rfl
  · intro states _hStates
    exact ((measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration states).ennreal_ofReal.indicator (hStateEvent states))

omit [Fintype State] [DecidableEq State] [MeasurableSpace State]
    [MeasurableSingletonClass State] in
/-- On an exact observed-count fibre, càdlàg evaluation selects the corresponding cut-state
coordinate of the complete state word. -/
theorem FiniteJumpHistory.stateAtTimeVector_eq_cutStateIndex_of_mem_observedCountSector
    (earlierCount laterCount : ℕ)
    (states : Fin (earlierCount + laterCount + 1) → State)
    (times : Fin (earlierCount + laterCount) → ℝ)
    (lower observationTime duration : ℝ)
    (hTimes : times ∈ orderedTimesInIntervalObservedCountSector
      (earlierCount + laterCount) lower observationTime duration earlierCount) :
    FiniteJumpHistory.stateAtTimeVector states times observationTime =
      states (finiteStateTimeDependentMarkovCutStateIndex earlierCount laterCount) := by
  unfold FiniteJumpHistory.stateAtTimeVector FiniteJumpHistory.stateIndexAtTimeVector
  apply congrArg states
  apply Fin.ext
  exact hTimes.2

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The literal state-at-time integrand on one exact observed-count fibre is the cut-state
integrand used by future-word erasure.  The equality uses the proved-null cut boundary to replace
the càdlàg fibre by the strict before/after sector. -/
theorem lintegral_finiteStateTimeDependentMarkovUniformizedStateAtTime_observedCountSector
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration observationTime : ℝ)
    (hObservationTime : 0 ≤ observationTime)
    (hObservationDuration : observationTime ≤ duration)
    (earlierCount laterCount : ℕ) (observed : State) :
    (∫⁻ times : Fin (earlierCount + laterCount) → ℝ in
        orderedTimesInIntervalObservedCountSector
          (earlierCount + laterCount) 0 observationTime duration earlierCount,
      ENNReal.ofReal
        (∑ states : Fin (earlierCount + laterCount + 1) → State,
          if FiniteJumpHistory.stateAtTimeVector states times observationTime = observed then
            finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states times
          else 0)) =
      ∫⁻ times : Fin (earlierCount + laterCount) → ℝ in
        orderedJumpTimesCutSector earlierCount laterCount 0 observationTime duration,
        ENNReal.ofReal
          (∑ states : Fin (earlierCount + laterCount + 1) → State,
            if states (finiteStateTimeDependentMarkovCutStateIndex
                earlierCount laterCount) = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0) := by
  let stateAtTimeIntegrand :
      (Fin (earlierCount + laterCount) → ℝ) → ℝ≥0∞ := fun times ↦
    ENNReal.ofReal
      (∑ states : Fin (earlierCount + laterCount + 1) → State,
        if FiniteJumpHistory.stateAtTimeVector states times observationTime = observed then
          finiteStateTimeDependentMarkovUniformizedSliceDensity
            initial rates duration states times
        else 0)
  let cutStateIntegrand :
      (Fin (earlierCount + laterCount) → ℝ) → ℝ≥0∞ := fun times ↦
    ENNReal.ofReal
      (∑ states : Fin (earlierCount + laterCount + 1) → State,
        if states (finiteStateTimeDependentMarkovCutStateIndex
            earlierCount laterCount) = observed then
          finiteStateTimeDependentMarkovUniformizedSliceDensity
            initial rates duration states times
        else 0)
  calc
    (∫⁻ times in orderedTimesInIntervalObservedCountSector
        (earlierCount + laterCount) 0 observationTime duration earlierCount,
      stateAtTimeIntegrand times) =
        ∫⁻ times in orderedTimesInIntervalObservedCountSector
          (earlierCount + laterCount) 0 observationTime duration earlierCount,
          cutStateIntegrand times := by
      apply setLIntegral_congr_fun
        (measurableSet_orderedTimesInIntervalObservedCountSector
          (earlierCount + laterCount) 0 observationTime duration earlierCount)
      intro times hTimes
      dsimp only [stateAtTimeIntegrand, cutStateIntegrand]
      congr 2
      funext states
      rw [FiniteJumpHistory.stateAtTimeVector_eq_cutStateIndex_of_mem_observedCountSector
        earlierCount laterCount states times 0 observationTime duration hTimes]
    _ = ∫⁻ times in orderedJumpTimesCutSector
          earlierCount laterCount 0 observationTime duration,
          cutStateIntegrand times := by
      rw [volume_restrict_orderedTimesInIntervalObservedCountSector_eq_cutSector
        earlierCount laterCount 0 observationTime duration
        hObservationTime hObservationDuration]
    _ = _ := rfl

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Summing all complete virtual event-count sectors at an intermediate time recovers exactly
the endpoint probability at that time, independently of the larger history
horizon. -/
theorem tsum_finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration observationTime : ℝ)
    (hObservationTime : 0 ≤ observationTime)
    (hObservationDuration : observationTime ≤ duration)
    (observed : State) :
    (∑' eventCount : ℕ,
      finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
        initial rates duration observationTime eventCount observed) =
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates observationTime observed := by
  unfold finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
  simp_rw [show ∀ eventCount : ℕ,
      orderedJumpTimes eventCount duration =
        orderedTimesInInterval eventCount 0 duration by
    intro eventCount
    rfl]
  let sectorMass : (eventCount : ℕ) → Fin (eventCount + 1) → ℝ≥0∞ :=
    fun eventCount observedCount ↦
      ∫⁻ times : Fin eventCount → ℝ in
          orderedTimesInIntervalObservedCountSector
            eventCount 0 observationTime duration observedCount,
        ENNReal.ofReal
          (∑ states : Fin (eventCount + 1) → State,
            if FiniteJumpHistory.stateAtTimeVector states times observationTime = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)
  have hPartition (eventCount : ℕ) :
      (∫⁻ times : Fin eventCount → ℝ in
          orderedTimesInInterval eventCount 0 duration,
        ENNReal.ofReal
          (∑ states : Fin (eventCount + 1) → State,
            if FiniteJumpHistory.stateAtTimeVector states times observationTime = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)) =
        ∑ observedCount : Fin (eventCount + 1),
          sectorMass eventCount observedCount := by
    exact lintegral_orderedTimesInInterval_eq_sum_observedCountSector
      eventCount 0 observationTime duration _
  simp_rw [hPartition]
  rw [ENNReal.tsum_nat_sum_finSucc_eq_tsum_tsum_split]
  dsimp only [sectorMass]
  calc
    (∑' earlierCount : ℕ, ∑' laterCount : ℕ,
      ∫⁻ times : Fin (earlierCount + laterCount) → ℝ in
          orderedTimesInIntervalObservedCountSector
            (earlierCount + laterCount) 0 observationTime duration earlierCount,
        ENNReal.ofReal
          (∑ states : Fin (earlierCount + laterCount + 1) → State,
            if FiniteJumpHistory.stateAtTimeVector states times observationTime = observed then
              finiteStateTimeDependentMarkovUniformizedSliceDensity
                initial rates duration states times
            else 0)) =
        ∑' earlierCount : ℕ, ∑' laterCount : ℕ,
          ∫⁻ times : Fin (earlierCount + laterCount) → ℝ in
              orderedJumpTimesCutSector
                earlierCount laterCount 0 observationTime duration,
            ENNReal.ofReal
              (∑ states : Fin (earlierCount + laterCount + 1) → State,
                if states (finiteStateTimeDependentMarkovCutStateIndex
                    earlierCount laterCount) = observed then
                  finiteStateTimeDependentMarkovUniformizedSliceDensity
                    initial rates duration states times
                else 0) := by
      apply tsum_congr
      intro earlierCount
      apply tsum_congr
      intro laterCount
      exact
        lintegral_finiteStateTimeDependentMarkovUniformizedStateAtTime_observedCountSector
          initial rates duration observationTime hObservationTime hObservationDuration
          earlierCount laterCount observed
    _ = ∑' earlierCount : ℕ,
        ENNReal.ofReal
            ((rates.uniformizationRate : ℝ) ^ earlierCount *
              Real.exp (-((rates.uniformizationRate : ℝ) * observationTime))) *
          finiteStateTimeDependentMarkovUniformizedEndpointCoefficient
            initial rates observationTime earlierCount observed := by
      apply tsum_congr
      intro earlierCount
      exact
        tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_cutSector
          initial rates duration observationTime hObservationDuration earlierCount observed
    _ = finiteStateTimeDependentMarkovEndpointProbability
          initial rates observationTime observed := by
      unfold finiteStateTimeDependentMarkovEndpointProbability
      unfold finiteStateTimeDependentMarkovUniformizedEndpointSeries
      have hClock (earlierCount : ℕ) :
          ENNReal.ofReal
              ((rates.uniformizationRate : ℝ) ^ earlierCount *
                Real.exp (-((rates.uniformizationRate : ℝ) * observationTime))) =
            ENNReal.ofReal
                (Real.exp (-((rates.uniformizationRate : ℝ) * observationTime))) *
              (rates.uniformizationRate : ℝ≥0∞) ^ earlierCount := by
        rw [ENNReal.ofReal_mul (pow_nonneg
          (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity) earlierCount)]
        rw [ENNReal.coe_nnreal_eq]
        rw [← ENNReal.ofReal_pow
          (show 0 ≤ (rates.uniformizationRate : ℝ) by positivity)]
        ac_rfl
      simp_rw [hClock, mul_assoc]
      rw [ENNReal.tsum_mul_left]

/-- Every intermediate-time marginal of the complete uniformized history law is the
endpoint law at that time.  In particular, the marginal is independent of the later observation
horizon once the latter contains the observation time. -/
theorem map_stateAtTime_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration observationTime : ℝ≥0)
    (hObservationDuration : observationTime ≤ duration) :
    Measure.map (fun history : FiniteJumpHistory State ↦
        history.stateAtTime observationTime)
        (finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration) =
      (finiteStateTimeDependentMarkovEndpointPMF
        initial rates observationTime).toMeasure := by
  apply Measure.ext_of_singleton
  intro observed
  rw [Measure.map_apply
    (FiniteJumpHistory.measurable_stateAtTime observationTime)
    (measurableSet_singleton observed)]
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [Measure.sum_apply _
    ((FiniteJumpHistory.measurable_stateAtTime observationTime)
      (measurableSet_singleton observed))]
  simp_rw [finiteStateTimeDependentMarkovUniformizedCountMeasure_stateAtTime]
  rw [tsum_finiteStateTimeDependentMarkovUniformizedStateAtTimeCountMass
    initial rates duration observationTime observationTime.coe_nonneg
      (NNReal.coe_le_coe.2 hObservationDuration) observed]
  rw [PMF.toMeasure_apply_singleton
    (finiteStateTimeDependentMarkovEndpointPMF initial rates observationTime)
    observed (measurableSet_singleton observed)]
  exact (finiteStateTimeDependentMarkovEndpointPMF_apply
    initial rates observationTime observed).symm

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Deleting virtual self-events preserves the occupied state at every time on a strictly ordered
history slice.  This is the pathwise statement needed to transport intermediate marginals from
the virtual common-clock source to the physical reduced source. -/
theorem FiniteJumpHistory.stateAtTime_deleteSelfEventsSlice
    {eventCount : ℕ} (states : Fin (eventCount + 1) → State)
    (times : Fin eventCount → ℝ) (observationTime : ℝ)
    (hTimes : StrictMono times) :
    (FiniteJumpHistory.deleteSelfEventsSlice states times).stateAtTime observationTime =
      FiniteJumpHistory.stateAtTimeVector states times observationTime := by
  let originalObserved :=
    FiniteJumpHistory.eventCountAtOrBeforeTimeVector times observationTime
  let reducedTimes : Fin (FiniteJumpHistory.genuineEventCount states) → ℝ :=
    fun index ↦ times (FiniteJumpHistory.genuineEventIndex states index)
  let reducedObserved :=
    FiniteJumpHistory.eventCountAtOrBeforeTimeVector reducedTimes observationTime
  have hReducedStrict : StrictMono reducedTimes :=
    hTimes.comp
      ((FiniteJumpHistory.genuineEventIndices states).orderEmbOfFin
        (rfl : (FiniteJumpHistory.genuineEventIndices states).card =
          FiniteJumpHistory.genuineEventCount states)).strictMono
  have hOriginalCharacterization (index : Fin eventCount) :
      times index ≤ observationTime ↔ index.val < originalObserved := by
    exact FiniteJumpHistory.eventTime_le_iff_val_lt_eventCountAtOrBefore
      hTimes observationTime index
  have hReducedCharacterization
      (index : Fin (FiniteJumpHistory.genuineEventCount states)) :
      reducedTimes index ≤ observationTime ↔ index.val < reducedObserved := by
    exact FiniteJumpHistory.eventTime_le_iff_val_lt_eventCountAtOrBefore
      hReducedStrict observationTime index
  have hOriginalObservedBound : originalObserved ≤ eventCount :=
    FiniteJumpHistory.eventCountAtOrBeforeTimeVector_le times observationTime
  have hReducedObservedBound :
      reducedObserved ≤ FiniteJumpHistory.genuineEventCount states :=
    FiniteJumpHistory.eventCountAtOrBeforeTimeVector_le reducedTimes observationTime
  by_cases hReducedZero : reducedObserved = 0
  · have hNoChange : ∀ index : Fin eventCount,
        0 ≤ index.val → index.val < originalObserved →
          states index.castSucc = states index.succ := by
      intro index _hZero hBefore
      by_contra hChange
      have hGenuine : index ∈ FiniteJumpHistory.genuineEventIndices states := by
        simpa [FiniteJumpHistory.genuineEventIndices] using hChange
      obtain ⟨selectedIndex, hSelectedIndex⟩ :=
        FiniteJumpHistory.exists_genuineEventIndex_eq states hGenuine
      have hSelectedTime : reducedTimes selectedIndex ≤ observationTime := by
        change times (FiniteJumpHistory.genuineEventIndex states selectedIndex) ≤
          observationTime
        rw [hSelectedIndex]
        exact (hOriginalCharacterization index).2 hBefore
      have hSelectedBefore := (hReducedCharacterization selectedIndex).1 hSelectedTime
      rw [hReducedZero] at hSelectedBefore
      omega
    have hState := FiniteJumpHistory.state_eq_of_no_change_between states
      (start := (0 : Fin (eventCount + 1)))
      (finish := ⟨originalObserved, Nat.lt_succ_of_le hOriginalObservedBound⟩)
      (Fin.zero_le _) hNoChange
    change (Fin.cases (states 0)
        (fun index ↦ states (FiniteJumpHistory.genuineEventIndex states index).succ)
          ⟨reducedObserved, Nat.lt_succ_of_le hReducedObservedBound⟩) =
      states ⟨originalObserved, Nat.lt_succ_of_le hOriginalObservedBound⟩
    rw [show (⟨reducedObserved, Nat.lt_succ_of_le hReducedObservedBound⟩ :
        Fin (FiniteJumpHistory.genuineEventCount states + 1)) = 0 by
      apply Fin.ext
      exact hReducedZero]
    rw [Fin.cases_zero]
    exact hState
  · have hReducedPositive : 0 < reducedObserved := Nat.pos_of_ne_zero hReducedZero
    let lastSelected : Fin (FiniteJumpHistory.genuineEventCount states) :=
      ⟨reducedObserved - 1, by omega⟩
    have hLastSelectedBefore : lastSelected.val < reducedObserved := by
      dsimp only [lastSelected]
      omega
    have hLastSelectedTime : reducedTimes lastSelected ≤ observationTime :=
      (hReducedCharacterization lastSelected).2 hLastSelectedBefore
    have hLastOriginalBefore :
        (FiniteJumpHistory.genuineEventIndex states lastSelected).val < originalObserved := by
      apply (hOriginalCharacterization
        (FiniteJumpHistory.genuineEventIndex states lastSelected)).1
      exact hLastSelectedTime
    let originalIndex : Fin (eventCount + 1) :=
      ⟨originalObserved, Nat.lt_succ_of_le hOriginalObservedBound⟩
    let selectedTarget : Fin (eventCount + 1) :=
      (FiniteJumpHistory.genuineEventIndex states lastSelected).succ
    have hSelectedTargetLe : selectedTarget ≤ originalIndex := by
      change (FiniteJumpHistory.genuineEventIndex states lastSelected).val + 1 ≤
        originalObserved
      omega
    have hNoChange : ∀ index : Fin eventCount,
        selectedTarget.val ≤ index.val → index.val < originalIndex.val →
          states index.castSucc = states index.succ := by
      intro index hAfter hBefore
      by_contra hChange
      have hGenuine : index ∈ FiniteJumpHistory.genuineEventIndices states := by
        simpa [FiniteJumpHistory.genuineEventIndices] using hChange
      obtain ⟨selectedIndex, hSelectedIndex⟩ :=
        FiniteJumpHistory.exists_genuineEventIndex_eq states hGenuine
      have hSelectedOrder : lastSelected < selectedIndex := by
        apply (((FiniteJumpHistory.genuineEventIndices states).orderEmbOfFin rfl).lt_iff_lt).mp
        change FiniteJumpHistory.genuineEventIndex states lastSelected <
          FiniteJumpHistory.genuineEventIndex states selectedIndex
        rw [hSelectedIndex]
        change (FiniteJumpHistory.genuineEventIndex states lastSelected).val < index.val
        change
          (FiniteJumpHistory.genuineEventIndex states lastSelected).val + 1 ≤ index.val
          at hAfter
        omega
      have hSelectedTime : reducedTimes selectedIndex ≤ observationTime := by
        change times (FiniteJumpHistory.genuineEventIndex states selectedIndex) ≤
          observationTime
        rw [hSelectedIndex]
        exact (hOriginalCharacterization index).2 hBefore
      have hSelectedBefore := (hReducedCharacterization selectedIndex).1 hSelectedTime
      change reducedObserved - 1 < selectedIndex.val at hSelectedOrder
      omega
    have hState := FiniteJumpHistory.state_eq_of_no_change_between states
      hSelectedTargetLe hNoChange
    have hReducedIndex :
        (⟨reducedObserved, Nat.lt_succ_of_le hReducedObservedBound⟩ :
          Fin (FiniteJumpHistory.genuineEventCount states + 1)) = lastSelected.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      change reducedObserved = (reducedObserved - 1) + 1
      omega
    change (Fin.cases (states 0)
        (fun index ↦ states (FiniteJumpHistory.genuineEventIndex states index).succ)
          ⟨reducedObserved, Nat.lt_succ_of_le hReducedObservedBound⟩) =
      states originalIndex
    rw [hReducedIndex, Fin.cases_succ]
    exact hState

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Whole-history form of occupied-state preservation under self-event deletion. -/
theorem FiniteJumpHistory.stateAtTime_deleteSelfEvents
    (history : FiniteJumpHistory State) (duration observationTime : ℝ)
    (hOrdered : history.OrderedBefore duration) :
    history.deleteSelfEvents.stateAtTime observationTime =
      history.stateAtTime observationTime := by
  rcases history with ⟨eventCount, states, times⟩
  exact FiniteJumpHistory.stateAtTime_deleteSelfEventsSlice
    states times observationTime hOrdered.2

/-- The physical reduced history source has the same exact projective intermediate-time
marginals as its virtual common-clock realization. -/
theorem map_stateAtTime_finiteStateTimeDependentMarkovReducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration observationTime : ℝ≥0)
    (hObservationDuration : observationTime ≤ duration) :
    Measure.map (fun history : FiniteJumpHistory State ↦
        history.stateAtTime observationTime)
        (finiteStateTimeDependentMarkovReducedHistoryMeasure
          initial rates duration) =
      (finiteStateTimeDependentMarkovEndpointPMF
        initial rates observationTime).toMeasure := by
  unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
  rw [Measure.map_map
    (FiniteJumpHistory.measurable_stateAtTime observationTime)
    FiniteJumpHistory.measurable_deleteSelfEvents]
  rw [Measure.map_congr]
  · exact map_stateAtTime_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
      initial rates duration observationTime hObservationDuration
  · filter_upwards [
      ae_orderedBefore_finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration] with history hOrdered
    exact FiniteJumpHistory.stateAtTime_deleteSelfEvents
      history duration observationTime hOrdered

end

end FiniteMarkovProcesses.Probability
