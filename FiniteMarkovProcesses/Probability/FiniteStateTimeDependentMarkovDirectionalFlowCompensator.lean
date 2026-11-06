/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMarkedTransitionCompensator
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovTransitionTestMoment
import FiniteMarkovProcesses.Probability.NatSuccessorIndexSplit

/-!
# Directional-flow compensator for bounded time-dependent Markov laws

This module identifies the expected cumulative count of one directed virtual transition with the
endpoint-probability--intensity integral.  It first expands the complete-history
observable into marked event sectors and then applies the exact before/after resummation.

## Main result

- `lintegral_directedTransitionCount_uniformizedHistoryMeasure`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Real transition test selecting one ordered edge and applying a nonnegative physical-time
weight to it. -/
def finiteStateDirectedTransitionNNRealWeightTest
    (weight : ℝ → ℝ≥0) (source target : State)
    (eventTime : ℝ) (eventSource eventTarget : State) : ℝ :=
  if eventSource = source ∧ eventTarget = target then weight eventTime else 0

/-- Real transition test selecting one ordered edge and applying an arbitrary physical-time
weight to it. -/
def finiteStateDirectedTransitionWeightTest
    (weight : ℝ → ℝ) (source target : State)
    (eventTime : ℝ) (eventSource eventTarget : State) : ℝ :=
  if eventSource = source ∧ eventTarget = target then weight eventTime else 0

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A measurable nonnegative time weight gives a measurable edge-selected transition test. -/
theorem measurable_finiteStateDirectedTransitionNNRealWeightTest
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight)
    (source target eventSource eventTarget : State) :
    Measurable fun eventTime ↦
      finiteStateDirectedTransitionNNRealWeightTest
        weight source target eventTime eventSource eventTarget := by
  by_cases hEdge : eventSource = source ∧ eventTarget = target
  · simpa only [finiteStateDirectedTransitionNNRealWeightTest, ite_eq_left hEdge,
      Function.comp_def] using
      NNReal.continuous_coe.measurable.comp hWeight
  · simp only [finiteStateDirectedTransitionNNRealWeightTest, hEdge, ite_false]
    exact measurable_const

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A measurable real time weight gives a measurable edge-selected transition test. -/
theorem measurable_finiteStateDirectedTransitionWeightTest
    (weight : ℝ → ℝ) (hWeight : Measurable weight)
    (source target eventSource eventTarget : State) :
    Measurable fun eventTime ↦
      finiteStateDirectedTransitionWeightTest
        weight source target eventTime eventSource eventTarget := by
  by_cases hEdge : eventSource = source ∧ eventTarget = target
  · simpa only [finiteStateDirectedTransitionWeightTest, ite_eq_left hEdge] using hWeight
  · simp only [finiteStateDirectedTransitionWeightTest, hEdge, ite_false]
    exact measurable_const

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Every edge-selected nonnegative transition test is pointwise nonnegative. -/
theorem finiteStateDirectedTransitionNNRealWeightTest_nonneg
    (weight : ℝ → ℝ≥0) (source target : State)
    (eventTime : ℝ) (eventSource eventTarget : State) :
    0 ≤ finiteStateDirectedTransitionNNRealWeightTest
      weight source target eventTime eventSource eventTarget := by
  unfold finiteStateDirectedTransitionNNRealWeightTest
  split
  · exact (weight eventTime).coe_nonneg
  · exact le_rfl

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A signed edge test is the difference of its nonnegative positive and negative parts. -/
theorem finiteStateDirectedTransitionWeightTest_eq_positivePart_sub_negativePart
    (weight : ℝ → ℝ) (source target : State)
    (eventTime : ℝ) (eventSource eventTarget : State) :
    finiteStateDirectedTransitionWeightTest
        weight source target eventTime eventSource eventTarget =
      finiteStateDirectedTransitionNNRealWeightTest
          (fun time ↦ Real.toNNReal (weight time)) source target
          eventTime eventSource eventTarget -
        finiteStateDirectedTransitionNNRealWeightTest
          (fun time ↦ Real.toNNReal (-weight time)) source target
          eventTime eventSource eventTarget := by
  by_cases hEdge : eventSource = source ∧ eventTarget = target
  · simp only [finiteStateDirectedTransitionWeightTest,
      finiteStateDirectedTransitionNNRealWeightTest, hEdge]
    by_cases hWeightNonnegative : 0 ≤ weight eventTime
    · rw [Real.coe_toNNReal _ hWeightNonnegative,
        Real.toNNReal_of_nonpos (neg_nonpos.mpr hWeightNonnegative)]
      simp
    · have hWeightNonpositive : weight eventTime ≤ 0 := le_of_not_ge hWeightNonnegative
      rw [Real.toNNReal_of_nonpos hWeightNonpositive,
        Real.coe_toNNReal _ (neg_nonneg.mpr hWeightNonpositive)]
      simp
  · simp only [finiteStateDirectedTransitionWeightTest,
      finiteStateDirectedTransitionNNRealWeightTest, hEdge, ite_false, sub_zero]

/-- The whole-history sum of one nonnegative weighted directed-edge test. -/
noncomputable def finiteJumpHistoryDirectedTransitionNNRealWeightSum
    (weight : ℝ → ℝ≥0) (source target : State)
    (history : FiniteJumpHistory State) : ℝ :=
  finiteJumpHistoryTransitionTestSum
    (finiteStateDirectedTransitionNNRealWeightTest weight source target) history

/-- The whole-history sum of one arbitrary real weighted directed-edge test. -/
noncomputable def finiteJumpHistoryDirectedTransitionWeightSum
    (weight : ℝ → ℝ) (source target : State)
    (history : FiniteJumpHistory State) : ℝ :=
  finiteJumpHistoryTransitionTestSum
    (finiteStateDirectedTransitionWeightTest weight source target) history

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A signed weighted edge sum is the difference of its nonnegative part sums. -/
theorem finiteJumpHistoryDirectedTransitionWeightSum_eq_positivePart_sub_negativePart
    (weight : ℝ → ℝ) (source target : State) (history : FiniteJumpHistory State) :
    finiteJumpHistoryDirectedTransitionWeightSum weight source target history =
      finiteJumpHistoryDirectedTransitionNNRealWeightSum
          (fun time ↦ Real.toNNReal (weight time)) source target history -
        finiteJumpHistoryDirectedTransitionNNRealWeightSum
          (fun time ↦ Real.toNNReal (-weight time)) source target history := by
  unfold finiteJumpHistoryDirectedTransitionWeightSum
    finiteJumpHistoryDirectedTransitionNNRealWeightSum
    finiteJumpHistoryTransitionTestSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _hIndex
  exact finiteStateDirectedTransitionWeightTest_eq_positivePart_sub_negativePart
    weight source target (history.jumpTimes index)
      (history.states index.castSucc) (history.states index.succ)

/-- The nonnegative weighted directed-edge history sum is measurable. -/
theorem measurable_finiteJumpHistoryDirectedTransitionNNRealWeightSum
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) (source target : State) :
    Measurable (finiteJumpHistoryDirectedTransitionNNRealWeightSum
      weight source target : FiniteJumpHistory State → ℝ) :=
  measurable_finiteJumpHistoryTransitionTestSum _ fun eventSource eventTarget ↦
    measurable_finiteStateDirectedTransitionNNRealWeightTest
      weight hWeight source target eventSource eventTarget

/-- The real weighted directed-edge history sum is measurable. -/
theorem measurable_finiteJumpHistoryDirectedTransitionWeightSum
    (weight : ℝ → ℝ) (hWeight : Measurable weight) (source target : State) :
    Measurable (finiteJumpHistoryDirectedTransitionWeightSum
      weight source target : FiniteJumpHistory State → ℝ) :=
  measurable_finiteJumpHistoryTransitionTestSum _ fun eventSource eventTarget ↦
    measurable_finiteStateDirectedTransitionWeightTest
      weight hWeight source target eventSource eventTarget

/-- On a fixed virtual-event-count slice, a nonnegative weighted directed-edge sum is the finite
sum of its weighted marked-sector integrals. -/
theorem lintegral_directedTransitionNNRealWeightSum_uniformizedCountMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (eventCount : ℕ) (source target : State)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) :
    (∫⁻ history : FiniteJumpHistory State,
        ENNReal.ofReal
          (finiteJumpHistoryDirectedTransitionNNRealWeightSum
            weight source target history)
      ∂finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount) =
      ∑ index : Fin eventCount,
        ∫⁻ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
          (weight (times index) : ℝ≥0∞) *
            ENNReal.ofReal
              (∑ states : Fin (eventCount + 1) → State,
                if states index.castSucc = source ∧ states index.succ = target then
                  finiteStateTimeDependentMarkovUniformizedSliceDensity
                    initial rates duration states times
                else 0) := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [lintegral_sum_measure, tsum_fintype]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure]
  have hObservable :=
    (measurable_finiteJumpHistoryDirectedTransitionNNRealWeightSum
      weight hWeight source target).ennreal_ofReal
  simp_rw [lintegral_map hObservable (measurable_embedJumpTimes eventCount _)]
  have hEmbeddedObservable (states : Fin (eventCount + 1) → State) :
      Measurable fun times : Fin eventCount → ℝ ↦
        ENNReal.ofReal
          (finiteJumpHistoryDirectedTransitionNNRealWeightSum
            weight source target (embedJumpTimes eventCount states times)) :=
    hObservable.comp (measurable_embedJumpTimes eventCount states)
  simp_rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration _).ennreal_ofReal (hEmbeddedObservable _)]
  rw [← lintegral_finsetSum]
  · rw [← lintegral_finsetSum]
    · apply setLIntegral_congr_fun
        (measurableSet_orderedJumpTimes eventCount duration)
      intro times _hTimes
      have hStateExpansion (states : Fin (eventCount + 1) → State) :
          ENNReal.ofReal
                (finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times) *
              ENNReal.ofReal
                (finiteJumpHistoryDirectedTransitionNNRealWeightSum
                  weight source target (embedJumpTimes eventCount states times)) =
            ∑ index : Fin eventCount,
              (weight (times index) : ℝ≥0∞) *
                ENNReal.ofReal
                  (if states index.castSucc = source ∧ states index.succ = target then
                    finiteStateTimeDependentMarkovUniformizedSliceDensity
                      initial rates duration states times
                  else 0) := by
        unfold finiteJumpHistoryDirectedTransitionNNRealWeightSum
          finiteJumpHistoryTransitionTestSum
          finiteStateDirectedTransitionNNRealWeightTest embedJumpTimes
          FiniteJumpHistory.states FiniteJumpHistory.jumpTimes
          FiniteJumpHistory.jumpCount
        simp only
        rw [ENNReal.ofReal_sum_of_nonneg]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro index _hIndex
          by_cases hEdge : states index.castSucc = source ∧ states index.succ = target
          · rw [ite_eq_left hEdge, ite_eq_left hEdge]
            rw [ENNReal.ofReal_coe_nnreal]
            ac_rfl
          · rw [ite_eq_right hEdge, ite_eq_right hEdge]
            simp
        · intro index _hIndex
          exact finiteStateDirectedTransitionNNRealWeightTest_nonneg
            weight source target (times index)
              (states index.castSucc) (states index.succ)
      simp only [Pi.mul_apply]
      simp_rw [hStateExpansion]
      rw [← Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro index _hIndex
      rw [← Finset.mul_sum]
      congr 1
      rw [← ENNReal.ofReal_sum_of_nonneg]
      intro states _hStates
      split
      · exact finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
          initial rates duration states times
      · exact le_rfl
    · intro index _hIndex
      have hMarkedDensity : Measurable fun times : Fin eventCount → ℝ ↦
          ENNReal.ofReal
            (∑ states : Fin (eventCount + 1) → State,
              if states index.castSucc = source ∧ states index.succ = target then
                finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times
              else 0) := by
        apply Measurable.ennreal_ofReal
        apply Finset.measurable_sum
        intro states _hStates
        by_cases hEdge : states index.castSucc = source ∧ states index.succ = target
        · simpa only [ite_eq_left hEdge] using
            measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
              initial rates duration states
        · simp only [hEdge, ite_false]
          exact measurable_const
      exact (hWeight.coe_nnreal_ennreal.comp (measurable_pi_apply index)).mul
        hMarkedDensity
  · intro states _hStates
    exact (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration states).ennreal_ofReal.mul (hEmbeddedObservable states)

/-- Under the complete virtual law, a nonnegative weighted directed-edge sum has the exact
endpoint-probability--intensity compensator integral. -/
theorem lintegral_directedTransitionNNRealWeightSum_uniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (source target : State)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) :
    (∫⁻ history : FiniteJumpHistory State,
        ENNReal.ofReal
          (finiteJumpHistoryDirectedTransitionNNRealWeightSum
            weight source target history)
      ∂finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ≥0∞) *
          finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) := by
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [lintegral_sum_measure]
  simp_rw [lintegral_directedTransitionNNRealWeightSum_uniformizedCountMeasure
    initial rates duration _ source target weight hWeight]
  rw [ENNReal.tsum_nat_sum_fin_eq_tsum_tsum_marked]
  exact
    tsum_tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition_mul
      initial rates duration source target weight hWeight

omit [Fintype State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- Self-event deletion preserves every nonnegative weighted count of one off-diagonal edge. -/
theorem finiteJumpHistoryDirectedTransitionNNRealWeightSum_deleteSelfEvents
    (weight : ℝ → ℝ≥0) {source target : State} (hNe : source ≠ target)
    (history : FiniteJumpHistory State) :
    finiteJumpHistoryDirectedTransitionNNRealWeightSum
        weight source target history.deleteSelfEvents =
      finiteJumpHistoryDirectedTransitionNNRealWeightSum
        weight source target history := by
  unfold finiteJumpHistoryDirectedTransitionNNRealWeightSum
  apply finiteJumpHistoryTransitionTestSum_deleteSelfEvents
  intro eventTime state
  unfold finiteStateDirectedTransitionNNRealWeightTest
  have hNotEdge : ¬(state = source ∧ state = target) := by
    intro hEdge
    exact hNe (hEdge.1.symm.trans hEdge.2)
  rw [ite_eq_right hNotEdge]

/-- For an off-diagonal edge, the nonnegative weighted virtual compensator transports to the
physical reduced law and restores the genuine jump rate. -/
theorem lintegral_directedTransitionNNRealWeightSum_reducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight) :
    (∫⁻ history : FiniteJumpHistory State,
        ENNReal.ofReal
          (finiteJumpHistoryDirectedTransitionNNRealWeightSum
            weight source target history)
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ≥0∞) *
          finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal (rates.rate markedTime source target : ℝ) := by
  calc
    (∫⁻ history : FiniteJumpHistory State,
        ENNReal.ofReal
          (finiteJumpHistoryDirectedTransitionNNRealWeightSum
            weight source target history)
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
        ∫⁻ history : FiniteJumpHistory State,
          ENNReal.ofReal
            (finiteJumpHistoryDirectedTransitionNNRealWeightSum
              weight source target history)
        ∂finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration := by
      unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
      have hObservable :=
        (measurable_finiteJumpHistoryDirectedTransitionNNRealWeightSum
          weight hWeight source target).ennreal_ofReal
      rw [lintegral_map hObservable FiniteJumpHistory.measurable_deleteSelfEvents]
      apply lintegral_congr
      intro history
      rw [finiteJumpHistoryDirectedTransitionNNRealWeightSum_deleteSelfEvents
        weight hNe history]
    _ = ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ≥0∞) *
          finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) :=
      lintegral_directedTransitionNNRealWeightSum_uniformizedHistoryMeasure
        initial rates duration source target weight hWeight
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro markedTime _hMarkedTime
      simp only
      rw [finiteStateTimeDependentMarkovUniformizedTransitionIntensity_of_ne
        rates markedTime hNe]

/-- On a fixed virtual-event-count slice, the terminal directed-count integral is the finite sum
of its marked-edge sector integrals. -/
theorem lintegral_directedTransitionCount_uniformizedCountMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (eventCount : ℕ) (source target : State) :
    (∫⁻ history : FiniteJumpHistory State,
        (history.directedTransitionCountAtTime duration source target : ℝ≥0∞)
      ∂finiteStateTimeDependentMarkovUniformizedCountMeasure
        initial rates duration eventCount) =
      ∑ index : Fin eventCount,
        ∫⁻ times : Fin eventCount → ℝ in orderedJumpTimes eventCount duration,
          ENNReal.ofReal
            (∑ states : Fin (eventCount + 1) → State,
              if states index.castSucc = source ∧ states index.succ = target then
                finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times
              else 0) := by
  unfold finiteStateTimeDependentMarkovUniformizedCountMeasure
  rw [lintegral_sum_measure, tsum_fintype]
  simp_rw [finiteStateTimeDependentMarkovUniformizedWordSliceMeasure]
  have hCount : Measurable fun history : FiniteJumpHistory State ↦
      (history.directedTransitionCountAtTime duration source target : ℝ≥0∞) :=
    (measurable_of_countable fun count : ℕ ↦ (count : ℝ≥0∞)).comp
      (FiniteJumpHistory.measurable_directedTransitionCountAtTime duration source target)
  simp_rw [lintegral_map hCount (measurable_embedJumpTimes eventCount _)]
  have hEmbeddedCount (states : Fin (eventCount + 1) → State) :
      Measurable fun times : Fin eventCount → ℝ ↦
        ((embedJumpTimes eventCount states times).directedTransitionCountAtTime
          duration source target : ℝ≥0∞) :=
    (measurable_of_countable fun count : ℕ ↦ (count : ℝ≥0∞)).comp
      ((FiniteJumpHistory.measurable_directedTransitionCountAtTimeVector
        duration source target).comp (measurable_const.prodMk measurable_id))
  simp_rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration _).ennreal_ofReal (hEmbeddedCount _)]
  rw [← lintegral_finsetSum]
  · rw [← lintegral_finsetSum]
    · apply setLIntegral_congr_fun
        (measurableSet_orderedJumpTimes eventCount duration)
      intro times hTimes
      have hStateExpansion (states : Fin (eventCount + 1) → State) :
          ((fun times ↦ ENNReal.ofReal
                (finiteStateTimeDependentMarkovUniformizedSliceDensity
                  initial rates duration states times)) *
              fun times ↦
                ((embedJumpTimes eventCount states times).directedTransitionCountAtTime
                  duration source target : ℝ≥0∞)) times =
            ∑ index : Fin eventCount,
              ENNReal.ofReal
                (if states index.castSucc = source ∧ states index.succ = target then
                  finiteStateTimeDependentMarkovUniformizedSliceDensity
                    initial rates duration states times
                else 0) := by
        simp only [Pi.mul_apply]
        unfold embedJumpTimes FiniteJumpHistory.directedTransitionCountAtTime
          FiniteJumpHistory.directedTransitionCountAtTimeVector
          FiniteJumpHistory.states FiniteJumpHistory.jumpTimes FiniteJumpHistory.jumpCount
        simp only
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _hIndex
        rw [mul_ite]
        by_cases hEdge : states index.castSucc = source ∧ states index.succ = target
        · rw [ite_eq_left hEdge]
          have hEventTime : times index ≤ (duration : ℝ) := (hTimes.1 index).2.le
          rw [ite_eq_left ⟨hEventTime, hEdge⟩]
          simp
        · rw [ite_eq_right hEdge]
          have hNotSelected : ¬(times index ≤ (duration : ℝ) ∧
              states index.castSucc = source ∧ states index.succ = target) := by
            intro hSelected
            exact hEdge hSelected.2
          rw [ite_eq_right hNotSelected]
          simp
      simp_rw [hStateExpansion]
      rw [← Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro index _hIndex
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · intro states _hStates
        split
        · exact finiteStateTimeDependentMarkovUniformizedSliceDensity_nonneg
            initial rates duration states times
        · exact le_rfl
    · intro index _hIndex
      apply Measurable.ennreal_ofReal
      apply Finset.measurable_sum
      intro states _hStates
      by_cases hEdge : states index.castSucc = source ∧ states index.succ = target
      · simpa only [ite_eq_left hEdge] using
          measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
            initial rates duration states
      · simp only [hEdge, ite_false]
        exact measurable_const
  · intro states _hStates
    exact (measurable_finiteStateTimeDependentMarkovUniformizedSliceDensity
      initial rates duration states).ennreal_ofReal.mul (hEmbeddedCount states)

/-- The terminal expected virtual directed count is the physical-time integral of the exact
endpoint probability times the restored common-clock transition intensity. -/
theorem lintegral_directedTransitionCount_uniformizedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (source target : State) :
    (∫⁻ history : FiniteJumpHistory State,
        (history.directedTransitionCountAtTime duration source target : ℝ≥0∞)
      ∂finiteStateTimeDependentMarkovUniformizedHistoryMeasure
        initial rates duration) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) := by
  unfold finiteStateTimeDependentMarkovUniformizedHistoryMeasure
  rw [lintegral_sum_measure]
  simp_rw [
    lintegral_directedTransitionCount_uniformizedCountMeasure]
  rw [ENNReal.tsum_nat_sum_fin_eq_tsum_tsum_marked]
  exact
    tsum_tsum_lintegral_finiteStateTimeDependentMarkovUniformizedSliceDensity_markedTransition
      initial rates duration source target

/-- For an off-diagonal edge, self-event deletion transports the virtual compensator to the
physical reduced source and restores the genuine time-dependent jump rate. -/
theorem lintegral_directedTransitionCount_reducedHistoryMeasure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target) :
    (∫⁻ history : FiniteJumpHistory State,
        (history.directedTransitionCountAtTime duration source target : ℝ≥0∞)
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
      ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal (rates.rate markedTime source target : ℝ) := by
  calc
    (∫⁻ history : FiniteJumpHistory State,
        (history.directedTransitionCountAtTime duration source target : ℝ≥0∞)
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
        ∫⁻ history : FiniteJumpHistory State,
          (history.directedTransitionCountAtTime duration source target : ℝ≥0∞)
        ∂finiteStateTimeDependentMarkovUniformizedHistoryMeasure
          initial rates duration := by
      unfold finiteStateTimeDependentMarkovReducedHistoryMeasure
      have hCount : Measurable fun history : FiniteJumpHistory State ↦
          (history.directedTransitionCountAtTime duration source target : ℝ≥0∞) :=
        (measurable_of_countable fun count : ℕ ↦ (count : ℝ≥0∞)).comp
          (FiniteJumpHistory.measurable_directedTransitionCountAtTime
            duration source target)
      rw [lintegral_map hCount FiniteJumpHistory.measurable_deleteSelfEvents]
      apply lintegral_congr
      intro history
      exact_mod_cast directedTransitionCountAtTime_deleteSelfEvents
        duration hNe history
    _ = ∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) :=
      lintegral_directedTransitionCount_uniformizedHistoryMeasure
        initial rates duration source target
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro markedTime _hMarkedTime
      change finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal
            (finiteStateTimeDependentMarkovUniformizedTransitionIntensity
              rates markedTime source target) =
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal (rates.rate markedTime source target : ℝ)
      rw [finiteStateTimeDependentMarkovUniformizedTransitionIntensity_of_ne
        rates markedTime hNe]

end

end FiniteMarkovProcesses.Probability
