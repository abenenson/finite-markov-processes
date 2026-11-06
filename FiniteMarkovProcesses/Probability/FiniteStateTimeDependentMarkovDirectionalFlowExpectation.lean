/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalTestConcentration
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovForwardEquation

/-!
# Signed directional-flow expectations for bounded time-dependent Markov laws

The nonnegative marked-transition compensator is extended to arbitrary bounded measurable real
weights on one ordered edge.  The resulting expectation is then inserted into the
existing finite-independent replica concentration theorem.

## Main results

- `integral_directedTransitionWeightSum_reducedHistoryMeasure_eq`.
- The heterogeneous-replica weighted-flow deviation theorem.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Mean of one physical-time weight tested against one ordered directional flow. -/
noncomputable def finiteStateTimeDependentMarkovDirectedTransitionWeightMean
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (weight : ℝ → ℝ) (source target : State) : ℝ :=
  ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
    weight markedTime *
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime source).toReal *
      (rates.rate markedTime source target : ℝ)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- A bounded nonnegative weight times occupied-source probability and physical rate is
integrable on every finite open physical-time interval. -/
theorem integrableOn_nnrealWeight_mul_endpointProbability_mul_rate
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight)
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ time, (weight time : ℝ) ≤ weightBound) :
    IntegrableOn (fun markedTime : ℝ ↦
      (weight markedTime : ℝ) *
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source).toReal *
        (rates.rate markedTime source target : ℝ))
      (Ioo 0 (duration : ℝ)) := by
  have hEndpointMeasurable : Measurable fun markedTime : ℝ ↦
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime source := by
    unfold finiteStateTimeDependentMarkovEndpointProbability
    have hSurvival : Measurable fun markedTime : ℝ ↦
        ENNReal.ofReal
          (Real.exp (-((rates.uniformizationRate : ℝ) * markedTime))) := by
      fun_prop
    exact hSurvival.mul
      (measurable_finiteStateTimeDependentMarkovUniformizedEndpointSeries
        initial rates source)
  have hRateMeasurable : Measurable fun markedTime : ℝ ↦
      (rates.rate markedTime source target : ℝ) :=
    NNReal.continuous_coe.measurable.comp (rates.measurable_rate source target)
  have hIntegrandMeasurable : Measurable fun markedTime : ℝ ↦
      (weight markedTime : ℝ) *
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source).toReal *
        (rates.rate markedTime source target : ℝ) :=
    ((NNReal.continuous_coe.measurable.comp hWeight).mul
      hEndpointMeasurable.ennreal_toReal).mul hRateMeasurable
  apply IntegrableOn.of_bound measure_Ioo_lt_top
    hIntegrandMeasurable.aestronglyMeasurable
    (weightBound * (rates.uniformizationRate : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with markedTime hMarkedTime
  have hEndpointENNRealLeOne :
      finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source ≤ 1 := by
    have hCoordinate :
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source ≤
          ∑ observed : State,
            finiteStateTimeDependentMarkovEndpointProbability
              initial rates markedTime observed :=
      Finset.single_le_sum (fun observed _hObserved ↦ zero_le)
        (Finset.mem_univ source)
    rwa [sum_finiteStateTimeDependentMarkovEndpointProbability
      initial rates markedTime hMarkedTime.1.le] at hCoordinate
  have hEndpointFinite :
      finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hEndpointENNRealLeOne
  have hEndpointRealLeOne :
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime source).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal hEndpointFinite ENNReal.one_ne_top).2
      hEndpointENNRealLeOne
  have hRateLeEscape :
      rates.rate markedTime source target ≤ rates.escapeRate markedTime source := by
    unfold FiniteStateTimeDependentMarkovRate.escapeRate
    exact Finset.single_le_sum (fun state _hState ↦ zero_le)
      (Finset.mem_erase.mpr ⟨hNe.symm, Finset.mem_univ target⟩)
  have hRateLeClock :
      (rates.rate markedTime source target : ℝ) ≤
        (rates.uniformizationRate : ℝ) := by
    exact_mod_cast hRateLeEscape.trans
      (rates.escapeRate_le_uniformizationRate markedTime source)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    (weight markedTime : ℝ) *
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source).toReal *
          (rates.rate markedTime source target : ℝ) ≤
        weightBound * 1 * (rates.uniformizationRate : ℝ) := by
      gcongr
      exact hWeightBound markedTime
    _ = weightBound * (rates.uniformizationRate : ℝ) := by ring

/-- The expectation of an arbitrary bounded measurable weighted off-diagonal transition sum is
the physical occupation--rate integral tested by that weight. -/
theorem integral_directedTransitionWeightSum_reducedHistoryMeasure_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ) (hWeight : Measurable weight)
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ time, |weight time| ≤ weightBound) :
    (∫ history : FiniteJumpHistory State,
        finiteJumpHistoryDirectedTransitionWeightSum
          weight source target history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
      finiteStateTimeDependentMarkovDirectedTransitionWeightMean
        initial rates duration weight source target := by
  unfold finiteStateTimeDependentMarkovDirectedTransitionWeightMean
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  let positiveWeight : ℝ → ℝ≥0 := fun time ↦ Real.toNNReal (weight time)
  let negativeWeight : ℝ → ℝ≥0 := fun time ↦ Real.toNNReal (-weight time)
  have hPositiveWeightMeasurable : Measurable positiveWeight :=
    measurable_real_toNNReal.comp hWeight
  have hNegativeWeightMeasurable : Measurable negativeWeight :=
    measurable_real_toNNReal.comp hWeight.neg
  have hPositiveWeightBound : ∀ time,
      (positiveWeight time : ℝ) ≤ weightBound := by
    intro time
    rw [Real.coe_toNNReal']
    exact max_le (le_abs_self (weight time) |>.trans (hWeightBound time))
      hWeightBoundNonnegative
  have hNegativeWeightBound : ∀ time,
      (negativeWeight time : ℝ) ≤ weightBound := by
    intro time
    rw [Real.coe_toNNReal']
    exact max_le (neg_le_abs (weight time) |>.trans (hWeightBound time))
      hWeightBoundNonnegative
  have hPositiveHistoryIntegrable : Integrable
      (finiteJumpHistoryDirectedTransitionNNRealWeightSum
        positiveWeight source target)
      law := by
    exact (memLp_two_finiteJumpHistoryTransitionTestSum
      initial rates duration
      (finiteStateDirectedTransitionNNRealWeightTest positiveWeight source target)
      (fun eventSource eventTarget ↦
        measurable_finiteStateDirectedTransitionNNRealWeightTest
          positiveWeight hPositiveWeightMeasurable source target eventSource eventTarget)
      hWeightBoundNonnegative (fun time eventSource eventTarget ↦ by
        unfold finiteStateDirectedTransitionNNRealWeightTest
        split
        · rw [abs_of_nonneg (positiveWeight time).coe_nonneg]
          exact hPositiveWeightBound time
        · simpa only [abs_zero] using hWeightBoundNonnegative)).integrable one_le_two
  have hNegativeHistoryIntegrable : Integrable
      (finiteJumpHistoryDirectedTransitionNNRealWeightSum
        negativeWeight source target)
      law := by
    exact (memLp_two_finiteJumpHistoryTransitionTestSum
      initial rates duration
      (finiteStateDirectedTransitionNNRealWeightTest negativeWeight source target)
      (fun eventSource eventTarget ↦
        measurable_finiteStateDirectedTransitionNNRealWeightTest
          negativeWeight hNegativeWeightMeasurable source target eventSource eventTarget)
      hWeightBoundNonnegative (fun time eventSource eventTarget ↦ by
        unfold finiteStateDirectedTransitionNNRealWeightTest
        split
        · rw [abs_of_nonneg (negativeWeight time).coe_nonneg]
          exact hNegativeWeightBound time
        · simpa only [abs_zero] using hWeightBoundNonnegative)).integrable one_le_two
  have hPositiveExpectation :=
    integral_directedTransitionNNRealWeightSum_reducedHistoryMeasure_eq
      initial rates duration hNe positiveWeight hPositiveWeightMeasurable
      hWeightBoundNonnegative hPositiveWeightBound
  have hNegativeExpectation :=
    integral_directedTransitionNNRealWeightSum_reducedHistoryMeasure_eq
      initial rates duration hNe negativeWeight hNegativeWeightMeasurable
      hWeightBoundNonnegative hNegativeWeightBound
  have hPositiveTimeIntegrable :=
    integrableOn_nnrealWeight_mul_endpointProbability_mul_rate
      initial rates duration hNe positiveWeight hPositiveWeightMeasurable
      hWeightBoundNonnegative hPositiveWeightBound
  have hNegativeTimeIntegrable :=
    integrableOn_nnrealWeight_mul_endpointProbability_mul_rate
      initial rates duration hNe negativeWeight hNegativeWeightMeasurable
      hWeightBoundNonnegative hNegativeWeightBound
  simp_rw [finiteJumpHistoryDirectedTransitionWeightSum_eq_positivePart_sub_negativePart]
  rw [integral_sub hPositiveHistoryIntegrable hNegativeHistoryIntegrable]
  rw [hPositiveExpectation, hNegativeExpectation]
  rw [← integral_sub hPositiveTimeIntegrable hNegativeTimeIntegrable]
  apply integral_congr_ae
  filter_upwards [] with markedTime
  dsimp only [positiveWeight, negativeWeight]
  have hWeightDecomposition :
      (Real.toNNReal (weight markedTime) : ℝ) -
          (Real.toNNReal (-weight markedTime) : ℝ) = weight markedTime := by
    by_cases hWeightNonnegative : 0 ≤ weight markedTime
    · rw [Real.coe_toNNReal _ hWeightNonnegative,
        Real.toNNReal_of_nonpos (neg_nonpos.mpr hWeightNonnegative)]
      simp
    · have hWeightNonpositive : weight markedTime ≤ 0 := le_of_not_ge hWeightNonnegative
      rw [Real.toNNReal_of_nonpos hWeightNonpositive,
        Real.coe_toNNReal _ (neg_nonneg.mpr hWeightNonpositive)]
      simp
  calc
    (Real.toNNReal (weight markedTime) : ℝ) *
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source).toReal *
          (rates.rate markedTime source target : ℝ) -
        (Real.toNNReal (-weight markedTime) : ℝ) *
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source).toReal *
          (rates.rate markedTime source target : ℝ) =
      ((Real.toNNReal (weight markedTime) : ℝ) -
          (Real.toNNReal (-weight markedTime) : ℝ)) *
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source).toReal *
        (rates.rate markedTime source target : ℝ) := by ring
    _ = _ := by rw [hWeightDecomposition]

/-- A bounded weighted ordered-flow coordinate under heterogeneous independent replicas
concentrates around the exact sum of its occupation--rate means. -/
theorem
finiteStateTimeDependentMarkovDeterministicReplica_directedFlowTestDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ) (hWeight : Measurable weight)
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ time, |weight time| ≤ weightBound)
    {deviation : ℝ} (hDeviation : 0 < deviation) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories |
        deviation ≤
          |∑ replica, finiteJumpHistoryDirectedTransitionWeightSum
              weight source target (histories replica) -
            ∑ replica,
              finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                (PMF.pure (initialConfiguration replica)) rates duration
                weight source target|} ≤
      ENNReal.ofReal
        ((replicaCount : ℝ) *
          (weightBound ^ 2 *
            (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
              (Real.exp 1 - 1)))) / deviation ^ 2) := by
  have hConcentration :=
    finiteStateTimeDependentMarkovDeterministicInitialReplica_transitionTestSumDeviation_le
      initialConfiguration rates duration
      (finiteStateDirectedTransitionWeightTest weight source target)
      (fun eventSource eventTarget ↦
        measurable_finiteStateDirectedTransitionWeightTest
          weight hWeight source target eventSource eventTarget)
      hWeightBoundNonnegative (fun time eventSource eventTarget ↦ by
        unfold finiteStateDirectedTransitionWeightTest
        split
        · exact hWeightBound time
        · simpa only [abs_zero] using hWeightBoundNonnegative)
      hDeviation
  change
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure {histories |
      deviation ≤
        |∑ replica, finiteJumpHistoryDirectedTransitionWeightSum
            weight source target (histories replica) -
          ∑ replica, ∫ history,
            finiteJumpHistoryDirectedTransitionWeightSum
              weight source target history
            ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
              (PMF.pure (initialConfiguration replica)) rates duration|} ≤ _ at hConcentration
  simp_rw [integral_directedTransitionWeightSum_reducedHistoryMeasure_eq
    (initial := _) (rates := rates) (duration := duration)
    (source := source) (target := target) hNe weight hWeight
    hWeightBoundNonnegative hWeightBound] at hConcentration
  exact hConcentration

/-- Any finite family of bounded weighted ordered-flow coordinates concentrates jointly around
its exact mean family, with the explicit finite union prefactor. -/
theorem finiteStateTimeDependentMarkovDeterministicReplica_finiteFlowTestFamilyDeviation_le
    {TestIndex : Type*} [Fintype TestIndex]
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (source target : TestIndex → State)
    (hNe : ∀ index, source index ≠ target index)
    (weight : TestIndex → ℝ → ℝ)
    (hWeight : ∀ index, Measurable (weight index))
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ index time, |weight index time| ≤ weightBound)
    {deviation : ℝ} (hDeviation : 0 < deviation) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories | ∃ index,
        deviation ≤
          |∑ replica, finiteJumpHistoryDirectedTransitionWeightSum
              (weight index) (source index) (target index) (histories replica) -
            ∑ replica,
              finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                (PMF.pure (initialConfiguration replica)) rates duration
                (weight index) (source index) (target index)|} ≤
      (Fintype.card TestIndex : ℝ≥0∞) *
        ENNReal.ofReal
          ((replicaCount : ℝ) *
            (weightBound ^ 2 *
              (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
                (Real.exp 1 - 1)))) / deviation ^ 2) := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let badEvent (index : TestIndex) :
      Set (Fin replicaCount → FiniteJumpHistory State) :=
    {histories |
      deviation ≤
        |∑ replica, finiteJumpHistoryDirectedTransitionWeightSum
            (weight index) (source index) (target index) (histories replica) -
          ∑ replica,
            finiteStateTimeDependentMarkovDirectedTransitionWeightMean
              (PMF.pure (initialConfiguration replica)) rates duration
              (weight index) (source index) (target index)|}
  have hSingle (index : TestIndex) :
      law (badEvent index) ≤
        ENNReal.ofReal
          ((replicaCount : ℝ) *
            (weightBound ^ 2 *
              (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
                (Real.exp 1 - 1)))) / deviation ^ 2) := by
    exact
      finiteStateTimeDependentMarkovDeterministicReplica_directedFlowTestDeviation_le
        initialConfiguration rates duration (hNe index) (weight index) (hWeight index)
        hWeightBoundNonnegative (hWeightBound index) hDeviation
  have hBadUnion :
      {histories | ∃ index,
          deviation ≤
            |∑ replica, finiteJumpHistoryDirectedTransitionWeightSum
                (weight index) (source index) (target index) (histories replica) -
              ∑ replica,
                finiteStateTimeDependentMarkovDirectedTransitionWeightMean
                  (PMF.pure (initialConfiguration replica)) rates duration
                  (weight index) (source index) (target index)|} =
        ⋃ index, badEvent index := by
    ext histories
    simp only [mem_ofPred_eq, mem_iUnion, badEvent]
  rw [hBadUnion]
  calc
    law (⋃ index, badEvent index) ≤ ∑ index, law (badEvent index) :=
      measure_iUnion_fintype_le law badEvent
    _ ≤ ∑ _index : TestIndex,
        ENNReal.ofReal
          ((replicaCount : ℝ) *
            (weightBound ^ 2 *
              (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
                (Real.exp 1 - 1)))) / deviation ^ 2) := by
      exact Finset.sum_le_sum fun index _hIndex ↦ hSingle index
    _ = _ := by simp

end

end FiniteMarkovProcesses.Probability
