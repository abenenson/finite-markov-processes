/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovDirectionalFlowCompensator
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEndpointMean

/-!
# Forward equation for bounded time-dependent finite-state Markov laws

The exact marked-transition compensator is converted from a nonnegative Lebesgue integral into
the existing real expected cumulative-flow coordinate.  Combining it with mean
continuity and the projective endpoint marginal yields the physical forward integral equation.

## Main results

- `finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_horizon_eq_toReal_lintegral`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- At the observation horizon, the real expected physical directed count is the real value of
the exact endpoint-probability--rate compensator integral. -/
theorem finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_horizon_eq_toReal_lintegral
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target) :
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration duration source target =
      (∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
        finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source *
          ENNReal.ofReal (rates.rate markedTime source target : ℝ)).toReal := by
  let count : FiniteJumpHistory State → ℝ := fun history ↦
    (history.directedTransitionCountAtTime duration source target : ℝ)
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  have hCountIntegrable : Integrable count law :=
    (memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
      initial rates duration duration source target).integrable one_le_two
  have hCountNonnegative : 0 ≤ᵐ[law] count :=
    Filter.Eventually.of_forall fun history ↦ by
      dsimp only [count]
      positivity
  have hEmbeddedIntegral :=
    ofReal_integral_eq_lintegral_ofReal hCountIntegrable hCountNonnegative
  have hCountEmbedding :
      (∫⁻ history : FiniteJumpHistory State,
          ENNReal.ofReal (count history) ∂law) =
        ∫⁻ history : FiniteJumpHistory State,
          (history.directedTransitionCountAtTime duration source target : ℝ≥0∞) ∂law := by
    apply lintegral_congr
    intro history
    dsimp only [count]
    simp only [ENNReal.ofReal_natCast]
  rw [hCountEmbedding] at hEmbeddedIntegral
  have hCompensator :=
    lintegral_directedTransitionCount_reducedHistoryMeasure
      initial rates duration hNe
  have hMeanNonnegative : 0 ≤
      finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration duration source target := by
    unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
    exact integral_nonneg fun history ↦ by positivity
  calc
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          initial rates duration duration source target =
        (ENNReal.ofReal
          (finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            initial rates duration duration source target)).toReal := by
      rw [ENNReal.toReal_ofReal hMeanNonnegative]
    _ = (∫⁻ history : FiniteJumpHistory State,
          (history.directedTransitionCountAtTime duration source target : ℝ≥0∞)
        ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
          initial rates duration).toReal := by
      apply congrArg ENNReal.toReal
      simpa only [finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt,
        count, law] using hEmbeddedIntegral
    _ = _ := congrArg ENNReal.toReal hCompensator

/-- The terminal expected physical directed count is the ordinary integral of the occupied-source
probability times the corresponding time-dependent jump rate. -/
theorem finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_horizon_eq_integral
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target) :
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration duration source target =
      ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source).toReal *
        (rates.rate markedTime source target : ℝ) := by
  rw [finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_horizon_eq_toReal_lintegral
    initial rates duration hNe]
  let integrand : ℝ → ℝ≥0∞ := fun markedTime ↦
    finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime source *
      ENNReal.ofReal (rates.rate markedTime source target : ℝ)
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
  have hIntegrandMeasurable : Measurable integrand :=
    hEndpointMeasurable.mul hRateMeasurable.ennreal_ofReal
  have hEndpointFinite (markedTime : ℝ) (hMarkedTime : 0 ≤ markedTime) :
      finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source ≠ ⊤ := by
    unfold finiteStateTimeDependentMarkovEndpointProbability
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteStateTimeDependentMarkovUniformizedEndpointSeries_ne_top
        initial rates markedTime hMarkedTime source)
  have hIntegrandFinite : ∀ᵐ markedTime
      ∂volume.restrict (Ioo 0 (duration : ℝ)), integrand markedTime < ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with markedTime hMarkedTime
    exact (ENNReal.mul_ne_top
      (hEndpointFinite markedTime hMarkedTime.1.le) ENNReal.ofReal_ne_top).lt_top
  rw [← integral_toReal hIntegrandMeasurable.aemeasurable hIntegrandFinite]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with markedTime hMarkedTime
  dsimp only [integrand]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal]
  exact (rates.rate markedTime source target).coe_nonneg

/-- The real expectation of a bounded nonnegative weighted off-diagonal transition sum is the
ordinary integral of weight times occupied-source probability times physical jump rate. -/
theorem integral_directedTransitionNNRealWeightSum_reducedHistoryMeasure_eq
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ≥0) (hWeight : Measurable weight)
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ time, (weight time : ℝ) ≤ weightBound) :
    (∫ history : FiniteJumpHistory State,
        finiteJumpHistoryDirectedTransitionNNRealWeightSum
          weight source target history
      ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
        initial rates duration) =
      ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
        (weight markedTime : ℝ) *
          (finiteStateTimeDependentMarkovEndpointProbability
            initial rates markedTime source).toReal *
          (rates.rate markedTime source target : ℝ) := by
  let observable : FiniteJumpHistory State → ℝ :=
    finiteJumpHistoryDirectedTransitionNNRealWeightSum weight source target
  let law := finiteStateTimeDependentMarkovReducedHistoryMeasure initial rates duration
  let : IsProbabilityMeasure law :=
    ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ initial rates duration⟩
  have hTestMeasurable : ∀ eventSource eventTarget,
      Measurable fun time ↦
        finiteStateDirectedTransitionNNRealWeightTest
          weight source target time eventSource eventTarget :=
    fun eventSource eventTarget ↦
      measurable_finiteStateDirectedTransitionNNRealWeightTest
        weight hWeight source target eventSource eventTarget
  have hTestBound : ∀ time eventSource eventTarget,
      |finiteStateDirectedTransitionNNRealWeightTest
        weight source target time eventSource eventTarget| ≤ weightBound := by
    intro time eventSource eventTarget
    unfold finiteStateDirectedTransitionNNRealWeightTest
    split
    · rw [abs_of_nonneg (weight time).coe_nonneg]
      exact hWeightBound time
    · simpa only [abs_zero] using hWeightBoundNonnegative
  have hObservableMemLp : MemLp observable 2 law := by
    exact memLp_two_finiteJumpHistoryTransitionTestSum
      initial rates duration
      (finiteStateDirectedTransitionNNRealWeightTest weight source target)
      hTestMeasurable hWeightBoundNonnegative hTestBound
  have hObservableIntegrable : Integrable observable law :=
    hObservableMemLp.integrable one_le_two
  have hObservablePointwise (history : FiniteJumpHistory State) :
      0 ≤ observable history := by
      unfold observable finiteJumpHistoryDirectedTransitionNNRealWeightSum
        finiteJumpHistoryTransitionTestSum
      exact Finset.sum_nonneg fun index _hIndex ↦
        finiteStateDirectedTransitionNNRealWeightTest_nonneg
          weight source target (history.jumpTimes index)
            (history.states index.castSucc) (history.states index.succ)
  have hObservableNonnegative : 0 ≤ᵐ[law] observable :=
    Filter.Eventually.of_forall hObservablePointwise
  have hEmbeddedIntegral :=
    ofReal_integral_eq_lintegral_ofReal
      hObservableIntegrable hObservableNonnegative
  have hCompensator :=
    lintegral_directedTransitionNNRealWeightSum_reducedHistoryMeasure
      initial rates duration hNe weight hWeight
  let integrand : ℝ → ℝ≥0∞ := fun markedTime ↦
    (weight markedTime : ℝ≥0∞) *
      finiteStateTimeDependentMarkovEndpointProbability
        initial rates markedTime source *
      ENNReal.ofReal (rates.rate markedTime source target : ℝ)
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
  have hIntegrandMeasurable : Measurable integrand :=
    (hWeight.coe_nnreal_ennreal.mul hEndpointMeasurable).mul
      hRateMeasurable.ennreal_ofReal
  have hEndpointFinite (markedTime : ℝ) (hMarkedTime : 0 ≤ markedTime) :
      finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime source ≠ ⊤ := by
    unfold finiteStateTimeDependentMarkovEndpointProbability
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (finiteStateTimeDependentMarkovUniformizedEndpointSeries_ne_top
        initial rates markedTime hMarkedTime source)
  have hIntegrandFinite : ∀ᵐ markedTime
      ∂volume.restrict (Ioo 0 (duration : ℝ)), integrand markedTime < ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with markedTime hMarkedTime
    exact (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (hEndpointFinite markedTime hMarkedTime.1.le))
      ENNReal.ofReal_ne_top).lt_top
  have hIntegralToReal :=
    integral_toReal hIntegrandMeasurable.aemeasurable hIntegrandFinite
  have hObservableIntegralNonnegative : 0 ≤ ∫ history, observable history ∂law :=
    integral_nonneg hObservablePointwise
  calc
    (∫ history : FiniteJumpHistory State, observable history ∂law) =
        (ENNReal.ofReal (∫ history : FiniteJumpHistory State,
          observable history ∂law)).toReal := by
      rw [ENNReal.toReal_ofReal hObservableIntegralNonnegative]
    _ = (∫⁻ history : FiniteJumpHistory State,
          ENNReal.ofReal (observable history) ∂law).toReal := by
      exact congrArg ENNReal.toReal hEmbeddedIntegral
    _ = (∫⁻ markedTime : ℝ in Ioo 0 (duration : ℝ),
          integrand markedTime).toReal := by
      exact congrArg ENNReal.toReal hCompensator
    _ = ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
          (integrand markedTime).toReal := hIntegralToReal.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with markedTime _hMarkedTime
      dsimp only [integrand]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
      · rw [ENNReal.coe_toReal]
      · exact (rates.rate markedTime source target).coe_nonneg

/-- The resummed endpoint probabilities solve the exact physical forward integral equation.  The
finite sums use the source's off-diagonal convention explicitly, so no virtual self-event enters
the equation. -/
theorem finiteStateTimeDependentMarkovEndpointProbability_eq_initial_add_incoming_sub_outgoing
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (observed : State) :
    (finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed).toReal =
      (initial observed).toReal +
        (∑ source ∈ Finset.univ.erase observed,
          ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
            (finiteStateTimeDependentMarkovEndpointProbability
              initial rates markedTime source).toReal *
            (rates.rate markedTime source observed : ℝ)) -
        (∑ target ∈ Finset.univ.erase observed,
          ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
            (finiteStateTimeDependentMarkovEndpointProbability
              initial rates markedTime observed).toReal *
            (rates.rate markedTime observed target : ℝ)) := by
  let flow : State → State → ℝ := fun source target ↦
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
      initial rates duration duration source target
  have hContinuity :=
    finiteStateTimeDependentMarkovMeanDensityAt_eq_initial_add_incoming_sub_outgoing
      initial rates duration duration observed
  rw [finiteStateTimeDependentMarkovMeanDensityAt_horizon_eq_endpointPMF,
    finiteStateTimeDependentMarkovMeanInitialDensity_eq] at hContinuity
  change (finiteStateTimeDependentMarkovEndpointProbability
      initial rates duration observed).toReal =
    (initial observed).toReal + ∑ source : State, flow source observed -
      ∑ target : State, flow observed target at hContinuity
  have hRemoveSelf :
      (∑ source : State, flow source observed) -
          ∑ target : State, flow observed target =
        (∑ source ∈ Finset.univ.erase observed, flow source observed) -
          ∑ target ∈ Finset.univ.erase observed, flow observed target := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ observed)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ observed)]
    ring
  have hIncoming :
      (∑ source ∈ Finset.univ.erase observed, flow source observed) =
        ∑ source ∈ Finset.univ.erase observed,
          ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
            (finiteStateTimeDependentMarkovEndpointProbability
              initial rates markedTime source).toReal *
            (rates.rate markedTime source observed : ℝ) := by
    apply Finset.sum_congr rfl
    intro source hSource
    have hNe : source ≠ observed := (Finset.mem_erase.mp hSource).1
    exact finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_horizon_eq_integral
      initial rates duration hNe
  have hOutgoing :
      (∑ target ∈ Finset.univ.erase observed, flow observed target) =
        ∑ target ∈ Finset.univ.erase observed,
          ∫ markedTime : ℝ in Ioo 0 (duration : ℝ),
            (finiteStateTimeDependentMarkovEndpointProbability
              initial rates markedTime observed).toReal *
            (rates.rate markedTime observed target : ℝ) := by
    apply Finset.sum_congr rfl
    intro target hTarget
    have hNe : observed ≠ target := by
      exact fun hEq ↦ (Finset.mem_erase.mp hTarget).1 hEq.symm
    exact finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_horizon_eq_integral
      initial rates duration hNe
  calc
    (finiteStateTimeDependentMarkovEndpointProbability
        initial rates duration observed).toReal =
        (initial observed).toReal +
          ((∑ source : State, flow source observed) -
            ∑ target : State, flow observed target) := by
      linarith [hContinuity]
    _ = (initial observed).toReal +
        ((∑ source ∈ Finset.univ.erase observed, flow source observed) -
          ∑ target ∈ Finset.univ.erase observed, flow observed target) := by
      rw [hRemoveSelf]
    _ = _ := by
      rw [hIncoming, hOutgoing]
      ring

end

end FiniteMarkovProcesses.Probability
