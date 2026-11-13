/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Probability.FiniteStateProbabilityDensityEmpiricalApproximation
public import
FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalHybridOpenSetConcentration
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovInitialMixture

/-!
# Rounded-initial convergence of finite-state Markov mean paths

This module identifies the heterogeneous deterministic-replica center with the Markov mean path
started from its exact empirical initial density.  It then proves convergence of those centers
when the empirical initial densities converge, including the canonical rounded configurations.

All rates and the physical horizon remain fixed.  No growing-cutoff estimate enters this layer.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction CompactlySupported ENNReal NNReal Topology

open FiniteMarkovProcesses _root_.FiniteMarkovProcesses.InformationTheory

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Inside the physical interval, the source-defined expected density is exactly the density
coordinate of the canonical mean hybrid path. -/
theorem finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (hTimeDuration : time ≤ duration) (state : State) :
    finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration time state =
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time (Sum.inl state) := by
  let nonnegativeTime : ℝ≥0 := ⟨time, hTimeNonnegative⟩
  calc
    finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration time state =
      (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time state).toReal := by
          simpa only [nonnegativeTime, NNReal.coe_mk] using!
            finiteStateTimeDependentMarkovMeanDensityAt_eq_endpointPMF
              initial rates duration nonnegativeTime (by
                exact_mod_cast hTimeDuration) state
    _ = finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time (Sum.inl state) :=
      (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
        initial rates duration hTimeNonnegative hTimeDuration state).symm

/-- At every nonnegative time, the source-defined expected cumulative ordered flow is exactly
the flow coordinate of the canonical mean hybrid path. -/
theorem
finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_meanHybridBVValueAtTime
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (edge : FiniteStateOffDiagonalEdge State) :
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        initial rates duration time edge.val.1 edge.val.2 =
      finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time (Sum.inr edge) := by
  let weight : ℝ → ℝ := (Iic time).indicator fun _ => 1
  have hWeightMeasurable : Measurable weight :=
    measurable_const.indicator measurableSet_Iic
  have hWeightBound : ∀ markedTime, |weight markedTime| ≤ 1 := by
    intro markedTime
    simp only [weight, Set.indicator]
    split <;> norm_num
  have hHistory (history : FiniteJumpHistory State) :
      finiteJumpHistoryDirectedTransitionWeightSum
          weight edge.val.1 edge.val.2 history =
        (history.directedTransitionCountAtTime
          time edge.val.1 edge.val.2 : ℝ) := by
    unfold weight finiteJumpHistoryDirectedTransitionWeightSum
      finiteJumpHistoryTransitionTestSum
      finiteStateDirectedTransitionWeightTest
      FiniteJumpHistory.directedTransitionCountAtTime
      FiniteJumpHistory.directedTransitionCountAtTimeVector
    simp only [Set.indicator, Set.mem_Iic, Nat.cast_sum, Nat.cast_ite]
    apply Finset.sum_congr rfl
    intro index _hIndex
    split_ifs with hMarkedTime hEdge hCount
    all_goals simp_all
  unfold finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
  rw [show (fun history : FiniteJumpHistory State =>
      (history.directedTransitionCountAtTime
        time edge.val.1 edge.val.2 : ℝ)) =
      finiteJumpHistoryDirectedTransitionWeightSum
        weight edge.val.1 edge.val.2 by
    funext history
    exact (hHistory history).symm]
  rw [integral_directedTransitionWeightSum_reducedHistoryMeasure_eq
    initial rates duration edge.property weight hWeightMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) hWeightBound]
  rw [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_flow,
    finiteIntervalIntegralPrimitive]
  simp only [zero_add]
  unfold finiteStateTimeDependentMarkovDirectedTransitionWeightMean weight
  rw [intervalIntegral.integral_of_le hTimeNonnegative]
  change
    (∫ markedTime : ℝ,
      (Iic time).indicator (fun _ => (1 : ℝ)) markedTime *
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime edge.val.1).toReal *
        (rates.rate markedTime edge.val.1 edge.val.2 : ℝ)
      ∂volume.restrict (Ioo 0 (duration : ℝ))) =
      ∫ markedTime : ℝ,
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime edge.val.1).toReal *
        (rates.rate markedTime edge.val.1 edge.val.2 : ℝ)
      ∂(finiteOpenIntervalVolume (duration : ℝ)).restrict (Ioc 0 time)
  rw [show (fun markedTime : ℝ =>
      (Iic time).indicator (fun _ => (1 : ℝ)) markedTime *
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime edge.val.1).toReal *
        (rates.rate markedTime edge.val.1 edge.val.2 : ℝ)) =
      (Iic time).indicator (fun markedTime =>
        (finiteStateTimeDependentMarkovEndpointProbability
          initial rates markedTime edge.val.1).toReal *
        (rates.rate markedTime edge.val.1 edge.val.2 : ℝ)) by
    funext markedTime
    by_cases hMarkedTime : markedTime ∈ Iic time
    · simp [hMarkedTime]
    · simp [hMarkedTime]]
  rw [integral_indicator measurableSet_Iic]
  unfold finiteOpenIntervalVolume
  congr 1
  ext event hEvent
  rw [Measure.restrict_apply hEvent, Measure.restrict_apply
    (hEvent.inter measurableSet_Iic), Measure.restrict_apply hEvent,
    Measure.restrict_apply (hEvent.inter measurableSet_Ioc)]
  congr 1
  ext markedTime
  constructor
  · rintro ⟨⟨hEvent, hUpper⟩, ⟨hPositive, hDuration⟩⟩
    exact ⟨⟨hEvent, ⟨hPositive, hUpper⟩⟩, ⟨hPositive, hDuration⟩⟩
  · rintro ⟨⟨hEvent, ⟨hPositive, hUpper⟩⟩, ⟨_hPositive, hDuration⟩⟩
    exact ⟨⟨hEvent, hUpper⟩, ⟨hPositive, hDuration⟩⟩

/-- Endpoint evolution is exactly linear in the finite initial PMF at every nonnegative time. -/
theorem finiteStateTimeDependentMarkovEndpointProbability_toReal_eq_sum_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    {time : ℝ} (hTimeNonnegative : 0 ≤ time) (observed : State) :
    (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time observed).toReal =
      ∑ state, (initial state).toReal *
        (finiteStateTimeDependentMarkovEndpointProbability
          (PMF.pure state) rates time observed).toReal := by
  let duration : ℝ≥0 := ⟨time + 1, by linarith⟩
  calc
    (finiteStateTimeDependentMarkovEndpointProbability
        initial rates time observed).toReal =
      finiteStateTimeDependentMarkovMeanDensityAt
        initial rates duration time observed := by
          rw [finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
            initial rates duration hTimeNonnegative (by
              change time ≤ time + 1
              linarith) observed]
          exact
            (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
              initial rates duration hTimeNonnegative (by
                change time ≤ time + 1
                linarith) observed).symm
    _ = ∑ state, (initial state).toReal *
        finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure state) rates duration time observed :=
      finiteStateTimeDependentMarkovMeanDensityAt_eq_sum_initial_mul_pure
        initial rates duration time observed
    _ = ∑ state, (initial state).toReal *
        (finiteStateTimeDependentMarkovEndpointProbability
          (PMF.pure state) rates time observed).toReal := by
      apply Finset.sum_congr rfl
      intro state _hState
      rw [finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
        (PMF.pure state) rates duration hTimeNonnegative (by
          change time ≤ time + 1
          linarith) observed]
      rw [finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_density_eq_endpointProbability
        (PMF.pure state) rates duration hTimeNonnegative (by
          change time ≤ time + 1
          linarith) observed]

/-- Every physical-time value of the canonical Markov mean hybrid path is the finite
initial-PMF mixture of the corresponding pure-initial values. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_eq_sum_initial_smul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {time : ℝ} (hTimeNonnegative : 0 ≤ time)
    (hTimeDuration : time ≤ duration) :
    finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration time =
      ∑ state, (initial state).toReal •
        finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
          (PMF.pure state) rates duration time := by
  apply PiLp.ext
  intro coordinate
  have hSumApply (selected : Finset State) :
      (∑ state ∈ selected, (initial state).toReal •
        finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
          (PMF.pure state) rates duration time) coordinate =
        ∑ state ∈ selected, (initial state).toReal *
          finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
            (PMF.pure state) rates duration time coordinate := by
    induction selected using Finset.induction_on with
    | empty => simp
    | @insert state selected hState hInduction =>
        simp only [Finset.sum_insert hState, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul, hInduction]
  rw [hSumApply Finset.univ]
  cases coordinate with
  | inl observed =>
      rw [← finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
        initial rates duration hTimeNonnegative hTimeDuration observed]
      rw [finiteStateTimeDependentMarkovMeanDensityAt_eq_sum_initial_mul_pure]
      apply Finset.sum_congr rfl
      intro state _hState
      rw [finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
        (PMF.pure state) rates duration hTimeNonnegative hTimeDuration observed]
  | inr edge =>
      rw [←
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_meanHybridBVValueAtTime
          initial rates duration hTimeNonnegative edge]
      rw [finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_sum_initial_mul_pure]
      apply Finset.sum_congr rfl
      intro state _hState
      rw [
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_meanHybridBVValueAtTime
          (PMF.pure state) rates duration hTimeNonnegative edge]

/-- The strong-`L1` Markov mean path is exactly the finite initial-PMF linear combination of its
pure-initial mean paths. -/
theorem finiteStateTimeDependentMarkovMeanHybridBVL1Path_eq_sum_initial_smul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) :
    finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration =
      ∑ state, (initial state).toReal •
        finiteStateTimeDependentMarkovMeanHybridBVL1Path
          (PMF.pure state) rates duration := by
  apply Lp.ext
  have hInitial :=
    (FiniteIntervalL1Path.represents_iff_eventuallyEq
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path initial rates duration)
      (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime initial rates duration)
      (memLp_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        initial rates duration)).mp
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path_represents initial rates duration)
  have hPure (state : State) :=
    (FiniteIntervalL1Path.represents_iff_eventuallyEq
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path (PMF.pure state) rates duration)
      (finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        (PMF.pure state) rates duration)
      (memLp_finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
        (PMF.pure state) rates duration)).mp
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path_represents
        (PMF.pure state) rates duration)
  have hFiniteSum (selected : Finset State) :
      (fun time =>
        (∑ state ∈ selected, (initial state).toReal •
          finiteStateTimeDependentMarkovMeanHybridBVL1Path
            (PMF.pure state) rates duration) time) =ᵐ[
              finiteOpenIntervalVolume (duration : ℝ)]
        fun time =>
          ∑ state ∈ selected, (initial state).toReal •
            (finiteStateTimeDependentMarkovMeanHybridBVL1Path
              (PMF.pure state) rates duration) time := by
    induction selected using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using!
          (Lp.coeFn_zero (E := FiniteCoordinateL1Value
            (EmpiricalDensityDirectionalFlowCoordinate State))
            (p := (1 : ℝ≥0∞))
            (μ := finiteOpenIntervalVolume (duration : ℝ)))
    | @insert state selected hState hInduction =>
        have hAdd := Lp.coeFn_add
          ((initial state).toReal •
            finiteStateTimeDependentMarkovMeanHybridBVL1Path
              (PMF.pure state) rates duration)
          (∑ candidate ∈ selected, (initial candidate).toReal •
            finiteStateTimeDependentMarkovMeanHybridBVL1Path
              (PMF.pure candidate) rates duration)
        have hSmul := Lp.coeFn_smul (initial state).toReal
          (finiteStateTimeDependentMarkovMeanHybridBVL1Path
            (PMF.pure state) rates duration)
        filter_upwards [hAdd, hSmul, hInduction] with markedTime
          hAddTime hSmulTime hInductionTime
        simp only [Finset.sum_insert hState]
        rw [hAddTime]
        simp only [Pi.add_apply]
        rw [hSmulTime, hInductionTime]
        simp only [Pi.smul_apply]
  filter_upwards [hInitial, Filter.eventually_all.2 hPure,
    hFiniteSum Finset.univ, ae_restrict_mem measurableSet_Ioo] with
      time hInitialTime hPureTime hFiniteSumTime hTime
  rw [← hInitialTime]
  rw [hFiniteSumTime]
  rw [show (∑ state, (initial state).toReal •
      (finiteStateTimeDependentMarkovMeanHybridBVL1Path
        (PMF.pure state) rates duration) time) =
      ∑ state, (initial state).toReal •
        finiteStateTimeDependentMarkovMeanHybridBVValueAtTime
          (PMF.pure state) rates duration time by
    apply Finset.sum_congr rfl
    intro state _hState
    rw [← hPureTime state]
    ]
  exact finiteStateTimeDependentMarkovMeanHybridBVValueAtTime_eq_sum_initial_smul_pure
    initial rates duration hTime.1.le hTime.2.le

/-- Every bounded measurable ordered-flow test mean is exactly linear in the finite initial PMF. -/
theorem
finiteStateTimeDependentMarkovDirectedTransitionWeightMean_eq_sum_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) {source target : State} (hNe : source ≠ target)
    (weight : ℝ → ℝ) (hWeight : Measurable weight)
    {weightBound : ℝ} (hWeightBoundNonnegative : 0 ≤ weightBound)
    (hWeightBound : ∀ time, |weight time| ≤ weightBound) :
    finiteStateTimeDependentMarkovDirectedTransitionWeightMean
        initial rates duration weight source target =
      ∑ state, (initial state).toReal *
        finiteStateTimeDependentMarkovDirectedTransitionWeightMean
          (PMF.pure state) rates duration weight source target := by
  rw [← integral_directedTransitionWeightSum_reducedHistoryMeasure_eq
    initial rates duration hNe weight hWeight hWeightBoundNonnegative hWeightBound]
  rw [integral_finiteStateTimeDependentMarkovReducedHistoryMeasure_eq_sum_initial_mul_pure]
  · apply Finset.sum_congr rfl
    intro state _hState
    rw [integral_directedTransitionWeightSum_reducedHistoryMeasure_eq
      (PMF.pure state) rates duration hNe weight hWeight
        hWeightBoundNonnegative hWeightBound]
  · intro state
    let : IsProbabilityMeasure
        (finiteStateTimeDependentMarkovReducedHistoryMeasure
          (PMF.pure state) rates duration) :=
      ⟨finiteStateTimeDependentMarkovReducedHistoryMeasure_univ
        (PMF.pure state) rates duration⟩
    exact
      (memLp_two_finiteJumpHistoryTransitionTestSum
        (PMF.pure state) rates duration
        (finiteStateDirectedTransitionWeightTest weight source target)
        (fun eventSource eventTarget =>
          measurable_finiteStateDirectedTransitionWeightTest
            weight hWeight source target eventSource eventTarget)
        hWeightBoundNonnegative (fun time eventSource eventTarget => by
          unfold finiteStateDirectedTransitionWeightTest
          split
          · exact hWeightBound time
          · simpa only [abs_zero] using hWeightBoundNonnegative)).integrable one_le_two

omit [DecidableEq State] [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The real mass of the PMF adapter is exactly the original finite-density coordinate. -/
@[simp]
theorem finiteStateProbabilityDensity_probabilityMassFunction_toReal
    (density : FiniteStateProbabilityDensity State) (state : State) :
    (density.probabilityMassFunction state).toReal = (density.weight state : ℝ) := by
  rfl

/-- The heterogeneous strong-`L1` center is exactly the canonical Markov mean path started from
the empirical initial density of the deterministic replica configuration. -/
theorem
finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path_eq_empiricalInitial_meanHybridBVL1Path
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0) :
    finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
        successorIndex initialConfiguration rates duration =
      finiteStateTimeDependentMarkovMeanHybridBVL1Path
        (finiteIIDEmpiricalProbabilityDensity
          successorIndex initialConfiguration).probabilityMassFunction rates duration := by
  unfold finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path
    finiteStateTimeDependentMarkovMeanHybridBVL1Path
  apply (FiniteIntervalL1Path.ofFunction_eq_iff_eventuallyEq _ _ _ _).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
  apply PiLp.ext
  intro coordinate
  cases coordinate with
  | inl observed =>
      rw [finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_density]
      rw [sum_div_eq_sum_finiteIIDEmpiricalProbabilityDensity_weight_mul
        successorIndex initialConfiguration (fun state =>
          finiteStateTimeDependentMarkovMeanDensityAt
            (PMF.pure state) rates duration time observed)]
      change (∑ state,
        ((finiteIIDEmpiricalProbabilityDensity successorIndex initialConfiguration)
          |>.probabilityMassFunction state).toReal *
          finiteStateTimeDependentMarkovMeanDensityAt
            (PMF.pure state) rates duration time observed) = _
      rw [← finiteStateTimeDependentMarkovMeanDensityAt_eq_sum_initial_mul_pure]
      rw [finiteStateTimeDependentMarkovMeanDensityAt_eq_meanHybridBVValueAtTime
        (finiteIIDEmpiricalProbabilityDensity
          successorIndex initialConfiguration).probabilityMassFunction
        rates duration hTime.1.le hTime.2.le observed]
  | inr edge =>
      rw [finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1ValueAtTime_flow]
      rw [sum_div_eq_sum_finiteIIDEmpiricalProbabilityDensity_weight_mul
        successorIndex initialConfiguration (fun state =>
          finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            (PMF.pure state) rates duration time edge.val.1 edge.val.2)]
      change (∑ state,
        ((finiteIIDEmpiricalProbabilityDensity successorIndex initialConfiguration)
          |>.probabilityMassFunction state).toReal *
          finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            (PMF.pure state) rates duration time edge.val.1 edge.val.2) = _
      rw [← finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_sum_initial_mul_pure]
      rw [
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt_eq_meanHybridBVValueAtTime
          (finiteIIDEmpiricalProbabilityDensity
            successorIndex initialConfiguration).probabilityMassFunction
          rates duration hTime.1.le edge]

/-- Fixed-rate canonical Markov mean paths depend continuously on the finite initial density. -/
theorem tendsto_finiteStateTimeDependentMarkovMeanHybridBVL1Path_of_weight_tendsto
    (initialDensity : ℕ → FiniteStateProbabilityDensity State)
    (targetDensity : FiniteStateProbabilityDensity State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (hWeight : ∀ state, Tendsto
      (fun index => ((initialDensity index).weight state : ℝ))
      atTop (𝓝 (targetDensity.weight state : ℝ))) :
    Tendsto
      (fun index => finiteStateTimeDependentMarkovMeanHybridBVL1Path
        (initialDensity index).probabilityMassFunction rates duration)
      atTop
      (𝓝 (finiteStateTimeDependentMarkovMeanHybridBVL1Path
        targetDensity.probabilityMassFunction rates duration)) := by
  have hTerm (state : State) : Tendsto
      (fun index => ((initialDensity index).weight state : ℝ) •
        finiteStateTimeDependentMarkovMeanHybridBVL1Path
          (PMF.pure state) rates duration)
      atTop
      (𝓝 ((targetDensity.weight state : ℝ) •
        finiteStateTimeDependentMarkovMeanHybridBVL1Path
          (PMF.pure state) rates duration)) :=
    (hWeight state).smul_const _
  have hSum := tendsto_finsetSum Finset.univ fun state _hState => hTerm state
  rw [show (fun index => finiteStateTimeDependentMarkovMeanHybridBVL1Path
      (initialDensity index).probabilityMassFunction rates duration) =
      fun index => ∑ state, ((initialDensity index).weight state : ℝ) •
        finiteStateTimeDependentMarkovMeanHybridBVL1Path
          (PMF.pure state) rates duration by
    funext index
    rw [finiteStateTimeDependentMarkovMeanHybridBVL1Path_eq_sum_initial_smul_pure]
    simp only [finiteStateProbabilityDensity_probabilityMassFunction_toReal]]
  rw [finiteStateTimeDependentMarkovMeanHybridBVL1Path_eq_sum_initial_smul_pure]
  simp only [finiteStateProbabilityDensity_probabilityMassFunction_toReal]
  exact hSum

/-- Every directional-flow derivative test of the canonical mean path is exactly the finite
initial-PMF mixture of its pure-initial test values. -/
theorem
finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq_sum_initial_mul_pure
    (initial : PMF State) (rates : FiniteStateTimeDependentMarkovRate State)
    (duration : ℝ≥0) (edge : FiniteStateOffDiagonalEdge State)
    (test : C_c(ℝ, ℝ)) :
    ((finiteStateTimeDependentMarkovMeanHybridBVPath initial rates duration).toDerivativePath
        |>.derivative (Sum.inr edge)).continuousTestIntegral test =
      ∑ state, (initial state).toReal *
        (((finiteStateTimeDependentMarkovMeanHybridBVPath
            (PMF.pure state) rates duration).toDerivativePath
          |>.derivative (Sum.inr edge)).continuousTestIntegral test) := by
  let boundedTest : ℝ →ᵇ ℝ :=
    ofCompactSupport test test.continuous test.hasCompactSupport
  have hTestBound (time : ℝ) : |test time| ≤ ‖boundedTest‖ := by
    simpa only [boundedTest, Real.norm_eq_abs] using!
      boundedTest.norm_coe_le_norm time
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq]
  rw [finiteStateTimeDependentMarkovDirectedTransitionWeightMean_eq_sum_initial_mul_pure
    initial rates duration edge.property test test.continuous.measurable
      (norm_nonneg boundedTest) hTestBound]
  apply Finset.sum_congr rfl
  intro state _hState
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq]

/-- Every directional-flow derivative test of a heterogeneous deterministic-replica center is
exactly the empirical-initial-density mixture of the pure-initial Markov test values. -/
theorem
finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq_sum_empiricalInitial_mul_pure
    (successorIndex : ℕ)
    (initialConfiguration : Fin (successorIndex + 1) → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (edge : FiniteStateOffDiagonalEdge State) (test : C_c(ℝ, ℝ)) :
    ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex initialConfiguration rates duration).derivative
          (Sum.inr edge)).continuousTestIntegral test =
      ∑ state,
        ((finiteIIDEmpiricalProbabilityDensity
          successorIndex initialConfiguration).weight state : ℝ) *
        (((finiteStateTimeDependentMarkovMeanHybridBVPath
            (PMF.pure state) rates duration).toDerivativePath
          |>.derivative (Sum.inr edge)).continuousTestIntegral test) := by
  rw [
    finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq]
  rw [sum_div_eq_sum_finiteIIDEmpiricalProbabilityDensity_weight_mul
    successorIndex initialConfiguration (fun state =>
      finiteStateTimeDependentMarkovDirectedTransitionWeightMean
        (PMF.pure state) rates duration test edge.val.1 edge.val.2)]
  apply Finset.sum_congr rfl
  intro state _hState
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq]

/-- Under coordinatewise convergence of deterministic empirical initial densities, every
directional-flow derivative test of the heterogeneous centers converges to the corresponding test
of the target-initial Markov mean path. -/
theorem
tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_of_empiricalInitial_weight_tendsto
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (targetDensity : FiniteStateProbabilityDensity State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex =>
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
      atTop (𝓝 (targetDensity.weight state : ℝ)))
    (edge : FiniteStateOffDiagonalEdge State) (test : C_c(ℝ, ℝ)) :
    Tendsto
      (fun successorIndex =>
        ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex (initialConfiguration successorIndex) rates duration).derivative
            (Sum.inr edge)).continuousTestIntegral test)
      atTop
      (𝓝 (((finiteStateTimeDependentMarkovMeanHybridBVPath
          targetDensity.probabilityMassFunction rates duration).toDerivativePath.derivative
            (Sum.inr edge)).continuousTestIntegral test)) := by
  let pureTestValue : State → ℝ := fun state =>
    (((finiteStateTimeDependentMarkovMeanHybridBVPath
        (PMF.pure state) rates duration).toDerivativePath.derivative
          (Sum.inr edge)).continuousTestIntegral test)
  have hTerm (state : State) : Tendsto
      (fun successorIndex =>
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ) * pureTestValue state)
      atTop
      (𝓝 ((targetDensity.weight state : ℝ) * pureTestValue state)) :=
    (hWeight state).mul_const _
  have hSum := tendsto_finsetSum Finset.univ fun state _hState => hTerm state
  rw [show (fun successorIndex =>
      ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex (initialConfiguration successorIndex) rates duration).derivative
          (Sum.inr edge)).continuousTestIntegral test) =
      fun successorIndex => ∑ state,
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ) * pureTestValue state by
    funext successorIndex
    exact
      finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_eq_sum_empiricalInitial_mul_pure
        successorIndex (initialConfiguration successorIndex) rates duration edge test]
  rw [
    finiteStateTimeDependentMarkovMeanHybridBVPath_flow_continuousTestIntegral_eq_sum_initial_mul_pure]
  simp only [finiteStateProbabilityDensity_probabilityMassFunction_toReal]
  exact hSum

/-- Density-derivative tests converge under the same empirical-initial hypothesis.  Both source
and target density derivatives are reduced to the exact incoming-minus-outgoing ordered-flow
balance, so no separate density estimate is introduced. -/
theorem
tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_density_continuousTestIntegral_of_empiricalInitial_weight_tendsto
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (targetDensity : FiniteStateProbabilityDensity State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex =>
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
      atTop (𝓝 (targetDensity.weight state : ℝ)))
    (observed : State) (test : C_c(ℝ, ℝ)) :
    Tendsto
      (fun successorIndex =>
        ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex (initialConfiguration successorIndex) rates duration).derivative
            (Sum.inl observed)).continuousTestIntegral test)
      atTop
      (𝓝 (((finiteStateTimeDependentMarkovMeanHybridBVPath
          targetDensity.probabilityMassFunction rates duration).toDerivativePath.derivative
            (Sum.inl observed)).continuousTestIntegral test)) := by
  rw [show (fun successorIndex =>
      ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
        successorIndex (initialConfiguration successorIndex) rates duration).derivative
          (Sum.inl observed)).continuousTestIntegral test) =
      fun successorIndex =>
        (∑ source : {source : State // source ≠ observed},
          ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
            successorIndex (initialConfiguration successorIndex) rates duration).derivative
              (Sum.inr ⟨(source, observed), source.property⟩)).continuousTestIntegral test) -
        ∑ target : {target : State // target ≠ observed},
          ((finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
            successorIndex (initialConfiguration successorIndex) rates duration).derivative
              (Sum.inr ⟨(observed, target), target.property.symm⟩)).continuousTestIntegral test by
    funext successorIndex
    exact
      finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_density_continuousTestIntegral_eq
        successorIndex (initialConfiguration successorIndex) rates duration observed test]
  rw [finiteStateTimeDependentMarkovMeanHybridBVPath_density_continuousTestIntegral_eq]
  exact
    (tendsto_finsetSum Finset.univ
      fun (source : {source : State // source ≠ observed}) _hSource =>
      tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_of_empiricalInitial_weight_tendsto
        initialConfiguration targetDensity rates duration hWeight
          ⟨(source, observed), source.property⟩ test).sub
      (tendsto_finsetSum Finset.univ
        fun (target : {target : State // target ≠ observed}) _hTarget =>
        tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_of_empiricalInitial_weight_tendsto
          initialConfiguration targetDensity rates duration hWeight
            ⟨(observed, target), target.property.symm⟩ test)

/-- Coordinatewise convergence of deterministic empirical initial densities implies convergence
of the complete heterogeneous centers in the fixed-rate strong-`L1` plus open-interval vague
derivative topology. -/
theorem
tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_of_empiricalInitial_weight_tendsto
    (initialConfiguration : (successorIndex : ℕ) → Fin (successorIndex + 1) → State)
    (targetDensity : FiniteStateProbabilityDensity State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (hWeight : ∀ state, Tendsto
      (fun successorIndex =>
        ((finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)).weight state : ℝ))
      atTop (𝓝 (targetDensity.weight state : ℝ))) :
    Tendsto
      (fun successorIndex =>
        finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex (initialConfiguration successorIndex) rates duration)
      atTop
      (𝓝 (finiteStateTimeDependentMarkovMeanHybridBVPath
        targetDensity.probabilityMassFunction rates duration).toDerivativePath) := by
  apply FiniteIntervalL1DerivativePath.tendsto_iff.mpr
  constructor
  · have hL1 :=
      tendsto_finiteStateTimeDependentMarkovMeanHybridBVL1Path_of_weight_tendsto
        (fun successorIndex => finiteIIDEmpiricalProbabilityDensity successorIndex
          (initialConfiguration successorIndex)) targetDensity rates duration hWeight
    rw [show (fun successorIndex =>
        (finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex (initialConfiguration successorIndex) rates duration).toL1Path) =
        fun successorIndex => finiteStateTimeDependentMarkovMeanHybridBVL1Path
          (finiteIIDEmpiricalProbabilityDensity successorIndex
            (initialConfiguration successorIndex)).probabilityMassFunction rates duration by
      funext successorIndex
      rw [
        finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_toL1Path,
        finiteStateTimeDependentMarkovMeanDensityDirectionalFlowL1Path_eq_empiricalInitial_meanHybridBVL1Path]]
    exact hL1
  · intro coordinate test
    cases coordinate with
    | inl observed =>
        exact
          tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_density_continuousTestIntegral_of_empiricalInitial_weight_tendsto
            initialConfiguration targetDensity rates duration hWeight observed test.1
    | inr edge =>
        exact
          tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_flow_continuousTestIntegral_of_empiricalInitial_weight_tendsto
            initialConfiguration targetDensity rates duration hWeight edge test.1

/-- Canonical rounded deterministic initial configurations have centers converging to the
requested fixed-rate target-initial Markov mean hybrid path. -/
theorem
tendsto_finiteStateTimeDependentMarkovRoundedInitialReplicaMeanL1DerivativePath
    (targetDensity : FiniteStateProbabilityDensity State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0) :
    Tendsto
      (fun successorIndex =>
        finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath
          successorIndex
          (finiteStateProbabilityDensityRoundedInitialConfiguration
            targetDensity successorIndex)
          rates duration)
      atTop
      (𝓝 (finiteStateTimeDependentMarkovMeanHybridBVPath
        targetDensity.probabilityMassFunction rates duration).toDerivativePath) := by
  apply
    tendsto_finiteStateTimeDependentMarkovDeterministicReplicaMeanL1DerivativePath_of_empiricalInitial_weight_tendsto
  intro state
  simpa only [finiteIIDEmpiricalProbabilityDensity_roundedInitialConfiguration] using
    finiteStateProbabilityDensityRoundedPositiveEmpiricalType_weight_tendsto
      targetDensity state

/-- Canonical rounded deterministic initial configurations concentrate in every open
neighborhood of their exact fixed-rate Markov mean hybrid path.  The rate and horizon are fixed
before the particle-number limit. -/
theorem
tendsto_measureReal_finiteStateTimeDependentMarkovRoundedInitialReplica_totalHybridObservation_not_mem_open_zero
    [TopologicalSpace State] [DiscreteTopology State] [BorelSpace State] [Nonempty State]
    (targetDensity : FiniteStateProbabilityDensity State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : ℝ≥0)
    (hDuration : 0 < duration)
    {openSet : Set (FiniteIntervalL1DerivativePath
      (EmpiricalDensityDirectionalFlowCoordinate State) (duration : ℝ))}
    (hOpen : IsOpen openSet)
    (hMean :
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        targetDensity.probabilityMassFunction rates duration).toDerivativePath ∈ openSet) :
    Tendsto
      (fun successorIndex ↦
        let law :=
          (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
            (finiteStateProbabilityDensityRoundedInitialConfiguration
              targetDensity successorIndex)
            rates duration).toMeasure
        law.real {histories |
          (PositiveFiniteJumpHistoryReplicas.empiricalDensityDirectionalFlowTotalHybridBVObservation
            successorIndex duration histories).toDerivativePath ∉ openSet})
      atTop (nhds 0) := by
  exact
    tendsto_measureReal_finiteStateTimeDependentMarkovDeterministicReplica_totalHybridObservation_not_mem_open_zero
      (fun successorIndex ↦
        finiteStateProbabilityDensityRoundedInitialConfiguration targetDensity successorIndex)
      rates duration hDuration
      (finiteStateTimeDependentMarkovMeanHybridBVPath
        targetDensity.probabilityMassFunction rates duration).toDerivativePath
      (tendsto_finiteStateTimeDependentMarkovRoundedInitialReplicaMeanL1DerivativePath
        targetDensity rates duration)
      hOpen hMean

end

end FiniteMarkovProcesses.Probability
