/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module
public import FiniteMarkovProcesses.Analysis.BoundedVariation.FiniteIntervalL1Path
public import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovEmpiricalTestConcentration
public import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovMeanContinuity
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Strong-L1 concentration of empirical density paths

This module integrates the exact fixed-time heterogeneous replica deviation bound over the
physical interval.  Joint history--time measurability and Fubini yield an explicit expected
strong-`L1` bound without discretizing time or truncating the finite-history carrier.

## Main results

- `finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime`.
- `integral_integral_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_le`.
- `finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime`.
- `integral_integral_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_le`.
-/

@[expose] public section

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Absolute deviation of one heterogeneous replica state-count coordinate from the exact sum
of its means at one physical time. -/
noncomputable def finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observed : State)
    (histories : Fin replicaCount → FiniteJumpHistory State) (time : ℝ) : ℝ :=
  |∑ replica,
      finiteJumpHistoryStateMembershipAtTime time observed (histories replica) -
    ∑ replica,
      finiteStateTimeDependentMarkovMeanDensityAt
        (PMF.pure (initialConfiguration replica)) rates duration time observed|

/-- The heterogeneous state-count deviation is jointly measurable in the complete replica
history family and physical time. -/
theorem measurable_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_uncurry
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observed : State) :
    Measurable fun data :
        (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
        initialConfiguration rates duration observed data.1 data.2 := by
  unfold finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
  have hObserved : Measurable fun data :
      (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      ∑ replica,
        finiteJumpHistoryStateMembershipAtTime
          data.2 observed (data.1 replica) := by
    apply Finset.measurable_sum
    intro replica _hReplica
    have hPair : Measurable fun data :
        (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      (data.1 replica, data.2) := by fun_prop
    exact
      (measurable_finiteJumpHistoryStateMembershipAtTime_uncurry observed).comp hPair
  have hMean : Measurable fun data :
      (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      ∑ replica,
        finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure (initialConfiguration replica)) rates duration data.2 observed := by
    apply Finset.measurable_sum
    intro replica _hReplica
    exact (measurable_finiteStateTimeDependentMarkovMeanDensityAt
      (PMF.pure (initialConfiguration replica)) rates duration observed).comp measurable_snd
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hObserved.sub hMean).norm

/-- The absolute state-count deviation never exceeds the number of replicas. -/
theorem finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observed : State)
    (histories : Fin replicaCount → FiniteJumpHistory State) (time : ℝ) :
    finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
        initialConfiguration rates duration observed histories time ≤
      (replicaCount : ℝ) := by
  have hObservedNonnegative :
      0 ≤ ∑ replica,
        finiteJumpHistoryStateMembershipAtTime time observed (histories replica) :=
    Finset.sum_nonneg fun replica _hReplica ↦
      (finiteJumpHistoryStateMembershipAtTime_mem_Icc
        time observed (histories replica)).1
  have hObservedUpper :
      (∑ replica,
        finiteJumpHistoryStateMembershipAtTime time observed (histories replica)) ≤
        (replicaCount : ℝ) := by
    calc
      (∑ replica,
          finiteJumpHistoryStateMembershipAtTime time observed (histories replica)) ≤
          ∑ _replica : Fin replicaCount, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro replica _hReplica
        exact (finiteJumpHistoryStateMembershipAtTime_mem_Icc
          time observed (histories replica)).2
      _ = (replicaCount : ℝ) := by simp
  have hMeanNonnegative :
      0 ≤ ∑ replica,
        finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure (initialConfiguration replica)) rates duration time observed :=
    Finset.sum_nonneg fun replica _hReplica ↦
      (finiteStateTimeDependentMarkovMeanDensityAt_mem_Icc
        (PMF.pure (initialConfiguration replica)) rates duration time observed).1
  have hMeanUpper :
      (∑ replica,
        finiteStateTimeDependentMarkovMeanDensityAt
          (PMF.pure (initialConfiguration replica)) rates duration time observed) ≤
        (replicaCount : ℝ) := by
    calc
      (∑ replica,
          finiteStateTimeDependentMarkovMeanDensityAt
            (PMF.pure (initialConfiguration replica)) rates duration time observed) ≤
          ∑ _replica : Fin replicaCount, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro replica _hReplica
        exact (finiteStateTimeDependentMarkovMeanDensityAt_mem_Icc
          (PMF.pure (initialConfiguration replica)) rates duration time observed).2
      _ = (replicaCount : ℝ) := by simp
  unfold finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
  rw [abs_le]
  constructor <;> linarith

/-- The joint history--time state-count deviation is integrable under the exact replica law and
physical-time volume. -/
theorem integrable_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_uncurry
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observed : State) :
    Integrable
      (fun data : (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
        finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
          initialConfiguration rates duration observed data.1 data.2)
      ((finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
          initialConfiguration rates duration).toMeasure.prod
        (finiteOpenIntervalVolume (duration : ℝ))) := by
  apply Integrable.of_bound
    (measurable_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_uncurry
      initialConfiguration rates duration observed).aestronglyMeasurable
    (replicaCount : ℝ)
  filter_upwards [] with data
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_le
      initialConfiguration rates duration observed data.1 data.2
  · unfold finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
    exact abs_nonneg _

/-- Integrating the fixed-time square-root deviation estimate over the physical interval gives
an explicit expected strong-`L1` state-count bound. -/
theorem
integral_integral_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observed : State) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories, ∫ time,
        finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
          initialConfiguration rates duration observed histories time
          ∂finiteOpenIntervalVolume (duration : ℝ) ∂law) ≤
      (duration : ℝ) * Real.sqrt (replicaCount : ℝ) := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let physicalTime := finiteOpenIntervalVolume (duration : ℝ)
  let : IsProbabilityMeasure law :=
    by dsimp only [law]; infer_instance
  have hJointMeasurable : Measurable fun data :
      (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
        finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
          initialConfiguration rates duration observed data.1 data.2 :=
    measurable_finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_uncurry
      initialConfiguration rates duration observed
  have hJointIntegrable : Integrable
      (fun data : (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
        finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
          initialConfiguration rates duration observed data.1 data.2)
      (law.prod physicalTime) := by
    apply Integrable.of_bound hJointMeasurable.aestronglyMeasurable (replicaCount : ℝ)
    filter_upwards [] with data
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime_le
        initialConfiguration rates duration observed data.1 data.2
    · exact abs_nonneg _
  have hPointwise (time : ℝ) :
      (∫ histories,
          finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
            initialConfiguration rates duration observed histories time ∂law) ≤
        Real.sqrt (replicaCount : ℝ) := by
    have hDeviation :=
      finiteStateTimeDependentMarkovDeterministicReplica_stateTestExpectedAbsDeviation_le
        initialConfiguration rates duration time observed
    simpa only [law,
      finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime,
      finiteStateTimeDependentMarkovMeanDensityAt] using hDeviation
  calc
    (∫ histories, ∫ time,
        finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
          initialConfiguration rates duration observed histories time
          ∂physicalTime ∂law) =
        ∫ time, ∫ histories,
          finiteStateTimeDependentMarkovReplicaStateSumDeviationAtTime
            initialConfiguration rates duration observed histories time
            ∂law ∂physicalTime :=
      integral_integral_swap hJointIntegrable
    _ ≤ ∫ _time : ℝ, Real.sqrt (replicaCount : ℝ) ∂physicalTime := by
      apply integral_mono hJointIntegrable.integral_prod_right (integrable_const _)
      exact hPointwise
    _ = (duration : ℝ) * Real.sqrt (replicaCount : ℝ) := by
      rw [integral_const, smul_eq_mul]
      change (physicalTime Set.univ).toReal * Real.sqrt (replicaCount : ℝ) = _
      rw [show physicalTime Set.univ = ENNReal.ofReal (duration : ℝ) by
        exact finiteOpenIntervalVolume_apply_univ (duration : ℝ)]
      rw [ENNReal.toReal_ofReal duration.coe_nonneg]

/-- Absolute deviation of one heterogeneous cumulative directional-flow count from the exact sum
of its means at one physical time. -/
noncomputable def finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (source target : State)
    (histories : Fin replicaCount → FiniteJumpHistory State) (time : ℝ) : ℝ :=
  |∑ replica,
      ((histories replica).directedTransitionCountAtTime time source target : ℝ) -
    ∑ replica,
      finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        (PMF.pure (initialConfiguration replica)) rates duration time source target|

/-- The heterogeneous cumulative one-way-flow deviation is jointly measurable in the complete
replica history family and physical time. -/
theorem
measurable_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_uncurry
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (source target : State) :
    Measurable fun data :
        (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
        initialConfiguration rates duration source target data.1 data.2 := by
  unfold finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
  have hObserved : Measurable fun data :
      (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      ∑ replica,
        ((data.1 replica).directedTransitionCountAtTime
          data.2 source target : ℝ) := by
    apply Finset.measurable_sum
    intro replica _hReplica
    have hPair : Measurable fun data :
        (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      (data.1 replica, data.2) := by fun_prop
    have hCountMeasurable : Measurable fun data :
        FiniteJumpHistory State × ℝ ↦
      (data.1.directedTransitionCountAtTime data.2 source target : ℝ) :=
      FiniteJumpHistory.measurable_real_directedTransitionCountAtTime_uncurry
        (State := State) source target
    simpa only [Function.comp_def] using hCountMeasurable.comp hPair
  have hMean : Measurable fun data :
      (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
      ∑ replica,
        finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
          (PMF.pure (initialConfiguration replica)) rates duration
            data.2 source target := by
    apply Finset.measurable_sum
    intro replica _hReplica
    exact
      (measurable_finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
        (PMF.pure (initialConfiguration replica)) rates duration source target).comp
          measurable_snd
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hObserved.sub hMean).norm

/-- The expected absolute centered cumulative directional-flow sum at one time has the common
clock square-root variance bound. -/
theorem
integral_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (source target : State) (time : ℝ) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories,
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target histories time ∂law) ≤
      Real.sqrt
        ((replicaCount : ℝ) *
          (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
            (Real.exp 1 - 1)))) := by
  dsimp only
  have hDeviation :=
    finiteStateTimeDependentMarkovDeterministicReplica_transitionTestExpectedAbsDeviation_le
      initialConfiguration rates duration
      (finiteStateTransitionAtOrBeforeTest time source target)
      (fun eventSource eventTarget ↦
        measurable_finiteStateTransitionAtOrBeforeTest
          time source target eventSource eventTarget)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (fun eventTime eventSource eventTarget ↦
        abs_finiteStateTransitionAtOrBeforeTest_le_one
          time source target eventSource eventTarget eventTime)
  change
    (∫ histories,
      |∑ replica,
          ((histories replica).directedTransitionCountAtTime time source target : ℝ) -
        ∑ replica, ∫ history,
          (history.directedTransitionCountAtTime time source target : ℝ)
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration|
      ∂(finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure) ≤ _
  simpa only [finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime,
    finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt,
    finiteJumpHistoryTransitionTestSum_transitionAtOrBefore_eq,
    one_pow, one_mul] using hDeviation

/-- The joint history--time cumulative directional-flow deviation is integrable under the exact
replica law and physical-time volume. -/
theorem
integrable_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_uncurry
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (source target : State) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    Integrable
      (fun data : (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target data.1 data.2)
      (law.prod (finiteOpenIntervalVolume (duration : ℝ))) := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let physicalTime := finiteOpenIntervalVolume (duration : ℝ)
  let varianceRoot :=
    Real.sqrt
      ((replicaCount : ℝ) *
        (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1))))
  let : IsProbabilityMeasure law := by dsimp only [law]; infer_instance
  have hJointMeasurable : Measurable fun data :
      (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target data.1 data.2 :=
    measurable_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_uncurry
      initialConfiguration rates duration source target
  have hSectionIntegrable (time : ℝ) : Integrable
      (fun histories : Fin replicaCount → FiniteJumpHistory State ↦
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target histories time) law := by
    have hCoordinateIntegrable (replica : Fin replicaCount) : Integrable
        (fun histories : Fin replicaCount → FiniteJumpHistory State ↦
          ((histories replica).directedTransitionCountAtTime
            time source target : ℝ)) law := by
      have hSingle :=
        memLp_two_finiteStateTimeDependentMarkovDirectedTransitionCountAtTime
          (PMF.pure (initialConfiguration replica)) rates duration time source target
      rw [← finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
        initialConfiguration rates duration replica] at hSingle
      exact (hSingle.comp_of_map
        (measurable_pi_apply replica).aemeasurable).integrable one_le_two
    have hObservedIntegrable : Integrable
        (fun histories : Fin replicaCount → FiniteJumpHistory State ↦
          ∑ replica,
            ((histories replica).directedTransitionCountAtTime
              time source target : ℝ)) law :=
      integrable_finsetSum Finset.univ fun replica _hReplica ↦
        hCoordinateIntegrable replica
    have hCenteredIntegrable := hObservedIntegrable.sub
      (integrable_const
        (∑ replica,
          finiteStateTimeDependentMarkovMeanCumulativeDirectionalFlowAt
            (PMF.pure (initialConfiguration replica)) rates duration
              time source target))
    simpa only [finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime,
      Real.norm_eq_abs, Pi.sub_apply] using hCenteredIntegrable.norm
  have hPointwise (time : ℝ) :
      (∫ histories,
          finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
            initialConfiguration rates duration source target histories time ∂law) ≤
        varianceRoot :=
    integral_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_le
      initialConfiguration rates duration source target time
  apply (integrable_prod_iff' hJointMeasurable.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall hSectionIntegrable
  · have hExpectedMeasurable : AEStronglyMeasurable
        (fun time : ℝ ↦ ∫ histories,
          ‖finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
            initialConfiguration rates duration source target histories time‖ ∂law)
        physicalTime :=
      hJointMeasurable.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    apply (integrable_const varianceRoot).mono' hExpectedMeasurable
    filter_upwards [] with time
    have hNonnegative : 0 ≤ ∫ histories,
        ‖finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target histories time‖ ∂law :=
      integral_nonneg fun _histories ↦ norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hNonnegative]
    have hNormIntegralEq :
        (∫ histories,
          ‖finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
            initialConfiguration rates duration source target histories time‖ ∂law) =
          ∫ histories,
            finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
              initialConfiguration rates duration source target histories time ∂law := by
      apply integral_congr_ae
      filter_upwards [] with histories
      rw [Real.norm_eq_abs]
      unfold finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
      exact abs_of_nonneg (abs_nonneg _)
    rw [hNormIntegralEq]
    exact hPointwise time

/-- Integrating the fixed-time cumulative-flow estimate over the physical interval gives an
explicit expected strong-`L1` directional-flow-count bound. -/
theorem
integral_integral_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (source target : State) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories, ∫ time,
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target histories time
          ∂finiteOpenIntervalVolume (duration : ℝ) ∂law) ≤
      (duration : ℝ) *
        Real.sqrt
          ((replicaCount : ℝ) *
            (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
              (Real.exp 1 - 1)))) := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let physicalTime := finiteOpenIntervalVolume (duration : ℝ)
  let varianceRoot :=
    Real.sqrt
      ((replicaCount : ℝ) *
        (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1))))
  let : IsProbabilityMeasure law := by dsimp only [law]; infer_instance
  have hPointwise (time : ℝ) :
      (∫ histories,
          finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
            initialConfiguration rates duration source target histories time ∂law) ≤
        varianceRoot := by
    exact
      integral_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_le
        initialConfiguration rates duration source target time
  have hJointIntegrable : Integrable
      (fun data : (Fin replicaCount → FiniteJumpHistory State) × ℝ ↦
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target data.1 data.2)
      (law.prod physicalTime) :=
    integrable_finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime_uncurry
      initialConfiguration rates duration source target
  calc
    (∫ histories, ∫ time,
        finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
          initialConfiguration rates duration source target histories time
          ∂physicalTime ∂law) =
        ∫ time, ∫ histories,
          finiteStateTimeDependentMarkovReplicaDirectionalFlowSumDeviationAtTime
            initialConfiguration rates duration source target histories time
            ∂law ∂physicalTime :=
      integral_integral_swap hJointIntegrable
    _ ≤ ∫ _time : ℝ, varianceRoot ∂physicalTime := by
      apply integral_mono hJointIntegrable.integral_prod_right (integrable_const _)
      exact hPointwise
    _ = (duration : ℝ) * varianceRoot := by
      rw [integral_const, smul_eq_mul]
      change (physicalTime Set.univ).toReal * varianceRoot = _
      rw [show physicalTime Set.univ = ENNReal.ofReal (duration : ℝ) by
        exact finiteOpenIntervalVolume_apply_univ (duration : ℝ)]
      rw [ENNReal.toReal_ofReal duration.coe_nonneg]

end

end FiniteMarkovProcesses.Probability
