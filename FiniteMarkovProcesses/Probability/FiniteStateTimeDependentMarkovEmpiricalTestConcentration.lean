/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteMarkovProcesses.Probability.FiniteIndependentVarianceConcentration
import
  FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovDeterministicInitialReplication
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovStateObservationMoment
import FiniteMarkovProcesses.Probability.FiniteStateTimeDependentMarkovTransitionTestMoment

/-!
# Empirical-test concentration for time-dependent Markov jump replicas

This module composes the normalized heterogeneous time-dependent replica source with the generic
finite-independent variance estimate.  The main theorem applies to any one-history observable
whose second moment and variance are controlled uniformly over every Dirac initial state.  Two
specializations give the density and directional-flow test coordinates generating the frozen
hybrid topology.

The centering retains the exact sum of coordinate-specific source means.  No identical-law or
exchangeability assumption is introduced.

## Main results

- `finiteStateTimeDependentMarkovDeterministicInitialReplica_testSumDeviation_le`.
- `finiteStateTimeDependentMarkovDeterministicInitialReplica_stateTestSumDeviation_le`.
- `finiteStateTimeDependentMarkovDeterministicInitialReplica_transitionTestSumDeviation_le`.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- A uniformly second-moment-controlled one-history observable satisfies an explicit
heterogeneous empirical-sum deviation bound under every prospectively supplied initial
configuration. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplica_testSumDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observable : FiniteJumpHistory State → ℝ) (hObservable : Measurable observable)
    (varianceBound : ℝ)
    (hMemLp : ∀ state, MemLp observable 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure state) rates duration))
    (hVariance : ∀ state,
      variance observable
          (finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure state) rates duration) ≤ varianceBound)
    {deviation : ℝ} (hDeviation : 0 < deviation) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories |
        deviation ≤
          |∑ replica, observable (histories replica) -
            ∑ replica, ∫ history, observable history
              ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                (PMF.pure (initialConfiguration replica)) rates duration|} ≤
      ENNReal.ofReal
        ((replicaCount : ℝ) * varianceBound / deviation ^ 2) := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let coordinateObservable : Fin replicaCount →
      (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
    fun replica histories ↦ observable (histories replica)
  have hIndependent : iIndepFun coordinateObservable law := by
    have hHistoryIndependent :=
      finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinates_iIndepFun
        initialConfiguration rates duration
    have hComposed := iIndepFun.comp
      (β := fun _ : Fin replicaCount ↦ FiniteJumpHistory State)
      (γ := fun _ : Fin replicaCount ↦ ℝ) hHistoryIndependent
      (fun _ history ↦ observable history) (fun _ ↦ hObservable)
    simpa only [law, coordinateObservable, Function.comp_def] using hComposed
  have hCoordinateMemLp : ∀ replica, MemLp (coordinateObservable replica) 2 law := by
    intro replica
    have hSingle := hMemLp (initialConfiguration replica)
    rw [← finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
      initialConfiguration rates duration replica] at hSingle
    exact hSingle.comp_of_map (measurable_pi_apply replica).aemeasurable
  have hCoordinateVariance : ∀ replica,
      variance (coordinateObservable replica) law ≤ varianceBound := by
    intro replica
    calc
      variance (coordinateObservable replica) law =
          variance observable (Measure.map (Function.eval replica) law) := by
        exact (variance_map hObservable.aemeasurable
          (measurable_pi_apply replica).aemeasurable).symm
      _ = variance observable
          (finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration) := by
        rw [finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
          initialConfiguration rates duration replica]
      _ ≤ varianceBound := hVariance (initialConfiguration replica)
  have hCoordinateIntegral (replica : Fin replicaCount) :
      ∫ histories, coordinateObservable replica histories ∂law =
        ∫ history, observable history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration := by
    calc
      ∫ histories, coordinateObservable replica histories ∂law =
          ∫ history, observable history ∂Measure.map (Function.eval replica) law := by
        exact (integral_map (measurable_pi_apply replica).aemeasurable
          hObservable.aestronglyMeasurable).symm
      _ = ∫ history, observable history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration := by
        rw [finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
          initialConfiguration rates duration replica]
  have hConcentration := measure_sum_deviation_ge_le_of_iIndepFun_of_variance_le
    law coordinateObservable hCoordinateMemLp hIndependent varianceBound
    hCoordinateVariance hDeviation
  simpa only [law, coordinateObservable, hCoordinateIntegral, Fintype.card_fin] using
    hConcentration

/-- The expected absolute centered deviation of a heterogeneous empirical observable sum has
the explicit square-root variance bound. -/
theorem finiteStateTimeDependentMarkovDeterministicReplica_testSumExpectedAbsDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (observable : FiniteJumpHistory State → ℝ) (hObservable : Measurable observable)
    (varianceBound : ℝ)
    (hMemLp : ∀ state, MemLp observable 2
      (finiteStateTimeDependentMarkovReducedHistoryMeasure
        (PMF.pure state) rates duration))
    (hVariance : ∀ state,
      variance observable
          (finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure state) rates duration) ≤ varianceBound) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories,
        |∑ replica, observable (histories replica) -
          ∑ replica, ∫ history, observable history
            ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
              (PMF.pure (initialConfiguration replica)) rates duration| ∂law) ≤
      Real.sqrt ((replicaCount : ℝ) * varianceBound) := by
  dsimp only
  let law :=
    (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration rates duration).toMeasure
  let coordinateObservable : Fin replicaCount →
      (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
    fun replica histories ↦ observable (histories replica)
  have hIndependent : iIndepFun coordinateObservable law := by
    have hHistoryIndependent :=
      finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinates_iIndepFun
        initialConfiguration rates duration
    have hComposed := iIndepFun.comp
      (β := fun _ : Fin replicaCount ↦ FiniteJumpHistory State)
      (γ := fun _ : Fin replicaCount ↦ ℝ) hHistoryIndependent
      (fun _ history ↦ observable history) (fun _ ↦ hObservable)
    simpa only [law, coordinateObservable, Function.comp_def] using hComposed
  have hCoordinateMemLp : ∀ replica, MemLp (coordinateObservable replica) 2 law := by
    intro replica
    have hSingle := hMemLp (initialConfiguration replica)
    rw [← finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
      initialConfiguration rates duration replica] at hSingle
    exact hSingle.comp_of_map (measurable_pi_apply replica).aemeasurable
  have hCoordinateVariance : ∀ replica,
      variance (coordinateObservable replica) law ≤ varianceBound := by
    intro replica
    calc
      variance (coordinateObservable replica) law =
          variance observable (Measure.map (Function.eval replica) law) := by
        exact (variance_map hObservable.aemeasurable
          (measurable_pi_apply replica).aemeasurable).symm
      _ = variance observable
          (finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration) := by
        rw [finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
          initialConfiguration rates duration replica]
      _ ≤ varianceBound := hVariance (initialConfiguration replica)
  have hCoordinateIntegral (replica : Fin replicaCount) :
      ∫ histories, coordinateObservable replica histories ∂law =
        ∫ history, observable history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration := by
    calc
      ∫ histories, coordinateObservable replica histories ∂law =
          ∫ history, observable history ∂Measure.map (Function.eval replica) law := by
        exact (integral_map (measurable_pi_apply replica).aemeasurable
          hObservable.aestronglyMeasurable).symm
      _ = ∫ history, observable history
          ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
            (PMF.pure (initialConfiguration replica)) rates duration := by
        rw [finiteStateTimeDependentMarkovDeterministicInitialReplica_coordinate_map
          initialConfiguration rates duration replica]
  have hExpectedDeviation :=
    integral_abs_sum_sub_mean_le_sqrt_card_mul_varianceBound
      law coordinateObservable hCoordinateMemLp hIndependent varianceBound
      hCoordinateVariance
  simpa only [law, coordinateObservable, hCoordinateIntegral, Fintype.card_fin] using
    hExpectedDeviation

/-- Fixed-time empirical state membership concentrates around the exact heterogeneous sum of its
coordinate source means. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplica_stateTestSumDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) (observed : State) {deviation : ℝ} (hDeviation : 0 < deviation) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories |
        deviation ≤
          |∑ replica,
              finiteJumpHistoryStateMembershipAtTime time observed (histories replica) -
            ∑ replica, ∫ history,
              finiteJumpHistoryStateMembershipAtTime time observed history
              ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                (PMF.pure (initialConfiguration replica)) rates duration|} ≤
      ENNReal.ofReal ((replicaCount : ℝ) / deviation ^ 2) := by
  simpa only [mul_one] using
    finiteStateTimeDependentMarkovDeterministicInitialReplica_testSumDeviation_le
      initialConfiguration rates duration
      (finiteJumpHistoryStateMembershipAtTime time observed)
      (measurable_finiteJumpHistoryStateMembershipAtTime time observed) 1
      (fun state ↦ memLp_two_finiteJumpHistoryStateMembershipAtTime
        (PMF.pure state) rates duration time observed)
      (fun state ↦ variance_finiteJumpHistoryStateMembershipAtTime_le_one
        (PMF.pure state) rates duration time observed) hDeviation

/-- The expected absolute centered sum of fixed-time state memberships is at most the square root
of the replica count. -/
theorem finiteStateTimeDependentMarkovDeterministicReplica_stateTestExpectedAbsDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (time : ℝ) (observed : State) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories,
        |∑ replica,
            finiteJumpHistoryStateMembershipAtTime time observed (histories replica) -
          ∑ replica, ∫ history,
            finiteJumpHistoryStateMembershipAtTime time observed history
            ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
              (PMF.pure (initialConfiguration replica)) rates duration| ∂law) ≤
      Real.sqrt (replicaCount : ℝ) := by
  simpa only [mul_one] using
    finiteStateTimeDependentMarkovDeterministicReplica_testSumExpectedAbsDeviation_le
      initialConfiguration rates duration
      (finiteJumpHistoryStateMembershipAtTime time observed)
      (measurable_finiteJumpHistoryStateMembershipAtTime time observed) 1
      (fun state ↦ memLp_two_finiteJumpHistoryStateMembershipAtTime
        (PMF.pure state) rates duration time observed)
      (fun state ↦ variance_finiteJumpHistoryStateMembershipAtTime_le_one
        (PMF.pure state) rates duration time observed)

/-- Every bounded directional transition test concentrates around the exact heterogeneous sum of
its coordinate source means, with the explicit common-clock variance constant. -/
theorem finiteStateTimeDependentMarkovDeterministicInitialReplica_transitionTestSumDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (test : ℝ → State → State → ℝ)
    (hTest : ∀ source target, Measurable fun time ↦ test time source target)
    {testBound : ℝ} (hTestBoundNonnegative : 0 ≤ testBound)
    (hTestBound : ∀ time source target, |test time source target| ≤ testBound)
    {deviation : ℝ} (hDeviation : 0 < deviation) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    law {histories |
        deviation ≤
          |∑ replica, finiteJumpHistoryTransitionTestSum test (histories replica) -
            ∑ replica, ∫ history, finiteJumpHistoryTransitionTestSum test history
              ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
                (PMF.pure (initialConfiguration replica)) rates duration|} ≤
      ENNReal.ofReal
        ((replicaCount : ℝ) *
          (testBound ^ 2 *
            (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
              (Real.exp 1 - 1)))) / deviation ^ 2) := by
  exact finiteStateTimeDependentMarkovDeterministicInitialReplica_testSumDeviation_le
    initialConfiguration rates duration (finiteJumpHistoryTransitionTestSum test)
    (measurable_finiteJumpHistoryTransitionTestSum test hTest)
    (testBound ^ 2 *
      (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
        (Real.exp 1 - 1))))
    (fun state ↦ memLp_two_finiteJumpHistoryTransitionTestSum
      (PMF.pure state) rates duration test hTest hTestBoundNonnegative hTestBound)
    (fun state ↦ variance_finiteJumpHistoryTransitionTestSum_le
      (PMF.pure state) rates duration test hTest hTestBoundNonnegative hTestBound)
    hDeviation

/-- The expected absolute centered sum of every bounded directional transition test has the
explicit common-clock square-root variance bound. -/
theorem finiteStateTimeDependentMarkovDeterministicReplica_transitionTestExpectedAbsDeviation_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (rates : FiniteStateTimeDependentMarkovRate State) (duration : NNReal)
    (test : ℝ → State → State → ℝ)
    (hTest : ∀ source target, Measurable fun time ↦ test time source target)
    {testBound : ℝ} (hTestBoundNonnegative : 0 ≤ testBound)
    (hTestBound : ∀ time source target, |test time source target| ≤ testBound) :
    let law :=
      (finiteStateTimeDependentMarkovDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration rates duration).toMeasure
    (∫ histories,
        |∑ replica, finiteJumpHistoryTransitionTestSum test (histories replica) -
          ∑ replica, ∫ history, finiteJumpHistoryTransitionTestSum test history
            ∂finiteStateTimeDependentMarkovReducedHistoryMeasure
              (PMF.pure (initialConfiguration replica)) rates duration| ∂law) ≤
      Real.sqrt
        ((replicaCount : ℝ) *
          (testBound ^ 2 *
            (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
              (Real.exp 1 - 1))))) := by
  exact
    finiteStateTimeDependentMarkovDeterministicReplica_testSumExpectedAbsDeviation_le
      initialConfiguration rates duration (finiteJumpHistoryTransitionTestSum test)
      (measurable_finiteJumpHistoryTransitionTestSum test hTest)
      (testBound ^ 2 *
        (2 * Real.exp (((rates.uniformizationRate * duration : NNReal) : ℝ) *
          (Real.exp 1 - 1))))
      (fun state ↦ memLp_two_finiteJumpHistoryTransitionTestSum
        (PMF.pure state) rates duration test hTest hTestBoundNonnegative hTestBound)
      (fun state ↦ variance_finiteJumpHistoryTransitionTestSum_le
        (PMF.pure state) rates duration test hTest hTestBoundNonnegative hTestBound)

end

end FiniteMarkovProcesses.Probability
