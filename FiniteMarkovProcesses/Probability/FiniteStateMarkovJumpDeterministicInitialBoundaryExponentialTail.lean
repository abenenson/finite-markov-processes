/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import
  FiniteMarkovProcesses.Probability.FiniteStateMarkovJumpInitialBoundaryExponentialBound

/-!
# Initial-boundary exponential tails for deterministic-initial jump replicas

This module tensors the one-history initial-layer score estimate across a heterogeneous finite
replica source.  The resulting particle-speed tail is the source-side control needed to exclude
nonzero cumulative-flow data at time zero, which the relative macroscopic dual topology cannot
detect by itself.
-/

namespace FiniteMarkovProcesses.Probability

open MeasureTheory Set
open scoped ENNReal BigOperators

universe u

noncomputable section

variable {State : Type u} [Fintype State] [DecidableEq State]
  [MeasurableSpace State] [MeasurableSingletonClass State]

/-- Sum of the weighted initial-boundary jump counts across a finite replica family. -/
noncomputable def finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount
    {replicaCount : ℕ} (margin : ℝ)
    (histories : Fin replicaCount → FiniteJumpHistory State) : ℝ :=
  ∑ replica, finiteJumpHistoryInitialBoundaryWeightedJumpCount margin (histories replica)

omit [DecidableEq State] in
/-- The weighted initial-boundary jump count is measurable on the complete history carrier. -/
theorem measurable_finiteJumpHistoryInitialBoundaryWeightedJumpCount
    (margin : ℝ) :
    Measurable (finiteJumpHistoryInitialBoundaryWeightedJumpCount
      (State := State) margin) := by
  rw [measurable_sigma_iff]
  intro eventCount
  apply measurable_from_prod_countable_right
  intro _states
  unfold finiteJumpHistoryInitialBoundaryWeightedJumpCount
  apply Finset.measurable_sum
  intro index _hIndex
  exact (continuous_finiteStateMarkovJumpInitialBoundaryTimeCutoff margin).measurable.comp
    (measurable_pi_apply index)

omit [DecidableEq State] in
/-- The total weighted initial-boundary jump count is measurable on a finite replica product. -/
theorem measurable_finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount
    {replicaCount : ℕ} (margin : ℝ) :
    Measurable (finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount
      (State := State) (replicaCount := replicaCount) margin) := by
  unfold finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount
  apply Finset.measurable_sum
  intro replica _hReplica
  exact (measurable_finiteJumpHistoryInitialBoundaryWeightedJumpCount margin).comp
    (measurable_pi_apply replica)

omit [MeasurableSpace State] [MeasurableSingletonClass State] in
/-- The sum of the microscopic initial-boundary scores dominates the scaled total weighted count
minus one uniform escape budget per replica. -/
theorem finiteStateMarkovInitialBoundaryReplicaWeightedJumpScoreLowerBound
    {replicaCount : ℕ} (generator : FiniteStateMarkovGenerator State)
    {duration margin scale : ℝ}
    (hDuration : 0 ≤ duration) (hMargin : 0 < margin)
    (hLayer : 2 * margin ≤ duration) (hScale : 0 ≤ scale)
    (histories : Fin replicaCount → FiniteJumpHistory State)
    (hOrdered : ∀ replica, (histories replica).OrderedBefore duration) :
    scale * finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories -
        (replicaCount : ℝ) *
          (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
            (Real.exp scale - 1)) ≤
      ∑ replica : Fin replicaCount,
        finiteStateMarkovExponentialTimeTiltHistoryScore generator
          (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
          duration (histories replica) := by
  calc
    scale * finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories -
        (replicaCount : ℝ) *
          (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
            (Real.exp scale - 1)) =
      ∑ replica : Fin replicaCount,
        (scale * finiteJumpHistoryInitialBoundaryWeightedJumpCount margin
            (histories replica) -
          2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
            (Real.exp scale - 1)) := by
      simp only [finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount,
        Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]
    _ ≤ ∑ replica : Fin replicaCount,
        finiteStateMarkovExponentialTimeTiltHistoryScore generator
          (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale)
          duration (histories replica) := by
      apply Finset.sum_le_sum
      intro replica _hReplica
      exact finiteStateMarkovInitialBoundaryWeightedJumpScoreLowerBound generator
        hDuration hMargin hLayer hScale (histories replica) (hOrdered replica)

/-- Particle-speed Chernoff control for the total weighted number of jumps in an initial boundary
layer.  The estimate is uniform over every labelled deterministic initial configuration. -/
theorem finiteStateMarkovJumpDeterministicInitialReplicaInitialBoundaryWeightedJumpCount_gt_le
    {replicaCount : ℕ} (initialConfiguration : Fin replicaCount → State)
    (generator : FiniteStateMarkovGenerator State)
    {duration margin scale : ℝ}
    (hDuration : 0 ≤ duration) (hMargin : 0 < margin)
    (hLayer : 2 * margin ≤ duration) (hScale : 0 < scale)
    (threshold : ℝ) :
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure
        {histories |
          threshold <
            finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories} ≤
      ENNReal.ofReal (Real.exp
        ((replicaCount : ℝ) *
            (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1)) -
          scale * threshold)) := by
  let law :=
    (finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
      initialConfiguration generator duration hDuration).toMeasure
  let totalScore : (Fin replicaCount → FiniteJumpHistory State) → ℝ :=
    fun histories =>
      ∑ replica : Fin replicaCount,
        finiteStateMarkovExponentialTimeTiltHistoryScore generator
          (finiteStateMarkovJumpInitialBoundaryTransitionExponent
            margin scale hScale.le)
          duration (histories replica)
  let exponentialScore : (Fin replicaCount → FiniteJumpHistory State) → ℝ≥0∞ :=
    fun histories => ENNReal.ofReal (Real.exp (totalScore histories))
  let scoreThreshold : ℝ :=
    scale * threshold -
      (replicaCount : ℝ) *
        (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
          (Real.exp scale - 1))
  let exponentialThreshold : ℝ≥0∞ := ENNReal.ofReal (Real.exp scoreThreshold)
  have hExponentialScoreMeasurable : Measurable exponentialScore := by
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    unfold totalScore
    apply Finset.measurable_sum
    intro replica _hReplica
    exact (measurable_finiteStateMarkovExponentialTimeTiltHistoryScore generator _ duration).comp
      (measurable_pi_apply replica)
  have hExponentialThresholdPositive : exponentialThreshold ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hEventDominated :
      ∀ᵐ histories ∂law,
        histories ∈ {histories |
          threshold <
            finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories} →
        histories ∈ {histories | exponentialThreshold ≤ exponentialScore histories} := by
    filter_upwards [
      ae_orderedBefore_finiteStateMarkovJumpDeterministicInitialReplicaProbabilityMeasure
        initialConfiguration generator duration hDuration] with histories hOrdered
    intro hThreshold
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hWeightedThreshold :
        scale * threshold ≤
          scale * finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories :=
      mul_le_mul_of_nonneg_left hThreshold.le hScale.le
    exact (sub_le_sub_right hWeightedThreshold _).trans
      (finiteStateMarkovInitialBoundaryReplicaWeightedJumpScoreLowerBound generator
        hDuration hMargin hLayer hScale.le histories hOrdered)
  have hMoment :=
    lintegral_exp_sum_finiteStateMarkovExponentialTimeTiltHistoryScore_le_one
      initialConfiguration generator
      (finiteStateMarkovJumpInitialBoundaryTransitionExponent margin scale hScale.le)
      duration hDuration
  change law {histories |
      threshold < finiteJumpHistoryReplicaInitialBoundaryWeightedJumpCount margin histories} ≤ _
  calc
    _ ≤ law {histories | exponentialThreshold ≤ exponentialScore histories} :=
      measure_mono_ae hEventDominated
    _ ≤ (∫⁻ histories, exponentialScore histories ∂law) / exponentialThreshold :=
      meas_ge_le_lintegral_div hExponentialScoreMeasurable.aemeasurable
        hExponentialThresholdPositive ENNReal.ofReal_ne_top
    _ ≤ 1 / exponentialThreshold := by
      apply ENNReal.div_le_div_right
      simpa only [law, exponentialScore, totalScore] using hMoment
    _ = ENNReal.ofReal (Real.exp
        ((replicaCount : ℝ) *
            (2 * margin * (finiteStateTotalEscapeBound generator : ℝ) *
              (Real.exp scale - 1)) -
          scale * threshold)) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp 0) by norm_num]
      rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
      congr 2
      unfold scoreThreshold
      ring

end

end FiniteMarkovProcesses.Probability
